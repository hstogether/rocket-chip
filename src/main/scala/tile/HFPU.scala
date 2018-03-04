// See LICENSE.Berkeley for license details.
// See LICENSE.SiFive for license details.

package tile

import Chisel._
import Chisel.ImplicitConversions._
import FPConstants._
import rocket.DecodeLogic
import rocket.Instructions._
import uncore.constants.MemoryOpConstants._
import config._
import util._


// Jecy
trait HasHFPUParameters {
  val fLen: Int
  val (hExpWidth, hSigWidth) = (5, 11)
  val (sExpWidth, sSigWidth) = (8, 24)
  val (dExpWidth, dSigWidth) = (11, 53)
  val floatWidths = fLen match {
    case 16 => List((hExpWidth, hSigWidth))
    case 32 => List((hExpWidth, hSigWidth),(sExpWidth, sSigWidth))
    case 64 => List((hExpWidth, hSigWidth),(sExpWidth, sSigWidth), (dExpWidth, dSigWidth))
  }
  val maxExpWidth = floatWidths.map(_._1).max
  val maxSigWidth = floatWidths.map(_._2).max
}

abstract class HFPUModule(implicit p: Parameters) extends CoreModule()(p) with HasHFPUParameters

// Jecy
class HFPToInt(implicit p: Parameters) extends FPUModule()(p) {
  class Output extends Bundle {
    val lt = Bool()
    val store = Bits(width = fLen)
    val toint = Bits(width = xLen)
    val exc = Bits(width = 5)
    override def cloneType = new Output().asInstanceOf[this.type]
  }
  val io = new Bundle {
    val in = Valid(new FPInput).flip
    val as_double = new FPInput().asOutput
    val out = Valid(new Output)
  }

  val in = Reg(new FPInput)
  val valid = Reg(next=io.in.valid)


  when (io.in.valid) {
    in := io.in.bits
  }

  val unrec_h = hardfloat.fNFromRecFN(hExpWidth, hSigWidth, in.in1).sextTo(xLen)
  val unrec_mem = unrec_h
  val unrec_int = unrec_mem

  val classify_h = ClassifyRecFN(hExpWidth, hSigWidth, in.in1)
  val classify_out = classify_h

  val dcmp = Module(new hardfloat.CompareRecFN(maxExpWidth, maxSigWidth))
  dcmp.io.a := in.in1
  dcmp.io.b := in.in2
  dcmp.io.signaling := !in.rm(1)

  io.out.bits.toint := Mux(in.rm(0), classify_out, unrec_int)
  io.out.bits.store := unrec_mem
  io.out.bits.exc := Bits(0)

  when (in.cmd === FCMD_CMP) {
    io.out.bits.toint := (~in.rm & Cat(dcmp.io.lt, dcmp.io.eq)).orR
    io.out.bits.exc := dcmp.io.exceptionFlags
  }
  when (in.cmd === FCMD_CVT_IF && in.half && in.fromhfp && in.toint) {
    val minXLen = 32
    val n = log2Ceil(xLen/minXLen) + 1
    for (i <- 0 until n) {
      val conv = Module(new hardfloat.RecFNToIN(maxExpWidth, maxSigWidth, minXLen << i))
      conv.io.in := in.in1
      conv.io.roundingMode := in.rm
      conv.io.signedOut := ~in.typ(0)
      when (in.typ.extract(log2Ceil(n), 1) === i) {
        io.out.bits.toint := conv.io.out.sextTo(xLen)
        io.out.bits.exc := Cat(conv.io.intExceptionFlags(2, 1).orR, UInt(0, 3), conv.io.intExceptionFlags(0))
      }
    }
  }

  io.out.valid := valid
  io.out.bits.lt := dcmp.io.lt
  io.as_double := in
}

// Jecy
class IntToHFP(val latency: Int)(implicit p: Parameters) extends FPUModule()(p) {
  val io = new Bundle {
    val in = Valid(new FPInput).flip
    val out = Valid(new FPResult)
  }

  val in = Pipe(io.in)

  val mux = Wire(new FPResult)
  mux.exc := Bits(0)
  mux.data := hardfloat.recFNFromFN(hExpWidth, hSigWidth, in.bits.in1)

  val intValue = {
    val minXLen = 32
    val n = log2Ceil(xLen/minXLen) + 1
    val res = Wire(init = in.bits.in1.asSInt)
    for (i <- 0 until n-1) {
      val smallInt = in.bits.in1((minXLen << i) - 1, 0)
      when (in.bits.typ.extract(log2Ceil(n), 1) === i) {
        res := Mux(in.bits.typ(0), smallInt.zext, smallInt.asSInt)
      }
    }
    res.asUInt
  }

  when (in.bits.cmd === FCMD_CVT_FI && in.bits.half && in.bits.fromint && in.bits.tohfp) {
    val l2h = Module(new hardfloat.INToRecFN(xLen, hExpWidth, hSigWidth))
    l2h.io.signedIn := ~in.bits.typ(0)
    l2h.io.in := intValue
    l2h.io.roundingMode := in.bits.rm
    mux.data := Cat(UInt((BigInt(1) << (fLen - 32)) - 1), l2h.io.out)
    mux.exc := l2h.io.exceptionFlags
   }

    io.out <> Pipe(in.valid, mux, latency-1)
}

// Jecy
class HFPToHFP(val latency: Int)(implicit p: Parameters) extends FPUModule()(p) {
    val io = new Bundle {
      val in = Valid(new FPInput).flip
      val out = Valid(new FPResult)
      val lt = Bool(INPUT) // from FPToInt
    }

    val in = Pipe(io.in)

    val signNum = Mux(in.bits.rm(1), in.bits.in1 ^ in.bits.in2, Mux(in.bits.rm(0), ~in.bits.in2, in.bits.in2))
    val fsgnj_h = Cat(signNum(32), in.bits.in1(31, 0))
    val fsgnj = fsgnj_h

    val mux = Wire(new FPResult)
    mux.exc := UInt(0)
    mux.data := fsgnj

    when (in.bits.cmd === FCMD_MINMAX) {
      def doMinMax(expWidth: Int, sigWidth: Int) = {
        val isnan1 = IsNaNRecFN(expWidth, sigWidth, in.bits.in1)
        val isnan2 = IsNaNRecFN(expWidth, sigWidth, in.bits.in2)
        val issnan1 = IsSNaNRecFN(expWidth, sigWidth, in.bits.in1)
        val issnan2 = IsSNaNRecFN(expWidth, sigWidth, in.bits.in2)
        val invalid = issnan1 || issnan2
        val isNaNOut = invalid || (isnan1 && isnan2)
        val cNaN = floatWidths.filter(_._1 >= expWidth).map(x => CanonicalNaN(x._1, x._2)).reduce(_+_)
        (isnan2 || in.bits.rm(0) =/= io.lt && !isnan1, invalid, isNaNOut, cNaN)
      }
      val (isLHS, isInvalid, isNaNOut, cNaN) = doMinMax(hExpWidth, hSigWidth)
      mux.exc := isInvalid << 4
      mux.data := Mux(isNaNOut, cNaN, Mux(isLHS, in.bits.in1, in.bits.in2))
    }

    fLen match {
      case 16 =>
      case 32 =>
      case 64 =>
        when (in.bits.cmd === FCMD_CVT_FF && in.bits.half && in.bits.fromhfp &&in.bits.tofp) { // TODO: in.bits.hflfp
          when (in.bits.single) {
            val h2s = Module(new hardfloat.RecFNToRecFN(hExpWidth, hSigWidth, sExpWidth, sSigWidth))
            h2s.io.in := in.bits.in1
            h2s.io.roundingMode := in.bits.rm
            mux.data := Cat(UInt((BigInt(1) << (fLen - 32)) - 1), h2s.io.out)
            mux.exc := h2s.io.exceptionFlags
          }.otherwise {
            val h2d = Module(new hardfloat.RecFNToRecFN(hExpWidth, hSigWidth, dExpWidth, dSigWidth))
            h2d.io.in := in.bits.in1
            h2d.io.roundingMode := in.bits.rm
            mux.data := h2d.io.out
            mux.exc := h2d.io.exceptionFlags
          }
    	}
     }

  io.out <> Pipe(in.valid, mux, latency-1)
}


// Jecy
class HFPToFP(val latency: Int)(implicit p: Parameters) extends FPUModule()(p) {
    val io = new Bundle {
      val in = Valid(new FPInput).flip
      val out = Valid(new FPResult)
      val lt = Bool(INPUT) // from FPToInt
    }

    val in = Pipe(io.in)

    val signNum = Mux(in.bits.rm(1), in.bits.in1 ^ in.bits.in2, Mux(in.bits.rm(0), ~in.bits.in2, in.bits.in2))
    val fsgnj_h = Cat(signNum(16), in.bits.in1(15, 0))
    val fsgnj = fsgnj_h

    val mux = Wire(new FPResult)
    mux.exc := UInt(0)
    mux.data := fsgnj

    when (in.bits.cmd === FCMD_MINMAX) {
      def doMinMax(expWidth: Int, sigWidth: Int) = {
        val isnan1 = IsNaNRecFN(expWidth, sigWidth, in.bits.in1)
        val isnan2 = IsNaNRecFN(expWidth, sigWidth, in.bits.in2)
        val issnan1 = IsSNaNRecFN(expWidth, sigWidth, in.bits.in1)
        val issnan2 = IsSNaNRecFN(expWidth, sigWidth, in.bits.in2)
        val invalid = issnan1 || issnan2
        val isNaNOut = invalid || (isnan1 && isnan2)
        val cNaN = floatWidths.filter(_._1 >= expWidth).map(x => CanonicalNaN(x._1, x._2)).reduce(_+_)
        (isnan2 || in.bits.rm(0) =/= io.lt && !isnan1, invalid, isNaNOut, cNaN)
      }
      val (isLHS, isInvalid, isNaNOut, cNaN) = doMinMax(hExpWidth, hSigWidth)
      mux.exc := isInvalid << 4
      mux.data := Mux(isNaNOut, cNaN, Mux(isLHS, in.bits.in1, in.bits.in2))
    }

    fLen match {
      case 16 =>
      case 32 =>
      case 64 =>
        when (in.bits.cmd === FCMD_CVT_FF && in.bits.half && in.bits.fromhfp &&in.bits.tofp) { // TODO: in.bits.hflfp
          when (in.bits.single) {
            val h2s = Module(new hardfloat.RecFNToRecFN(hExpWidth, hSigWidth, sExpWidth, sSigWidth))
            h2s.io.in := in.bits.in1
            h2s.io.roundingMode := in.bits.rm
            mux.data := Cat(UInt((BigInt(1) << (fLen - 32)) - 1), h2s.io.out)
            mux.exc := h2s.io.exceptionFlags
          }.otherwise {
            val h2d = Module(new hardfloat.RecFNToRecFN(hExpWidth, hSigWidth, dExpWidth, dSigWidth))
            h2d.io.in := in.bits.in1
            h2d.io.roundingMode := in.bits.rm
            mux.data := h2d.io.out
            mux.exc := h2d.io.exceptionFlags
          }
    	}
     }

  io.out <> Pipe(in.valid, mux, latency-1)
}


// Jecy
class FPToHFP(val latency: Int)(implicit p: Parameters) extends FPUModule()(p) {
    val io = new Bundle {
      val in = Valid(new FPInput).flip
      val out = Valid(new FPResult)
      val lt = Bool(INPUT) // from FPToInt
    }

    val in = Pipe(io.in)

    val signNum = Mux(in.bits.rm(1), in.bits.in1 ^ in.bits.in2, Mux(in.bits.rm(0), ~in.bits.in2, in.bits.in2))
    val fsgnj_h = Cat(signNum(32), in.bits.in1(31, 0))
    val fsgnj = fsgnj_h

    val mux = Wire(new FPResult)
    mux.exc := UInt(0)
    mux.data := fsgnj

    when (in.bits.cmd === FCMD_MINMAX) {
      def doMinMax(expWidth: Int, sigWidth: Int) = {
        val isnan1 = IsNaNRecFN(expWidth, sigWidth, in.bits.in1)
        val isnan2 = IsNaNRecFN(expWidth, sigWidth, in.bits.in2)
        val issnan1 = IsSNaNRecFN(expWidth, sigWidth, in.bits.in1)
        val issnan2 = IsSNaNRecFN(expWidth, sigWidth, in.bits.in2)
        val invalid = issnan1 || issnan2
        val isNaNOut = invalid || (isnan1 && isnan2)
        val cNaN = floatWidths.filter(_._1 >= expWidth).map(x => CanonicalNaN(x._1, x._2)).reduce(_+_)
        (isnan2 || in.bits.rm(0) =/= io.lt && !isnan1, invalid, isNaNOut, cNaN)
      }
      val (isLHS, isInvalid, isNaNOut, cNaN) = doMinMax(hExpWidth, hSigWidth)
      mux.exc := isInvalid << 4
      mux.data := Mux(isNaNOut, cNaN, Mux(isLHS, in.bits.in1, in.bits.in2))
    }

    fLen match {
      case 16 =>
      case 32 =>
      case 64 =>
        when (in.bits.cmd === FCMD_CVT_FF && in.bits.half && in.bits.fromfp && in.bits.tohfp) { // TODO: in.bits.hflfp
          when (in.bits.single) {
            val s2h = Module(new hardfloat.RecFNToRecFN(sExpWidth, sSigWidth, hExpWidth, hSigWidth))
            s2h.io.in := in.bits.in1
            s2h.io.roundingMode := in.bits.rm
            mux.data := Cat(UInt((BigInt(1) << (fLen - 48)) - 1), s2h.io.out)
            mux.exc := s2h.io.exceptionFlags
          }.otherwise {
            val d2h = Module(new hardfloat.RecFNToRecFN(dExpWidth, dSigWidth, hExpWidth, hSigWidth))
            d2h.io.in := in.bits.in1
            d2h.io.roundingMode := in.bits.rm
            mux.data := d2h.io.out
            mux.exc := d2h.io.exceptionFlags
          }
    	}
     }

  io.out <> Pipe(in.valid, mux, latency-1)
}

// class HFPToHFP(implicit p: Parameters) extends FPUModule()(p) {
//   class Output extends Bundle {
//     val lt = Bool()
//     val store = Bits(width = fLen)
//     val toint = Bits(width = xLen)
//     val exc = Bits(width = 5)
//     override def cloneType = new Output().asInstanceOf[this.type]
//   }
//   val io = new Bundle {
//     val in = Valid(new FPInput).flip
//     val as_double = new FPInput().asOutput
//     val out = Valid(new Output)
//   }
// 
//   val in = Reg(new FPInput)
//   val valid = Reg(next=io.in.valid)
// 
//   //def upconvert(x: UInt) = RecFNToRecFN_noncompliant(x, sExpWidth, sSigWidth, maxExpWidth, maxSigWidth)
// 
//   when (io.in.valid) {
//     in := io.in.bits
//     //if (fLen > 32) when (io.in.bits.single && !io.in.bits.ldst && io.in.bits.cmd =/= FCMD_MV_XF) {
//     //  in.in1 := upconvert(io.in.bits.in1)
//     //  in.in2 := upconvert(io.in.bits.in2)
//     }
//   }
// 
//   //val unrec_s = hardfloat.fNFromRecFN(sExpWidth, sSigWidth, in.in1).sextTo(xLen)
//   //val unrec_mem = fLen match {
//   //  case 32 => unrec_s
//   //  case 64 =>
//   //    val unrec_d = hardfloat.fNFromRecFN(dExpWidth, dSigWidth, in.in1).sextTo(xLen)
//   //    Mux(in.single, unrec_s, unrec_d)
//   //}
//   //val unrec_int = xLen match {
//   //  case 32 => unrec_s
//   //  case fLen => unrec_mem
//   //}
// 
//   val unrec_mem = hardfloat.fNFromRecFN(hExpWidth,hSigWidth, in.in1).sextTo(xLen)
//   val unrec_int = unrec_mem
//   
//   //val classify_s = ClassifyRecFN(sExpWidth, sSigWidth, in.in1)
//   //val classify_out = fLen match {
//   //  case 32 => classify_s
//   //  case 64 =>
//   //    val classify_d = ClassifyRecFN(dExpWidth, dSigWidth, in.in1)
//   //    Mux(in.single, classify_s, classify_d)
//   //}
//   val classify_out = ClassifyRecFN(hExpWidth, hSigWidth, in.in1)
// 
//   //val dcmp = Module(new hardfloat.CompareRecFN(maxExpWidth, maxSigWidth))
//   val dcmp = Module(new hardfloat.CompareRecFN(hExpWidth, hSigWidth))
//   dcmp.io.a := in.in1
//   dcmp.io.b := in.in2
//   dcmp.io.signaling := !in.rm(1)
// 
//   io.out.bits.toint := Mux(in.rm(0), classify_out, unrec_int)
//   io.out.bits.store := unrec_mem
//   io.out.bits.exc := Bits(0)
// 
//   when (in.cmd === FCMD_CMP) {
//     io.out.bits.toint := (~in.rm & Cat(dcmp.io.lt, dcmp.io.eq)).orR
//     io.out.bits.exc := dcmp.io.exceptionFlags
//   }
//   when (in.cmd === FCMD_CVT_IF) {
//     val minXLen = 32
//     val n = log2Ceil(xLen/minXLen) + 1
//     for (i <- 0 until n) {
//       val conv = Module(new hardfloat.RecFNToIN(maxExpWidth, maxSigWidth, minXLen << i))
//       conv.io.in := in.in1
//       conv.io.roundingMode := in.rm
//       conv.io.signedOut := ~in.typ(0)
//       when (in.typ.extract(log2Ceil(n), 1) === i) {
//         io.out.bits.toint := conv.io.out.sextTo(xLen)
//         io.out.bits.exc := Cat(conv.io.intExceptionFlags(2, 1).orR, UInt(0, 3), conv.io.intExceptionFlags(0))
//       }
//     }
//   }
// 
//   io.out.valid := valid
//   io.out.bits.lt := dcmp.io.lt
//   io.as_double := in
// }
// 
// 
