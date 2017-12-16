// See LICENES.PkU for license details.
// See LICENES.MPRC for license details.

package tile

import Chisel._

case class HFPUParams(
  divSqrt: Boolean = true,
  hfmaLatency: Int =3
)
