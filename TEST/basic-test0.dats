
#include "share/atspre_staload.hats"
#include "share/atspre_define.hats"

#include "../mydepies.hats"


staload "./../SATS/basic.sats"
staload _ = "./../DATS/basic.dats"


fun loop(msg: string, n: int): void =
  if n <= 0 then
    ()
  else {
    val () = println!(msg)
    val () = msleep(100ll)
    val _ = loop(msg, n-1)
  }




implement main0() = {
  val xx = gou(loop("Hello 4", 15))
  val () = go(loop("Hello 0", 1))
  val () = go(loop("Hello 1", 1))
  val () = go(loop("Hello 2", 1))
  val () = go(loop("Hello 3", 1))
  val () = join(xx)
}




