
#include "share/atspre_staload.hats"
#include "share/atspre_define.hats"

#include "../mydepies.hats"

staload UN = "prelude/SATS/unsafe.sats"

staload "./../SATS/rlist.sats"


staload B = "./../SATS/basic.sats"
staload "./../SATS/session.sats"
staload _ = "./../DATS/session.dats"
staload _ = "./../DATS/basic.dats"


viewtypedef producer(j:int) =
  loop(
      send(j,int)
    ::send(j,string)
    ::send(j,bool)
    ::rnil
  )

viewtypedef consumer(i:int) =
  loop(
      recv(i,int)
    ::recv(i,string)
    ::recv(i,bool)
    ::rnil
  )

viewtypedef protocol(i:int,j:int) =
    fork(consumer(i))
  ::fork(producer(j))
  ::rnil



extern praxi role{i,j:int}{b:bool}(!chr(i), !chw(j)): session0(protocol(i,j))



fun ploop{i:int}(sm: session0(producer(i)) | cout: chw(i)): void = let
  prval (repeat) = do_loop(sm)
  val () = chsend(sm | cout, 55)
  val () = chsend(sm | cout, "jjj")
  val () = chsend(sm | cout, true)
  prval () = repeat(sm)
  val () = $B.msleep(250ll)
in ploop(sm | cout) end


fun cloop{i:int}(sm: session0(consumer(i)) | cin: chr(i)): void = let
  prval (repeat) = do_loop(sm)
  val a = chrecv(sm | cin) val () = println!(a)
  val b = chrecv(sm | cin) val () = println!(b)
  val c = chrecv(sm | cin) val () = println!(c)
  prval () = repeat(sm)
in cloop(sm | cin)  end




implement main0() = {
  val $tup(cin,cout) = chmake1()
  prval (sm) = role(cin, cout)
  val t0 = forku(sm | llam (sm|) => cloop(sm | cin))
  val t1 = forku(sm | llam (sm|) => ploop(sm | cout))
  val () = $B.join(t0)
  val () = $B.join(t1)
  prval () = session_free(sm)
}






