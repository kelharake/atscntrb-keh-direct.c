
#include "share/atspre_staload.hats"
#include "share/atspre_define.hats"


staload UN = "prelude/SATS/unsafe.sats"


#include "./../mydepies.hats"
staload "./../SATS/basic.sats"
staload "./../SATS/rlist.sats"



// Processes                                                                   
// =========================================================================== 

%{#

#ifndef ATSCNTRB_KEH_DIRECTC_BASIC_DATS
#define ATSCNTRB_KEH_DIRECTC_BASIC_DATS

int coroutine_manager_channel = -1;

void set_coroutine_manager_channel(int p) {
  coroutine_manager_channel = p;
}

int get_coroutine_manager_channel() {
  return coroutine_manager_channel;
} 

#endif

%}

extern fun set_coroutine_manager_channel(int): void = "mac#set_coroutine_manager_channel"
extern fun get_coroutine_manager_channel(): int     = "mac#get_coroutine_manager_channel"


dataviewtype manager_request =
  | request_cloptr_unmonitored of ((*requester ch*) int, (*func*) () -<lin,cloptr1> void)
  | request_cloptr_monitored of ((*func*) () -<lin,cloptr1> void)
  | request_coroutine_free of (int)


fun{} coroutine_manager(mgrch: int): void = {
  val-~Some_vt(self) = $D.chrecv_boxed<int>(mgrch)
  val () = for (;;) {
    val () = case+ $D.chrecv_boxed<manager_request>(mgrch) of
    | ~None_vt() => {
      // CATCH ERROR
      //val () = println!("coroutine manager is dying!")
      //val _ = $D.hclose(self)
      //val _ = $D.hclose(mgrch)
    }
    | ~Some_vt(req) => 
      case+ req of
      | ~request_cloptr_unmonitored(chre, f) => {
        val chs0 = $D.chmake_boxed()
        val chs1 = $D.hdup(chs0)
  
        val n = $D.go(let
          val () = f()
          val _ = cloptr_free($UN.castvwtp0{cloptr(void)}(f))
          val _ = $D.chdone(chs0)
          val _ = $D.hclose(chs0)
        in end)
      
        val cr = coroutine(n, chs1)
        val-~None_vt() = $D.chsend_boxed<coroutine>(chre, cr)
      }
      | ~request_cloptr_monitored(f) => {
        val chs0 = $D.chmake_boxed()
        val coid = $D.go(let
          val-~Some_vt(childid) = $D.chrecv_boxed<int>(chs0)
          //val () = print!("childid is: ")
          //val () = println!($UN.cast{int}(childid))
          val () = f()
          val _ = cloptr_free($UN.castvwtp0{cloptr(void)}(f))
          val _ = $D.chdone(chs0)
          val _ = $D.hclose(chs0)
          val-~None_vt() = $D.chsend_boxed<manager_request>(mgrch, request_coroutine_free(childid))
          //val _ = $D.hdone(childid,~1ll)
          //val _ = $D.hclose(childid)
        in end)
        val-~None_vt() = $D.chsend_boxed<int>(chs0, coid)
      }
      | ~request_coroutine_free(childid) => {
          val _ = $D.hdone(childid,~1ll)
          val _ = $D.hclose(childid)
      }
  }
}

fun{} maybe_spawn_coroutine_manager_and_get_channel(): int = let
  val chidm = get_coroutine_manager_channel()
in
  if chidm <> ~1 then
    chidm
  else
    chid where {
    val chid       = $D.chmake_boxed()
    val ()         = set_coroutine_manager_channel(chid)
    val coid       = $D.go(coroutine_manager(chid))
    val-~None_vt() = $D.chsend_boxed<int>(chid, coid)
  }
end


implement go_cloptr_unmonitored<>(f) = let
  val chmg = maybe_spawn_coroutine_manager_and_get_channel()
  val chre = $D.chmake_boxed()
  val-~None_vt() = $D.chsend_boxed<manager_request>(chmg, request_cloptr_unmonitored(chre,f))
  val-~Some_vt(cr) = $D.chrecv_boxed<coroutine>(chre)
  val _ = $D.hclose(chre)
in
  cr
end


implement go_cloptr_monitored<>(f) = let
  val chmg = maybe_spawn_coroutine_manager_and_get_channel()
  val-~None_vt() = $D.chsend_boxed<manager_request>(chmg, request_cloptr_monitored(f))
in
  ()
end

implement join<>(cr) = let
  val ~coroutine(h,s) = cr
  val-~None_vt() = $D.chrecv_boxed<bool>(s)
  val _ = $D.chdone(s)
  val _ = $D.hclose(s)
  val _ = $D.hdone(h, ~1ll)
  val _ = $D.hclose(h)
in end

implement monitor<>(cr) = let
  val () = go(join(cr))
in end

implement msleep<>(ms) = () where { val _ = $D.msleep($D.now() + ms) }

implement pause<>() = () where { val _ = $D.msleep(~1ll) }










// Uni-Directional Channels                                                    
// =========================================================================== 


// Management                                                                  
// --------------------------------------------------------------------------- 


implement{} ch1make() = let
  val chr = $D.chmake_boxed()
  val chw = $D.hdup(chr)
in
  $tuple(ch1in(chr), ch1out(chw))
end


implement{} ch1outdup(ch) = let
  val+@ch1out(i) = ch
  val j = $D.hdup(i)
  val () = fold@(ch) 
in
  ch1out(j)
end


implement{} ch1indup(ch) = let
  val+@ch1in(i) = ch
  val j = $D.hdup(i)
  val () = fold@(ch) 
in
  ch1in(j)
end


implement{} ch1infree(ch) = let
  val+~ch1in(i) = ch
//  val _ = $D.chdone(i)
  val _ = $D.hclose(i)
in end

implement{} ch1outfree(ch) = let
  val+~ch1out(i) = ch
//  val _ = $D.chdone(i)
  val _ = $D.hclose(i)
in end


// Communication                                                               
// --------------------------------------------------------------------------- 

implement (v) ch1send<v>(chw,v) = let
  val+@ch1out(h) = chw
  val result = $D.chsend_boxed<v>(h,v)
  val () = fold@(chw) 
in
  result
end

implement (v) ch1recv<v>(chr) = let
  val+@ch1in(h) = chr
  val result = $D.chrecv_boxed<v>(h)
  val () = fold@(chr)
in
  result
end

implement (v,i) ch1choose<v>{i}(chw,v) = let
  val+@ch1out(h) = chw
  val result = $D.chsend_boxed<choicevs0(i,v)>(h,v)
  val () = fold@(chw) 
in
  result
end

implement (i,v,r) ch1choice<v>(chr) = let
  val+@ch1in(h) = chr
  val result = $D.chrecv_boxed<choicev(i,v,r)>(h)
  val () = fold@(chr) 
in
  result
end


// --------------------------------------------------------------------------- 

fun{a,b:vt@ype} map_loop(chr:ch1in, chw:ch1out, f: (a) -> b): void = 
  case+ ch1recv<a>(chr) of
  | ~None_vt() => {
    val () = ch1infree(chr)
    val () = ch1outfree(chw)
  }
  | ~Some_vt(v) => map_loop(chr,chw,f) where {
    // FIXME bug if chw closes first. 
    val-~None_vt() = ch1send<b>(chw,f(v))
  }

implement (a,b) ch1map<a><b>(chr, f) = let
  val $tup(cin,cout) = ch1make()
  val _ = go(map_loop<a,b>(chr, cout, f))
in
  cin
end



fun{a,b:vt@ype} filter_loop(chr:ch1in, chw:ch1out, f: (!a) -> bool, free: (a) -> void): void = 
  case+ ch1recv<a>(chr) of
  | ~None_vt() => {
    val () = ch1infree(chr)
    val () = ch1outfree(chw)
  }
  | ~Some_vt(v) =>
    (case+ f(v) of
    | true =>
      (case+ ch1send<a>(chw,v) of
      | ~Some_vt(v) => {
        val () = free(v)
        val () = ch1infree(chr)
        val () = ch1outfree(chw)
      }
      | ~None_vt() => {
        val () = filter_loop(chr,chw,f,free)
      })
    | false => {
      val () = free(v)
      val () = filter_loop(chr,chw,f,free)
    })
       

implement (a,b) ch1filter<a><b>(chr, f, free) = let
  val $tup(cin,cout) = ch1make()
  val _ = go(filter_loop<a,b>(chr, cout, f, free))
in
  cin
end


// Multiplexing                                                                
// --------------------------------------------------------------------------- 

extern castfn {a:vt@ype}unsafe_copy(!a): a
extern praxi {a:vt@ype}unsafe_free(a): void


implement (v0) ch1select1<v0>(c0) =
  case+ c0 of
  | ~ch1op_recv(cin) => let
    val msg = ch1recv<v0>(cin)
    val () = c0 := ch1op_nil()
  in
    selection1_0(cin, msg)
  end
  | ~ch1op_send(cout, vx) => let
    val msg = ch1send<v0>(cout, vx)
    val () = c0 := ch1op_nil()
  in
    selection1_0(cout, msg)
  end
  | ~ch1op_choice(cout) => let
    val msg = ch1choice(cout)
    val () = c0 := ch1op_nil()
  in
    selection1_0(cout, msg)
  end
  | ~ch1op_choose(cin, vx) => let
    val msg = ch1choose(cin, vx)
    val () = c0 := ch1op_nil()
  in
    selection1_0(cin, msg)
  end


// TODO complete using templates/code generation.  
implement (v0,v1) ch1select2<v0><v1>(c0, c1) = let
in
  case- (c0, c1) of
  | (@ch1op_recv(ch1in(h0))      ,@ch1op_recv(ch1in(h1)))        => let
    var p : ptr
    var clauses = @[$D.chclause][2](
      $D.chclause($D.CHRECV, h0, addr@p, sizeof<ptr>),
      $D.chclause($D.CHRECV, h1, addr@p, sizeof<ptr>)
    )
    val () = fold@(c0)
    val () = fold@(c1)
    val n   = $D.choose(addr@clauses, 2, ~1ll)
    val err = $D.errno
  in
    (case+ n of
    | 0 => let
      val ~ch1op_recv(cin) = c0 
      val () = c0 := ch1op_nil()
      val~$D.linbox(v) = $UN.castvwtp0{$D.linbox(v0)}(p)
    in
      (if err = 0 then selection2_0(cin, Some_vt(v)) else selection2_0(cin, None_vt()))
    end
    | _ => let
      val ~ch1op_recv(cin) = c1 
      val () = c1 := ch1op_nil()
      val~$D.linbox(v) = $UN.castvwtp0{$D.linbox(v1)}(p)
    in
      (if err = 0 then selection2_1(cin, Some_vt(v)) else selection2_1(cin, None_vt()))
    end)
  end

  | (@ch1op_recv(ch1in(h0))      ,@ch1op_send(ch1out(h1), vx))        => let
    var p : ptr
    var clauses = @[$D.chclause][2](
      $D.chclause($D.CHRECV, h0, addr@p, sizeof<ptr>),
      $D.chclause($D.CHSEND, h1, addr@p, sizeof<ptr>)
    )
    val () = p := $UN.castvwtp0{ptr}($D.linbox(unsafe_copy(vx)))
    val () = fold@(c0)
    val () = fold@(c1)
    val n   = $D.choose(addr@clauses, 2, ~1ll)
    val err = $D.errno
  in
    (case+ n of
    | 0 => let
      val ~ch1op_recv(cin) = c0 
      val () = c0 := ch1op_nil()
      val~$D.linbox(v) = $UN.castvwtp0{$D.linbox(v0)}(p)
    in
      (if err = 0 then selection2_0(cin, Some_vt(v)) else selection2_0(cin, None_vt()))
    end
    | _ => let
      val ~ch1op_send(cout,vx) = c1 
      prval () = unsafe_free(vx)
      val () = c1 := ch1op_nil()
    in
      (if err = 0 then let 
          val~$D.linbox(v) = $UN.castvwtp0{$D.linbox(v0)}(p)
        in
          selection2_1(cout, Some_vt(v))
        end
      else 
        selection2_1(cout, None_vt()))
    end)
  end
//  | (ch1op_recv(ch0)      , ch1op_send(ch1, v1))   => let
//
//  in end

//  | (ch1op_recv(ch0)      , ch1op_choice(ch1))      => let
//
//  in end
//  | (ch1op_recv(ch0)      , ch1op_choose(ch1, v1)) => let
//
//  in end
//
//  | (ch1op_send(ch0, v0)  , ch1op_recv(ch1))        => ()
//  | (ch1op_send(ch0, v0)  , ch1op_send(ch1, v1))   => ()
//  | (ch1op_send(ch0, v0)  , ch1op_choice(ch1))      => ()
//  | (ch1op_send(ch0, v0)  , ch1op_choose(ch1, v1)) => ()
//
//  | (ch1op_choice(ch0)    , ch1op_recv(ch1))        => ()
//  | (ch1op_choice(ch0)    , ch1op_send(ch1, v1))   => ()
//  | (ch1op_choice(ch0)    , ch1op_choice(ch1))      => ()
//  | (ch1op_choice(ch0)    , ch1op_choose(ch1, v1)) => ()
//
//  | (ch1op_choose(ch0, v0), ch1op_recv(ch1))        => ()
//  | (ch1op_choose(ch0, v0), ch1op_send(ch1, v1))   => ()
//  | (ch1op_choose(ch0, v0), ch1op_choice(ch1))      => ()
//  | (ch1op_choose(ch0, v0), ch1op_choose(ch1, v1)) => ()
end



// Bi-Directional Channels                                                     
// =========================================================================== 

// Management                                                                  
// --------------------------------------------------------------------------- 


implement{} ch2make() = let
  val $tuple(ain, aout) = ch1make() 
  val $tuple(bin, bout) = ch1make()
  val a2 = ch2(ain, bout)
  val b2 = ch2(bin, aout)
in
  $tuple(a2, b2)
end


implement{} ch2free(ch) = let
  val~ch2(cin,cout) = ch
  val () = ch1infree(cin)
  val () = ch1outfree(cout)
in end



// Communication                                                               
// --------------------------------------------------------------------------- 


implement (v) ch2send<v>(ch,v) = let
  val+@ch2(_,cout) = ch
  val result = ch1send<v>(cout,v)
  val () = fold@(ch) 
in
  result
end

implement (v) ch2recv<v>(ch) = let
  val+@ch2(cin,_) = ch
  val result = ch1recv<v>(cin)
  val () = fold@(ch)
in
  result
end





