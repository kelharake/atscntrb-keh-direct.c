
#include "share/atspre_staload.hats"
#include "share/atspre_define.hats"

#include "../mydepies.hats"

staload UN = "prelude/SATS/unsafe.sats"

staload "./../SATS/session.sats"


staload B = "./../SATS/basic.sats"
staload _ = "./../DATS/basic.dats"

staload "./../SATS/rlist.sats"






extern praxi unsafe_session_pop_discard{s0:vtype}{ss:vtype}{rep:int}(!session(s0::ss,rep) >> session(ss,rep)): void 

extern praxi unsafe_session_pop{s0:vtype}{ss:vtype}{rep:int}(!session(s0::ss,rep) >> session(ss,rep)): session0(s0)
extern praxi unsafe_consume_recv{i:int}{v:vt@ype}{rep:int}(session(recv(i, v),rep)): void
extern praxi unsafe_consume_send{i:int}{v:vt@ype}{rep:int}(session(send(i, v),rep)): void
extern praxi unsafe_consume_recvopt{i:int}{v:vt@ype}{f:vtype}{rep:int}(session(recvopt(i, v, f),rep)): void
extern praxi unsafe_consume_sendopt{i:int}{v:vt@ype}{f:vtype}{rep:int}(session(sendopt(i, v, f),rep)): void
extern praxi unsafe_choose{i:int}{cont:vtype}{vv:vtype}{ss:vtype}{rep:int}(!session(choose(i,vv,ss),rep) >> session(cont,rep)): void
extern praxi unsafe_chooseopt{i:int}{cont:vtype}{vv:vtype}{ss:vtype}{f:vtype}{rep:int}(!session(chooseopt(i,vv,ss,f),rep) >> session(cont,rep)): void


extern praxi unsafe_consume_exn{rep:int}(session(exn,rep)): void


extern praxi unsafe_recvopt2fail{i:int}{v:vt@ype}{f:vtype}{ss:vtype}{rep:int}(!session(recvopt(i, v, f)::ss,rep) >> session(f,rep)): void
extern praxi unsafe_sendopt2fail{i:int}{v:vt@ype}{f:vtype}{ss:vtype}{rep:int}(!session(sendopt(i, v, f)::ss,rep) >> session(f,rep)): void


extern praxi unsafe_channel_session2basic{m:int}{c:int}(!channel(c,m) >> $B.ch(m)): ((!$B.ch(m) >> channel(c,m)) -<prf> void)

extern praxi unsafe_session_convert{s1:vtype}{s0:vtype}{rep:int}(!session(s0,rep) >> session(s1,rep)): void

extern castfn unsafe_tempcast{b:vt@ype}{a:vt@ype}(a): (b -> a | b)

extern praxi unsafe_fork_pop{body:vtype}{rep:int}(!session(fork(body),rep) >> session(body,rep)): void


extern praxi unsafe_session_choice_0
  {ss:vtype}{vv:vtype}{v0:vt@ype}{s0:vtype}{fc:vtype}{rep:int}{i:int}
  (!session(choiceopt(i,v0::vv,s0::ss,fc),rep) >> session(s0,rep)): void

extern praxi unsafe_session_choice_1
  {ss:vtype}{vv:vtype}{v0,v1:vt@ype}{s0,s1:vtype}{fc:vtype}{rep:int}{i:int}
  (!session(choiceopt(i,v0::v1::vv,s0::s1::ss,fc),rep) >> session(s1,rep)): void

extern praxi unsafe_session_choice_2
  {ss:vtype}{vv:vtype}{v0,v1,v2:vt@ype}{s0,s1,s2:vtype}{fc:vtype}{rep:int}{i:int}
  (!session(choiceopt(i,v0::v1::v2::vv,s0::s1::s2::ss,fc),rep) >> session(s2,rep)): void


implement (v) chrecv_opt<v>(sm | ch) = let
  prval (ret) = unsafe_channel_session2basic(ch)
in
  case+ ch  of
  | @$B.ch1in(_) => let
    val () = fold@(ch) 
    val result = $B.ch1recv<v>(ch)
    val err    = $D.errno
    prval () = ret(ch)
  in
    case+ result of
    | ~None_vt()  => ssfail_0(err) where {
      prval () = unsafe_recvopt2fail(sm)
    }
    | ~Some_vt(v) => sspass_0(v) where {
      prval pf = unsafe_session_pop(sm)
      prval () = unsafe_consume_recvopt(pf)
    }
  end
  | @$B.ch2(cin,_) => let
    val result = $B.ch1recv<v>(cin)
    val err    = $D.errno
    val () = fold@(ch)
    prval () = ret(ch)
  in
    case+ result of
    | ~None_vt()  => ssfail_0(err) where {
      prval () = unsafe_recvopt2fail(sm)
    }
    | ~Some_vt(v) => sspass_0(v) where {
      prval pf = unsafe_session_pop(sm)
      prval () = unsafe_consume_recvopt(pf)
    }
  end
end



implement (v) chsend_opt<v>(sm | ch, v) = let
  prval (ret) = unsafe_channel_session2basic(ch)
in
  case+ ch  of
  | @$B.ch1out(_) => let
    val () = fold@(ch) 
    val result = $B.ch1send<v>(ch, v)
    val err    = $D.errno
    prval () = ret(ch)
  in
    case+ result of
    | ~None_vt()  => sspass_0(0) where {
      prval pf = unsafe_session_pop(sm)
      prval () = unsafe_consume_sendopt(pf)
    }
    | ~Some_vt(v) => ssfail_0(v) where {
      prval () = unsafe_sendopt2fail(sm)
    }
  end
  | @$B.ch2(_,cout) => let
    val result = $B.ch1send<v>(cout,v)
    val err    = $D.errno
    val () = fold@(ch)
    prval () = ret(ch)
  in
    case+ result of
    | ~None_vt()  => sspass_0(0) where {
      prval pf = unsafe_session_pop(sm)
      prval () = unsafe_consume_sendopt(pf)
    }
    | ~Some_vt(v) => ssfail_0(v) where {
      prval () = unsafe_sendopt2fail(sm)
    }
  end
end



implement (v) chrecv<v>(sm | ch) = let
  val result = chrecv_opt(sm | ch)
in
  case+ result of
  | ~sspass_0(v) => v
  | ~ssfail_0(_) => $raise AssertExn
end


implement (v) chsend<v>(sm | ch, v) = let
  val result = chsend_opt(sm | ch, v)
in
  case+ result of
  | ~sspass_0(_) => ()
  | ~ssfail_0(v) => let
    // FIXME leak 
    val _ = $UN.castvwtp0{ptr}(v) 
  in $raise AssertExn end
end

implement (i,j) chmake1<>() = 
  $UN.castvwtp0{$tup(chr(i), chw(j))}($B.ch1make())

implement (i,j) chmake2<>() = 
  $UN.castvwtp0{$tup(chrw(i), chrw(j))}($B.ch2make())

implement (i) chfree<>(ch) = let
  val chb = $UN.castvwtp0{$B.ch(i)}(ch)
in
  case+ chb of
  | @$B.ch1in(_) => (fold@(chb); $B.ch1infree(chb))
  | @$B.ch1out(_) => (fold@(chb); $B.ch1outfree(chb))
  | @$B.ch2(_,_) => (fold@(chb); $B.ch2free(chb))
end

implement (r,i) chchoose_opt<r>{i}{sc}{fc}(sm | ch, cv) =  let
  prval (ret) = unsafe_channel_session2basic(ch) 
  val (uncast | v) = unsafe_tempcast{$B.choicevs0(i,r)}(cv)
in
  case+ ch of
  | @$B.ch1out(_) => let
    val () = fold@(ch) 
    val x = $B.ch1choose<r>{i}(ch, v)
    prval () = ret(ch)
  in
    case+ x of
    | ~None_vt() => sspass_0(0) where { prval () = unsafe_session_convert{sc}(sm) }
    | ~Some_vt(v) => ssfail_0(uncast(v)) where { prval () = unsafe_session_convert{fc}(sm) }
  end 
  | @$B.ch2(_,cout) => let
    val x = $B.ch1choose<r>{i}(cout, v)
    val () = fold@(ch) 
    prval () = ret(ch)
  in
    case+ x of
    | ~None_vt() => sspass_0(0) where { prval () = unsafe_session_convert{sc}(sm) }
    | ~Some_vt(v) => ssfail_0(uncast(v)) where { prval () = unsafe_session_convert{fc}(sm) }
  end
end


implement (v) chchoose<v>{ci}(sm | ch, v) = let
  val result = chchoose_opt<v>{ci}(sm | ch, v)
in
  case+ result of
  | ~sspass_0(_) => ()
  | ~ssfail_0(v) => let
    // FIXME leak 
    val _ = $UN.castvwtp0{ptr}(v) 
  in $raise AssertExn end
end


implement (sc,i,cont,ret) chchoice_opt<>{fc}{ss}{vv}(sm | ch) = let
  prval (ret) = unsafe_channel_session2basic(ch) 
in
  case+ ch of
  | @$B.ch1in(_) => (let
    val () = fold@(ch) 
    val m = $B.ch1choice<vv>(ch)
    val x = $UN.castvwtp0{Option_vt(choicev(i,vv,ss,ret,cont))}(m)
    prval () = ret(ch)
  in
    case+ x of
    | ~None_vt() => ssfail_0(0) where { prval () = unsafe_session_convert{fc}(sm) }
    | ~Some_vt(cv) =>
      (case+ cv of
      | ~choicev_0(v0) => sspass_0(v0) where { prval () = unsafe_session_choice_0(sm) }
      | ~choicev_1(v1) => sspass_1(v1) where { prval () = unsafe_session_choice_1(sm) }
      | ~choicev_2(v2) => sspass_2(v2) where { prval () = unsafe_session_choice_2(sm) }
      )
  end)
  | @$B.ch2(cin,_) => (let
    val m = $B.ch1choice<vv>(cin)
    val x = $UN.castvwtp0{Option_vt(choicev(i,vv,ss,ret,cont))}(m)
    val () = fold@(ch) 
    prval () = ret(ch)
  in
    case+ x of
    | ~None_vt() => ssfail_0(0) where { prval () = unsafe_session_convert{fc}(sm) }
    | ~Some_vt(cv) =>
      case+ cv of
      | ~choicev_0(v) => sspass_0(v) where { prval () = unsafe_session_choice_0(sm) }
      | ~choicev_1(v) => sspass_1(v) where { prval () = unsafe_session_choice_1(sm) }
      | ~choicev_2(v) => sspass_2(v) where { prval () = unsafe_session_choice_2(sm) }
  end)
end



// TODO incomplete.  
implement chselect1<>{ss0}(sm | c0) =
  case- c0 of
  | ~chop_recv(chr) => let
    val () = c0 := chop_nil()
    prval (ret) = unsafe_channel_session2basic(chr)
  in
    case- chr of
    | @$B.ch1in(_) => let
      val () = fold@(chr) 
      var op1 = $B.ch1op_recv(chr)
      val sel = $B.ch1select1(op1)
      val err = $D.errno
      val+~$B.ch1op_nil() = op1
      val+~$B.selection1_0(chr, opt) = sel
      prval () = ret(chr)
      prval () = unsafe_session_convert{ss0}(sm)
    in
      case+ opt of
      | ~None_vt() => let
        prval () = unsafe_recvopt2fail(sm)
      in
        selection_0(chr, ssfail_0(err))
      end
      | ~Some_vt(v) => let
        prval () = unsafe_session_pop_discard(sm)
      in
        selection_0(chr, sspass_0(v))
      end
    end
  end


// TODO incomplete.  
implement chselect2<>{ss0}{ss1}(sm | c0, c1) =
  case- c0 of
  | ~chop_recv(chr) => let
    val () = c0 := chop_nil()
    prval (ret) = unsafe_channel_session2basic(chr)
  in
    case- chr of
    | @$B.ch1in(_) => let
      val () = fold@(chr) 
      var op1 = $B.ch1op_recv(chr)
      val sel = $B.ch1select1(op1)
      val err = $D.errno
      val+~$B.ch1op_nil() = op1
      val+~$B.selection1_0(chr, opt) = sel
      prval () = ret(chr)
      prval () = unsafe_session_convert{ss0}(sm)
    in
      case+ opt of
      | ~None_vt() => let
        prval () = unsafe_recvopt2fail(sm)
      in
        selection_0(chr, ssfail_0(err))
      end
      | ~Some_vt(v) => let
        prval () = unsafe_session_pop_discard(sm)
      in
        selection_0(chr, sspass_0(v))
      end
    end
  end


implement fork<>(sm | f) = let
  prval (sms) = unsafe_session_pop(sm)
in
  $B.go(let
    prval () = unsafe_fork_pop(sms)
    val () = f(sms|)
    val _ = cloptr_free($UN.castvwtp0{cloptr(void)}(f))
  in end)
end 

implement forku<>(sm | f) = let
  prval (sms) = unsafe_session_pop(sm)
in
  $B.gou(let
    prval () = unsafe_fork_pop(sms)
    val () = f(sms|)
    val _ = cloptr_free($UN.castvwtp0{cloptr(void)}(f))
  in end)
end 




