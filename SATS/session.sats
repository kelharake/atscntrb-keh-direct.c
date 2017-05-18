

staload "./rlist.sats"
staload "./basic.sats"


absviewtype session(vtype,int)
viewtypedef session0(ss:vtype) = [r:int] session(ss,r)


absviewtype select(vtype)

absviewtype exn
absviewtype sendopt(dst: int, value: vt@ype, failss: vtype)
absviewtype recvopt(src: int, value: vt@ype, failss: vtype)

viewtypedef recv(src: int, value: vt@ype) = recvopt(src, value, exn)
viewtypedef send(dst: int, value: vt@ype) = sendopt(dst, value, exn)

absviewtype loop(session: vtype)
absviewtype fork(session: vtype)


praxi do_loop{ss:vtype}{rep:int}(!session(loop(ss),rep) >> session(ss,rep1)): 
  #[rep1:int] (!session(rnil,rep1) >> session(loop(ss),rep)) -<lin> void

absviewtype channel(i:int,mode:int) = ch(i)
viewtypedef channel0(mode: int) = [i:int] channel(i, mode)
viewtypedef chw(i: int)  = [mode:nat | mode - 2 >= 0] channel(i, mode)
viewtypedef chr(i: int)  = [mode:nat | mode - 1 <> 1] channel(i, mode)
viewtypedef chrw(i: int) = channel(i, 3)
sortdef writable = {mode:int | mode - 2 >= 0}
sortdef readable = {mode:int | mode - 1 <> 1}


absviewtype choiceopt(chanid: int, sv:vtype, session: vtype, failss: vtype)
viewtypedef choice(chanid:int,sv:vtype, session:vtype) = choiceopt(chanid,sv,session,exn)


absviewtype chooseopt(chanid: int, sv:vtype, session: vtype, failss: vtype)
viewtypedef choose(chanid:int,sv:vtype,session:vtype) = chooseopt(chanid,sv,session,exn)


dataviewtype choicev(int, sv:vtype, sc: vtype, vx: vt@ype, cont: vtype) =
  | {c0,cc:vtype}
    {vn:vtype}
//    {v0:vt@ype}
//    {vx:vt@ype}
    choicev_0(0, vx::vn, c0::cc, vx, c0) of (vx)
  | {c0,c1,cc:vtype}
    {vn:vtype}
    {v0:vt@ype}
//    {vx:vt@ype}
    choicev_1(1, v0::vx::vn, c0::c1::cc, vx, c1) of (vx)
  | {c0,c1,c2,cc:vtype}
    {vn:vtype}
    {v0,v1:vt@ype}
    {vx:vt@ype}
    choicev_2(2, v0::v1::vx::vn, c0::c1::c2::cc, vx, c2) of (vx)

viewtypedef choicev0(v:vtype, s:vtype,c:vtype) = [i:int][r:vt@ype] choicev(i,v,s,r,c)
viewtypedef choicevc0(v:vtype, s:vtype) = [i:int][c:vtype][r:vt@ype] choicev(i,v,s,r,c)
viewtypedef choices0(i:int,r:vt@ype) = [i:int][c:vtype][s:vtype] [v:vtype] choicev(i,v,s,r,c)

viewtypedef choicer0(i:int,v:vtype,s:vtype,c:vtype) = [r:vt@ype] choicev(i,v,s,r,c)


dataviewtype ssbranch(sv:vtype, sc:vtype, fv:vtype, fc:vtype, cv:vt@ype, cc:vtype, status:bool) =
  | {fv0:vt@ype}{fc0:vtype}
    {fvn,fcn:vtype}
    ssfail_0(sv, sc, fv0::fvn, fc0::fcn, fv0, fc0, false) of (fv0)
  | {sv0:vt@ype}
    {sc0:vtype}
    {svn,scn:vtype}
    sspass_0(sv0::svn, sc0::scn, fv, fc, sv0, sc0, true) of (sv0)
  | {sv1:vt@ype}
    {sc1:vtype}
    {svn,scn:vtype}
    {sv0:vt@ype}
    {sc0:vtype}
    sspass_1(sv0::sv1::svn, sc0::sc1::scn, fv, fc, sv1, sc1, true) of (sv1)
  | {sv2:vt@ype}
    {sc2:vtype}
    {svn,scn:vtype}
    {sv0,sv1:vt@ype}
    {sc0,sc1:vtype}
    sspass_2(sv0::sv1::sv2::svn, sc0::sc1::sc2::scn, fv, fc, sv2, sc2, true) of (sv2)


/*

dataviewtype ssbranch(svc:vtype, fvc:vtype, cv:vt@ype, cc:vtype, status:bool) =
  | {fv0:vt@ype}{fc0:vtype}
    {fvcn:vtype}
    ssfail_0(svc, (fv0::fc0)::fvcn, fv0, fc0, false) of (fv0)
  | {sv0:vt@ype}
    {sc0:vtype}
    {svcn:vtype}
    sspass_0((sv0::sc0)::svcn, fvc, sv0, sc0, true) of (sv0)
  | {sv1:vt@ype}
    {sc1:vtype}
    {svcn:vtype}
    {svc0:vtype}
    sspass_1(svc0::(sv1::sc1)::svcn, fvc, sv1, sc1, true) of (sv1)
  | {sv2:vt@ype}
    {sc2:vtype}
    {svcn:vtype}
    {svc0,svc1:vtype}
    sspass_2(svc0::svc1::(sv2::sc2)::svcn, fvc, sv2, sc2, true) of (sv2)

*/



dataviewtype chop(exec:bool,                  com:vtype, chid:int, mode:int,       asv:vtype, asc:vtype,       afv:vtype, afc:vtype) =
  | chop_nil     (true,                       com,     chid,     mode,             asv, asc,             afv, afc) of ()
  | {mode: readable}
    //{svn,fvn,scn,fcn:vtype}
    {sv:vt@ype}
    {sc,fc:vtype}
    chop_recv    (false, recvopt(chid, sv, fc)::sc,     chid,      mode,  sv::rnil, sc::rnil, int::rnil, fc::rnil) of (channel(chid, mode))
  | {mode: writable}
    {fv:vt@ype}
    {sc,fc:vtype}
    chop_send    (false, sendopt(chid, fv, fc)::sc,     chid,      mode, int::rnil, sc::rnil,  fv::rnil, fc::rnil) of (channel(chid, mode), fv)
  | {mode: readable}
    {sc: vtype}
    {fc: vtype}
    chop_choice  (false,   choiceopt(chid, asv, asc, fc),     chid,      mode,    asv, asc, int::rnil, fc::rnil) of (channel(chid, mode))    // some kind of int. recv 
  | {mode: writable}
    {isv, isc:vtype}
    {sc: vtype}
    {fc: vtype}
    {ci: int}
    chop_choose  (false, chooseopt(chid, isv, isc, fc),     chid,      mode,         int::rnil, sc::rnil, choicer0(ci,isv,isc,sc)::rnil, fc::rnil) of (channel(chid, mode), choicer0(ci,isv,isc,sc)) // some kind of int. send 


praxi session_free(session0(rnil)): void
praxi unsafe_session_free{ss:vtype}(session0(ss)): void



dataviewtype selection(chops: vtype, echops:vtype, ret:vt@ype, cont: vtype) =
  | {cc,cn:vtype}
    {com:vtype}
    {chid: int}
    {mode: int}
    {cv:vt@ype}
    {sv,sc,fv,fc: vtype}
    {status:bool}
    {ee:vtype}
    selection_0(chop(false,com,chid,mode,sv,sc,fv,fc)::cn, chop(true,com,chid,mode,sv,sc,fv,fc)::cn, cv, cc)
    of (channel(chid, mode), ssbranch(sv,sc, fv,fc, cv, cc, status))
  | {c0,cc,cn:vtype}
    {com:vtype}
    {chid: int}
    {mode: int}
    {cv:vt@ype}
    {sv,sc,fv,fc: vtype}
    {status:bool}
    selection_1(c0::chop(false,com,chid,mode,sv,sc,fv,fc)::cn, c0::chop(true,com,chid,mode,sv,sc,fv,fc)::cn, cv, cc)
    of (channel(chid, mode), ssbranch(sv,sc, fv,fc, cv, cc, status))



// Processes                                                                   
// =========================================================================== 
fun
  {}
  fork
  {sf:vtype}{ss:vtype}{rep:int}
  (pf: !session(fork(sf)::ss,rep) >> session(ss,rep) | f: (session0(sf) |) -<lin,cloptr1> void): void

fun
  {}
  forku
  {sf:vtype}{ss:vtype}{rep:int}
  (pf: !session(fork(sf)::ss,rep) >> session(ss,rep) | f: (session0(sf) |) -<lin,cloptr1> void): coroutine



// Channels                                                                    
// =========================================================================== 

// Management                                                                  
// --------------------------------------------------------------------------- 
fun{} chmake1(): [i,j:int] $tup(chr(i), chw(j))

fun{} chmake2(): [i,j:int] $tup(chrw(i), chrw(j))

fun{} chfree{i:int}{m:int}(channel(i,m)): void

// Communication                                                               
// --------------------------------------------------------------------------- 

fun
  {v:vt@ype}
  chsend
  {i:int}{fc:vtype}{ss:vtype}{rep:int}
  (smgr: !session(sendopt(i, v, fc)::ss,rep) >> session(ss,rep) | ch: !chw(i), v: v):
  void


fun
  {v:vt@ype}
  chsend_opt
  {i:int}{fc:vtype}{ss:vtype}{rep:int}
  (smgr: !session(sendopt(i, v, fc)::ss,rep) >> session(cont,rep) | ch: !chw(i), v: v):
  #[cont:vtype] #[status:bool] #[ret:vt@ype] ssbranch(int::rnil, ss::rnil, v::rnil, fc::rnil, ret, cont, status)


fun
  {v:vt@ype}
  chrecv
  {i:int}{ss:vtype}{rep:int}
  (smgr: !session(recv(i,v)::ss,rep) >> session(ss,rep) | ch: !chr(i)):
  v

fun
  {v:vt@ype}
  chrecv_opt
  {i:int}{fc:vtype}{ss:vtype}{rep:int}
  (smgr: !session(recvopt(i,v,fc)::ss, rep) >> session(cont,rep) | ch: !chr(i)):
  #[cont:vtype] #[status:bool] #[ret:vt@ype] ssbranch(v::rnil, ss::rnil, int::rnil, fc::rnil, ret, cont, status)

fun 
  {r:vt@ype}
  chchoose
  {ci:int}{sc:vtype}{i:int}{vv:vtype}{ss:vtype}{rep:int}
  (!session(choose(i,vv,ss),rep) >> session(sc,rep) | !chw(i), choicev(ci,vv,ss,r,sc)):
  void

fun 
  {r:vt@ype}
  chchoose_opt
  {ci:int}{sc:vtype}{fc:vtype}{i:int}{vv:vtype}{ss:vtype}{rep:int}{ci:int}
  (!session(chooseopt(i,vv,ss,fc),rep) >> session(cont,rep) | !chw(i), choicev(ci,vv,ss,r,sc)):
  #[cont:vtype] #[status:bool] #[ret:vt@ype] ssbranch(int::rnil, sc::rnil, choicev(ci,vv,ss,r,sc)::rnil, fc::rnil, ret, cont, status)


fun 
  {}
  chchoice_opt
  {fc:vtype}{ss:vtype}{vv:vtype}{i:int}{rep:int}{ci:int}
  (!session(choiceopt(i,vv,ss,fc),rep) >> session(cont,rep)
  | !chr(i)):
  #[cont:vtype] #[status:bool] #[ret:vt@ype]
  ssbranch(vv, ss, int::rnil, fc::rnil, ret, cont, status)





// Multiplexing                                                                
// --------------------------------------------------------------------------- 
fun {}
  chselect1
  {ss0:vtype}
  {fc0:vtype}
  {sc0:vtype}
  {chid0: int}
  {mode0: int}
  {sv0,fv0:vtype}
  //{xx0,xx1:vtype}
  {rep:int}
  //(!session(select((s0::ss0)::(s1::ss1)::rnil),rep) >> session(cont,rep) |
  (!session(select(ss0::rnil),rep) >> session(cc,rep) |
   !chop(false, ss0, chid0, mode0, sv0,sc0, fv0,fc0) >> chop(true, ss0, chid0, mode0, sv0,sc0, fv0,fc0)
  ): #[cc:vtype] #[cv:vt@ype] selection(
    chop(false, ss0, chid0, mode0, sv0,sc0, fv0,fc0)
  ::rnil,
    chop(true, ss0, chid0, mode0, sv0,sc0, fv0,fc0)
  ::rnil,
    cv,
    cc
  )

fun {}
  chselect2
  {ss0:vtype}
  {ss1:vtype}
  {chid0,chid1: int}
  {mode0,mode1: int}
  {sv0,sc0,fv0,fc0:vtype}
  {sv1,sc1,fv1,fc1:vtype}
  //{xx0,xx1:vtype}
  {rep:int}
  //(!session(select((s0::ss0)::(s1::ss1)::rnil),rep) >> session(cont,rep) |
  (!session(select(ss0::ss1::rnil),rep) >> session(cc,rep) |
   !chop(false, ss0, chid0, mode0, sv0,sc0, fv0,fc0) >> chop(ee0, ss0, chid0, mode0, sv0,sc0, fv0,fc0),
   !chop(false, ss1, chid1, mode1, sv1,sc1, fv1,fc1) >> chop(ee1, ss1, chid1, mode1, sv1,sc1, fv1,fc1) 
  ): #[cc:vtype] #[cv:vt@ype] #[ee0,ee1:bool] selection(
    chop(false, ss0, chid0, mode0, sv0,sc0, fv0,fc0)
  ::chop(false, ss1, chid1, mode1, sv1,sc1, fv1,fc1)  
  ::rnil,
    chop(ee0, ss0, chid0, mode0, sv0,sc0, fv0,fc0)
  ::chop(ee1, ss1, chid1, mode1, sv1,sc1, fv1,fc1)  
  ::rnil,
    cv,
    cc
  )








