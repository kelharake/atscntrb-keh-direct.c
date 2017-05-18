
staload "./rlist.sats"

dataviewtype ch(mode:int) =
  | ch1in (1) of (int)
  | ch1out(2) of (int)
  | ch2   (3) of (ch(1), ch(2))

viewtypedef ch1in  = ch(1)
viewtypedef ch1out = ch(2)
viewtypedef ch2    = ch(3)

viewtypedef chw0  = {mode:nat | mode - 2 >= 0} ch(mode)
viewtypedef chr0  = {mode:nat | mode - 1 <> 1} ch(mode)
viewtypedef chrw0 = ch(3)


dataviewtype choicev(int, values:vtype, result:vt@ype) =
  | {v0:vt@ype}{vn:vtype}
    choicev_0(0, v0::vn, v0) of (v0)
  | {v0,v1:vt@ype}{vn:vtype}
    choicev_1(1, v0::v1::vn, v1) of (v1)
  | {v0,v1,v2:vt@ype}{vn:vtype}
    choicev_2(2, v0::v1::v2::vn, v2) of (v2)

viewtypedef choicev0(s:vtype,c:vt@ype) = [i:int] choicev(i,s,c)
viewtypedef choicevs0(i:int,c:vt@ype) = [s:vtype] choicev(i,s,c)
viewtypedef choicevr0(s:vtype) = [r:vt@ype] choicev0(s,r)
viewtypedef choicevis0(r:vt@ype) = [s:vtype] choicev0(s,r)

dataviewtype coroutine = coroutine of ((*process handle*)int, (*completion signal*)int)


// Processes                                                                   
// =========================================================================== 
fun{} go_cloptr_monitored(() -<lin,cloptr1> void): void
fun{} go_cloptr_unmonitored(() -<lin,cloptr1> void): coroutine

macdef go(f) = go_cloptr_monitored(llam() =<lin,cloptr1> ,(f))
macdef gou(f) = go_cloptr_unmonitored(llam() =<lin,cloptr1> ,(f))

fun{} join(coroutine): void

fun{} monitor(coroutine): void

fun{} msleep(llint): void

fun{} pause(): void


// Uni-Directional Channels                                                    
// =========================================================================== 

// Management                                                                  
// --------------------------------------------------------------------------- 
fun{} ch1make(): $tup(ch1in, ch1out)

fun{} ch1infree(ch1in): void

fun{} ch1outfree(ch1out): void

fun{} ch1indup(!ch1in): ch1in

fun{} ch1outdup(!ch1out): ch1out


// Communication                                                               
// --------------------------------------------------------------------------- 
fun
  {v:vt@ype}
  ch1send
  (ch: !ch1out, v: v):
  Option_vt(v)

fun
  {v:vt@ype}
  ch1recv
  (ch: !ch1in):
  Option_vt(v)


fun
  {v:vt@ype}
  ch1choose
  {i:int}
  (ch: !ch1out, v: choicevs0(i,v)):
  Option_vt(choicevs0(i,v))

fun
  {vs:vtype}
  ch1choice
  (ch: !ch1in):
  #[i:int]
  #[v:vt@ype]
  Option_vt(choicev(i,vs,v))


// Stream                                                                      
// --------------------------------------------------------------------------- 
fun
  {a:vt@ype}
  {b:vt@ype}
  ch1map
  (ch1in, (a) -> b): ch1in

fun
  {a:vt@ype}
  {b:vt@ype}
  ch1filter
  (ch1in, (!a) -> bool, (a) -> void): ch1in


// Multiplexing                                                                
// --------------------------------------------------------------------------- 

dataviewtype ch1op(int, v:vt@ype, chtype:vt@ype) =
  | ch1op_nil    (0, v, chtype) of ()
  | ch1op_recv   (1, v, ch1in)  of (ch1in)
  | ch1op_send   (2, v, ch1out) of (ch1out, v)
  | ch1op_choice (3, v, ch1in)  of (ch1in)                 // some kind of int. recv 
  | ch1op_choose (4, v, ch1out) of (ch1out, choicevis0(v)) // some kind of int. send 


dataviewtype selection1(chtype:vt@ype,t0:vt@ype,i0r:int,v0r:vt@ype) =
  | selection1_0(t0,t0,0,v0r) of (t0,Option_vt(v0r))

dataviewtype selection2(chtype:vt@ype,t0:vt@ype,t1:vt@ype,i0r:int,i1r:int,v0r:vt@ype,v1r:vt@ype) =
  | selection2_0(t0,t0,t1,0,i1r,v0r,v1r) of (t0,Option_vt(v0r))
  | selection2_1(t1,t0,t1,i0r,0,v0r,v1r) of (t1,Option_vt(v1r))

fun
  {v0:vt@ype}
  ch1select1
  {i0:pos}
  {t0:vt@ype}
  (c0: !ch1op(i0,v0,t0) >> ch1op(0,v0,t0)):
  #[tr:vt@ype]
  selection1(tr,t0,0,v0)

fun
  {v0:vt@ype}
  {v1:vt@ype}
  ch1select2
  {i0,i1:nat}
  {t0,t1:vt@ype}
  (c0: !ch1op(i0,v0,t0) >> ch1op(i0r,v0,t0), c1: !ch1op(i1,v1,t1) >> ch1op(i1r,v1,t1)):
  #[i0r,i1r:nat]
  #[tr:vt@ype]
  selection2(tr,t0,t1,i0r,i1r,v0,v1)

// Bi-Directional Channels                                                     
// ============================================================================

// Management                                                                  
// --------------------------------------------------------------------------- 
fun{} ch2make(): $tuple(ch2, ch2)

fun{} ch2free(ch2): void

// Communication                                                               
// --------------------------------------------------------------------------- 
fun
  {v:vt@ype}
  ch2send
  (ch: !ch2, v: v):
  Option_vt(v)

fun
  {v:vt@ype}
  ch2recv
  (ch: !ch2):
  Option_vt(v)


