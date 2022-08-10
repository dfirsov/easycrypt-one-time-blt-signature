pragma Goals:printall.

require import Int Real Distr SmtMap FSet DInterval.

require import BLT_Instance.
require import RandomnessOracle.

theory Case4_A2_Theory.

module Case4_Adv2(A : BLT_Adv, A2:BLT_Adv_Set,
  RO : ROracle, Tag_O : Tag_Oracle ) = {

  module Ts_O     = TsU_Set(A2)
  module BLT_Wrap = BLT_Wrap(Tag_O, Ts_O)
  module A        = A(BLT_Wrap)

  var guess : int
  var r : bool
  var m : message
  var tg : tag
  var  c : chain

  proc forge(pk:pkey) : chain = {
    var it;
    it <@ RO.rndStr();

    Ts_O.init(initialTime it);
    BLT_Wrap.init();
    
    (m,tg,c) <@ A.forge(pk, it);

    return c;
  }
}.



section Adv2. 


op timeX        : pkey -> int -> int.
op hash_setX    : pkey -> int -> int -> hash_output fset option.
op time_setX    : pkey -> int -> int fset.
op message_setX : pkey -> int -> message fset.
op messageX     : pkey -> int -> message.
op boolX        : pkey -> int -> bool.
op chainX       : pkey -> int -> chain.

declare module A <: BLT_Adv{-Tag_Wrap, -BLT_Wrap, -TsU, -BLTGame, -BLT_Dummy_Time, -Tag_Wrap, -TsU, -RO}.
declare module A2 <: BLT_Adv_Set{-Tag_Wrap, -BLT_Wrap, -TsU, -A, -BLTGame, -BLT_Dummy_Time, -Tag_Wrap, -TsU, -RO}.

axiom A_ll : forall (O <: BLT_AdvOracle{-A}), 
  islossless O.sign => islossless O.put => islossless O.get => islossless A(O).forge.
axiom A2_ll : islossless A2.react.

axiom computableAdvs &m  pkk skk : (pkk, skk) \in keys => 
  Pr [ BLTGameD(TsU_Set(A2),Tag_Wrap, A).main(pkk, skk) @ &m :  
     toTime BLT_Wrap.qt = timeX  pkk RO.t 
  /\ BLT_Wrap.used = boolX pkk RO.t
  /\ fset1 (toTime BLT_Wrap.qt) = time_setX pkk RO.t
  /\ (ogetff BLT_Wrap.qs)   = message_setX pkk RO.t
  /\ BLTGameD.m = messageX pkk RO.t
  /\ BLTGameD.c = chainX pkk RO.t
  /\ (forall x, TsU.r.[x] = hash_setX pkk RO.t x) ] = 1%r.


  
local lemma a1  &m pkk skk :  (pkk, skk) \in keys => Pr [ BLTGameD(TsU_Set(A2),Tag_Wrap, A).main(pkk, skk) @ &m : 
     (forall x, TsU.r.[x] = hash_setX pkk RO.t x) /\ BLTGameD.c = chainX pkk RO.t /\ timeX pkk RO.t = toTime BLT_Wrap.qt ] = 1%r.
proof.  move => h.
have : Pr [ BLTGameD(TsU_Set(A2),Tag_Wrap, A).main(pkk, skk) @ &m :  
     toTime BLT_Wrap.qt = timeX  pkk RO.t 
  /\ BLT_Wrap.used = boolX pkk RO.t
  /\ fset1 (toTime BLT_Wrap.qt) = time_setX pkk RO.t
  /\ (ogetff BLT_Wrap.qs)   = message_setX pkk RO.t
  /\ BLTGameD.m = messageX pkk RO.t
  /\ BLTGameD.c = chainX pkk RO.t
  /\ (forall x, TsU.r.[x] = hash_setX pkk RO.t x) ] <= Pr [ BLTGameD(TsU_Set(A2),Tag_Wrap, A).main(pkk, skk) @ &m : 
     (forall x, TsU.r.[x] = hash_setX pkk RO.t x) /\ BLTGameD.c = chainX pkk RO.t /\ timeX pkk RO.t = toTime BLT_Wrap.qt ].
rewrite Pr[mu_sub]. auto. auto.

have : Pr[BLTGameD(TsU_Set(A2),Tag_Wrap, A).main(pkk, skk) @ &m :
   toTime BLT_Wrap.qt = timeX pkk RO.t /\

   BLT_Wrap.used = boolX pkk RO.t /\
   fset1 (toTime BLT_Wrap.qt) = time_setX pkk RO.t /\
    (ogetff BLT_Wrap.qs) = message_setX pkk RO.t /\
   BLTGameD.m = messageX pkk RO.t  /\
   BLTGameD.c = chainX pkk RO.t /\
    (forall x, TsU.r.[x] = hash_setX pkk RO.t x) ] = 1%r. 
apply (computableAdvs &m pkk skk h).
smt. auto.  
rewrite (computableAdvs &m pkk skk h).
smt.
qed.


local lemma fullRun pkk skk : (pkk, skk) \in keys => equiv [ Case4_Adv2(A, A2, RO, Tag_Wrap).forge ~ BLTGameD(TsU_Set(A2),Tag_Wrap, A).main 
  : ={glob A, glob A2, glob RO, glob Tag_Wrap} /\ pk{1} = pk{2} /\ (pkk, skk) = (pk{2}, sk{2}) /\
   Tag_Wrap.usedTag{2} = deftag 
 /\ Tag_Wrap.usedFlag{2} = false 
 /\ Tag_Wrap.sk{2} = skk
 /\ Tag_Wrap.pk{2} = pkk  ==>  ={glob BLT_Wrap, glob TsU,RO.t} /\ res{1} = BLTGameD.c{2} ].
move => h.

proc.

inline*.
wp.
call (_: ={glob A2, glob RO, glob TsU, glob BLT_Wrap, glob Tag_Wrap} /\ BLT_Wrap.qt{1} = Tag_Wrap.usedTag{1} /\ BLT_Wrap.used{1} = Tag_Wrap.usedFlag{1}).
proc. if. auto. inline*. wp. call (_:true). wp. skip. auto. wp. skip. auto. smt.
proc. inline*. wp. call (_:true). wp. skip. auto. 
proc. inline*. wp. skip. auto. 
wp. wp. skip. progress.
qed.



local lemma a3' &m pkk skk :  (pkk, skk) \in keys =>  Tag_Wrap.usedTag{m} = deftag 
 /\ Tag_Wrap.usedFlag{m} = false 
 /\ Tag_Wrap.sk{m} = skk{m}
 /\ Tag_Wrap.pk{m} = pkk{m} =>
  Pr [ Case4_Adv2(A,A2,RO, Tag_Wrap).forge(pkk) @ &m : 
  (forall x, TsU.r.[x] = hash_setX pkk RO.t x) /\ res = chainX pkk RO.t /\ timeX pkk RO.t = toTime BLT_Wrap.qt   
  ]
 = Pr [ BLTGameD(TsU_Set(A2),Tag_Wrap,A).main(pkk, skk) @ &m : 
   
    (forall x, TsU.r.[x] = hash_setX pkk RO.t x) /\ BLTGameD.c = chainX pkk RO.t /\ timeX pkk RO.t = toTime BLT_Wrap.qt
 ].
proof. move => p1 p2.

byequiv (_ : ={glob A, pk, glob A2, glob RO, glob TsU, glob BLT_Wrap, glob Tag_Wrap} /\ (pkk, skk) = (pk{2}, sk{2}) /\ pk{1} = pk{2} /\ (Tag_Wrap.usedTag = deftag 
 /\ Tag_Wrap.usedFlag = false 
 /\ Tag_Wrap.sk = skk
/\ Tag_Wrap.pk = pkk){1} ==>  ={glob BLT_Wrap, glob TsU,RO.t} /\ res{1} = BLTGameD.c{2} ).
conseq (fullRun pkk skk p1).
progress. progress. progress. 
qed.

local lemma a3 &m pkk skk :  (pkk, skk) \in keys =>  Tag_Wrap.usedTag{m} = deftag 
 /\ Tag_Wrap.usedFlag{m} = false 
 /\ Tag_Wrap.sk{m} = skk{m}
 /\ Tag_Wrap.pk{m} = pkk{m} =>
  Pr [ Case4_Adv2(A,A2,RO, Tag_Wrap).forge(pkk) @ &m : 
  (forall x, TsU.r.[x] = hash_setX pkk RO.t x) /\ res = chainX pkk RO.t /\ timeX pkk RO.t = toTime BLT_Wrap.qt   
  ]
 = 1%r.
proof. move => p1 p2. rewrite  (a3' &m pkk skk p1 p2).
apply (a1 &m pkk skk p1).
qed.

lemma a2_premise pkk skk :  
  phoare [ Case4_Adv2(A,A2, RO, Tag_Wrap).forge : 
  (pkk, skk) \in keys /\ pk = pkk /\ Tag_Wrap.usedTag = deftag 
 /\ Tag_Wrap.usedFlag = false 
 /\ Tag_Wrap.sk = skk
 /\ Tag_Wrap.pk = pkk ==>
  (forall x, TsU.r.[x] = hash_setX pkk RO.t x) /\ res = chainX pkk RO.t /\ timeX pkk RO.t = toTime BLT_Wrap.qt ]
 = 1%r.
bypr.
move => &m0 ps.
elim ps. move => q1 q2. elim q2. move => z1 z2.
rewrite z1.
apply (a3 &m0 pkk skk q1 z2).
qed.

end section Adv2.

end Case4_A2_Theory.
