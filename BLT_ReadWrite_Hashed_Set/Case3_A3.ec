pragma Goals:printall.

require import Int Real Distr SmtMap FSet.

require import BLT_Instance.
require import RandomnessOracle.

theory Case3_A3_Theory.

module Case3_Adv3(A : BLT_Adv, A2 : BLT_Adv_Set, RO : ROracle, Tag_O : Tag_Oracle) = {
    
  module TsU_Set = TsU_Set(A2)
  module BLT_Wrap = BLT_Wrap(Tag_O, TsU_Set)
  module A = A(BLT_Wrap)

  proc main(pk:pkey) = {
    var it : int;
    var tg : tag;
    var m : message;

    it <@ RO.rndStr();
    TsU_Set.init(initialTime it);
    BLT_Wrap.init();

    (m,tg) <@ A.forge(pk, it);
    
    return HM.H m; 
  }
  
}.



section. 

op timeX        : pkey -> int -> int.
op hash_setX    : pkey -> int -> hash_output fset.
op time_setX    : pkey -> int -> int fset.
op message_setX : pkey -> int -> message fset.
op messageX     : pkey -> int -> message.
op boolX        : pkey -> int -> bool.


declare module A <: BLT_Adv{-Tag_Wrap, -BLT_Wrap, -TsU, -BLTGame,  -TsU, -Tag_Wrap, -Case3_Adv3, -BLTGameD}.
declare module A2 <: BLT_Adv_Set{-Tag_Wrap, -BLT_Wrap, -TsU, -A, -BLTGame, -TsU, -Tag_Wrap, -Case3_Adv3, -BLTGameD}.

axiom A_ll : forall (O <: BLT_AdvOracle{-A}), 
  islossless O.sign => islossless O.put => islossless O.get => islossless A(O).forge.

axiom A2_ll : islossless A2.react.

axiom computableAdvs &m  pkk skk : (pkk, skk) \in keys => 
  Pr [ BLTGameD(TsU_Set(A2),Tag_Wrap, A).main(pkk, skk) @ &m :  
     toTime BLT_Wrap.qt = timeX  pkk RO.t 
  /\ (ogetf TsU.r.[toTime BLT_Wrap.qt]) = hash_setX pkk RO.t
  /\ BLT_Wrap.used = boolX pkk RO.t
  /\ fset1 (toTime BLT_Wrap.qt) = time_setX pkk RO.t
  /\ (ogetff BLT_Wrap.qs)   = message_setX pkk RO.t
  /\ HM.H BLTGameD.m = HM.H (messageX pkk RO.t) ] = 1%r.


local lemma fullRun pkk skk : (pkk, skk) \in keys => 
  equiv [ Case3_Adv3(A, A2, RO, Tag_Wrap).main ~ BLTGameD(TsU_Set(A2),Tag_Wrap, A).main 
  : ={glob A, pk, glob A2, glob RO, glob TsU, glob BLT_Wrap, glob Tag_Wrap}
 /\ Tag_Wrap.usedTag{2} = deftag 
 /\ Tag_Wrap.usedFlag{2} = false 
 /\ Tag_Wrap.sk{2} = sk{2}
 /\ Tag_Wrap.pk{2} = pk{2}   ==> ={glob A,  glob A2, glob RO, glob TsU, glob BLT_Wrap, glob Tag_Wrap}  
 /\ res{1} = HM.H BLTGameD.m{2}
 /\ BLT_Wrap.qt{1} = Tag_Wrap.usedTag{1}
 /\ BLT_Wrap.used{1} = Tag_Wrap.usedFlag{1}
    ].
proof. move => pr.
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
  Pr [ Case3_Adv3(A,A2,RO, Tag_Wrap).main(pkk) @ &m : 
  toTime BLT_Wrap.qt = timeX  pkk RO.t 
  /\ (ogetf TsU.r.[toTime BLT_Wrap.qt]) = hash_setX pkk RO.t
  /\ BLT_Wrap.used = boolX pkk RO.t
  /\ Tag_Wrap.usedFlag = boolX pkk RO.t 
  /\ fset1 (toTime BLT_Wrap.qt) = time_setX pkk RO.t
  /\  (ogetff BLT_Wrap.qs)   = message_setX pkk RO.t
  /\ res = HM.H (messageX pkk RO.t)
  /\ BLT_Wrap.qt = Tag_Wrap.usedTag     
  ]
 = Pr [ BLTGameD(TsU_Set(A2),Tag_Wrap,A).main(pkk, skk) @ &m : 
   
     toTime BLT_Wrap.qt = timeX  pkk RO.t 
  /\ (ogetf TsU.r.[toTime BLT_Wrap.qt]) = hash_setX pkk RO.t
  /\ BLT_Wrap.used = boolX pkk RO.t  
  /\ fset1 (toTime BLT_Wrap.qt) = time_setX pkk RO.t
  /\  (ogetff BLT_Wrap.qs)   = message_setX pkk RO.t
  /\ HM.H BLTGameD.m = HM.H (messageX pkk RO.t)
 ].
proof. move => p1 p2.

byequiv (_ : ={glob A, pk, glob A2, glob RO, glob TsU, glob BLT_Wrap, glob Tag_Wrap} /\ (pkk, skk) = (pk{2}, sk{2}) /\ pk{1} = pk{2} /\ (Tag_Wrap.usedTag = deftag 
 /\ Tag_Wrap.usedFlag = false 
 /\ Tag_Wrap.sk = skk
/\ Tag_Wrap.pk = pkk){1} ==>  ={glob A,  glob A2, glob RO, glob TsU, glob BLT_Wrap, glob Tag_Wrap}  /\ HM.H BLTGameD.m{2} = res{1} /\ BLT_Wrap.qt{1} = Tag_Wrap.usedTag{1} /\  BLT_Wrap.used{1} = Tag_Wrap.usedFlag{1} ).
conseq (fullRun pkk skk p1).
progress. progress. progress. progress. 
qed.

local lemma a3'' &m pkk skk :  (pkk, skk) \in keys =>  Tag_Wrap.usedTag{m} = deftag 
 /\ Tag_Wrap.usedFlag{m} = false 
 /\ Tag_Wrap.sk{m} = skk{m}
 /\ Tag_Wrap.pk{m} = pkk{m} =>
  Pr [ Case3_Adv3(A,A2, RO, Tag_Wrap).main(pkk) @ &m : 
  toTime BLT_Wrap.qt = timeX  pkk RO.t 
  /\ (ogetf TsU.r.[toTime BLT_Wrap.qt]) = hash_setX pkk RO.t
  /\ BLT_Wrap.used = boolX pkk RO.t 
  /\ Tag_Wrap.usedFlag = boolX pkk RO.t 
  /\ fset1 (toTime BLT_Wrap.qt) = time_setX pkk RO.t
  /\ (ogetff BLT_Wrap.qs)   = message_setX pkk RO.t
  /\ res = HM.H (messageX pkk RO.t)
  /\ BLT_Wrap.qt = Tag_Wrap.usedTag     
  ]
 = 1%r.
proof. move => p1 p2. rewrite  (a3' &m pkk skk p1 p2).
apply (computableAdvs &m pkk skk p1).
qed.

lemma a3_premise pkk skk :  
  phoare [ Case3_Adv3(A,A2, RO, Tag_Wrap).main : 
  (pkk, skk) \in keys /\ pk = pkk /\ Tag_Wrap.usedTag = deftag 
 /\ Tag_Wrap.usedFlag = false 
 /\ Tag_Wrap.sk = skk
 /\ Tag_Wrap.pk = pkk ==>
  
  toTime BLT_Wrap.qt = timeX  pkk RO.t 
  /\ (ogetf TsU.r.[toTime BLT_Wrap.qt]) = hash_setX pkk RO.t
  /\ BLT_Wrap.used = boolX pkk RO.t 
  /\ Tag_Wrap.usedFlag = boolX pkk RO.t 
  /\ fset1 (toTime BLT_Wrap.qt) = time_setX pkk RO.t
  /\  (ogetff BLT_Wrap.qs)   = message_setX pkk RO.t
  /\ res = HM.H (messageX pkk RO.t)
  /\ BLT_Wrap.qt = Tag_Wrap.usedTag     
  ]
 = 1%r.
bypr.
move => &m0 ps.


elim ps. move => q1 q2. elim q2. move => z1 z2.
rewrite z1.
apply (a3'' &m0 pkk skk q1 z2).
qed.


end section. 

end Case3_A3_Theory.
