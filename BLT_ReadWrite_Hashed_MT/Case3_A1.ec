pragma Goals:printall.

require import Int Real Distr SmtMap FSet.

require import BLT_Instance.
require import RandomnessOracle.

theory Case3_A1_Theory.

module Case3_Adv1(A : BLT_Adv, A2:BLT_Adv_Set, RO : ROracle) = {
    
  module TsU_Set_1 = TsU_Set_1(A2)
  module BLT_Dummy_Time = BLT_Dummy_Time(Tag_Wrap_1, TsU_Set_1)
  module A = A(BLT_Dummy_Time)

  proc main(pk:pkey) = {

    var m : message;
    var tg : tag;
    var it : int;
    var c  : chain;
    it <@ RO.rndStr();

    Tag_Wrap_1.init(pk, witness);
    TsU_Set_1.init(initialTime it);
    BLT_Dummy_Time.init();

    (m,tg, c) <@ A.forge(pk, it);

    return BLT_Dummy_Time.usedTime;
  }
    
}.




section Adv1. 


op timeX        : pkey -> int -> int.
op hash_setX    : pkey -> int -> int -> hash_output fset option.
op time_setX    : pkey -> int -> int fset.
op message_setX : pkey -> int -> message fset.
op messageX     : pkey -> int -> message.
op boolX        : pkey -> int -> bool.
op chainX        : pkey -> int -> chain.


declare module A <: BLT_Adv{-Tag_Wrap_1, -BLT_Wrap, -TsU, -BLTGame, -BLT_Dummy_Time, -Tag_Wrap, -TsU_1, -RO}.
declare module A2 <: BLT_Adv_Set{-Tag_Wrap_1, -BLT_Wrap, -TsU, -A, -BLTGame, -BLT_Dummy_Time, -Tag_Wrap, -TsU_1, -RO}.

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


lemma a1  &m pkk skk :  (pkk, skk) \in keys => Pr [ BLTGameD(TsU_Set(A2),Tag_Wrap, A).main(pkk, skk) @ &m : 
     toTime BLT_Wrap.qt = timeX pkk RO.t ] = 1%r.
proof.  move => h.
have : Pr [ BLTGameD(TsU_Set(A2),Tag_Wrap, A).main(pkk, skk) @ &m :  
     toTime BLT_Wrap.qt = timeX  pkk RO.t 
  /\ BLT_Wrap.used = boolX pkk RO.t
  /\ fset1 (toTime BLT_Wrap.qt) = time_setX pkk RO.t
  /\ (ogetff BLT_Wrap.qs)   = message_setX pkk RO.t
  /\ BLTGameD.m = messageX pkk RO.t
  /\ BLTGameD.c = chainX pkk RO.t
  /\ (forall x, TsU.r.[x] = hash_setX pkk RO.t x) ] <= Pr [ BLTGameD(TsU_Set(A2),Tag_Wrap, A).main(pkk, skk) @ &m : 
     toTime BLT_Wrap.qt = timeX pkk RO.t ].
rewrite Pr[mu_sub]. auto. auto.

have : Pr[BLTGameD(TsU_Set(A2),Tag_Wrap, A).main(pkk, skk) @ &m :
   toTime BLT_Wrap.qt = timeX pkk RO.t /\
   BLT_Wrap.used = boolX pkk RO.t /\
   fset1 (toTime BLT_Wrap.qt) = time_setX pkk RO.t /\
    (ogetff BLT_Wrap.qs) = message_setX pkk RO.t /\
   BLTGameD.m = messageX pkk RO.t 
  /\ BLTGameD.c = chainX pkk RO.t
  /\ (forall x, TsU.r.[x] = hash_setX pkk RO.t x)  ] = 1%r. 
apply (computableAdvs &m pkk skk h).
smt.
qed.




local lemma timeExtractor' :
  equiv [ A(BLT_Dummy_Time(Tag_Wrap_1, TsU_Set_1(A2))).forge 
           ~ A(BLT_Wrap(Tag_Wrap, TsU_Set(A2))).forge 
   : ={rs, glob A, pk, glob A2} /\ TsU.r{2} = TsU_1.r{1} /\ TsU.t{2} = TsU_1.t{1} /\ BLT_Wrap.qs{2} = None 
     /\ toTime BLT_Wrap.qt{2} = BLT_Dummy_Time.usedTime{1}
     /\ BLT_Dummy_Time.used{1} = BLT_Wrap.used{2}
     /\ BLT_Wrap.used{2} = Tag_Wrap.usedFlag{2}
     /\ (Tag_Wrap.pk{2}, Tag_Wrap.sk{2}) \in keys
    ==> toTime BLT_Wrap.qt{2} = BLT_Dummy_Time.usedTime{1} ].
proof. proc*. 

call (_: BLT_Wrap.used,  ={glob A2} /\ (toTime BLT_Wrap.qt{2} = BLT_Dummy_Time.usedTime{1}) /\ BLT_Dummy_Time.used{1} = BLT_Wrap.used{2} /\ TsU_1.t{1} = TsU.t{2} /\ TsU.r{2} = TsU_1.r{1}
  /\ (Tag_Wrap.pk{2}, Tag_Wrap.sk{2}) \in keys /\ Tag_Wrap.usedFlag{2} = BLT_Wrap.used{2} , (toTime BLT_Wrap.qt{2} = BLT_Dummy_Time.usedTime{1}) /\ BLT_Dummy_Time.used{1} = BLT_Wrap.used{2}   /\ Tag_Wrap.usedFlag{2} = BLT_Wrap.used{2} 
  /\ (Tag_Wrap.pk{2}, Tag_Wrap.sk{2}) \in keys /\ BLT_Dummy_Time.used{1} = BLT_Wrap.used{2}).
apply A_ll.

proc. wp. if. auto.
inline*.
wp. call (_: true ==> true).  proc*. call {1} A2_ll. call {2} A2_ll. skip. auto.

wp. skip. progress. smt (toTimeProp). smt. skip. smt. 

move => &2 used. proc.
inline*. if. wp. call (_:true). apply A2_ll.  wp. skip. smt.
wp. skip. smt.

move => &1. proc.
inline*. if. wp. call (_:true). apply A2_ll.  wp. skip. smt.
wp. skip. smt.

proc. inline*. wp.
call (_:true). wp.
skip. progress.

move => &2 used. proc.
inline*.  wp. call (_:true). apply A2_ll.  wp. skip. progress.

move => &1. proc.
inline*. wp. call (_:true). apply A2_ll.  wp. skip. smt.

proc. inline*. wp.
skip. progress.

move => &2 used. proc.
inline*.  wp.  skip. progress.

move => &1. proc.
inline*. wp. skip. smt.
 
skip. progress. smt.

qed. 


local lemma timeExtractor pkk skk : (pkk, skk) \in keys => equiv [ Case3_Adv1(A, A2, RO).main ~ BLTGameD(TsU_Set(A2),Tag_Wrap, A).main 
  : ={glob A, glob A2, glob RO} /\ pk{1} = pk{2} /\ (pkk, skk) = (pk{2}, sk{2})  ==> res{1} = toTime BLT_Wrap.qt{2} /\ ={RO.t} ].
proof. move => pksk. proc. inline*.
wp.  call timeExtractor'. wp. wp. skip. progress. 
qed.


local lemma a2 &m pkk skk :  (pkk, skk) \in keys =>
   Pr [ Case3_Adv1(A,A2, RO).main(pkk) @ &m : res = timeX pkk RO.t ] 
 = Pr [ BLTGameD(TsU_Set(A2),Tag_Wrap, A).main(pkk, skk) @ &m : toTime BLT_Wrap.qt = timeX pkk RO.t ].
proof.   move => pr.
byequiv (_ : ={pk, glob RO, glob A, glob A2, glob Tag_Wrap, glob TsU, glob BLT_Wrap} 
  /\ (pk{2}, sk{2}) = (pkk, skk)   ==> res{1} = toTime BLT_Wrap.qt{2} /\ ={RO.t}).
conseq (timeExtractor pkk skk pr). progress.
progress. progress. 
qed.



local lemma a222 &m pkk skk: (pkk, skk) \in keys => Pr [ Case3_Adv1(A,A2, RO).main(pkk) @ &m : res = timeX pkk RO.t ] = 1%r.
proof. 
move => pr. rewrite  (a2 &m pkk skk). auto. apply (a1 &m pkk skk pr). qed.

        
lemma a1_premise pkk skk : phoare [ Case3_Adv1(A,A2, RO).main  : (pkk, skk) \in keys /\  pk = pkk ==> res = timeX pkk RO.t ] = 1%r.
 bypr. move => &m1 h. elim h. move => h1 h2. rewrite h2. apply (a222 &m1 pkk skk h1).
qed.

end section Adv1.

end Case3_A1_Theory.
