pragma Goals:printall.

require import AllCore.
require import BLT_Instance.
require import Case1.
require import Case2.
require import Case3.
require import Case4.
require import Dummy_Tag.


lemma pr1 &m (A <: BLT_Adv{-BLT_Wrap, -TsU}) : 
    Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : res ]
  = Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : res  /\  BLT_Wrap.used ]
  + Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : res  /\ !BLT_Wrap.used ].
proof. rewrite Pr[mu_split BLT_Wrap.used]. done. qed.


lemma pr2 &m (A <: BLT_Adv{-BLT_Wrap, -TsU}) : 
    Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : res /\ BLT_Wrap.used ]
  = Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : (res /\ BLT_Wrap.used) /\ toTime BLTGame.tg < toTime BLT_Wrap.qt ] 
  + Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : (res /\ BLT_Wrap.used) /\ !(toTime BLTGame.tg < toTime BLT_Wrap.qt) ].
proof. rewrite Pr[mu_split (toTime BLTGame.tg < toTime BLT_Wrap.qt)]. done. qed.


lemma pr3 &m (A <: BLT_Adv{-BLT_Wrap,  -TsU}) : 
    Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : (res /\ BLT_Wrap.used) /\ !(toTime BLTGame.tg < toTime BLT_Wrap.qt) ]
  = Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : (res /\ BLT_Wrap.used) /\  (toTime BLT_Wrap.qt <= toTime BLTGame.tg) ].
proof. rewrite Pr[mu_eq]. smt. done. qed.


lemma pr4 &m (A <: BLT_Adv{-BLT_Wrap,  -TsU}) : 
   Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : (res /\ BLT_Wrap.used) /\ (toTime BLT_Wrap.qt <= toTime BLTGame.tg) ]
 = Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ (toTime BLT_Wrap.qt <= toTime BLTGame.tg)) /\ (toTime BLT_Wrap.qt = toTime BLTGame.tg) ]
 + Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ (toTime BLT_Wrap.qt <= toTime BLTGame.tg)) /\ !(toTime BLT_Wrap.qt = toTime BLTGame.tg) ].
proof. rewrite Pr[mu_split (toTime BLT_Wrap.qt = toTime BLTGame.tg)]. done. qed.


lemma pr5 &m (A <: BLT_Adv{-BLT_Wrap, -TsU}) : 
   Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ (toTime BLT_Wrap.qt <= toTime BLTGame.tg)) /\ !(toTime BLT_Wrap.qt = toTime BLTGame.tg) ]
 = Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ (toTime BLT_Wrap.qt < toTime BLTGame.tg)) ].
proof. rewrite Pr[mu_eq]. smt. done. qed.


lemma pr6 &m (A <: BLT_Adv{-BLT_Wrap, -TsU}) : 
   Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ (toTime BLT_Wrap.qt <= toTime BLTGame.tg)) /\ (toTime BLT_Wrap.qt = toTime BLTGame.tg) ]
 = Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ (toTime BLTGame.tg = toTime BLT_Wrap.qt)) ].
proof. rewrite Pr[mu_eq]. smt. done. qed.


lemma pr_split &m (A <: BLT_Adv{-BLT_Wrap, -TsU}) : 
    Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : res ]
  = Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : (res /\ BLT_Wrap.used) /\ toTime BLTGame.tg < toTime BLT_Wrap.qt ] 
  + Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : res /\ BLT_Wrap.used /\ toTime BLTGame.tg = toTime BLT_Wrap.qt ] 
  + Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : (res /\ BLT_Wrap.used) /\ toTime BLT_Wrap.qt < toTime BLTGame.tg  ]   
  + Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : res /\ !BLT_Wrap.used ].
proof. rewrite (pr1 &m A) (pr2 &m A). rewrite (pr3 &m A).  rewrite (pr4 &m A). rewrite (pr5 &m A) (pr6  &m A). smt. 
qed.



lemma security &m (A <: BLT_Adv{-BLT_Wrap, -TsU, -Tag_Wrap, -BLTGame}) : 
 (forall (O <: BLT_AdvOracle{-A}),
       islossless O.sign => islossless O.put => islossless O.get => islossless A(O).forge)
  =>  Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : res ]
  <= (Pr[ BLTGameH(Tag_Wrap, TsU, HT_Adv(A)).main() @ &m : res ] * queryBound%r) (* tg < qt *)
   + Pr[ HMT.CR_H(H_AdvCR(A)).main() @ &m : res ]  (* qt = tg *)
   + Pr[ TagGame(Tag_Wrap, B(A, TsU)).main() @ &m : res ] (* qt < tg *)
   + Pr[ BLTGame(Tag_Wrap, TsU, BLT_Dummy, A).main() @ &m : res ]. (* not used *)

proof. rewrite (pr_split &m (A)). move => il. 

have : Pr[BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m :
   res /\ BLT_Wrap.used /\ toTime BLTGame.tg = toTime BLT_Wrap.qt] <= Pr[ HMT.CR_H(H_AdvCR(A)).main() @ &m : res ]. 
 apply (case3 A  &m ). 
move => q. 

have : Pr[BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m :
   (res /\ BLT_Wrap.used) /\ toTime BLT_Wrap.qt < toTime BLTGame.tg]
 <= Pr[TagGame(Tag_Wrap, B(A, TsU)).main() @ &m : res]. apply (case2 A &m).

move => i1.

have : Pr[BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m :
     (res /\ BLT_Wrap.used) /\ toTime BLTGame.tg < toTime BLT_Wrap.qt]
 <= (Pr[ BLTGameH(Tag_Wrap, TsU, HT_Adv(A)).main() @ &m : res ] * queryBound%r).
apply (case4 A  &m).
move => i2.

have : Pr[BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : res /\ !BLT_Wrap.used]
   <= Pr[BLTGame(Tag_Wrap, TsU, BLT_Dummy, A).main() @ &m : res].
apply (case1 A  &m).
move => i3.
   
smt.
qed.


lemma security_tg1 &m (A <: BLT_Adv{-BLT_Wrap, -TsU, -Tag_Wrap}) :  
    Pr[BLTGame(Tag_Wrap, TsU, BLT_Dummy, A).main() @ &m : res] <=
      Pr[TagGame(Tag_Wrap, BTG(A)).main() @ &m : res].
proof. apply (blt_dummy_tag_pr(A)  &m). qed.



lemma security_tg2 &m (A <: BLT_Adv{-BLT_Wrap, -TsU, -Tag_Wrap}) :  
    Pr[BLTGame(Tag_Wrap, TsU, BLT_Dummy, A).main() @ &m : res] <=
      Pr[TagGame(Tag_Wrap, BTG(A)).main() @ &m : res].
proof. apply (blt_dummy_tag_pr(A)  &m). qed.


require import Pure_Wrap.
section.

declare module A <: BLT_Adv{-BLT_Wrap, -TsU, -Tag_Wrap, -BLT_Pure, -BLTGame}.

axiom ll : (forall (O <: BLT_AdvOracle{-A}),
    islossless O.sign => islossless O.put => islossless O.get => islossless A(O).forge).



lemma main_security &m : 
    Pr[BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : res] <= 
    (Pr[ BLTGameH(Tag_Wrap, TsU, HT_Adv(A)).main() @ &m : res ] * queryBound%r) (* tg < qt *)
  + Pr[ HMT.CR_H(H_AdvCR(A)).main() @ &m : res ]  (* qt = tg *)
  + Pr[ TagGame(Tag_Wrap, B(A, TsU)).main() @ &m : res ] (* qt < tg *)
  + Pr[TagGame(Tag_Wrap, BTG(A)).main() @ &m : res].

proof.  

have : Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : res ] <= 
    (Pr[ BLTGameH(Tag_Wrap, TsU, HT_Adv(A)).main() @ &m : res ] * queryBound%r) (* tg < qt *)
  + Pr[ HMT.CR_H(H_AdvCR(A)).main() @ &m : res ]  (* qt = tg *)
  + Pr[ TagGame(Tag_Wrap, B(A, TsU)).main() @ &m : res ] (* qt < tg *)
  + Pr[ BLTGame(Tag_Wrap, TsU, BLT_Dummy, A).main() @ &m : res ]. 

apply (security &m A ll).

have : Pr[BLTGame(Tag_Wrap, TsU, BLT_Dummy, A).main() @ &m : res]
  <= Pr[TagGame(Tag_Wrap, BTG(A)).main() @ &m : res]. apply (security_tg1 &m A).

move => qq1 qq2.
smt.    
qed.


lemma wrap_to_pure &m : 
    Pr[BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : res] = 
    Pr[BLTGame(Tag_Wrap, TsU, BLT_Pure, A).main() @ &m : res].
proof. byequiv (_: ={glob A,glob TsU, glob Tag_Wrap} ==> ={res}). symmetry. conseq (pure_wrap_eq A Tag_Wrap TsU) => //. auto. auto.
qed.


lemma final_security &m : 
    Pr[BLTGame(Tag_Wrap, TsU, BLT_Pure, A).main() @ &m : res]
  <= (Pr[ BLTGameH(Tag_Wrap, TsU, HT_Adv(A)).main() @ &m : res ] * queryBound%r) (* tg < qt *)
   + Pr[ HMT.CR_H(H_AdvCR(A)).main() @ &m : res ]                            (* qt = tg *)
   + Pr[ TagGame(Tag_Wrap, B(A, TsU)).main() @ &m : res ]                    (* qt < tg *)
   + Pr[TagGame(Tag_Wrap, BTG(A)).main() @ &m : res].                        (* not used *)

proof. rewrite - (wrap_to_pure &m). apply (main_security &m).
qed.

end section.


lemma BLT_Scheme_security &m (A <: BLT_Adv{-BLT_Wrap, -TsU, -Tag_Wrap, -BLT_Pure, -BLTGame}) : 
 (forall (O <: BLT_AdvOracle{-A}),
   islossless O.sign => islossless O.put => islossless O.get => islossless A(O).forge) =>
  Pr[ BLTGame(Tag_Wrap, TsU, BLT_Pure, A).main() @ &m : res ] 
 <= (Pr[ BLTGameH(Tag_Wrap, TsU, HT_Adv(A)).main() @ &m : res ] * queryBound%r) (* tg < qt *)
  + Pr[ HMT.CR_H(H_AdvCR(A)).main() @ &m : res ]                               (* qt = tg *)
  + Pr[ TagGame(Tag_Wrap, B(A, TsU)).main() @ &m : res ]                       (* qt < tg *)
  + Pr[ TagGame(Tag_Wrap, BTG(A)).main() @ &m : res ].                         (* not used *)

proof. move => ll. apply (final_security A  &m).
qed.
