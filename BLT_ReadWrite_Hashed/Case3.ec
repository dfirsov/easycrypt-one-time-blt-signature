pragma Goals:printall.

require import Int Real Distr SmtMap.

require import BLT_Instance.


(* If A^BLT_Wrap uses signing oracle at time t' and forges a signature
for the same time then we turn A^BLT_Wrap into adversary H_AdvCR(A)
who finds a collision of a hash function. *)

module H_AdvCR(A:BLT_Adv) = {

  var p1, p2 : message * tag
  var b : bool

  module G = BLTGame(Tag_Wrap, TsU, BLT_Wrap, A)

  proc adv() : (message * tag) * (message * tag) = {

   b <@ G.main();

   p1 <- (oget BLT_Wrap.qs, BLT_Wrap.qt);    
   p2 <- (BLTGame.m, BLTGame.tg);

   return (p1, p2);
  }

}.


section. 

declare module A <: BLT_Adv{-Tag_Wrap, -BLT_Wrap, -TsU, -BLTGame}.

axiom A_ll : forall (O <: BLT_AdvOracle{-A}), 
  islossless O.sign => islossless O.put => islossless O.get => islossless A(O).forge.


local lemma forgeInv0 :
 phoare [ A(BLT_Wrap(Tag_Wrap, TsU)).forge : 
     TsU.r = empty /\ TsU.t = TsU.i 
 /\  toTime BLT_Wrap.qt <= TsU.t
 /\  Tag_Wrap.usedFlag = BLT_Wrap.used
 /\  !BLT_Wrap.used /\ (Tag_Wrap.pk, Tag_Wrap.sk) \in keys 
 ==> BLT_Wrap.used => exists m, Some m = BLT_Wrap.qs 
        /\ TsU.r.[toTime BLT_Wrap.qt] 
        = Some (HMT.H (m, BLT_Wrap.qt), HT.H BLT_Wrap.qt) ] = 1%r.
proof. proc*.

call (_: (BLT_Wrap.used => exists m, Some m = BLT_Wrap.qs 
            /\ TsU.r.[toTime BLT_Wrap.qt] 
            = Some (HMT.H (m, BLT_Wrap.qt), (HT.H BLT_Wrap.qt)))
   /\ toTime BLT_Wrap.qt <= TsU.t
   /\ Tag_Wrap.usedFlag = BLT_Wrap.used
   /\ (Tag_Wrap.pk, Tag_Wrap.sk) \in keys).
apply A_ll.

proc. if. inline*. wp. skip. progress;smt.

wp. skip.  progress;smt.

proc. inline*. wp. skip. progress;smt.
proc. inline*. wp. skip. smt. 

skip. progress. 
qed.


local lemma reductionCR : 
  phoare [ HMT.CR_H(H_AdvCR(A)).main : true 
  ==> H_AdvCR.b /\ BLT_Wrap.used 
   /\ toTime BLT_Wrap.qt = toTime BLTGame.tg 
        => HMT.H H_AdvCR.p1 = HMT.H H_AdvCR.p2 
           /\ H_AdvCR.p1 <> H_AdvCR.p2 ] = 1%r.
proof. proc.
inline*. wp. call forgeInv0. wp. rnd predT.
wp. rnd predT. skip. progress. apply d_ll. 
apply keys_lossless.
smt. smt.
have : r <> empty. smt.
move => h1.
have : exists (m : message) (t'' : tag), (Some m) = qs 
      /\ r.[toTime qt] = Some (HMT.H (m, t''), HT.H t''). smt.
elim. move => m' t' ip.

smt. smt.
qed.


local lemma hzc &m : 
  (Pr[HMT.CR_H(H_AdvCR(A)).main() @ &m :
     H_AdvCR.b /\ BLT_Wrap.used 
 /\ toTime BLT_Wrap.qt = toTime BLTGame.tg
     =>  HMT.H H_AdvCR.p1 = HMT.H H_AdvCR.p2 
 /\ H_AdvCR.p1 <> H_AdvCR.p2 ] = 1%r) => 

  Pr[HMT.CR_H(H_AdvCR(A)).main() @ &m :
   !(H_AdvCR.b /\ BLT_Wrap.used 
 /\ toTime BLT_Wrap.qt = toTime BLTGame.tg 
     => HMT.H H_AdvCR.p1 = HMT.H H_AdvCR.p2 
 /\ H_AdvCR.p1 <> H_AdvCR.p2)] = 0%r.
proof. move => i. rewrite Pr [mu_not]. smt. qed.


local lemma reductionCRH : 
  hoare [ HMT.CR_H(H_AdvCR(A)).main : true 
  ==> H_AdvCR.b /\ BLT_Wrap.used 
  /\  toTime BLT_Wrap.qt = toTime BLTGame.tg 
       => HMT.H H_AdvCR.p1 = HMT.H H_AdvCR.p2 
       /\ H_AdvCR.p1 <> H_AdvCR.p2 ].
proof. bypr. move => &m. move=> _. apply (hzc &m).
byphoare. apply reductionCR. auto. auto. qed.


local lemma reductioneq' : 
  equiv [ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main ~ HMT.CR_H(H_AdvCR(A)).main :
  ={glob A}
  ==> res{1} = H_AdvCR.b{2} 
  /\ ={glob BLT_Wrap, glob BLTGame} ].
proof. proc.
inline*. wp.

call (_: ={glob TsU, glob BLT_Wrap, glob Tag_Wrap}).

proc. inline*. wp. skip. progress.
proc. inline*. wp. skip. smt.
proc. inline*. wp. skip. smt.

wp. rnd. wp. rnd. skip. progress.
qed.


local lemma reductioneq'' : 
  hoare [ HMT.CR_H(H_AdvCR(A)).main : true 
  ==> res = (HMT.H H_AdvCR.p1 = HMT.H H_AdvCR.p2
            /\ H_AdvCR.p1 <> H_AdvCR.p2) ]. 
proof. proc.
inline*. wp.

call (_:true).

proc. inline*. wp. skip. auto.
proc. inline*. wp. skip. auto.
proc. inline*. wp. skip. auto.

wp. rnd. wp. rnd. skip. smt.

qed.


local lemma reductioneq : 
  equiv [ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main ~ HMT.CR_H(H_AdvCR(A)).main
  : ={glob A} 
  ==> res{1} /\ BLT_Wrap.used{1} 
   /\ toTime BLT_Wrap.qt{1} = toTime BLTGame.tg{1} 
       => HMT.H H_AdvCR.p1{2} = HMT.H H_AdvCR.p2{2} 
       /\ H_AdvCR.p1{2} <> H_AdvCR.p2{2} ].
proof. 

conseq (_: ={glob A} ==> res{1} = H_AdvCR.b{2} 
  /\ ={glob BLT_Wrap, glob BLTGame}) (_:true ==> true) 
  (_:true ==> (H_AdvCR.b /\ BLT_Wrap.used 
              /\ toTime BLT_Wrap.qt = toTime BLTGame.tg 
              => HMT.H H_AdvCR.p1 = HMT.H H_AdvCR.p2 
              /\ H_AdvCR.p1 <> H_AdvCR.p2)).
auto. progress.

apply reductionCRH. apply reductioneq'.
qed.


local lemma reductioneqf : 
  equiv [ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main ~ HMT.CR_H(H_AdvCR(A)).main 
  : ={glob A} ==> res{1} /\ BLT_Wrap.used{1} 
  /\ toTime BLT_Wrap.qt{1} = toTime BLTGame.tg{1} => res{2} ].
proof. 

conseq (_: ={glob A} 
  ==> res{1} 
   /\ BLT_Wrap.used{1} 
   /\ toTime BLT_Wrap.qt{1} = toTime BLTGame.tg{1} => 
       (HMT.H H_AdvCR.p1 = HMT.H H_AdvCR.p2 /\ H_AdvCR.p1 <> H_AdvCR.p2){2}) 

  (_: true ==> true) 

  (_: true ==> 
    res = (HMT.H H_AdvCR.p1 = HMT.H H_AdvCR.p2 /\ H_AdvCR.p1 <> H_AdvCR.p2)).
smt.

proc. inline*. wp. call (_:true). 
proc. inline*. wp. skip. auto.
proc. inline*. wp. skip. auto.
proc. inline*. wp. skip. auto.

wp. rnd. wp. rnd. skip. auto.
conseq reductioneq''. conseq reductioneq.

qed.


lemma case3 &m :
  Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m 
      : res /\ BLT_Wrap.used /\ toTime BLTGame.tg = toTime BLT_Wrap.qt ] 
  <= Pr[ HMT.CR_H(H_AdvCR(A)).main() @ &m : res ].
proof. byequiv. 
conseq reductioneqf;smt. 
auto. auto. 
qed.

end section.
