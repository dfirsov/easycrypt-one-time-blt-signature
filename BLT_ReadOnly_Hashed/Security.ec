pragma Goals:printall.

require import FSet Int Real SmtMap Distr.

require import BLT_Instance.


(* converting BLT_Adv_RO into adversary who breaks collision resistance of H *)
module H_AdvCR(A:BLT_Adv_RO) = {

  var p1, p2 : (message * tag)
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

declare module A <: BLT_Adv_RO{-BLT_Wrap, -Tag_Wrap, -TsU, -H_AdvCR}.

axiom A_ll : forall (O <: BLT_AdvOracle{-A}), islossless O.get => islossless O.sign => islossless A(O).forge.


local lemma forgeInv1'  :
 phoare [ A(BLT_Wrap(Tag_Wrap, TsU)).forge : TsU.r = empty /\ TsU.t = TsU.i ==>
    forall y, TsU.r.[toTime BLT_Wrap.qt] = y => y <> None
           => exists m, (Some m) = BLT_Wrap.qs 
          /\ y = Some (H (m, BLT_Wrap.qt))  ] = 1%r.
proof. proc*.

call (_: (forall y, TsU.r.[toTime BLT_Wrap.qt] = y => y <> None => exists m, (Some m) = BLT_Wrap.qs 
     /\ y = (Some (H (m, BLT_Wrap.qt)) ))
     /\ (!BLT_Wrap.used => TsU.r = empty)).

apply A_ll.

proc. inline*. wp. skip. smt.
proc. if. inline*. wp. skip. progress. smt. smt. 

wp. skip.  progress. skip. progress. smt. 
qed.


local lemma forgeInv1  :
 phoare [ A(BLT_Wrap(Tag_Wrap, TsU)).forge : TsU.r = empty /\ TsU.t = TsU.i ==>
    forall i y, TsU.r.[i] = y => y <> None
           => exists m, (Some m) = BLT_Wrap.qs 
          /\ y = Some (H (m, BLT_Wrap.qt))  ] = 1%r.
proof. proc*.

call (_: (forall i y, TsU.r.[i] = y => y <> None => exists m, (Some m) = BLT_Wrap.qs 
     /\ y = (Some (H (m, BLT_Wrap.qt)) ))
     /\ (!BLT_Wrap.used => TsU.r = empty)).

apply A_ll.

proc. inline*. wp. skip. smt.
proc. if. inline*. wp. skip. progress. smt. smt. 

wp. skip.  progress. skip. progress. smt. 
qed.



local lemma forgeInv2 : phoare [ A(BLT_Wrap(Tag_Wrap, TsU)).forge : TsU.r = empty /\ TsU.t = TsU.i /\ (Tag_Wrap.usedFlag = BLT_Wrap.used) ==>
      (forall i, i <= TsU.t /\ TsU.i < i => TsU.r.[i] <> None)
   /\ (card (fdom TsU.r)) <= 1
   /\  TsU.t = TsU.i + (card (fdom TsU.r)) ] = 1%r.
proof.  proc*.
call (_: (Tag_Wrap.usedFlag = BLT_Wrap.used) /\ ((forall i, i <= TsU.t /\ TsU.i < i => TsU.r.[i] <> None) ) /\  (!BLT_Wrap.used => TsU.r = empty) /\ (card (fdom TsU.r)) <= 1 /\  TsU.t = TsU.i + (card (fdom TsU.r))).
apply A_ll.

proc. inline*. wp. skip. smt.

proc.
if.
inline*.
wp.
skip.
progress. smt.
have z:= H0 H2.
rewrite z. 
  simplify.
rewrite fdom_set.
smt.
have z:= H0 H2.
rewrite z.

have : card (fdom empty<:int, hash_output>) = 0. smt.
move => o.

rewrite o.
simplify.
rewrite fdom_set.
 smt. smt. smt. smt. 
wp. skip.
smt.
skip. progress. smt. smt. smt. qed.


local lemma forgeInv1And2 : phoare [ A(BLT_Wrap(Tag_Wrap, TsU)).forge : TsU.r = empty /\ TsU.t = TsU.i /\ (Tag_Wrap.usedFlag = BLT_Wrap.used) ==>
      ((forall i, i <= TsU.t /\ TsU.i < i => TsU.r.[i] <> None)
        /\  (card (fdom TsU.r)) <= 1
        /\ TsU.t = TsU.i + (card (fdom TsU.r)))
   /\ (forall i y, TsU.r.[i] = y => y <> None => exists m, (Some m) = BLT_Wrap.qs 
         /\ y = (Some (H (m, BLT_Wrap.qt)))) ] = 1%r.
proof. phoare split 1%r 1%r 1%r.
trivial. apply  forgeInv2. conseq  forgeInv1. progress. progress.
proc*.
seq 1: ((forall (i : int), i <= TsU.t /\ TsU.i < i => TsU.r.[i] <> None) /\   (card (fdom TsU.r)) <= 1 /\ TsU.t = TsU.i + (card (fdom TsU.r))). 
call (_:true). auto. auto. skip. auto.
call  forgeInv2. auto.
 progress. skip.  smt.
  phoare split ! 1%r 1%r. trivial.
call  forgeInv2. auto.
call  forgeInv2. auto.
auto.
qed.


local lemma forgeInvsConseq : phoare [ A(BLT_Wrap(Tag_Wrap, TsU)).forge : TsU.r = empty /\ TsU.t = TsU.i  /\ (Tag_Wrap.usedFlag = BLT_Wrap.used) ==>
      (TsU.r <> empty =>
           exists m, (Some m) = BLT_Wrap.qs /\ TsU.r.[TsU.t] = (Some (H (m, BLT_Wrap.qt)))) 
 /\  ((forall i, i <= TsU.t /\ TsU.i < i => TsU.r.[i] <> None) 
        /\ (card (fdom TsU.r)) <= 1 /\ TsU.t = TsU.i + (card (fdom TsU.r)))
 /\
    (forall i y, TsU.r.[i] = y => y <> None => exists m, (Some m) = BLT_Wrap.qs /\ y = (Some (H (m, BLT_Wrap.qt)))) ] = 1%r.
proof. conseq forgeInv1And2. progress.
have : 0 < card (fdom r). smt. 
move => h1.
smt.  qed.


local lemma mapFact ['a, 'b] (r : (int, 'b) fmap) q q' i j : 
  card (fdom r) = 1 => r.[j] = Some q => r.[i] = Some q' => i = j.
proof.  
move => z1 z2 z3.
have : j \in (fdom r). smt.
have : i \in (fdom r). smt.
move => ih1 ih2.
case (i = j). smt.
move => q''.
have : j \in (fdom r) `\` fset1 i. smt.
smt.
qed.


(* local lemma reductionCR' : phoare [ CR_H(H_AdvCR(A)).main : true ==> *)
(*   H_AdvCR.b => H H_AdvCR.p1 = H H_AdvCR.p2 /\ H_AdvCR.p1 <> H_AdvCR.p2 ] = 1%r. *)
(* proof. proc. *)
(* inline*. *)
(* wp. *)
(* call forgeInv1'. wp. rnd predT. *)
(* wp. rnd predT. skip. *)
(* progress. apply d_ll. apply keys_lossless. *)
(* timeout 20. smt. *)
(* admit. *)

(* have : r <> empty. smt. *)
(* move => h1. *)
(* smt.  *)
(* qed. *)

local lemma reductionCR : phoare [ CR_H(H_AdvCR(A)).main : true ==>
  H_AdvCR.b => H H_AdvCR.p1 = H H_AdvCR.p2 /\ H_AdvCR.p1 <> H_AdvCR.p2 ] = 1%r.
proof. proc.
inline*.
wp.
call forgeInvsConseq. wp. rnd predT.
wp. rnd predT. skip.
progress. apply d_ll. apply keys_lossless.
have : r <> empty. smt.
move => h1.
have : exists (m : message) (t'' : tag), (Some m) = qs 
      /\ r.[v + card (fdom r)] = Some ((H (m, t''))). smt.
elim. move => m' t' ip.

have : card (fdom r) = 1. smt.
move => hh.    
smt.
have : toTime result.`2 = v + card (fdom r).  timeout 20. smt.
move => hhh. 
smt. 
qed.


local lemma hzc &m : (Pr[CR_H(H_AdvCR(A)).main() @ &m :
     (H_AdvCR.b => H H_AdvCR.p1 = H H_AdvCR.p2 /\ H_AdvCR.p1 <> H_AdvCR.p2)] =
  1%r) => (Pr[CR_H(H_AdvCR(A)).main() @ &m :
     !(H_AdvCR.b => H H_AdvCR.p1 = H H_AdvCR.p2 /\ H_AdvCR.p1 <> H_AdvCR.p2)] =
  0%r).
proof. move => i. rewrite Pr [mu_not]. smt. qed.

local lemma reductionCRH : hoare [ CR_H(H_AdvCR(A)).main : true ==>
  H_AdvCR.b => (H H_AdvCR.p1) = (H H_AdvCR.p2) /\ H_AdvCR.p1 <> H_AdvCR.p2 ].
proof. bypr. move => &m. move => q. apply (hzc &m).
byphoare. apply reductionCR. auto. auto. qed.


local lemma reductioneq' : equiv [ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main ~ CR_H(H_AdvCR(A)).main : ={glob A} ==>  res{1} = H_AdvCR.b{2} ].
proof. proc.
inline*. wp.
call (_: ={glob TsU, glob BLT_Wrap, glob Tag_Wrap} ).
proc.
inline*. wp. skip. auto.
proc.  inline*. wp. skip. smt.
wp. rnd. wp. rnd.
skip. progress.  qed.


lemma reductioneq : equiv [ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main ~ CR_H(H_AdvCR(A)).main : ={glob A} ==>  res{1} => (H H_AdvCR.p1){2} = (H H_AdvCR.p2){2} /\ H_AdvCR.p1{2} <> H_AdvCR.p2{2} ].
proof. conseq (_: ={glob A} ==> res{1} = H_AdvCR.b{2}) (_:true ==> true ) (_:true ==> (H_AdvCR.b => (H H_AdvCR.p1) = (H H_AdvCR.p2) /\ H_AdvCR.p1 <> H_AdvCR.p2)).
auto.
progress.
apply reductionCRH.
apply reductioneq'.
qed.


local lemma reductioneq'' : hoare [ CR_H(H_AdvCR(A)).main : true ==>  res = ((H H_AdvCR.p1) = (H H_AdvCR.p2) /\ H_AdvCR.p1 <> H_AdvCR.p2) ]. 
proc. inline*.
wp.
call (_:true).
proc. inline*. wp. skip. auto.
proc. inline*. wp. skip. auto.
wp.
rnd. wp. rnd.  skip. smt.
qed.


local lemma reductioneqf : equiv [ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main ~ CR_H(H_AdvCR(A)).main : ={glob A} ==>  res{1} => res{2} ].
proof. conseq (_: ={glob A} ==> res{1} => (((H H_AdvCR.p1) = (H H_AdvCR.p2) /\ H_AdvCR.p1 <> H_AdvCR.p2)){2}) (_:true ==> true ) (_:true ==> res = ((H H_AdvCR.p1) = (H H_AdvCR.p2) /\ H_AdvCR.p1 <> H_AdvCR.p2)  ). smt.
proc. inline*. wp. call(_:true). 
proc. inline*. wp.  skip. auto.
proc. inline*. wp.  skip. auto.
wp. rnd. wp. rnd. skip. auto.
conseq reductioneq''. 
conseq reductioneq.
qed.

  
lemma final_sec &m :
     Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : res ] 
  <= Pr [ CR_H(H_AdvCR(A)).main() @ &m : res ].
proof. byequiv. conseq reductioneqf. auto. auto. auto. qed.

end section.
