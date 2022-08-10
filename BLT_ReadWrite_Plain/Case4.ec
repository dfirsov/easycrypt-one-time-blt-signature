pragma Goals:printall.

require import FSet.
require import Int.
require import Real.
require import SmtMap.
require import Distr.

require import BLT_Instance.

op hzc : (int -> message * tag -> bool)-> (int, (message * tag)) fmap -> (int * (message * tag)).  
axiom hzc_lemma (mp : (int, (message * tag)) fmap) t x (P : int -> message * tag -> bool) :  mp.[t] = (Some x) /\ P t x => exists t' e,  hzc P mp = (t' , e) /\ P t' e /\ t' <= t /\ P t' e /\ mp.[t'] = Some e.

module B_BLT(A:BLT_Adv, O:BLT_AdvOracle) = {

   module A = A(O) 
   proc forge(pk:pkey) = {
      var z, t, r;
      A.forge(pk);
      r <@ O.get();
      (t,z) <- hzc (fun (a:int) (b:message * tag) => a = toTime b.`2 && tagVerify pk a b.`2) r;
     
      return z;
    }
}.



section. 
declare module A <: BLT_Adv{-Tag_Wrap, -BLT_Wrap, -TsU}.


local module BA : BLT_Adv = B_BLT(A).  
local lemma opp : exists (A <: BLT_Adv{-Tag_Wrap, -BLT_Wrap, -TsU}), true.
proof. exists BA. done. qed.


axiom A_ll : forall (O <: BLT_AdvOracle{-A}), islossless O.sign => islossless O.put => islossless O.get => islossless A(O).forge.

local lemma wwwForB : 
  equiv [ BLTGame(Tag_Wrap, TsU, BLT_Dummy, B_BLT(A)).main ~ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main
  :  ={glob A} ==> res{2} /\ BLT_Wrap.used{2} /\ toTime BLTGame.tg{2} < toTime BLT_Wrap.qt{2} => (forall x, x < (toTime BLT_Wrap.qt{2}) /\ TsU.i{2} < x => TsU.r.[x]{1} = TsU.r.[x]{2}) /\ (forall x, x <= TsU.i{2} => x \notin TsU.r{2}) /\ (TsU.r.[toTime BLTGame.tg]{2} = Some (BLTGame.m, BLTGame.tg){2}) /\ res{1}  ]. 
proof. proc.
inline*. wp.

call (_: BLT_Wrap.used,   

  (0 <= TsU.i{2})  /\
     (TsU.i{2} <= TsU.t{2}) /\ (forall x, x <= TsU.i{2} => x \notin TsU.r{2})
 /\  ={glob TsU} /\ BLT_Wrap.used{2} = Tag_Wrap.usedFlag{2}  /\ 
   (forall x, x < toTime BLT_Wrap.qt{2} => TsU.i{2} < x => (TsU.r.[x]{2} = TsU.r.[x]{1}))
/\ (forall x, x <= TsU.t{2} => TsU.i{2} < x => x \in TsU.r{2})
/\ (Tag_Wrap.pk{2}, Tag_Wrap.sk{2}) \in keys /\ (forall y, y \in TsU.r{1} => y <= TsU.t{1}  ),    



((Tag_Wrap.usedFlag = BLT_Wrap.used) /\ ((Tag_Wrap.pk, Tag_Wrap.sk) \in keys /\ BLT_Wrap.used /\ Tag_Wrap.usedFlag  => TsU.r.[toTime BLT_Wrap.qt] = Some (oget BLT_Wrap.qs, BLT_Wrap.qt) /\ toTime BLT_Wrap.qt <= TsU.t)){2} 
 /\  (TsU.i{2} <= TsU.t{2}) /\ (forall x, x <= TsU.i{2} => x \notin TsU.r{2})
 /\  (forall x, x < toTime BLT_Wrap.qt{2} => TsU.i{2} < x => (TsU.r.[x]{2} = TsU.r.[x]{1}))
 /\ (forall x, x <= TsU.t{2} => TsU.i{2} < x => x \in TsU.r{2})
 /\ BLT_Wrap.used{2} /\ (toTime BLT_Wrap.qt{2} <= TsU.t{2}) /\ (Tag_Wrap.pk{2}, Tag_Wrap.sk{2}) \in keys  /\ (forall y, y \in TsU.r{1} => y <= TsU.t{1})). apply A_ll. 

proc. wp. if {2}. inline*. wp. skip.  progress;smt.
wp. skip. smt.
move => &2 z. proc. auto.
move => &1. proc. auto. 
if.  inline*. wp. skip. smt.
wp. skip. smt.
proc. inline*. wp. skip.
progress;smt. 
move => &2 z. proc. inline*.
wp. skip. progress. timeout 15. smt(@SmtMap). smt.
move => &2.  proc.  inline*. wp. skip.
progress;smt. 
(* get *)
proc. inline*.
wp. skip. smt.
move => &2 z. proc. inline*. wp. skip. smt.
move => &2.  proc. inline*.  wp. skip. smt.
wp.
rnd. wp. rnd. skip.  progress.
smt. smt . smt. smt. smt. smt. smt. 
have : r_L.[toTime result_R.`2] = r_R.[toTime result_R.`2].  smt.
move =>  h3.
have : exists t' e,  hzc (fun (a : int) (b : message * tag) =>
           a = toTime b.`2 && tagVerify pkskL.`1 a b.`2) r_L = (t' , e) /\ (fun (a : int) (b : message * tag) =>
           a = toTime b.`2 && tagVerify pkskL.`1 a b.`2) t' e /\ t' <= toTime result_R.`2 /\ (fun (a : int) (b : message * tag) =>
           a = toTime b.`2 && tagVerify pkskL.`1 a b.`2) t' e /\ r_L.[t'] = Some e.
apply (hzc_lemma r_L (toTime result_R.`2) result_R). smt.
move => qq. elim qq.
move => qq1 qq2.  move => qq3. smt.
have : exists t' e,  hzc (fun (a : int) (b : message * tag) =>
           a = toTime b.`2 && tagVerify pkskL.`1 a b.`2) r_L = (t' , e) /\ (fun (a : int) (b : message * tag) =>
           a = toTime b.`2 && tagVerify pkskL.`1 a b.`2) t' e /\ t' <= toTime result_R.`2 /\ (fun (a : int) (b : message * tag) =>
           a = toTime b.`2 && tagVerify pkskL.`1 a b.`2) t' e /\ r_L.[t'] = Some e.
apply (hzc_lemma r_L (toTime result_R.`2) result_R). smt.
move => qq. elim qq.
move => qq1 qq2.  move => qq3. elim qq3. simplify.  move => opp. rewrite opp. 
smt. 
have : exists t' e,  hzc (fun (a : int) (b : message * tag) =>
           a = toTime b.`2 && tagVerify pkskL.`1 a b.`2) r_L = (t' , e) /\ (fun (a : int) (b : message * tag) =>
           a = toTime b.`2 && tagVerify pkskL.`1 a b.`2) t' e /\ t' <= toTime result_R.`2 /\ (fun (a : int) (b : message * tag) =>
           a = toTime b.`2 && tagVerify pkskL.`1 a b.`2) t' e /\ r_L.[t'] = Some e.
apply (hzc_lemma r_L (toTime result_R.`2) result_R). smt.
move => qq. elim qq.
move => qq1 qq2.  move => qq3. elim qq3. simplify.  move => opp. rewrite opp. smt.
qed.


local lemma gl : 
  equiv [ BLTGame(Tag_Wrap, TsU, BLT_Dummy, B_BLT(A)).main ~ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main
  :  ={glob A} ==> res{2} /\ BLT_Wrap.used{2} /\ toTime BLTGame.tg{2} < toTime BLT_Wrap.qt{2} =>  res{1}  ]. 
proof. conseq wwwForB. progress. smt. qed.


lemma case4 &m : Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : (res /\ BLT_Wrap.used) /\ toTime BLTGame.tg < toTime BLT_Wrap.qt ] <= Pr[ BLTGame(Tag_Wrap, TsU, BLT_Dummy, B_BLT(A)).main() @ &m : res ].
proof. byequiv. symmetry. conseq wwwForB. smt. smt. smt. smt. qed.

 
end section.
