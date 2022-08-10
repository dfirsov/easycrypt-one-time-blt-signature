pragma Goals:printall.

require import FSet.
require import Int.
require import Real.
require import SmtMap.
require import Distr.

require import BLT_Instance.

section. 

declare module A <: BLT_Adv{-Tag_Wrap, -BLT_Wrap, -TsU}.

axiom A_ll : forall (O <: BLT_AdvOracle{-A}), islossless O.sign => islossless O.put => islossless O.get => islossless A(O).forge.

local lemma www'' : 
  phoare [ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main
    :  true ==>  res /\ BLT_Wrap.used => TsU.r.[toTime BLT_Wrap.qt] = Some (oget BLT_Wrap.qs, BLT_Wrap.qt) /\ TsU.r.[toTime BLTGame.tg] = Some (BLTGame.m, BLTGame.tg) /\ toTime BLTGame.tg <> toTime BLT_Wrap.qt  ] = 1%r. 
proof. proc.
inline*. wp.
call (_: (0 <= TsU.i) /\ (TsU.i <= TsU.t) /\ (Tag_Wrap.usedFlag = BLT_Wrap.used) /\ ((Tag_Wrap.pk, Tag_Wrap.sk) \in keys /\ BLT_Wrap.used /\ Tag_Wrap.usedFlag  => TsU.r.[toTime BLT_Wrap.qt] = Some (oget BLT_Wrap.qs, BLT_Wrap.qt) /\ BLT_Wrap.qs = Some (oget BLT_Wrap.qs) /\ toTime BLT_Wrap.qt <= TsU.t)  ). apply A_ll.

proc. inline*. if.  sp 4. if.
 
wp. skip. progress.
smt.  smt.  smt. wp. skip. progress. 
wp. skip. smt.

proc. inline*.  wp. skip.  progress. 
smt.  
smt (@SmtMap).  smt. smt.


(* get *)
proc. inline*.
wp. skip. smt.

wp. rnd predT. wp. rnd predT. skip. progress. smt. smt. smt. smt. smt. qed.


local lemma case3' &m : 
Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : res /\ BLT_Wrap.used => TsU.r.[toTime BLT_Wrap.qt] = Some (oget BLT_Wrap.qs, BLT_Wrap.qt) /\ BLT_Wrap.qs = Some (oget BLT_Wrap.qs) /\ TsU.r.[toTime BLTGame.tg] = Some (BLTGame.m, BLTGame.tg) /\ toTime BLTGame.tg <> toTime BLT_Wrap.qt  ] <=
  Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : res /\ BLT_Wrap.used => toTime BLTGame.tg <> toTime BLT_Wrap.qt   ].
proof. rewrite Pr [mu_sub]. smt. trivial. qed.

local lemma case3'' &m : 
  Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : res /\ BLT_Wrap.used => TsU.r.[toTime BLT_Wrap.qt] = Some (oget BLT_Wrap.qs, BLT_Wrap.qt) /\  TsU.r.[toTime BLTGame.tg] = Some (BLTGame.m, BLTGame.tg) /\ toTime BLTGame.tg <> toTime BLT_Wrap.qt  ] = 1%r.
proof. byphoare. conseq www''. progress;smt. smt. qed.



local lemma case3''' &m : Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : res /\ BLT_Wrap.used => toTime BLTGame.tg <> toTime BLT_Wrap.qt   ] >= 1%r.
proof.  rewrite - (case3'' &m). rewrite Pr [mu_sub]. smt. done. qed.

local lemma case3'''' &m : Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : ! (res /\ BLT_Wrap.used => toTime BLTGame.tg <> toTime BLT_Wrap.qt) ] = 0%r.
proof.  rewrite Pr [mu_not]. smt. qed.

(* de morgan *)
lemma case3 &m : Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : res /\ BLT_Wrap.used /\ toTime BLTGame.tg = toTime BLT_Wrap.qt ] = 0%r.
proof. smt. qed.


end section.
