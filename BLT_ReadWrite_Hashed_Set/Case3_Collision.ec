
pragma Goals:printall.

require import Int Real Distr SmtMap FSet.

require import BLT_Instance.
require import RandomnessOracle.

module H_AdvCR(A:BLT_Adv, A2 : BLT_Adv_Set) = {

  var p1, p2 : message * tag
  var b : bool

  module G = BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A)

  proc adv() : message * message = {

   b <@ G.main();

   return (oget BLT_Wrap.qs, BLTGame.m);
  }

}.




section. 

declare module A <: BLT_Adv{-Tag_Wrap, -BLT_Wrap, -TsU, -BLTGame,  -TsU, -Tag_Wrap, -H_AdvCR}.
declare module A2 <: BLT_Adv_Set{-Tag_Wrap, -BLT_Wrap, -TsU, -A, -BLTGame, -TsU, -Tag_Wrap, -H_AdvCR}.

local lemma reductioneqf : 
  equiv [ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main ~ HM.CR_H(H_AdvCR(A, A2)).main 
  : ={glob A, glob A2} ==> res{1} /\ BLT_Wrap.used{1} 
  /\ toTime BLT_Wrap.qt{1} = toTime BLTGame.tg{1} /\ HM.H (oget BLT_Wrap.qs{1}) = (HM.H BLTGame.m{1}) => res{2} ].
proof.  
proc.
inline*. wp. call (_: ={glob TsU, glob BLT_Wrap, glob Tag_Wrap, glob A2} /\ (BLT_Wrap.used{1} => BLT_Wrap.qs{1} <> None)). 
proc. if. auto. inline*. wp. call (_:true). wp. skip. progress.  wp. skip. progress.
proc. inline*. wp. call (_:true). wp. skip. progress. 
proc. inline*. wp.  skip. progress.
wp. rnd.   wp. rnd. progress.  wp.  skip.
progress.

have : qs_R <> None. smt.
move => qsrnn.

have : exists z, qs_R = Some z. smt.
elim. move => z prfz.
rewrite prfz.
simplify oget.



smt.
qed.


lemma case3_collision &m :
  Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ toTime BLTGame.tg = toTime BLT_Wrap.qt /\ HM.H (oget BLT_Wrap.qs) = (HM.H BLTGame.m) ]
  <= Pr[ HM.CR_H(H_AdvCR(A, A2)).main() @ &m : res ].
proof. byequiv. 
conseq reductioneqf;smt. 
auto. auto. 
qed.

end section.

