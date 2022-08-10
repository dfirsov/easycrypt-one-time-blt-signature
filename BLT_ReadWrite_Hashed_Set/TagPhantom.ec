pragma Goals:printall.

require import FSet.
require import Int.
require import Real.
require import SmtMap.
require import Distr.


require import RandomnessOracle.
require import BLT_Instance.
import BST.



module BTG'(RO : ROracle, A2 : BLT_Adv_Set, A:BLT_Adv, O:Tag_Oracle) = {

  module BLT_O = BLT_Wrap(O, TsU_Set(A2))
  module A = A(BLT_O)
  module TsU_Set = TsU_Set(A2)

  proc forgeTag(pk:pkey, rs:int) = {
   var tg, m;
   var it : int;
   BLT_O.init();
   it  <@ RO.rndStr();
   TsU_Set.init(initialTime it);
   (m, tg) <@ A.forge(pk,rs);

   return tg;
  }

}.


section. 
declare module A <: BLT_Adv{-Tag_Wrap, -TsU, -RO, -BLT_Wrap}.
declare module A2 <: BLT_Adv_Set{-Tag_Wrap, -TsU, -A, -RO, -BLT_Wrap}.


local lemma tgcollision : 
  equiv [ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main ~ TagGamePhantom(RO, Tag_Wrap, BTG'(RO,A2,A)).main
  : ={glob A, glob A2, glob RO, glob Tag_Wrap, glob BLT_Wrap, glob TsU} ==> ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) <> BLTGame.tg)){1} => res{2} ].
proof. proc.

inline*. wp.

call (_: ={glob A2, glob RO, glob Tag_Wrap, glob BLT_Wrap, glob TsU}).

proc. if.  auto. inline*. wp. call (_:true). wp. skip. progress. wp. skip. smt.
proc. inline*.  wp. call (_:true). wp. skip. smt.
proc. inline*. wp. skip. smt.

wp.  wp. rnd. wp. rnd. skip. progress. smt.
qed.

lemma tgcollision_pr &m : 
  Pr [ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) <> BLTGame.tg)) ] <= Pr [ TagGamePhantom(RO, Tag_Wrap, BTG'(RO,A2,A)).main() @ &m  : res ].
byequiv (_: ={glob A, glob A2, glob RO, glob Tag_Wrap, glob BLT_Wrap, glob TsU} ==> ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) <> BLTGame.tg)){1} => res{2}).
conseq tgcollision. auto.
auto. auto.
qed.

end section.



