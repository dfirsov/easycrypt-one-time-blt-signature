pragma Goals:printall.

require import FSet Int Real SmtMap Distr.

require import RandomnessOracle.
require import BLT_Instance.


module BTG(RO : ROracle, A2 : BLT_Adv_Set, A:BLT_Adv, O:Tag_Oracle) = {

  module BLT_O = BLT_Dummy(O, TsU_Set(A2))
  module A = A(BLT_O)
  module TsU_Set = TsU_Set(A2)

  proc forgeTag(pk:pkey, rs:int) = {
   var tg, m, c;
   var it : int;
   it  <@ RO.rndStr();
   TsU_Set.init(initialTime it);
   (m, tg, c) <@  A.forge(pk,rs);

   return tg;
  }

}.


section. 
declare module A <: BLT_Adv{-Tag_Wrap, -TsU, -RO}.
declare module A2 <: BLT_Adv_Set{-Tag_Wrap, -TsU, -A, -RO}.


local lemma bbbla : 
  equiv [ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Dummy, A).main ~ TagGame(RO, Tag_Wrap, BTG(RO,A2,A)).main
  : ={glob A, glob A2, glob RO, glob Tag_Wrap} ==>  res{1} => res{2} ].

proof. proc.    

inline*. wp. call (_: ={glob RO,glob Tag_Wrap, glob TsU, glob A2} /\ (forall x, x \in TsU.r{1} => 0 < x) /\ 0 <= TsU.i{1} /\ TsU.i{1} <= TsU.t{1} ).

proc. skip. smt.
proc. inline*. wp.  call (_:true). wp. skip. progress. smt. smt.
proc. inline*. wp. skip. progress.  swap {2} 12 -8. wp. rnd. wp. rnd. skip.

progress. smt. smt. 

have : toTime deftag = 0. smt.
move => dtt. rewrite dtt. clear dtt.
smt. 

qed.

lemma blt_dummy_tag_pr &m : 
  Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Dummy, A).main() @ &m : res ] <=
    Pr[ TagGame(RO, Tag_Wrap, BTG(RO, A2, A)).main() @ &m : res ].
proof. byequiv (_: ={glob A, glob A2, glob RO, glob Tag_Wrap} ==>  res{1} => res{2}).  conseq bbbla. progress. smt. auto. qed.

end section.
