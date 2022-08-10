pragma Goals:printall.

require import FSet.
require import Int.

require import Real.
require import SmtMap.
require import Distr.


require import BLT_Instance.
import BST.



module BTG(A:BLT_Adv, O:Tag_Oracle) = {

  module BLT_O = BLT_Dummy(O, TsU)
  module A = A(BLT_O)


  proc forgeTag(pk:pkey) = {
   var tg, m;
   TsU.init();
   (m, tg) <@ A.forge(pk);

   return (toTime tg, tg);
  }

}.


section. 
declare module A <: BLT_Adv{-Tag_Wrap, -TsU}.


local lemma bbbla : 
  equiv [ BLTGame(Tag_Wrap, TsU, BLT_Dummy, A).main ~ TagGame(Tag_Wrap, BTG(A)).main
  : ={glob A} ==>  res{1} => res{2} ].

proof. proc.    

inline*. wp.


  call (_: ={glob Tag_Wrap, glob TsU} /\ (forall x, x \in TsU.r{1} => 0 < x) /\ 0 <= TsU.i{1} /\ TsU.i{1} <= TsU.t{1} ).

proc. skip. smt.
proc. inline*. wp. skip. progress.
smt. smt.

proc. inline*. wp. skip. progress. 

wp. swap {2} 6 -5.
 wp. rnd.

wp. rnd.

skip.

progress.

smt.
smt.
have : toTime deftag = 0. smt.
move => dtt. rewrite dtt. clear dtt.
smt. qed.



lemma blt_dummy_tag_pr &m : 
  Pr[ BLTGame(Tag_Wrap, TsU, BLT_Dummy, A).main() @ &m : res ] <=
    Pr[ TagGame(Tag_Wrap, BTG(A)).main() @ &m : res ].
proof. byequiv.  conseq bbbla;smt. smt. smt. qed.

end section.
