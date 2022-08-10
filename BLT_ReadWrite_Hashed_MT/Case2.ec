pragma Goals:printall.

require import Int Real.

require import BLT_Instance.
require import RandomnessOracle.


(* If adversary A^BLT_Wrap uses oracle at time t', but returns
signature with tag for time t so that t' < t then we use A to
construct adversary B(A) against tag-system. *)

module B(RO : ROracle,A:BLT_Adv, Ts_O:TS, O:Tag_Oracle) = {

  module BLT_O = BLT_Wrap(O, Ts_O)
  module A = A(BLT_O)

  proc forgeTag(pk:pkey, rs:int) = {
     var m : message;
     var tg : tag;
     var it : int;
     var c  : chain;
     it <@ RO.rndStr();

     Ts_O.init(initialTime it);
     BLT_Wrap.used <- false;
     BLT_Wrap.qt <- deftag;
     (m, tg, c) <@ A.forge(pk, rs);

     return tg;
  }
}.

section. 


declare module A <: BLT_Adv{-Tag_Wrap, -BLT_Wrap, -TsU, -RO}.
declare module A2 <: BLT_Adv_Set{-Tag_Wrap, -BLT_Wrap, -TsU, -A, -RO}.
              
local lemma mmm' : 
  equiv [ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main ~ TagGame(RO, Tag_Wrap, B(RO, A, TsU_Set(A2))).main : 
  ={glob A, glob A2} 
  ==> BLT_Wrap.used{1} 
   /\ toTime BLT_Wrap.qt{1} < toTime BLTGame.tg{1}
   /\ res{1} => res{2} ]. 
proof. proc.
inline*. wp.

call (_: ={glob Tag_Wrap, glob TsU, glob A2, glob RO} 
  /\ BLT_Wrap.qt{1} = Tag_Wrap.usedTag{2} 
  /\ BLT_Wrap.qt{2} = Tag_Wrap.usedTag{2} 
  /\ BLT_Wrap.used{1} = Tag_Wrap.usedFlag{2} 
  /\ Tag_Wrap.usedFlag{2} = BLT_Wrap.used{2}).

proc. inline*. wp. if. smt. wp. call (_:true). wp. skip. smt. skip. smt.
proc. inline*. wp. call (_:true). wp. skip. smt.
proc. inline*. wp. skip. smt.

wp.    wp. rnd. wp. rnd. skip. progress. smt.

qed.


lemma case2 &m : 
  Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : 
  (((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg))
   /\ toTime BLT_Wrap.qt < toTime BLTGame.tg ] <=
    Pr[ TagGame(RO, Tag_Wrap, B(RO, A, TsU_Set(A2))).main() @ &m : res ].
proof. byequiv. conseq mmm';smt. smt. smt. qed.

end section.
  
