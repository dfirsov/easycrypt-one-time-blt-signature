pragma Goals:printall.

require import Int Real.

require import BLT_Instance.


(* If adversary A^BLT_Wrap uses oracle at time t', but returns
signature with tag for time t so that t' < t then we use A to
construct adversary B(A) against tag-system. *)

module B(A:BLT_Adv, Ts_O:TS, O:Tag_Oracle) = {

  module BLT_O = BLT_Wrap(O, Ts_O)
  module A = A(BLT_O)

  proc forgeTag(pk:pkey) = {
     var m : message;
     var tg : tag;

     Ts_O.init();
     BLT_Wrap.used <- false;
     BLT_Wrap.qt <- deftag;
     (m, tg) <@ A.forge(pk);

     return (toTime tg, tg);
  }
}.

section. 

declare module A <: BLT_Adv{-Tag_Wrap, -BLT_Wrap, -TsU}.
              
local lemma mmm' : 
  equiv [ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main ~ TagGame(Tag_Wrap, B(A, TsU)).main : 
  ={glob A} 
  ==> BLT_Wrap.used{1} 
   /\ toTime BLT_Wrap.qt{1} < toTime BLTGame.tg{1}
   /\ res{1} => res{2} ]. 
proof. proc.
inline*. wp.

call (_: ={glob Tag_Wrap, glob TsU} 
  /\ BLT_Wrap.qt{1} = Tag_Wrap.usedTag{2} 
  /\ BLT_Wrap.qt{2} = Tag_Wrap.usedTag{2} 
  /\ BLT_Wrap.used{1} = Tag_Wrap.usedFlag{2} 
  /\ Tag_Wrap.usedFlag{2} = BLT_Wrap.used{2}).

proc. inline*. wp. skip. smt.  
proc. inline*. wp. skip. smt.
proc. inline*. wp. skip. smt.

wp. swap {2} 6 -5. wp.
rnd. wp. rnd. skip.  progress. smt.

qed.


lemma case2 &m : 
  Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : 
  (res /\ BLT_Wrap.used)
   /\ toTime BLT_Wrap.qt < toTime BLTGame.tg ] <=
    Pr[ TagGame(Tag_Wrap, B(A, TsU)).main() @ &m : res ].
proof. byequiv. conseq mmm';smt. smt. smt. qed.

end section.
