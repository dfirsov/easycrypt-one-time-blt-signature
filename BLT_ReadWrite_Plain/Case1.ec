pragma Goals:printall.

require import Int Real.
require import BLT_Instance.

(*

If adversary A^BLT_Wrap wins without using the oracle signing oracle (BLT_Wrap) then 
A^BLT_Dummy also wins (where BLT_Dummy is a fake oracle). 

*)

section.

declare module A <: BLT_Adv{- Tag_Wrap, -BLT_Wrap, -TsU}.

axiom A_ll : forall (O <: BLT_AdvOracle{-A}), islossless O.sign => 
       islossless O.put => islossless O.get => islossless A(O).forge.

local lemma notUsed4A :
  equiv [ A(BLT_Dummy(Tag_Wrap, TsU)).forge 
           ~ A(BLT_Wrap(Tag_Wrap, TsU)).forge 
   : ={glob A, pk,TsU.t} /\ TsU.r{2} = TsU.r{1} /\ BLT_Wrap.qs{2} = None 
     /\ Tag_Wrap.pk{2} = Tag_Wrap.pk{1} 
    ==> !BLT_Wrap.used{2} => ={res, TsU.r}  /\ BLT_Wrap.qs{2} = None  /\ Tag_Wrap.pk{2} = Tag_Wrap.pk{1} ].
proof. proc*. 
call (_ : BLT_Wrap.used, 
  !BLT_Wrap.used{2} /\ TsU.r{2} = TsU.r{1} 
 /\ TsU.t{2} = TsU.t{1} 
 /\ BLT_Wrap.qs{2} = None 
 /\ Tag_Wrap.pk{2} = Tag_Wrap.pk{1}, BLT_Wrap.used{2}).
apply A_ll.
proc. rcondt {2} 1. move => &m. skip. smt. inline*.
wp. skip. smt. move => &2 a.  
proc. skip. smt. move => _. 
proc. if. inline*. wp. skip. smt. wp. skip. smt.
proc. inline*. wp. skip. progress. 
move => &2 a. proc. inline*.  wp. skip. smt.
move => _. proc. inline*.  wp. skip. smt.
proc. inline*. wp. skip. smt.
move => &2 z. proc. inline*. wp. skip. smt.
move => _.  proc. inline*.  wp. skip. smt.
skip. progress; smt. 
qed.


(* if oracle was not used then adversary without it gets the same result *)
local lemma notUsed4G :
  equiv [ BLTGame(Tag_Wrap, TsU, BLT_Dummy, A).main ~ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main
   : ={glob A} ==> !BLT_Wrap.used{2} => ={res} ].
proof. proc. 
inline*. wp. call notUsed4A. wp. rnd. wp. rnd. skip. progress. smt. 
qed.


lemma case1 &m : Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : res /\ !BLT_Wrap.used ] <=
                 Pr[ BLTGame(Tag_Wrap, TsU, BLT_Dummy, A).main() @ &m : res ].
proof. byequiv. symmetry. conseq notUsed4G;smt. smt. smt. qed.

end section.
