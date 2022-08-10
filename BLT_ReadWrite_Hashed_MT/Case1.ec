pragma Goals : printall.

require import Int Real.

require import BLT_Instance.
require import RandomnessOracle.

section.

declare module RO <: ROracle.
declare module A <: BLT_Adv{-Tag_Wrap, -BLT_Wrap, -TsU, -BLT_Dummy, -TsU_Set, -RO}.
declare module A2 <: BLT_Adv_Set{-Tag_Wrap, -BLT_Wrap, -TsU, -BLT_Dummy, -TsU_Set, -A, -RO}.


axiom A_ll : forall (O <: BLT_AdvOracle{-A}), islossless O.sign => 
       islossless O.put => islossless O.get => islossless A(O).forge.

axiom A2_ll : islossless A2.react.

local lemma notUsed4A :
  equiv [ A(BLT_Dummy(Tag_Wrap, TsU_Set(A2))).forge 
           ~ A(BLT_Wrap(Tag_Wrap, TsU_Set(A2))).forge 
   : ={rs, glob A, pk,TsU.t, glob A2} /\ TsU.r{2} = TsU.r{1} /\ BLT_Wrap.qs{2} = None 
     /\ Tag_Wrap.pk{2} = Tag_Wrap.pk{1} 
    ==> !BLT_Wrap.used{2} => ={res, TsU.r}  /\ BLT_Wrap.qs{2} = None  /\ Tag_Wrap.pk{2} = Tag_Wrap.pk{1} ].
proof. proc*. 

call (_ : BLT_Wrap.used, 
  !BLT_Wrap.used{2} /\ TsU.r{2} = TsU.r{1} 
 /\ TsU.t{2} = TsU.t{1} 
 /\ BLT_Wrap.qs{2} = None 
 /\ Tag_Wrap.pk{2} = Tag_Wrap.pk{1} /\ ={glob A2}, BLT_Wrap.used{2}).
apply A_ll.

proc. rcondt {2} 1. move => &m. skip. smt. inline*.
wp. call {2} (_: true ==> true). apply A2_ll. wp. skip. smt. move => &2 a.  

proc. skip. smt. move => _. 

proc. if. inline*. wp. call (_:true). apply A2_ll. wp. skip. smt. wp. skip. smt.

proc. inline*. wp. call (_: true). wp. skip. progress. 

move => &2 a. proc. inline*.  wp. call (_:true). apply A2_ll. wp. skip. smt.
move => _. proc. inline*.  wp.  call (_:true). apply A2_ll. wp. skip. smt.

proc. inline*. wp. skip. smt.
move => &2 z. proc. inline*. wp. skip. smt.
move => _.  proc. inline*.  wp. skip. smt.
skip. progress; smt. 

qed.


(* if oracle was not used then adversary without it gets the same result *)
local lemma notUsed4G :
  equiv [ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Dummy, A).main ~ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main
   : ={glob A, glob A2, glob RO} ==> !BLT_Wrap.used{2} => ={res} ].
proof. proc. 
inline*. wp. call notUsed4A. wp. rnd. call (_:true).  skip. progress. smt. 
qed.


lemma case1 &m : Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : res /\ !BLT_Wrap.used ] <=
                 Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Dummy, A).main() @ &m : res ].
proof. byequiv. symmetry. conseq notUsed4G;smt. smt. smt. qed.

end section.
