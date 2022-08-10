pragma Goals:printall.

require import AllCore.
require import BLT_Instance.
require import Security.


(* BLT Scheme inherits its security from the underlying tag system. *)

lemma BLT_Scheme_security &m (A <: BLT_Adv{-BLT_Wrap, -TsU, -Tag_Wrap, -BLT_Pure}) : 
 (forall (O <: BLT_AdvOracle{-A}),
   islossless O.sign => islossless O.put => islossless O.get => islossless A(O).forge) =>

    Pr[ BLTGame(Tag_Wrap, TsU, BLT_Pure, A).main() @ &m : res ] <= 
    Pr[ TagGame(Tag_Wrap, BTG(B_BLT(A))).main() @ &m : res ]
  + Pr[ TagGame(Tag_Wrap, B(A, TsU)).main() @ &m : res ]
  + Pr[ TagGame(Tag_Wrap, BTG(A)).main() @ &m : res ].

proof. move => ll. apply (final_security  A (* ll *) &m).
qed.


(* 

Note that it would be simple to implement TagGame
adversary who will always win by simply reading the Tag_Wrap.sk.

Hence, we also need to show that memories of constructed TagGame
adversaries are disjoint from oracle Tag_Wrap.

One needs to check the proof to verify that the correct adversary is
provided as a witness.

*)

lemma BTG_TagWrap_disjoint_Adv1 (A <: BLT_Adv{-Tag_Wrap}) : 
  exists (B <: Tag_Adv{-Tag_Wrap}), true.
proof. exists (BTG(B_BLT(A))). done. qed.

lemma BTG_TagWrap_disjoint_Adv2 (A <: BLT_Adv{-Tag_Wrap}) : 
  exists (B <: Tag_Adv{-Tag_Wrap}), true.
proof. exists (B(A, TsU)). done. qed.

lemma BTG_TagWrap_disjoint_Adv3 (A <: BLT_Adv{-Tag_Wrap}) : 
  exists (B <: Tag_Adv{-Tag_Wrap}), true.
proof. exists (BTG(A)). done. qed.
