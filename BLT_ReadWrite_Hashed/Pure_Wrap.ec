pragma Goals:printall.

require import FSet.
require import Int.
require import Real.
require import SmtMap.
require import Distr.

require import BLT_Instance.

section. 
declare module A <: BLT_Adv{-Tag_Wrap, -BLT_Wrap, -TsU, -BLT_Pure}.
declare module Tag_O <: Tag_Oracle{-BLTGame, -BLT_Wrap, -BLT_Pure, -A}.
declare module Ts_O <: TS{-BLTGame, -BLT_Wrap, -BLT_Pure, -Tag_O, -A}.


lemma pure_wrap_eq : 
  equiv [ BLTGame(Tag_O, Ts_O, BLT_Pure, A).main ~ BLTGame(Tag_O, Ts_O, BLT_Wrap, A).main
  : ={glob A, glob Ts_O, glob Tag_O} ==> ={res} ].
proof. proc. inline*. wp.
call (_:true).
call (_:true).
wp.
call (_: ={used, qs, qt}(BLT_Pure, BLT_Wrap) /\ ={glob Ts_O, glob Tag_O}   ).
proc. auto. if.  auto. wp. call (_: ={glob Ts_O, glob Tag_O} ). call (_:true). wp. call(_:true). call(_:true).
skip. progress. wp. skip. progress. wp. skip. progress. auto.

proc. call (_:true). wp. skip. auto.

proc. call (_:true). wp. skip. auto.

wp. call(_:true). wp. call(_:true). skip. progress. 
qed.

end section.
