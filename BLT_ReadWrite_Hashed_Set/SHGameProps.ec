pragma Goals:printall.

require import FSet.
require import Int.
require import Real.
require import SmtMap.
require import Distr.


require import RandomnessOracle.
require import BLT_Instance.

require import SHGame.

module MyA(Ts_O : TS, A : BLT_AdvH, O : Tag_Oracle, RO : ROracle) = {

  var y : hash_output fset

  proc main(pk : pkey) = {
    var it : int;
    var tg : tag;
    var m : message;
    var r : int;
    
    it <@ RO.rndStr();
    
    (y, r) <@ A.forge(pk , it);

    return r;
  }

}.

module MyB(RO : ROracle, O : SH_OracleT) = {
  proc main(pk : pkey) = {
    return MyA.y; 
  }
}.

module MyC(RO : ROracle, O : Tag_Oracle) = {
  proc main(pk : pkey) = {
    return EMPTY; 
  }
}.

section. 

declare module A <: BLT_AdvH{-Tag_Wrap, -RO, -BLT_Wrap, -SHGame}.
declare module A2 <: BLT_Adv_Set{-Tag_Wrap, -RO, -BLT_Wrap, -SHGame}.

lemma main_sh_security &m : 
   Pr[ SHGameSimple(RO, Tag_Wrap,  A).main() @ &m : res] 
  <= Pr[ SHGame(RO, MyA(TsU_Set(A2), A, Tag_Wrap), MyB, MyC).main() @ &m : res ].
proof. byequiv.

proc. inline*. wp. call (_: true). wp. rnd. wp. rnd.
skip.
progress. smt. smt. smt.
smt.  (* relies on empty_prop axiom *)
auto. 
qed.

end section.
