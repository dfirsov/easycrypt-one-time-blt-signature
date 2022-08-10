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
  module A = A(RO)

  proc main(pk : pkey) = {
    var it : int;
    var tg : tag;
    var m : message;
    var r : int;
    var c : chain;
    it <@  RO.rndStr();
    
    (y, r) <@ A.forge(pk);

    return r;
  }

}.

module MyB(RO : ROracle, O : SH_OracleT) = {
  proc main(pk : pkey) = {
    return MyA.y; 
  }
}.

module MyC(A : BLT_AdvH2, RO : ROracle,  O : Tag_Oracle) = {
  module A = A(RO, O)

  proc main(pk : pkey) = {
    var c : chain;
    c <@ A.forge(pk);
    return (EMPTY, c); 
  }
}.

section. 

declare module A <: BLT_AdvH{-Tag_Wrap, -RO,  -SHGame, -SHGameSimple}.
declare module A2 <: BLT_AdvH2{-Tag_Wrap, -RO,  -SHGame, -SHGameSimple, -MyA}.
declare module A3 <: BLT_Adv_Set{-Tag_Wrap, -RO,  -SHGame, -SHGameSimple}.

axiom main_sh_security &m : 
   Pr[ SHGameSimple(RO, Tag_Wrap, A, A2).main() @ &m : res] 
  <= Pr[ SHGame(RO, MyA(TsU_Set(A3), A, Tag_Wrap), MyB, MyC(A2)).main() @ &m : res ].

end section.
