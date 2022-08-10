
require import AllCore FSet.

require import BLT_Instance.
require import RandomnessOracle.


module type SH_OracleT = {
  proc init(pk: pkey, sk:skey) : unit
  proc h(m : message, t : int) : hash_output
}.

module type SH_Adv1(RO : ROracle) = {
   proc main(pk : pkey) : int
}.

module type SH_Adv2(RO : ROracle, SH_O : SH_OracleT) = {
   proc main(pk:pkey) : hash_output fset
}.

module type SH_Adv3(RO : ROracle, Tag_O : Tag_Oracle) = {
   proc main(pk:pkey) : message
}.

module type BLT_AdvH  = {
  proc forge(pk : pkey, rs : int) : (hash_output fset) * int
}.

module SH_Oracle = {

  var sk : skey

  var logT : int fset
  var logM : message fset

  proc  init(p : pkey, s : skey) = {
      sk <- s;
      logT <- fset0;
      logM <- fset0;
  }

  proc h(m : message, t : int) : hash_output = {
    var ho : hash_output;

    logT <- logT `|` fset1 t;
    logM <- logM `|` fset1 m;

    ho <- HMT.H(m, tag sk t);

    return ho;
  }

}.


module SHGameSimple(RO : ROracle, Tag_O : Tag_Oracle,  A : BLT_AdvH) = {

  var t : int
  var y : hash_output fset

  proc main() : bool = {
    var pk : pkey;
    var sk : skey;
    var it : int;
    
    it <@ RO.init();
    (pk, sk) <$ keys;

    Tag_O.init(pk, sk);

    (y, t) <@ A.forge(pk, it);

    return HT.H (tag sk t) \in y;
  }
}.



module SHGame(RO : ROracle, A1 : SH_Adv1, A2 : SH_Adv2, A3 : SH_Adv3) = {

  var pk : pkey
  var sk : skey

  var t : int
  var y : hash_output fset
  var m : message

  module A1 = A1(RO)
  module A2 = A2(RO, SH_Oracle)  
  module A3 = A3(RO, Tag_Wrap)

  proc main() = {
    var rs : int;

    rs <@ RO.init();
    (pk, sk) <$ keys;
    
    t <@ A1.main(pk);  

    SH_Oracle.init(pk, sk);
    y <@ A2.main(pk);

    Tag_Wrap.init(pk, sk);  
    m <@ A3.main(pk);  
    
    return SH_Oracle.logT \subset (fset1 t)
        /\ if Tag_Wrap.usedFlag then toTime Tag_Wrap.usedTag = t else true
        /\ ! (m \in SH_Oracle.logM)
        /\ HMT.H (m, tag sk t) \in y;
    
  }
}.
