pragma Goals : printall.

require import FSet Int Real SmtMap Distr.

require import RandomnessOracle.

theory BLT_Scheme_Theory.

type pkey, skey, tag, message, RI.
op keys : (pkey * skey) distr.
op toRI : message * tag -> RI.
op queryBound : int.
op checkRepo : RI option -> RI -> bool.
op tdistr : int distr.
op initialTime : int ->  int.
op deftag : tag.
op toTime : tag -> int.


require Timestamp.
clone import Timestamp.Repo as R with type d      <- RI,
                                      op   tdistr <- tdistr.



require TagSystem.
clone import TagSystem.Tags as T with type pkey   <- pkey,
                                      type skey   <- skey,
                                      type tag    <- tag,
                                      op   keys   <- keys,
                                      op   deftag <- deftag,
                                      op   toTime <- toTime.


(* BLT signature scheme parameterized by tag and timestamping oracles *)
module BLT_Scheme(Tag_O : Tag_Oracle, Ts_O : TS) = {

  proc sign(m : message) : tag = {
    var t  : int;
    var tg : tag;
    var ri : RI;
 
    t  <@ Ts_O.clock();
    tg <@ Tag_O.createTag(t+1);
    ri <- toRI (m, tg);
    Ts_O.put(ri);

    return tg; 
  }

  proc verify(m : message, t : tag) : bool = {
    var b  : bool;
    var s' : RI option;
    var tm : int;

    tm <- toTime t;
    b  <@ Tag_O.verifyTag(t);
    s' <@ Ts_O.getE(tm);

    return b /\ checkRepo s' (toRI (m, t));  
  }
}.

(* BLT oracle + Repo access for the Game and adversary *)
module type BLT_Oracle(Tag_O : Tag_Oracle, Ts_O : TS) = {
  proc init() : unit
  proc sign(m : message) : tag             
  proc verify(m : message, s : tag) : bool
  proc fresh(m : message) : bool
  proc put(ri : RI) : unit      
  proc get() : (int, RI) fmap
}.

(* subtype of BLT_Oracle for the adversary *)
module type BLT_AdvOracle = { 
  proc sign(m : message) : tag    
  proc put(ri : RI) : unit 
  proc get() : (int, RI) fmap
}.


module type BLT_Adv(O : BLT_AdvOracle)  = {
  proc forge(pk : pkey, rs : int) : message * tag 
}.


module BLTGame(RO : ROracle, Tag_O : Tag_Oracle, Ts_O : TS, BLT_O : BLT_Oracle, A : BLT_Adv) = {
  module BLT_O = BLT_O(Tag_O, Ts_O)
  module A = A(BLT_O)

  var tg : tag
  var m : message

  proc main() : bool = {
    var forged, fresh : bool;
    var pk : pkey;
    var sk : skey;
    var it : int;

    it <@ RO.init();
    (pk, sk) <$ keys;

    Tag_O.init(pk, sk);
    Ts_O.init(initialTime it);
    BLT_O.init();
    
    (m, tg) <@ A.forge(pk, it);
    forged  <@ BLT_O.verify(m, tg);
    fresh   <@ BLT_O.fresh(m);

    return forged /\ fresh /\ (toTime tg < queryBound);
  }
}.


(* default one-time BLT oracle parameterized by tag and timestamping oracles *)
module (BLT_Wrap : BLT_Oracle) (Tag_O : Tag_Oracle) (Ts_O : TS) = {

  module BLT = BLT_Scheme(Tag_O, Ts_O)

  var qs : message option
  var qt : tag
  var used : bool  (* one-time oracle  *)

  proc init() : unit = {
    qs   <- None;
    qt   <- deftag;
    used <- false;
  }



  proc sign(m : message) : tag = {
    if(!used){
      qs <- Some m;
      qt <@ BLT.sign(m);
    }
    used <- true;

    return qt;
  }

  proc verify(m : message, s : tag): bool = {
      var b : bool;

      b <@ BLT.verify(m, s);

      return b;    
  }

  proc put(ri : RI) : unit = {
    Ts_O.put (ri);
  }

  proc fresh(m : message) : bool = {
    return qs <> (Some m);
  }

  proc get() : (int, RI) fmap = {
    var q;

    q <@ Ts_O.get();

    return q;
  }
}.


(* "fake" BLT oracle with no capabilities for signature producing  *)
module (BLT_Dummy : BLT_Oracle) (Tag_O : Tag_Oracle) (Ts_O : TS) = {

  module BLT = BLT_Scheme(Tag_O, Ts_O)

  proc init() : unit = {}

  proc sign(m : message) : tag = {
     return deftag;
  }

  proc verify(m : message, s : tag) : bool = {
      var b : bool;

      b <@ BLT.verify(m, s);

      return b;    
  }

  proc fresh(m : message) : bool = {
    return true;
  }

  proc put(ri : RI) : unit = {
    Ts_O.put(ri);
  }

  proc get() : (int, RI) fmap = {
    var q;

    q <@ Ts_O.get();

    return q;
  }
}.


(* BLT oracle which stores the time when adversary called it in variabled "usedTime" *)
module (BLT_Dummy_Time : BLT_Oracle) (Tag_O : Tag_Oracle) (Ts_O : TS) = {

  module BLT = BLT_Scheme(Tag_O, Ts_O)

  var used : bool
  var usedTime : int
  
  proc init() : unit = {
    used <- false;
    usedTime <- toTime deftag;
  }

  proc sign(m : message) : tag = {
    var t : int;
    if(!used){
      t <@ Ts_O.clock();
      usedTime <- t + 1;
      Ts_O.put(witness);
    }
    used <- true;

     return deftag;
  }

  proc verify(m : message, s : tag) : bool = {
      var b : bool;

      b <@ BLT.verify(m, s);

      return b;    
  }

  proc fresh(m : message) : bool = {
    return true;
  }

  proc put(ri : RI) : unit = {
    Ts_O.put(ri);
  }

  proc get() : (int, RI) fmap = {
    var q;

    q <@ Ts_O.get();

    return q;
  }
}.



(* Entropy-free deterministic game with (pk, sk) being parameters. *)
module BLTGameD(Ts_O : TS, Tag_O : Tag_Oracle, A : BLT_Adv) = {
    
  module BLT_Wrap = BLT_Wrap(Tag_O, Ts_O)
  module A        = A(BLT_Wrap)

  var m : message
  var tg : tag

  proc main(pk : pkey, sk:skey) = {
    var it : int;
    it <- RO.t;

    Tag_O.init(pk, sk);
    Ts_O.init(initialTime it);
    BLT_Wrap.init();
    
    (m,tg) <@ A.forge(pk, it);
  }  

}.

end BLT_Scheme_Theory.

