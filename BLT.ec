pragma Goals : printall.

require import FSet.
require import Int.

require import Real.
require import SmtMap.
require import Distr.


theory BLT_Scheme_Theory.

type pkey, skey, tag, message, RI.
op keys : (pkey * skey) distr.
op toRI : message * tag -> RI.
op queryBound : int.
axiom keys_lossless : is_lossless keys.
axiom queryBoundPos : 0 < queryBound.

lemma queryBoundPosR : 0%r < queryBound%r. 
proof. smt. qed.


require Timestamp.
clone import Timestamp.Repo as R with type d <- RI.
export R.


require TagSystem.
clone import TagSystem.Tags as T with type pkey <- pkey,
                                      type skey <- skey,
                                      type tag  <- tag,
                                      op   keys <- keys.
export T.



                                      
module BLT_Scheme(Tag_O : Tag_Oracle, Ts_O : TS) = {

  proc sign(m : message) : tag = {
    var t  : Time;
    var tg : tag;
    var ri : RI;
 
    t  <@ Ts_O.clock();
    tg <@ Tag_O.createTag(t+1);
    ri <- toRI (m,tg);
    Ts_O.put(ri);

    return tg; 
  }

  proc verify(m : message, t : tag) : bool = {
    var b  : bool;  
    var s' : RI option;
    var tm : Time;

    tm <- toTime t;    
    b  <@ Tag_O.verifyTag(tm, t);
    s' <@ Ts_O.getE(tm);        
    return b /\ s' = Some (toRI (m, t));  
  }
}.


module type BLT_Oracle(Tag_O : Tag_Oracle, Ts_O : TS) = {
  proc init() : pkey
  proc sign(m : message) : tag             
  proc verify(m : message,s : tag) : bool
  proc fresh(m : message) : bool
  proc put(ri : RI) : unit      
  proc get() : (Time, RI) fmap
}.


module type BLT_AdvOracle = { 
  proc sign(m : message) : tag    
  proc put(ri : RI) : unit 
  proc get() : (Time, RI) fmap
}.


module type BLT_Adv(O : BLT_AdvOracle)  = {
  proc forge(pk : pkey) : message * tag 
}.


module BLTGame(Tag_O : Tag_Oracle, Ts_O : TS, BLT_O : BLT_Oracle, A : BLT_Adv) = {
  module BLT_O = BLT_O(Tag_O, Ts_O)
  module A = A(BLT_O)

  var tg : tag
  var forged, fresh : bool
  var m : message

  proc main() : bool = {
    var pk : pkey;

    Ts_O.init();
    pk <@ BLT_O.init();
    (m,tg) <@ A.forge(pk);
    forged <@ BLT_O.verify(m,tg);
    fresh <@ BLT_O.fresh(m);

    return forged /\ fresh /\ (toTime tg < queryBound);
  }
}.




module (BLT_Pure : BLT_Oracle) (Tag_O : Tag_Oracle) (Ts_O : TS) = {

  module BLT = BLT_Scheme(Tag_O, Ts_O)

  var qs   : message option
  var qt   : tag
  var used : bool

  proc init(): pkey = {
    var pk : pkey;

    qs <- None;
    qt <- deftag;
    used <- false;
    pk <@ Tag_O.init();

    return pk;
  }

  proc sign(m : message) : tag = {
    if(!used){
      qs <- Some m;
      qt <@ BLT.sign(m);
    }
    used <- true;   
    return qt;
  }

  proc verify(m : message, s : tag) : bool = {
      var b : bool;

      b <@ BLT.verify(m, s);

      return b;    
  }

  proc put(ri : RI) : unit = {
    Ts_O.put (ri);
  }

  proc fresh(m : message) : bool = {
    return qs <> Some m;
  }

  proc get() : (Time, RI) fmap = {
    var q;

    q <@ Ts_O.get();

    return q;
  }
}.


module (BLT_Wrap : BLT_Oracle) (Tag_O : Tag_Oracle) (Ts_O : TS) = {

  module BLT = BLT_Scheme(Tag_O, Ts_O)

  var qs : message option
  var qt : tag

  var used, submitted : bool  (* extra variables for adversary tracking *)


  proc init() : pkey = {
    var pk : pkey;

    qs   <- None;
    qt   <- deftag;
    used <- false;
    submitted <- false;
    pk   <@ Tag_O.init();

    return pk;
  }

  proc sign(m : message) : tag = {
    if(!used){
      qs <- Some m;
      qt <@ BLT.sign(m);
    }
    used <- true;

    return qt;
  }

  proc verify(m : message,s : tag): bool = {
      var b : bool;

      b <@ BLT.verify(m, s);

      return b;    
  }

  proc put(ri : RI) : unit = {
    submitted <- true;
    Ts_O.put (ri);
  }

  proc fresh(m : message) : bool = {
    return qs <> (Some m);
  }

  proc get() : (Time, RI) fmap = {
    var q;

    q <@ Ts_O.get();

    return q;
  }
}.





module (BLT_Dummy : BLT_Oracle) (Tag_O : Tag_Oracle) (Ts_O : TS) = {

  module BLT = BLT_Scheme(Tag_O, Ts_O)

  proc init() : pkey = {
    var pk : pkey;
    pk <@ Tag_O.init();
    return pk;
  }

  proc sign(m : message) : tag = {
     return deftag;
  }

  proc verify(m : message,s : tag) : bool = {
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

  proc get() : (Time, RI) fmap = {
    var q;

    q <@ Ts_O.get();

    return q;
  }
}.

end BLT_Scheme_Theory.
