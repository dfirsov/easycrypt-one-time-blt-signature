require import Int Bool Distr.
require import RandomnessOracle.


abstract theory Tags.

type pkey, skey, tag.

(* tag system is functional (stateless) *)
op tag : skey -> int -> tag.
op tagVerify : pkey -> int -> tag -> bool.
op toTime : tag -> int.
(* instead of using option monad we have a default tag *)
op deftag : tag.

op keys : (pkey * skey) distr.


module type Tag_Oracle = {
  proc init(pk:pkey, sk:skey) : unit {}
  proc createTag(m : int) : tag
  proc verifyTag(s : tag) : bool
  proc askedTag() : tag
}.


module type Tag_AdvOracle = { proc createTag(m : int) : tag }.

module type Tag_Adv(O:Tag_Oracle) = {
  proc forgeTag(pk : pkey, rs:int) : tag  {O.createTag}
}.


module Tag_Wrap : Tag_Oracle = {
   var usedFlag : bool
   var usedTag  : tag

   var pk : pkey
   var sk : skey

  proc init(pk : pkey, sk : skey) : unit = {
    Tag_Wrap.pk <- pk;
    Tag_Wrap.sk <- sk;
    usedFlag <-  false;
    usedTag  <-  deftag;
  }

  proc createTag(t : int) : tag = {

    if(!usedFlag){
      usedTag <- tag sk t;
    }
    usedFlag <- true;

    return usedTag;
  }

  proc verifyTag(s : tag) : bool = {
    return tagVerify pk (toTime s) s;
  }

  proc askedTag() : tag = {
    return usedTag;
  }
   
}.


module TagGame(RO : ROracle, O : Tag_Oracle, A : Tag_Adv) = {
  module A = A(O)

  var tg, tg' : tag
  var m, m' : int
  var forged, fresh : bool
  
  proc main() : bool = {
    var pk : pkey;
    var sk : skey;
    var it : int;

    it <@ RO.init();
    (pk, sk) <$ keys;
    
    O.init(pk, sk);
    tg <@ A.forgeTag(pk, it);
    m <- toTime tg;
    
    forged <@ O.verifyTag(tg);
    tg' <@ O.askedTag();
    m' <- toTime tg';
    

    return forged /\ (m' < m \/ (m = m' /\ tg <> tg'));
  }
}.


module TagGamePhantom(RO : ROracle, Tag_O : Tag_Oracle, A : Tag_Adv) = {
  module A = A(Tag_O)

  var tg : tag
  
  proc main() : bool = {
    var pk : pkey;
    var sk : skey;
    var it : int;
    var forged : bool;

    it <@ RO.init();
    (pk, sk) <$ keys;
    
    Tag_O.init(pk, sk);
    tg <@ A.forgeTag(pk, it);
  
    forged <@ Tag_O.verifyTag(tg);    

    return forged /\ tg <> tag sk (toTime tg);
  }
}.



module Tag_Wrap_1 : Tag_Oracle = {
   var usedFlag : bool
   var usedTag  : tag

  proc init(pk: pkey, sk:skey) : unit = {      
    usedFlag <- false;
    usedTag  <- deftag;
  }

  proc createTag(t : int) : tag = {
    usedFlag <- true;
    return usedTag;
  }

  proc verifyTag(s : tag) : bool = {
    return true;
  }

  proc askedTag() : tag = {
    return usedTag;
  }   
}.


end Tags.


