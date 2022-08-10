require import Int Bool SmtMap Distr.


abstract theory Tags.

type pkey, skey, tag.
type Time = int.
op keys : (pkey * skey) distr.


(* tag system is functional (stateless) *)
op tag : skey -> Time -> tag.
op tagVerify : pkey -> Time -> tag -> bool.
op toTime : tag -> Time.

axiom validKeys pk sk t :  (pk, sk) \in keys => tagVerify pk t (tag sk t) = true.  
axiom toTimeProp pk sk t : (pk, sk) \in keys => toTime (tag sk t) = t.

(* instead of using option monad we have a default tag *)
op defpksk : pkey * skey.
axiom defvalid : defpksk \in keys.
op deftag = tag defpksk.`2 0.
   
    
module type Tag_Oracle = {
  proc  init() : pkey {}
  proc createTag(m : Time) : tag
  proc verifyTag(m : Time, s : tag) : bool
  proc askedTag() : tag
}.


module type Tag_AdvOracle = { proc createTag(m : Time) : tag }.


module type Tag_Adv(O:Tag_Oracle) = {
  proc forgeTag(pk : pkey) : Time * tag  {O.createTag}
}.


module Tag_Wrap : Tag_Oracle = {
   var usedFlag : bool
   var usedTag  : tag

   var pk : pkey
   var sk : skey

  proc init() : pkey = {
      
    (pk, sk) <$ keys;
    usedFlag <- false;
    usedTag  <-  deftag;

    return pk;
  }

  proc createTag(t : Time) : tag = {
    if(!usedFlag){
      usedTag <- tag sk t;
    }
    usedFlag <- true;
    return usedTag;
  }

  proc verifyTag(m : Time, s : tag) : bool = {
    return tagVerify pk m s;
  }

  proc askedTag() : tag = {
    return usedTag;
  }
   
}.


module TagGame(O : Tag_Oracle, A : Tag_Adv) = {
  module A = A(O)

  var tg, tg' : tag
  var m, m' : Time
  var forged, fresh : bool
  
  proc main() : bool = {
    var pk : pkey;
    
    pk <@ O.init();
    (m, tg) <@ A.forgeTag(pk);

    
    forged <@ O.verifyTag(m,tg);
    tg' <@ O.askedTag();
    m' <- toTime tg';
    

    return forged /\ (m' < m \/ (m = m' /\ tg <> tg'));
  }
}.




end Tags.
