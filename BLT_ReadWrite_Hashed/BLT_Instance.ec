pragma Goals : printall.

require import FSet.
require import Int.
require import Real.
require import SmtMap.
require import Distr.


type pkey, skey, tag, message, hash_output.
op keys : (pkey * skey) distr.


(* instantiating a CR hash function with domain (message * tag) *)
require Hash.
clone import Hash.CR_HashF as HMT with type hash_input  <- message * tag,
                                       type hash_output <- hash_output.

clone import Hash.CR_HashF as HT with type hash_input  <- tag,
                                      type hash_output <- hash_output.



require BLT.

clone export BLT.BLT_Scheme_Theory as BST with type pkey <- pkey,
                                             type skey <- skey,
                                             type tag  <- tag,
                                             type message <- message,
                                             type RI      <- (hash_output * hash_output),
                                             op   keys <- keys,
                                             op   toRI <- fun x, (HMT.H x, HT.H x.`2).                                          




module type BLT_AdvH(O : BLT_AdvOracle)  = {
  proc forge(pk : pkey) : hash_output * Time
}.

module BLTGameH(Tag_O : Tag_Oracle, Ts_O : TS, A : BLT_AdvH) = {
  module BLT_O = BLT_Dummy(Tag_Wrap, Ts_O)
  module A = A(BLT_O)

  var t : Time
  var forged, fresh : bool
  var y : hash_output

  proc main() : bool = {
    var pk : pkey;

    Ts_O.init();
    pk <@ BLT_O.init();
    (y,t) <@ A.forge(pk);

    return HT.H (tag Tag_Wrap.sk t) = y ;
  }
}.

