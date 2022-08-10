
require import FSet Int Real SmtMap Distr.

(* specifying main datatypes *)
type pkey, skey, tag, hash_output, message.
type Time = int.

(* distribution of "valid" key pairs *)
op keys : (pkey * skey) distr.

(* instantiating a hash function with domain (message * tag) *)
require Hash.
clone import Hash.CR_HashF as HT with type hash_input  <- message * tag,
                                      type hash_output <- hash_output.
export HT.

(* instantiating BLT *)
require BLT.
clone import BLT.BLT_Scheme_Theory as B with type pkey    <- pkey,
                                             type skey    <- skey,
                                             type tag     <- tag,
                                             type message <- message,
                                             type RI      <- hash_output,
                                             op   keys    <- keys,
                                             op   toRI    <- H.                                          
export B.


(* Type for adversaries who only can READ from the repository  *)
module type BLT_Adv_RO(O : BLT_AdvOracle)  = {
  proc forge(pk : pkey) : message * tag  {O.get, O.sign}  (* O.put is forbidden *)
}.
