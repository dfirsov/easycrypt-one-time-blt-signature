pragma Goals : printall.

require import FSet Int Real SmtMap Distr.

require import RandomnessOracle.

require HashFunc BLT Timestamp TagSystem.

type pkey, skey, tag, message, hash_output.
op keys : (pkey * skey) distr.
op tdistr : int distr.
op EMPTY : message.
op tag : skey -> int -> tag.
op tagVerify : pkey -> int -> tag -> bool.
op toTime : tag -> int.
op defpksk : pkey * skey.
op initialTime : int ->  int.
op queryBound : int.

axiom validKeys pk sk t :  (pk, sk) \in keys => tagVerify pk t (tag sk t) = true.  
axiom toTimeProp pk sk t : (pk, sk) \in keys => toTime (tag sk t) = t.                                     
axiom defvalid : defpksk \in keys.
axiom it_pos s : 0 <= initialTime s.
axiom keys_lossless : is_lossless keys.
axiom queryBoundPos : 0 < queryBound.

axiom d_ll : is_lossless tdistr.
axiom tdistr_pos t : t \in tdistr => 0 <= t. 


(* instantiating CR functions for relevant types *)
clone import HashFunc.CR_HashF as HMT with type hash_input  <- message * tag,
                                       type hash_output <- hash_output.

clone import HashFunc.CR_HashF as HT  with type hash_input  <- tag,
                                       type hash_output <- hash_output.

clone import HashFunc.CR_HashF as HM  with type hash_input  <- message,
                                       type hash_output <- message.


                                      
axiom empty_prop tg : HMT.H (EMPTY, tg)  = HT.H tg.
axiom hash_not_empty m : HM.H m <> EMPTY.


op deftag = tag defpksk.`2 0.
op ogetf ['a] (ox : ('a fset) option) : 'a fset = odflt fset0 ox.
op ogetff (ox : message option) : message fset 
  =  if ox = None then fset0 else fset1 (HM.H (oget ox)). 

  
lemma queryBoundPosR : 0%r < queryBound%r. 
proof. smt. qed.


clone export Timestamp.RepoSet as RS with type d <- hash_output,
                                          op   tdistr <- tdistr.

clone export TagSystem.Tags as T with type pkey <- pkey,
                                      type skey <- skey,
                                      type tag  <- tag,
                                      op   keys <- keys,
                                      op   deftag <- deftag,
                                      op   tag <- tag,
                                      op   tagVerify <- tagVerify, 
                                      op   toTime <- toTime.


clone export BLT.BLT_Scheme_Theory as 
    BST with type pkey      <- pkey,
             type skey      <- skey,
             type tag       <- tag,
             type message   <- message,
             type RI        <- hash_output fset,
             op   keys      <- keys,
             op   tdistr    <- tdistr,
             op   toRI      <- fun (x : message * tag), 
                                fset1 (HMT.H (HM.H x.`1 , x.`2)) `|` fset1 (HT.H x.`2),
             op   checkRepo <- fun x y, y \subset (ogetf x),
             op   deftag    <- deftag,
             op   toTime    <- toTime,
             op   queryBound <- queryBound,
             op   initialTime <- initialTime.

