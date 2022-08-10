require import FSet Int Real SmtMap Distr.
require HashFunc BLT Timestamp TagSystem MerkleTree.


type pkey, skey, tag, message, hash_output, chain.

op keys : (pkey * skey) distr.
op EMPTY : message.
op tag : skey -> int -> tag.
op tagVerify : pkey -> int -> tag -> bool.
op toTime : tag -> int.
op defpksk : pkey * skey.
op deftag = tag defpksk.`2 0.
op initialTime : int -> int.
op queryBound : int.

axiom validKeys pk sk t :  (pk, sk) \in keys => tagVerify pk t (tag sk t) = true.  
axiom toTimeProp pk sk t : (pk, sk) \in keys => toTime (tag sk t) = t.                                     
axiom defvalid : defpksk \in keys.
axiom it_pos s : 0 <= initialTime s.
axiom keys_lossless : is_lossless keys.
axiom queryBoundPos : 0 < queryBound.




(* instantiating CR functions for relevant types *)
clone import HashFunc.CR_HashF as HMT with type hash_input  <- message * tag,
                                       type hash_output <- hash_output.

clone import HashFunc.CR_HashF as HT  with type hash_input  <- tag,
                                       type hash_output <- hash_output.

clone import HashFunc.CR_HashF as HM  with type hash_input  <- message,
                                       type hash_output <- message.


                                      
axiom empty_prop tg : HMT.H (EMPTY, tg)  = HT.H tg.
axiom hash_not_empty m : HM.H m <> EMPTY.


clone export MerkleTree.MerkleTree as MT with type hash_input <- message * tag,
                                              type hash_output <- hash_output fset,
                                              type chain       <- chain.



                                        
axiom root_non_empty i : root i <> fset0.


op ogetf ['a] (ox : ('a fset) option) : 'a fset = odflt fset0 ox.
op ogetff (ox : message option) : message fset 
  =  if ox = None then fset0 else fset1 (HM.H (oget ox)). 

  
lemma queryBoundPosR : 0%r < queryBound%r. 
proof. smt. qed.



clone export Timestamp.RepoSet as RS with type d <- hash_output.


clone export Timestamp.RepoType with type d <- hash_output fset,
                                     type o <- hash_output fset,
                                     type r <- int.


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
             type chain     <- chain,
             op   keys      <- keys,
             op   toRI      <- fun (x : message * tag), 
                                 fset1 (HMT.H (HM.H x.`1 , x.`2)) `|` fset1 (HT.H x.`2),
             op   checkRepo <- fun re c ri, leaf c = ri /\ root c \subset (ogetf re),
             op   deftag    <- deftag,
             op   toTime    <- toTime,
             op   queryBound <- queryBound,
             op   initialTime <- initialTime.


