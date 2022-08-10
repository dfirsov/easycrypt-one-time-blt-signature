

require import AllCore FSet.
require HashFunc.

abstract theory MerkleTree.

type hash_input.
type hash_output.
type chain.



clone import HashFunc.CR_HashF as HF with type hash_input  <- hash_input,
                                          type hash_output <- hash_output.

op leaf : chain -> hash_output.
op root : chain -> hash_output.

(* this type provides almost a visiual representation of a MT *)
op buildChains : hash_output fset -> chain fset * hash_output.
op verifyChain : chain -> hash_output -> bool.

axiom leavesPreserved hf : hf = image leaf (buildChains hf).`1.   

axiom chainCollision rt c1 c2 : 
  verifyChain c1 rt = true => verifyChain c2 rt = true
  => c1 <> c2
  => exists i1 i2, i1 <> i2 => H i1 = H i2.




end MerkleTree.
