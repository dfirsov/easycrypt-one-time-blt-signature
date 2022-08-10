
abstract theory CR_HashF.


type hash_input.
type hash_output.

op H : hash_input -> hash_output.

module type AdvCR = {
  proc adv() : hash_input * hash_input
}.

module CR_H(A:AdvCR) = {
  
  proc main(): bool= {
    var x, x' : hash_input;

    (x, x') <@ A.adv();

    return H x = H x' /\ x <> x';
  }
}.


end CR_HashF.
