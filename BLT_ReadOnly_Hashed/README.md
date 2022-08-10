Repository
==========

At each moment `t`, repository contains a hash of a tag and a message

```
   R.get(t : int) : hash option 
```
More specifically, the valid signature of message `m` at time `t` must contain an entry`R.get(t) = Some H(tag sk t || m)`.

Adversary can only read from the repository:

```
  R.put(x : hash) := {
    t := t + 1;
    r[t] = x;    
    return t;
  }
```


Sketch of the proof of EUF
=========================

Assume that `A` makes a forgery. Since adversary `A` does not have a permission to write to the
repository then he MUST use an oracle and find a collision with what oracle is writing into the repository.
