

Repository
==========

At each moment `t`, repository contains a pair of a tag and a message

```
   R.get(t : int) : (message * tag) option 
```
More specifically, the valid signature of message `m` at time `t` must contain an entry `R.get(t) = Some (m, tag sk t)`.

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

Assume that `A` makes a forgery.

1. Oracle not used:  Tag-system is unsafe.

2. Oracle used at time `t` and signature is forged for time `t'`.

   2.1. `t < t'`: Tag-system is unsafe.

   2.2. `t > t'`: Tag-system is unsafe.

   2.3. `t = t'`: This case is impossible since the adversary succeeded with a
   forgery only if the message is fresh (which did not happen for the reason that repository contains plain message).

        

