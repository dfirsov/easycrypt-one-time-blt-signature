pragma Goals:printall.

require import Int Real SmtMap Distr DInterval.

require import BLT_Instance.


(* If A^BLT_Wrap uses signing oracle at time t' and forges a signature
for time t so that t < t' then we turn A^BLT_Wrap into adversary HT_Adv(A)
who finds an H-image of a tag (without access to tag-oracle)  *)



module BLTGame'(Tag_O : Tag_Oracle, 
  Ts_O : TS, BLT_O : BLT_Oracle, A : BLT_Adv) = {

  module G = BLTGame(Tag_O,Ts_O, BLT_O, A)
  var guess : int
  var r : bool

  proc main() : bool = {
    r <@ G.main();
    guess <$ dinter 1 queryBound;
    return r;
  }
}.


module HT_Adv(A:BLT_Adv, O:BLT_AdvOracle) = {
   module A = A(O) 

   var guess : int   

   proc forge(pk:pkey) = {
      var r;
      A.forge(pk);
     
      r <@ O.get();
      guess <$ dinter 1 queryBound;
     
      return ((oget r.[guess]).`2, guess);
    }
}.


section. 

declare module A <: BLT_Adv{-Tag_Wrap, -BLT_Wrap, -TsU}.


axiom A_ll : forall (O <: BLT_AdvOracle{-A}),
  islossless O.sign =>
  islossless O.put => islossless O.get => islossless A(O).forge.


local module BA : BLT_AdvH = HT_Adv(A).  

  
local lemma zz2 &m : 
  phoare [ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main : 
    (glob A) = (glob A){m} ==> 
      (res /\ BLT_Wrap.used) 
  /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
  /\ toTime BLTGame.tg < queryBound 
  /\ 1 <= toTime BLTGame.tg ]  
  = Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m : 
        (res /\ BLT_Wrap.used) 
      /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
      /\ toTime BLTGame.tg < queryBound 
      /\ 1 <= toTime BLTGame.tg ]. 
proof. bypr.
move => &m0 q. byequiv (_: ={glob A} /\ (glob A){1} = (glob A){m0} ==> ={res, BLT_Wrap.used, BLT_Wrap.qt, BLTGame.tg}).

proc. inline*. wp. call (_: ={glob BLT_Wrap, glob Tag_Wrap, glob TsU}).
proc. if. smt. wp. inline*. wp. skip. progress. wp. skip. smt.
proc. inline*. wp. skip. smt.
proc. inline*. wp. skip. smt.

wp. rnd. wp. rnd. skip. progress.  smt. smt.

qed.


local lemma zz &m : 
  phoare [ BLTGame'(Tag_Wrap, TsU, BLT_Wrap, A).main : 
    (glob A) = (glob A){m}  ==> 
       (res /\ BLT_Wrap.used) 
     /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
     /\ toTime BLTGame.tg < queryBound 
     /\ 1 <= toTime BLTGame.tg  
     /\ toTime BLTGame.tg = BLTGame'.guess ]
  = (Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m 
     :  (res /\ BLT_Wrap.used) 
     /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
     /\ toTime BLTGame.tg < queryBound 
     /\ 1 <= toTime BLTGame.tg ] * (1%r/queryBound%r)).
proof. proc*.

inline BLTGame'(Tag_Wrap, TsU, BLT_Wrap, A).main.

seq 1 : ((BLTGame'.r /\ BLT_Wrap.used)
  /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
  /\ toTime BLTGame.tg < queryBound 
  /\ 1 <= toTime BLTGame.tg)

 Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m 
   : (res /\ BLT_Wrap.used) 
  /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
  /\ toTime BLTGame.tg < queryBound 
  /\ 1 <= toTime BLTGame.tg ]

  (1%r/queryBound%r)

  (1%r - Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m 
         : (res /\ BLT_Wrap.used) 
        /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
        /\ toTime BLTGame.tg < queryBound 
        /\ 1 <= toTime BLTGame.tg])

  0%r. 

inline*. wp. call(_:true); auto.
call (zz2 &m);auto.
wp. rnd (fun (x : int) => toTime BLTGame.tg = x). 
skip. progress.

have : 1 <= toTime BLTGame.tg{hr} <= queryBound. smt.
move => www.

have z := dinter1E 1 queryBound  (toTime BLTGame.tg{hr}).
rewrite www in z.

have : mu1 [1..queryBound] (toTime BLTGame.tg{hr}) = inv (queryBound)%r. smt.
move => opp. rewrite - opp.

have : ((=) (toTime BLTGame.tg{hr})) = pred1 (toTime BLTGame.tg{hr}).
apply fun_ext. move => x. smt.

move => oppz. rewrite oppz. smt.

wp. rnd. skip. smt. smt.  
qed.


local lemma zz3 &m : 
  Pr[ BLTGame'(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m 
    : (res /\ BLT_Wrap.used) 
   /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
   /\ toTime BLTGame.tg < queryBound /\ 1 <= toTime BLTGame.tg
   /\ toTime BLTGame.tg = BLTGame'.guess ] 
  = (Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m 
    : (res /\ BLT_Wrap.used) 
    /\ toTime BLTGame.tg < toTime BLT_Wrap.qt
    /\ toTime BLTGame.tg < queryBound /\ 1 <= toTime BLTGame.tg ] * (1%r/queryBound%r)). 
proof.  byphoare (_: (glob A) = (glob A){m} ==> _). 
apply (zz &m). auto. auto. 
qed.


local lemma zz4 &m : Pr[ BLTGame'(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m 
    : (res /\ BLT_Wrap.used) 
    /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
    /\ toTime BLTGame.tg = BLTGame'.guess ]
  = Pr[ BLTGame'(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m 
    : (res /\ BLT_Wrap.used) 
    /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
    /\ toTime BLTGame.tg < queryBound 
    /\ 1 <= toTime BLTGame.tg 
    /\ toTime BLTGame.tg = BLTGame'.guess ].

proof. byequiv.
proc. inline*. rnd. wp.

call (_: ={glob BLT_Wrap, glob Tag_Wrap, glob TsU} 
        /\ (forall x, x \in TsU.r{2} => 1 <= x) 
        /\ BLT_Wrap.used{2} = Tag_Wrap.usedFlag{2} 
        /\ 0 <= TsU.t{2}).

proc. if. smt. wp. inline*. wp. skip. progress. smt. smt.  smt. smt. wp. skip. smt.
proc. inline*. wp. skip. progress. smt. smt.
proc. inline*. wp. skip. smt. 
wp. rnd. wp. rnd. skip. progress. smt.
smt. smt. auto. smt. 
qed.

 
local lemma wwwForB : equiv [ BLTGameH(Tag_Wrap, TsU, HT_Adv(A)).main 
  ~ BLTGame'(Tag_Wrap, TsU, BLT_Wrap, A).main
  : ={glob A}
  ==> res{2} /\ BLT_Wrap.used{2}
   /\ toTime BLTGame.tg{2} < toTime BLT_Wrap.qt{2}
      => (forall x, x < (toTime BLT_Wrap.qt{2}) /\ TsU.i{2} < x => TsU.r.[x]{1} = TsU.r.[x]{2})
      /\ (forall x, x <= TsU.i{2} => x \notin TsU.r{2})
      /\ (TsU.r.[toTime BLTGame.tg]{2} = Some ((HMT.H (BLTGame.m, BLTGame.tg)), ((HT.H (BLTGame.tg)))){2})
      /\ (BLTGame'.guess{2} = toTime BLTGame.tg{2} => res{1}) ].
proof. proc. 

inline*. wp. rnd. wp.

call (_: BLT_Wrap.used, (0 <= TsU.i{2})  
 /\ (TsU.i{2} <= TsU.t{2}) /\ (forall x, x <= TsU.i{2} => x \notin TsU.r{2})
 /\ ={glob TsU} /\ BLT_Wrap.used{2} = Tag_Wrap.usedFlag{2}  
 /\ (forall x, x < toTime BLT_Wrap.qt{2} => TsU.i{2} < x => (TsU.r.[x]{2} = TsU.r.[x]{1}))
 /\ (forall x, x <= TsU.t{2} => TsU.i{2} < x => x \in TsU.r{2})
 /\ (Tag_Wrap.pk{2}, Tag_Wrap.sk{2}) \in keys 
 /\ (forall y, y \in TsU.r{1} => y <= TsU.t{1}),

 ((Tag_Wrap.usedFlag = BLT_Wrap.used) /\ ((Tag_Wrap.pk, Tag_Wrap.sk) \in keys 
 /\ BLT_Wrap.used 
 /\ Tag_Wrap.usedFlag => (TsU.r.[toTime BLT_Wrap.qt] 
     = Some ((HMT.H (oget BLT_Wrap.qs, BLT_Wrap.qt)), ((HT.H (BLT_Wrap.qt))))) 
 /\ toTime BLT_Wrap.qt <= TsU.t)){2} 
 /\  (TsU.i{2} <= TsU.t{2}) /\ (forall x, x <= TsU.i{2} => x \notin TsU.r{2})
 /\  (forall x, x < toTime BLT_Wrap.qt{2} => TsU.i{2} < x => (TsU.r.[x]{2} = TsU.r.[x]{1}))
 /\ (forall x, x <= TsU.t{2} => TsU.i{2} < x => x \in TsU.r{2})
 /\ BLT_Wrap.used{2} /\ (toTime BLT_Wrap.qt{2} <= TsU.t{2}) 
 /\ (Tag_Wrap.pk{2}, Tag_Wrap.sk{2}) \in keys  
 /\ (forall y, y \in TsU.r{1} => y <= TsU.t{1})). 
apply A_ll.

proc. wp. if {2}. inline*. wp. skip. progress;smt. wp. skip. smt.

move => &2 z. proc. auto.
move => &1
      . proc. auto. if. inline*. wp. skip. smt. wp. skip. smt. 

proc. inline*. wp. skip. progress;smt. 

move => &2 z. proc. inline*. wp. skip. progress. timeout 15. smt(@SmtMap). smt.
move => &1.  proc. inline*. wp. skip. progress;smt. 

proc. inline*. wp. skip. smt.

move => &2 z. proc. inline*. wp. skip. smt.
move => &1.   proc. inline*. wp. skip. smt.

wp. rnd. wp. rnd. skip. 
progress. smt. smt. smt. smt. smt. smt. smt. 

have : r_L.[toTime result_R.`2] = r_R.[toTime result_R.`2]. smt.
move => h3. rewrite h3 H12.

simplify oget.

have : result_R.`2 = (tag pkskL.`2 (toTime result_R.`2)). admit.

smt. 
qed.


local lemma zz4' &m : Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m 
   : (res /\ BLT_Wrap.used) 
  /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
  /\ toTime BLTGame.tg < queryBound 
  /\ 1 <= toTime BLTGame.tg ] =
  Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m 
    : (res /\ BLT_Wrap.used) 
   /\ toTime BLTGame.tg < toTime BLT_Wrap.qt ].
proof. byequiv. 
proc. inline*. wp. 

call (_: ={glob BLT_Wrap, glob Tag_Wrap, glob TsU} 
  /\ (forall x, x \in TsU.r{2} => 1 <= x) 
  /\ BLT_Wrap.used{2} = Tag_Wrap.usedFlag{2} 
  /\ 0 <= TsU.t{2}).

proc. if. smt. wp. inline*. wp. skip. progress. smt. smt. smt. smt. wp. skip. smt.
proc. inline*. wp. skip. progress. smt. smt.
proc. inline*. wp. skip. smt. 

wp. rnd. wp. rnd. skip. progress. smt.
smt. smt. auto. smt. 

qed.


local lemma ccc &m : 
  Pr[ BLTGame'(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m
   :  (res /\ BLT_Wrap.used) 
   /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
   /\ toTime BLTGame.tg = BLTGame'.guess ]
  = (Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m 
    : (res /\ BLT_Wrap.used) 
   /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
   /\ toTime BLTGame.tg < queryBound 
   /\ 1 <= toTime BLTGame.tg ] * (1%r/queryBound%r)).
proof. rewrite (zz4 &m). apply (zz3 &m). qed.


local lemma case4' &m : 
  Pr[ BLTGame'(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m 
  : (res /\ BLT_Wrap.used) 
 /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
 /\ toTime BLTGame.tg = BLTGame'.guess ] 
 <= Pr[ BLTGameH(Tag_Wrap, TsU, HT_Adv(A)).main() @ &m : res ].
proof. byequiv. symmetry. conseq wwwForB. smt. smt. smt. smt. qed.



local lemma case4'' &m : (Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m 
    : (res /\ BLT_Wrap.used) /\ toTime BLTGame.tg < toTime BLT_Wrap.qt ] * (1%r/queryBound%r))
  <= Pr[ BLTGameH(Tag_Wrap, TsU, HT_Adv(A)).main() @ &m : res ].
proof. rewrite - (zz4' &m). rewrite - (ccc &m). apply (case4' &m). qed.


local lemma fact (a b c : real) : a <= b => 0%r <= c => a * c <= b * c. 
proof. smt. qed.


lemma case4 &m : Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m 
  : (res /\ BLT_Wrap.used) /\ toTime BLTGame.tg < toTime BLT_Wrap.qt ]
  <= (Pr[ BLTGameH(Tag_Wrap, TsU, HT_Adv(A)).main() @ &m : res ] * queryBound%r).
proof. 

pose x := Pr[ BLTGame(Tag_Wrap, TsU, BLT_Wrap, A).main() @ &m 
 : (res /\ BLT_Wrap.used) /\ toTime BLTGame.tg < toTime BLT_Wrap.qt ].

pose y := Pr[BLTGameH(Tag_Wrap, TsU, HT_Adv(A)).main() @ &m : res].

have : 0%r < queryBound%r. smt (queryBoundPosR).
move => ik.

smt (case4'').
qed.

end section.
