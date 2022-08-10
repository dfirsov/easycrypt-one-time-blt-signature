pragma Goals:printall.

require import Int Real SmtMap Distr DInterval FSet.

require import BLT_Instance.

require import RandomnessOracle.

require import SHGame.

(* If A^BLT_Wrap uses signing oracle at time t' and forges a signature
for time t so that t < t' then we turn A^BLT_Wrap into adversary HT_Adv(A)
who finds an H-image of a tag (without access to tag-oracle)  *)

module HT_Adv(A:BLT_Adv, Ts : TS) = {
   module A = A(BLT_Dummy(Tag_Wrap, Ts)) 

   var guess : int   

   proc forge(pk:pkey, rs: int) = {
      var r;

      Ts.init(initialTime rs);
      A.forge(pk, rs);
     
      r <@ Ts.get();
      guess <$ dinter 1 queryBound;
     
      return ((ogetf r.[guess]), guess);
    }
}.


section. 

local module BLTGame'(RO : ROracle, Tag_O : Tag_Oracle, 
  Ts_O : TS, BLT_O : BLT_Oracle, A : BLT_Adv) = {

  module G = BLTGame(RO, Tag_O,Ts_O, BLT_O, A)
  var guess : int
  var r : bool

  proc main() : bool = {
    r <@ G.main();
    guess <$ dinter 1 queryBound;
    return r;
  }
}.


declare module RO <: ROracle{-TsU}.
declare module A <: BLT_Adv{-Tag_Wrap, -BLT_Wrap, -TsU, -BLTGame, -RO}.
declare module A2 <: BLT_Adv_Set{-Tag_Wrap, -BLT_Wrap, -TsU, -A, -BLTGame, -RO}.


axiom A_ll : forall (O <: BLT_AdvOracle{-A}),
  islossless O.sign =>
  islossless O.put => islossless O.get => islossless A(O).forge.

axiom A2_ll : islossless A2.react.

local module BA : BLT_AdvH = HT_Adv(A, TsU_Set(A2)).  


  
local lemma zz2 &m : 
  phoare [ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main : 
    (glob A) = (glob A){m} /\ (glob A2) = (glob A2){m} /\ (glob RO) = (glob RO){m}  ==> 
      ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) 
  /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
  /\ toTime BLTGame.tg < queryBound 
  /\ 1 <= toTime BLTGame.tg ]  
  = Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : 
        ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) 
      /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
      /\ toTime BLTGame.tg < queryBound 
      /\ 1 <= toTime BLTGame.tg ]. 
proof. bypr.
move => &m0 a. byequiv.

proc. inline*. wp. call (_: ={glob BLT_Wrap, glob Tag_Wrap, glob TsU, glob A2}).
proc. if. smt. wp. inline*. wp.  call(_:true). wp. skip. progress. wp. skip. smt.
proc. inline*. wp. call (_:true). wp. skip. smt.
proc. inline*. wp. skip. smt.

wp. rnd. call (_:true). skip. smt. smt. smt. qed.




local lemma zz &m : 
  phoare [ BLTGame'(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main : 
    (glob A) = (glob A){m} /\ (glob A2) = (glob A2){m} /\ (glob RO) = (glob RO){m}  ==> 
       ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) 
     /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
     /\ toTime BLTGame.tg < queryBound 
     /\ 1 <= toTime BLTGame.tg  
     /\ toTime BLTGame.tg = BLTGame'.guess ]
  = (Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m 
     :  ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) 
     /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
     /\ toTime BLTGame.tg < queryBound 
     /\ 1 <= toTime BLTGame.tg ] * (1%r/queryBound%r)).
proof. proc*.

inline BLTGame'(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main.

seq 1 : ((BLTGame'.r /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)
  /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
  /\ toTime BLTGame.tg < queryBound 
  /\ 1 <= toTime BLTGame.tg)

 Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m 
   : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg))
  /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
  /\ toTime BLTGame.tg < queryBound 
  /\ 1 <= toTime BLTGame.tg ]

  (1%r/queryBound%r)

  (1%r - Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m 
         : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) 
        /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
        /\ toTime BLTGame.tg < queryBound 
        /\ 1 <= toTime BLTGame.tg])

  0%r. 

inline*. wp. call(_:true); auto.
call (zz2 &m);auto. progress.
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
  Pr[ BLTGame'(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m 
    : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg))
   /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
   /\ toTime BLTGame.tg < queryBound /\ 1 <= toTime BLTGame.tg
   /\ toTime BLTGame.tg = BLTGame'.guess ] 
  = (Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m 
    : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) 
    /\ toTime BLTGame.tg < toTime BLT_Wrap.qt
    /\ toTime BLTGame.tg < queryBound /\ 1 <= toTime BLTGame.tg ] * (1%r/queryBound%r)). 
proof.  byphoare (_: (glob A) = (glob A){m} /\ (glob A2) = (glob A2){m} /\ (glob RO) = (glob RO){m} ==> _). 
apply (zz &m). auto. auto. 
qed.


local lemma zz4 &m : Pr[ BLTGame'(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m 
    : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg))
    /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
    /\ toTime BLTGame.tg = BLTGame'.guess ]
  = Pr[ BLTGame'(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m 
    : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) 
    /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
    /\ toTime BLTGame.tg < queryBound 
    /\ 1 <= toTime BLTGame.tg 
    /\ toTime BLTGame.tg = BLTGame'.guess ].

proof. byequiv.
proc. inline*. rnd. wp.

call (_: ={glob BLT_Wrap, glob Tag_Wrap, glob TsU, glob A2} 
        /\ (forall x, x \in TsU.r{2} => 1 <= x) 
        /\ BLT_Wrap.used{2} = Tag_Wrap.usedFlag{2} 
        /\ 0 <= TsU.t{2}).

proc. if. smt. wp. inline*. wp. call (_:true). wp. skip. progress. smt. smt.  smt. smt. wp. skip. smt.
proc. inline*. wp. call (_:true). wp. skip. progress. smt. smt.
proc. inline*. wp. skip. smt. 
wp. rnd. call (_:true).  skip. smt. smt.
smt. 
qed.




local lemma wwwForB : equiv [ SHGameSimple(RO, Tag_Wrap, HT_Adv(A, TsU_Set(A2))).main 
  ~ BLTGame'(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main
  : ={glob A, glob A2, glob RO} 
  ==> res{2} /\ BLT_Wrap.used{2}
   /\ toTime BLTGame.tg{2} < toTime BLT_Wrap.qt{2}
   /\ (tag Tag_Wrap.sk{2} (toTime BLTGame.tg{2}) = BLTGame.tg{2})
      => (forall x, x < (toTime BLT_Wrap.qt{2}) => TsU.r.[x]{1} = TsU.r.[x]{2})
      /\ (forall x, x <= TsU.i{2} => x \notin TsU.r{2})
      /\ (((fset1 (HT.H (BLTGame.tg)))){2} \subset (ogetf TsU.r.[toTime BLTGame.tg]{2}))
      /\ (BLTGame'.guess{2} = toTime BLTGame.tg{2} => res{1}) ].
proof. proc. 

inline*. wp. rnd. wp.

call (_: BLT_Wrap.used, (0 <= TsU.i{2})  
 /\ (TsU.i{2} <= TsU.t{2}) /\ (TsU.i{1} <= TsU.t{1}) /\ (forall x, x <= TsU.i{2} => x \notin TsU.r{2})
 /\ ={glob TsU, glob A2} /\ BLT_Wrap.used{2} = Tag_Wrap.usedFlag{2}  
 /\ (forall x, x < toTime BLT_Wrap.qt{2} =>  (TsU.r.[x]{2} = TsU.r.[x]{1}))
 /\ (forall x, x <= TsU.t{2} => TsU.i{2} < x => x \in TsU.r{2})
 /\ (Tag_Wrap.pk{2}, Tag_Wrap.sk{2}) \in keys 
 /\ (forall y, y \in TsU.r{1} => y <= TsU.t{1}) /\ ={glob TsU} 

 ,
 (TsU.i{1} = TsU.i{2}) /\
 ((Tag_Wrap.usedFlag = BLT_Wrap.used) /\ ((Tag_Wrap.pk, Tag_Wrap.sk) \in keys 
 /\ BLT_Wrap.used 
 /\ Tag_Wrap.usedFlag => (((fset1 (HT.H (BLT_Wrap.qt)))) \subset (ogetf TsU.r.[toTime BLT_Wrap.qt]))  
 /\ toTime BLT_Wrap.qt <= TsU.t)){2} 
 /\  (TsU.i{2} <= TsU.t{2}) /\ (TsU.i{1} <= TsU.t{1}) /\ (forall x, x <= TsU.i{2} => x \notin TsU.r{2})
 /\  (forall x, x < toTime BLT_Wrap.qt{2} =>  (TsU.r.[x]{2} = TsU.r.[x]{1}))
 /\ (forall x, x <= TsU.t{2} => TsU.i{2} < x => x \in TsU.r{2})
 /\ (forall x, x <= TsU.t{2} => x \in TsU.r{2} => TsU.i{2} < x)
 /\ BLT_Wrap.used{2} /\ (toTime BLT_Wrap.qt{2} <= TsU.t{2}) 
 /\ (Tag_Wrap.pk{2}, Tag_Wrap.sk{2}) \in keys  
 /\ (forall y, y \in TsU.r{1} => y <= TsU.t{1} )  ). 
apply A_ll.

proc. rcondt {2} 1. 
move => &1.  skip. auto.

inline*. wp. simplify.  call {2} (_:true ==> true). 

apply A2_ll.

rcondt {2} 6. move => &1. wp. skip. auto.  wp. skip. progress. smt.   smt. smt. smt. smt. smt. smt. smt.

move => &2 z. proc. auto.
move => &1. proc. auto. if. inline*. wp. call (_:true). apply A2_ll. wp. skip. smt. wp. skip. smt. 

proc. inline*. wp. call (_:true). wp. skip. progress. smt.  smt.  smt. 

smt. smt. smt . smt.  smt. smt.  smt.  smt. smt. smt. smt.

move => &h z. proc. inline*. wp. call (_:true). apply A2_ll. wp. skip. progress. timeout 15.

 smt(@SmtMap). 
rewrite /ogetf in H.



smt(@SmtMap). smt.
move => &1.  proc. inline*. wp. call (_:true). apply A2_ll. wp. skip. progress;smt. 

proc. inline*. wp. skip. smt.

move => &2 z. proc. inline*. wp. skip. smt.
move => &1.   proc. inline*. wp. skip. smt.

wp. inline*. rnd.  call (_: true ). skip. 
progress. smt. smt. smt. smt. smt. smt. smt. smt.  


have : initialTime result_R < toTime qt_R. smt. 
move => zzop.
have : initialTime result_R < toTime result_R0.`2. timeout 30. smt.

move => h55 .

have : r_L.[toTime result_R0.`2] = r_R.[toTime result_R0.`2]. smt. 

simplify ogetf.


(*
cut : result_R0.`2 = (tag pkskL.`2 (toTime result_R0.`2)). 
have z := (determProp pkskL.`1 pkskL.`2 (toTime result_R0.`2) result_R0.`2  )  .
apply z; smt.
*)

smt. 

qed.



local lemma zz4' &m : Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m 
   : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) 
  /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
  /\ toTime BLTGame.tg < queryBound 
  /\ 1 <= toTime BLTGame.tg ] =
  Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m 
    : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) 
   /\ toTime BLTGame.tg < toTime BLT_Wrap.qt ].
proof. byequiv. 
proc. inline*. wp. 

call (_: ={glob BLT_Wrap, glob Tag_Wrap, glob TsU, glob A2} 
  /\ (forall x, x \in TsU.r{2} => 1 <= x) 
  /\ BLT_Wrap.used{2} = Tag_Wrap.usedFlag{2} 
  /\ 0 <= TsU.t{2}).

proc. if. smt. wp. inline*. wp. call(_:true). wp. skip. progress. smt. smt. smt. smt. wp. skip. smt.
proc. inline*. wp. call (_:true). wp. skip. progress. smt. smt.
proc. inline*. wp. skip. smt. 

wp. rnd. call (_:true).  skip. progress. smt.
smt. 


have : r_R.[toTime result_R0.`2] <> None. smt.

move => ho.

smt. 
auto.
smt.
qed.


local lemma ccc &m : 
  Pr[ BLTGame'(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m
   :  ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg))
   /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
   /\ toTime BLTGame.tg = BLTGame'.guess ]
  = (Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m 
    : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg))
   /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
   /\ toTime BLTGame.tg < queryBound 
   /\ 1 <= toTime BLTGame.tg ] * (1%r/queryBound%r)).
proof. rewrite (zz4 &m). apply (zz3 &m). qed.


local lemma case4' &m : 
  Pr[ BLTGame'(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m 
  : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg))
 /\ toTime BLTGame.tg < toTime BLT_Wrap.qt 
 /\ toTime BLTGame.tg = BLTGame'.guess ] 
 <= Pr[ SHGameSimple(RO, Tag_Wrap, HT_Adv(A, TsU_Set(A2))).main() @ &m : res ].
proof. byequiv. symmetry. conseq wwwForB. smt. smt. smt. smt. qed.



local lemma case4'' &m : (Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m 
    : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ toTime BLTGame.tg < toTime BLT_Wrap.qt ] * (1%r/queryBound%r))
  <= Pr[ SHGameSimple(RO, Tag_Wrap, HT_Adv(A, TsU_Set(A2))).main() @ &m : res ].
proof. rewrite - (zz4' &m). rewrite - (ccc &m). apply (case4' &m). qed.


local lemma fact (a b c : real) : a <= b => 0%r <= c => a * c <= b * c. 
proof. smt. qed.


lemma case4 &m : Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m 
  : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ toTime BLTGame.tg < toTime BLT_Wrap.qt ]
  <= (Pr[ SHGameSimple(RO, Tag_Wrap, HT_Adv(A, TsU_Set(A2))).main() @ &m : res ] * queryBound%r).
proof. 

pose x := Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m 
 : (res /\ BLT_Wrap.used) /\ toTime BLTGame.tg < toTime BLT_Wrap.qt ].

pose y := Pr[SHGameSimple(RO, Tag_Wrap,  HT_Adv(A, TsU_Set(A2))).main() @ &m : res].

have : 0%r < queryBound%r. smt (queryBoundPosR).
move => ik.

smt (case4'').
qed.

end section. 
