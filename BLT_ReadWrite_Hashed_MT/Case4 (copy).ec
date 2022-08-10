pragma Goals:printall.

require import Int Real SmtMap Distr DInterval FSet.

require import BLT_Instance.

require import RandomnessOracle.

require import SHGame.

require Case4_A1 Case4_A2.



(* If A^BLT_Wrap uses signing oracle at time t' and forges a signature
for time t so that t < t' then we turn A^BLT_Wrap into adversary HT_Adv(A)
who finds an H-image of a tag (without access to tag-oracle)  *)
op timeX        : pkey -> int -> int.
op chainX        : pkey -> int -> chain.
op hash_setX    : pkey -> int -> int -> hash_output fset option.

clone export Case4_A1.Case4_A1_Theory.
clone export Case4_A2.Case4_A2_Theory.


module SHGameSimple1(RO : ROracle, Tag_O : Tag_Oracle,  A2 : BLT_AdvH2) = {

  var guess : int
  var y : hash_output fset
  var pk : pkey
  var sk : skey

  var c  : chain
  module A2 = A2(RO, Tag_O)

  proc main() : bool = {
    var it : int;

    it = RO.init();
    (pk, sk) =$ keys;

    guess =$ dinter 1 queryBound;
    Tag_O.init(pk, sk);
    c = A2.forge(pk);

    (* return (HT.H (tag sk guess) \in (leaf c)) /\ (root c) \subset (ogetf (hash_setX pk it guess)); *)
    return   (HT.H (tag sk guess) \in (leaf c))
             /\  (root c) \subset (ogetf TsU.r.[guess]); 
  }
}.


module SHGameSimple2(RO : ROracle, Tag_O : Tag_Oracle,  A2 : BLT_AdvH2) = {

  var t : int
  var y : hash_output fset

  module A2 = A2(RO, Tag_O)
  var guess : int
  proc main() : bool = {
    var pk : pkey;
    var sk : skey;
    var it : int;
    var c  : chain;
    it = RO.init();
    (pk, sk) =$ keys;


    guess =$ dinter 1 queryBound;
    Tag_O.init(pk, sk);
    c = A2.forge(pk);


    return   (HT.H (tag sk guess) \in (leaf c))
             /\  (root c) \subset (ogetf TsU.r.[guess]);
  }
}.


section. 


local module BLTGame'(RO : ROracle, Tag_O : Tag_Oracle, 
  Ts_O : TS, BLT_O : BLT_Oracle, A : BLT_Adv) = {

  module G = BLTGame(RO, Tag_O,Ts_O, BLT_O, A)
  var guess : int
  var r : bool

  proc main() : bool = {
    r = G.main();
    guess <$ dinter 1 queryBound;
    return r;
  }
}.



declare module A : BLT_Adv{Tag_Wrap, BLT_Wrap, TsU, BLTGame, RO, SHGameSimple, SHGameSimple1, SHGameSimple2, Case4_Adv1, BLTGame'}.
declare module A2 : BLT_Adv_Set{Tag_Wrap, BLT_Wrap, TsU, A, BLTGame, RO, SHGameSimple, SHGameSimple1, SHGameSimple2, Case4_Adv1, BLTGame'}.



axiom A_ll : forall (O <: BLT_AdvOracle{A}),
  islossless O.sign =>
  islossless O.put => islossless O.get => islossless A(O).forge.

axiom A2_ll : islossless A2.react.



axiom a1_premise pkk skk  : phoare [ Case4_Adv1(A,A2, RO).forge' : (pkk, skk) \in keys /\ pk = pkk ==>  (forall x, x < timeX pkk RO.t => TsU_1.r.[x] = hash_setX pkk RO.t x)  ] = 1%r.

axiom a2_premise pkk skk  : phoare [ Case4_Adv2(A,TsU_Set(A2), RO, Tag_Wrap).forge : (pkk, skk) \in keys /\
  pk = pkk /\ Tag_Wrap.usedTag = deftag 
 /\ Tag_Wrap.usedFlag = false 
 /\ Tag_Wrap.sk = skk
 /\ Tag_Wrap.pk = pkk  ==>  (forall x, TsU.r.[x] = hash_setX pkk RO.t x) /\ res = chainX pkk RO.t /\ timeX pkk RO.t = toTime BLT_Wrap.qt ] = 1%r.

local lemma ig1 : equiv [ SHGameSimple(RO, Tag_Wrap, Case4_Adv1(A, A2), Case4_Adv2(A, TsU_Set(A2))  ).main ~ SHGameSimple1(RO, Tag_Wrap, Case4_Adv2(A, TsU_Set(A2))).main :
  true
     ==> (SHGameSimple.t{1}  < toTime BLT_Wrap.qt{1}) =>
  ={res} ].
proof. proc. 

seq 2 2 : (it{2} = it{1} /\ it{1} = RO.t{1}  /\  SHGameSimple.pk{1} = SHGameSimple1.pk{2} /\ SHGameSimple.sk{1} = SHGameSimple1.sk{2} /\ ={RO.t}  /\  (SHGameSimple.pk{1}, SHGameSimple.sk{1}) \in keys ).

wp. inline*. wp. rnd. wp. rnd. skip. progress. smt. 




seq 1 1 : (it{2} = it{1} /\ it{1} = RO.t{1} /\   SHGameSimple.pk{1} = SHGameSimple1.pk{2} /\ SHGameSimple.sk{1} = SHGameSimple1.sk{2} /\ ={RO.t} /\ (SHGameSimple.pk{1}, SHGameSimple.sk{1}) \in keys /\ SHGameSimple1.guess{2} = SHGameSimple.t{1} /\ (SHGameSimple.t < timeX SHGameSimple.pk RO.t => SHGameSimple.y = ogetf (hash_setX SHGameSimple.pk RO.t SHGameSimple.t)){1}  /\ Case4_Adv1.guess{1} = SHGameSimple.t{1} /\ SHGameSimple.t{1} = SHGameSimple1.guess{2} ). 




inline  SHGameSimple(RO, Tag_Wrap, Case4_Adv1(A, A2), Case4_Adv2(A, TsU_Set(A2))).A.forge.
wp. rnd.

exists* RO.t{1}, SHGameSimple.pk{1}, SHGameSimple.sk{1}.
elim*. move => ttt pk_L pk_R.

call {1} (a1_premise pk_L  pk_R). wp. skip. progress. smt. 

exists* RO.t{1}, SHGameSimple.pk{1}, SHGameSimple.sk{1}.
elim*. move => ttt pk_L sk_L.

call {1} (a2_premise pk_L sk_L). 
call {2} (a2_premise pk_L sk_L). 

inline Tag_Wrap.init. wp.



skip. progress.  rewrite H0. smt. smt.

qed.





local lemma wwwForB2 : equiv [ SHGameSimple1(RO, Tag_Wrap, Case4_Adv2(A, TsU_Set(A2))).main 
  ~ BLTGame'(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main
  : ={glob A, glob A2} 
  ==> res{2} /\ (toTime BLTGame.tg{2} = BLTGame'.guess{2})  => res{1}  ].
proof. proc.

swap{1} 3 2.

rnd. 

inline*. wp.

call (_: ={glob TsU, glob BLT_Wrap}).
admit. admit. admit.


wp. rnd. wp. rnd.


skip.
progress.
admit.
qed.




local lemma wwwForB3 : equiv [ SHGameSimple(RO, Tag_Wrap, Case4_Adv1(A, A2), Case4_Adv2(A, TsU_Set(A2))).main 
  ~ BLTGame'(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main
  : ={glob A, glob A2} 
  ==> res{2} /\ (toTime BLTGame.tg = BLTGame'.guess){2} /\ SHGameSimple.t{1}  < toTime BLT_Wrap.qt{1} => res{1} ].
proof. 
symmetry. 

transitivity SHGameSimple1(RO, Tag_Wrap, Case4_Adv2(A, TsU_Set(A2))).main 
   (={glob A, glob A2}  ==> res{1} /\ (toTime BLTGame.tg{1} = BLTGame'.guess{1})  => res{2})
   (={glob A, glob A2} ==>  (SHGameSimple.t  < toTime BLT_Wrap.qt){2} =>  ={res}). smt. progress. smt.
symmetry. conseq wwwForB2. smt. 

symmetry. conseq ig1. progress. smt.
qed.



local lemma zz2 &m : 
  phoare [ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main : 
    (glob A) = (glob A){m} /\ (glob A2) = (glob A2){m}  ==> 
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
move => &m0 _. byequiv.

proc. inline*. wp. call (_: ={glob BLT_Wrap, glob Tag_Wrap, glob TsU, glob A2}).
proc. if. smt. wp. inline*. wp.  call(_:true). wp. skip. progress. wp. skip. smt.
proc. inline*. wp. call (_:true). wp. skip. smt.
proc. inline*. wp. skip. smt.

wp. rnd.  wp.  rnd. skip. smt. smt. smt. qed.




local lemma zz &m : 
  phoare [ BLTGame'(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main : 
    (glob A) = (glob A){m} /\ (glob A2) = (glob A2){m}  ==> 
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

cut : 1 <= toTime BLTGame.tg{hr} <= queryBound. smt.
move => www.

have z := dinter1E 1 queryBound  (toTime BLTGame.tg{hr}).
rewrite www in z.

cut : mu1 [1..queryBound] (toTime BLTGame.tg{hr}) = inv (queryBound)%r. smt.
move => opp. rewrite - opp.

cut : ((=) (toTime BLTGame.tg{hr})) = pred1 (toTime BLTGame.tg{hr}).
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
proof.  byphoare (_: (glob A) = (glob A){m} /\ (glob A2) = (glob A2){m}  ==> _). 
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
wp. rnd. wp.  rnd. skip. smt. smt.
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

wp. rnd. wp. rnd. skip. progress. smt.
smt. 

cut : root result_R.`3 <> fset0. admit. 

move => sh.
cut : r_R.[toTime result_R.`2] <> None. timeout 15. smt.

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
 <= Pr[ SHGameSimple(RO, Tag_Wrap, Case4_Adv1(A, A2), Case4_Adv2(A, TsU_Set(A2))).main () @ &m : res ].
proof. byequiv. symmetry. conseq wwwForB3. smt. progress. admit. smt. smt. smt. qed.



local lemma case4'' &m : (Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m 
    : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ toTime BLTGame.tg < toTime BLT_Wrap.qt ] * (1%r/queryBound%r))
  <= Pr[ SHGameSimple(RO, Tag_Wrap, Case4_Adv1(A, A2), Case4_Adv2(A, TsU_Set(A2))).main() @ &m : res ].
proof. rewrite - (zz4' &m). rewrite - (ccc &m). apply (case4' &m). qed.


local lemma fact (a b c : real) : a <= b => 0%r <= c => a * c <= b * c. 
proof. smt. qed.



lemma case4 &m : Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m 
  : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ toTime BLTGame.tg < toTime BLT_Wrap.qt ]
  <= (Pr[ SHGameSimple(RO, Tag_Wrap, Case4_Adv1(A, A2), Case4_Adv2(A, TsU_Set(A2))).main()  @ &m : res ] * queryBound%r).
proof. 

pose x := Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m 
 : (res /\ BLT_Wrap.used) /\ toTime BLTGame.tg < toTime BLT_Wrap.qt ].

pose y := Pr[ SHGameSimple(RO, Tag_Wrap, Case4_Adv1(A, A2), Case4_Adv2(A, TsU_Set(A2))).main () @ &m : res].

cut : 0%r < queryBound%r. smt (queryBoundPosR).
move => ik.

smt (case4'').
qed.





  
