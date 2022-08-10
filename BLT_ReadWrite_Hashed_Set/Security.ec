pragma Goals:printall.

require import Int Real Distr SmtMap FSet DInterval.
require import BLT_Instance.
require import Case1.
require import Case2.
require  Case3_A1_A2_A3.
require import Case4.
require import Dummy_Tag.

require import RandomnessOracle.

require import SHGame.

require import TagPhantom.

require import Case3_Collision.
require import SHGame.
require Case3_A1 Case3_A2 Case3_A3.

require import SHGameProps.


section.

op timeX        : pkey -> int -> int.
op hash_setX    : pkey -> int -> hash_output fset.
op time_setX    : pkey -> int -> int fset.
op message_setX : pkey -> int -> message fset.
op messageX     : pkey -> int -> message.
op boolX        : pkey -> int -> bool.


clone import Case3_A1_A2_A3.A1_A2_A3_Theory as A1A2A3 with op timeX <- timeX,       
                                                           op hash_setX      <- hash_setX,   
                                                           op time_setX      <- time_setX,   
                                                           op message_setX   <- message_setX,
                                                           op messageX       <- messageX,    
                                                           op boolX          <- boolX.       



declare module A <: BLT_Adv{-Tag_Wrap_1, -BLT_Wrap, -TsU, -BLTGame, -BLT_Dummy_Time, -Tag_Wrap, -TsU_1, -TsU_2,  -Tag_Wrap_2, -SH_Oracle, -SHGame, -SHGame1, -SHGame2, -SHGame3, -RO, -Case3_Adv3, -BLTGameD, -BLT_Dummy_Repo,  -H_AdvCR, -HT_Adv}.
declare module A2 <: BLT_Adv_Set{-Tag_Wrap_1, -BLT_Wrap, -TsU, -A, -BLTGame, -BLT_Dummy_Time, -Tag_Wrap, -TsU_1, -TsU_2, -Tag_Wrap_2,  -SH_Oracle, -SHGame, -SHGame1, -SHGame2, -SHGame3, -RO, -Case3_Adv3, -BLTGameD, -BLT_Dummy_Repo, -H_AdvCR, -HT_Adv}.

axiom A_ll : forall (O <: BLT_AdvOracle{-A}), 
  islossless O.sign => islossless O.put => islossless O.get => islossless A(O).forge.
axiom A2_ll : islossless A2.react.


axiom computableAdvs_A &m  pkk skk : (pkk, skk) \in keys => 
  Pr [ BLTGameD(TsU_Set(A2),Tag_Wrap, A).main(pkk, skk) @ &m :  
     toTime BLT_Wrap.qt = timeX  pkk RO.t 
  /\ (ogetf TsU.r.[toTime BLT_Wrap.qt]) = hash_setX pkk RO.t
  /\ BLT_Wrap.used = boolX pkk RO.t
  /\ fset1 (toTime BLT_Wrap.qt) = time_setX pkk RO.t
  /\ (ogetff BLT_Wrap.qs)   = message_setX pkk RO.t
  /\ BLTGameD.m = (messageX pkk RO.t) ] = 1%r.



local lemma computableAdvs_Ap &m  pkk skk : (pkk, skk) \in keys => 
  Pr [ BLTGameD(TsU_Set(A2), Tag_Wrap, A).main(pkk, skk) @ &m :  
     toTime BLT_Wrap.qt = timeX  pkk RO.t 
  /\ (ogetf TsU.r.[toTime BLT_Wrap.qt]) = hash_setX pkk RO.t
  /\ BLT_Wrap.used = boolX pkk RO.t
  /\ fset1 (toTime BLT_Wrap.qt) = time_setX pkk RO.t
  /\ (ogetff BLT_Wrap.qs)   = message_setX pkk RO.t
  /\ HM.H BLTGameD.m = HM.H (messageX pkk RO.t) ] = 1%r.
proof.  move => or. 

have : Pr [ BLTGameD(TsU_Set(A2), Tag_Wrap, A).main(pkk, skk) @ &m :  
     toTime BLT_Wrap.qt = timeX  pkk RO.t 
  /\ (ogetf TsU.r.[toTime BLT_Wrap.qt]) = hash_setX pkk RO.t
  /\ BLT_Wrap.used = boolX pkk RO.t
  /\ fset1 (toTime BLT_Wrap.qt) = time_setX pkk RO.t
  /\ (ogetff BLT_Wrap.qs)   = message_setX pkk RO.t
  /\ HM.H BLTGameD.m = HM.H (messageX pkk RO.t) ] <= 1%r.
rewrite Pr [mu_le1]. auto.

have : Pr [ BLTGameD(TsU_Set(A2),Tag_Wrap, A).main(pkk, skk) @ &m :  
     toTime BLT_Wrap.qt = timeX  pkk RO.t 
  /\ (ogetf TsU.r.[toTime BLT_Wrap.qt]) = hash_setX pkk RO.t
  /\ BLT_Wrap.used = boolX pkk RO.t
  /\ fset1 (toTime BLT_Wrap.qt) = time_setX pkk RO.t
  /\ (ogetff BLT_Wrap.qs)   = message_setX pkk RO.t
  /\ HM.H BLTGameD.m = HM.H (messageX pkk RO.t) ] >= 1%r.

rewrite - (computableAdvs_A &m pkk skk or).
rewrite Pr [mu_sub]. progress. auto. 

move => i1 i2. smt.
qed.


local lemma pr1 &m (A <: BLT_Adv{-BLT_Wrap, -TsU}) (A2 <: BLT_Adv_Set{-BLT_Wrap, -TsU}) : 
    Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : res ]
  = Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : res  /\  BLT_Wrap.used ]
  + Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : res  /\ !BLT_Wrap.used ].
proof. rewrite Pr[mu_split BLT_Wrap.used]. done. qed.



local lemma pr2' &m (A <: BLT_Adv{-BLT_Wrap, -TsU}) (A2 <: BLT_Adv_Set{-BLT_Wrap, -TsU}) : 
    Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : res /\ BLT_Wrap.used ]
  = Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : (res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg) ] 
  + Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : (res /\ BLT_Wrap.used) /\ !(tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg) ].
proof. rewrite Pr[mu_split (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)]. done. qed.

     
local lemma pr2 &m (A <: BLT_Adv{-BLT_Wrap, -TsU}) (A2 <: BLT_Adv_Set{-BLT_Wrap, -TsU}) : 
    Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) ]
  = Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ toTime BLTGame.tg < toTime BLT_Wrap.qt ] 
  + Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ !(toTime BLTGame.tg < toTime BLT_Wrap.qt) ].
proof. rewrite Pr[mu_split (toTime BLTGame.tg < toTime BLT_Wrap.qt)]. done. qed.


local lemma pr3 &m (A <: BLT_Adv{-BLT_Wrap,  -TsU}) (A2 <: BLT_Adv_Set{-BLT_Wrap, -TsU}) : 
    Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ !(toTime BLTGame.tg < toTime BLT_Wrap.qt) ]
  = Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\  (toTime BLT_Wrap.qt <= toTime BLTGame.tg) ].
proof. rewrite Pr[mu_eq]. smt. done. qed.


local lemma pr4 &m (A <: BLT_Adv{-BLT_Wrap, -TsU}) (A2 <: BLT_Adv_Set{-BLT_Wrap, -TsU}) : 
   Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ (toTime BLT_Wrap.qt <= toTime BLTGame.tg) ]
 = Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : (((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ (toTime BLT_Wrap.qt <= toTime BLTGame.tg)) /\ (toTime BLT_Wrap.qt = toTime BLTGame.tg) ]
 + Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : (((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ (toTime BLT_Wrap.qt <= toTime BLTGame.tg)) /\ !(toTime BLT_Wrap.qt = toTime BLTGame.tg) ].
proof. rewrite Pr[mu_split (toTime BLT_Wrap.qt = toTime BLTGame.tg)]. done. qed.


local lemma pr5 &m (A <: BLT_Adv{-BLT_Wrap, -TsU}) (A2 <: BLT_Adv_Set{-BLT_Wrap, -TsU}) : 
   Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : (((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ (toTime BLT_Wrap.qt <= toTime BLTGame.tg)) /\ !(toTime BLT_Wrap.qt = toTime BLTGame.tg) ]
 = Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : (((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ (toTime BLT_Wrap.qt < toTime BLTGame.tg)) ].
proof. rewrite Pr[mu_eq]. smt. done. qed.


local lemma pr6 &m (A <: BLT_Adv{-BLT_Wrap, -TsU}) (A2 <: BLT_Adv_Set{-BLT_Wrap, -TsU}) : 
   Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : (((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ (toTime BLT_Wrap.qt <= toTime BLTGame.tg)) /\ (toTime BLT_Wrap.qt = toTime BLTGame.tg) ]
 = Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : (((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ (toTime BLTGame.tg = toTime BLT_Wrap.qt)) ].
proof. rewrite Pr[mu_eq]. smt. done. qed.


local lemma pr7 &m (A <: BLT_Adv{-BLT_Wrap, -TsU}) (A2 <: BLT_Adv_Set{-BLT_Wrap, -TsU}) : 
   Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ toTime BLTGame.tg = toTime BLT_Wrap.qt ] 
   = 
   Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ toTime BLTGame.tg = toTime BLT_Wrap.qt /\ HM.H (oget BLT_Wrap.qs) = (HM.H BLTGame.m) ] 
  +  Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ toTime BLTGame.tg = toTime BLT_Wrap.qt /\ HM.H (oget BLT_Wrap.qs) <> (HM.H BLTGame.m) ]. 
rewrite Pr[mu_split (HM.H (oget BLT_Wrap.qs) = (HM.H BLTGame.m))].  

have ->: Pr[BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m :
   (((res /\ BLT_Wrap.used) /\
     tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg) /\
    toTime BLTGame.tg = toTime BLT_Wrap.qt) /\
   (HM.H (oget BLT_Wrap.qs)) = (HM.H BLTGame.m)%HM]
 = Pr[BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m :
   ((res /\ BLT_Wrap.used) /\
    tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg) /\
   toTime BLTGame.tg = toTime BLT_Wrap.qt /\
   (HM.H (oget BLT_Wrap.qs))%HM = (HM.H BLTGame.m)%HM].
smt.
smt.
qed.


local lemma pr_split &m (A <: BLT_Adv{-BLT_Wrap, -TsU}) (A2 <: BLT_Adv_Set{-BLT_Wrap, -TsU}) : 
    Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : res ]
  = Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ toTime BLTGame.tg < toTime BLT_Wrap.qt ] 
   + Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ toTime BLTGame.tg = toTime BLT_Wrap.qt /\ HM.H (oget BLT_Wrap.qs) = (HM.H BLTGame.m) ] 
  +  Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ toTime BLTGame.tg = toTime BLT_Wrap.qt /\ HM.H (oget BLT_Wrap.qs) <> (HM.H BLTGame.m) ]
  + Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ toTime BLT_Wrap.qt < toTime BLTGame.tg  ]   
  + Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ !(tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) ]
  + Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : res /\ !BLT_Wrap.used ].
proof. rewrite (pr1 &m A A2) (pr2' &m A A2) (pr2 &m A A2). rewrite (pr3 &m A A2).  rewrite (pr4 &m A A2). rewrite (pr5 &m A A2) (pr6  &m A A2) (pr7  &m A A2). smt. 
qed.



local lemma security &m : Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : res ]
  <= 
     Pr[BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Dummy, A).main() @ &m : res]
   + Pr[TagGame(RO, Tag_Wrap, B(RO, A, TsU_Set(A2))).main() @ &m : res]
   + Pr[SHGame(RO, Case3_Adv1(A, A2), Case3_Adv2(A, A2), Case3_Adv3(A, A2)).main() @ &m : res]
   + Pr[HM.CR_H(H_AdvCR(A, A2)).main() @ &m : res]
   + Pr[TagGamePhantom(RO, Tag_Wrap, BTG'(RO,A2,A)).main() @ &m : res ]
   + Pr[SHGameSimple(RO, Tag_Wrap, HT_Adv(A, TsU_Set(A2))).main() @ &m : res] * queryBound%r.
proof. rewrite (pr_split &m A A2). 

have : Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : res /\ !BLT_Wrap.used ] <=
                 Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Dummy, A).main() @ &m : res ].
apply (case1 RO A A2 (* A_ll A2_ll *) &m). move => case1_pr.

have : Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : 
  (((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg))
   /\ toTime BLT_Wrap.qt < toTime BLTGame.tg ] <=
 Pr[ TagGame(RO, Tag_Wrap, B(RO, A, TsU_Set(A2))).main() @ &m : res ]. 
apply (case2 A A2 &m).

move => case2_pr.


have : Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ toTime BLTGame.tg = toTime BLT_Wrap.qt /\ HM.H (oget BLT_Wrap.qs) <> (HM.H BLTGame.m) ] <= Pr [ SHGame(RO, Case3_Adv1(A,A2), Case3_Adv2(A,A2), Case3_Adv3(A,A2)).main() @ &m : res ] .
apply (case3 A A2 (* A_ll A2_ll  computableAdvs_Ap  computableAdvs_A *) &m). move => case3_pr.

have : Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m 
  : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ toTime BLTGame.tg < toTime BLT_Wrap.qt ]
  <= (Pr[ SHGameSimple(RO, Tag_Wrap,  HT_Adv(A, TsU_Set(A2))).main() @ &m : res ] * queryBound%r).
apply (case4 RO A A2 (* A_ll A2_ll *) &m). move => case4_pr.

have :  Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ !(tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) ]
  <= Pr[TagGamePhantom(RO, Tag_Wrap, BTG'(RO,A2,A)).main() @ &m : res ].
 
apply (tgcollision_pr A A2 &m).


have : Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : ((res /\ BLT_Wrap.used) /\ (tag Tag_Wrap.sk (toTime BLTGame.tg) = BLTGame.tg)) /\ toTime BLTGame.tg = toTime BLT_Wrap.qt /\ HM.H (oget BLT_Wrap.qs) = (HM.H BLTGame.m) ]
  <= Pr[ HM.CR_H(H_AdvCR(A, A2)).main() @ &m : res ].
apply (case3_collision A A2 &m).

timeout 40. smt.

qed.


local lemma security_tg1 &m :  
    Pr[BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Dummy, A).main() @ &m : res] <=
      Pr[TagGame(RO, Tag_Wrap, BTG(RO, A2, A)).main() @ &m : res].
proof. apply (blt_dummy_tag_pr A A2 &m). qed.


lemma main_security &m : 
  Pr[ BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Wrap, A).main() @ &m : res ] <= 
     Pr[TagGame(RO, Tag_Wrap, BTG(RO, A2, A)).main() @ &m : res]
   + Pr[TagGame(RO, Tag_Wrap, B(RO, A, TsU_Set(A2))).main() @ &m : res]
   + Pr[SHGame(RO, Case3_Adv1(A, A2), Case3_Adv2(A, A2), 
          Case3_Adv3(A, A2)).main() @ &m : res]
   + Pr[HM.CR_H(H_AdvCR(A, A2)).main() @ &m : res]
   + Pr[TagGamePhantom(RO, Tag_Wrap, BTG'(RO,A2,A)).main() @ &m : res ]
   + Pr[ SHGame(RO, MyA(TsU_Set(A2), HT_Adv(A, TsU_Set(A2)), Tag_Wrap), MyB, MyC).main() @ &m : res ] * queryBound%r.

proof.  

have : Pr[BLTGame(RO, Tag_Wrap, TsU_Set(A2), BLT_Dummy, A).main() @ &m : res]
  <= Pr[TagGame(RO, Tag_Wrap, BTG(RO, A2, A)).main() @ &m : res]. apply (security_tg1 &m).
move => qq1.

have : Pr[ SHGameSimple(RO, Tag_Wrap,  HT_Adv(A, TsU_Set(A2))).main() @ &m : res] <= Pr[ SHGame(RO, MyA(TsU_Set(A2), HT_Adv(A, TsU_Set(A2)), Tag_Wrap), MyB, MyC).main() @ &m : res ]. 


apply (main_sh_security (HT_Adv(A, TsU_Set(A2))) A2 &m).
move => qq2.

smt.    
qed.

end section.
