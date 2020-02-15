From mathcomp Require Import all_ssreflect all_algebra all_field all_fingroup.
From codegen Require Import codegen.
Require irreducible.
Require Import polyn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma triv01 n : 1 < n -> 0 < n.-1.
Proof. by case: n. Qed.
Section phi.
Variables w n m r : nat.
Variable a : w.-tuple [fieldType of 'F_2].
Notation p := (n * w - r).
Hypothesis pm : prime (2 ^ p - 1).
Hypothesis mn : m < n.
Hypothesis m0 : 0 < m.
Hypothesis rw : r <= w.
Hypothesis r0 : 0 < r.

Lemma n2 : 2 <= n.
Proof.
  case: n mn m0 => //.
  case: m => []//[]// ?? + _.
  by apply ltn_trans.
Qed.

Hint Resolve n2 : core.

Lemma poly_exp_leq (t : poly_ringType [finFieldType of 'F_2]) p :
  1 < size t -> size (t ^+ p)%R < size (t ^+ p.+1)%R.
Proof.
  move=> Ht. elim: p => [|p IHp].
   by rewrite GRing.expr0 size_polyC GRing.oner_neq0 GRing.expr1.
  case s00: (size (t ^+ p.+1)%R == 0).
   by move/eqP: s00 IHp => ->.
  case s0: (size (t ^+ p.+2)%R == 0).
   rewrite size_poly_eq0 GRing.exprS GRing.mulf_eq0 -!size_poly_eq0 in s0.
   case/orP: s0 => s0.
    by move/eqP: s0 Ht => ->.
   by move/eqP: s0 IHp => ->.
  rewrite -(@prednK (size (t ^+ p.+1)%R)) ?(lt0n, s00) //
          -(@prednK (size (t ^+ p.+2)%R)) ?(lt0n, s0) //
          !size_exp ltnS ltn_mul2l ltnSn.
  case: (size t) Ht => // ?.
  by rewrite ltnS => ->.
Qed.

Lemma poly_exp_leq' (t : poly_ringType [finFieldType of 'F_2]) p q :
  p < q -> 1 < size t -> size (t ^+ p)%R < size (t ^+ q)%R.
Proof.
  elim: q => // q IHq pq t1.
  case pq0: (p == q).
   by move/eqP: pq0 => ->; apply/poly_exp_leq.
  apply/ltn_trans/poly_exp_leq/t1/IHq => //.
  by rewrite ltnNge leq_eqVlt eq_sym pq0 negb_or /= -ltnNge.
Qed.

Lemma mon_max r' E F :
  ((forall i, E i <= F i) -> \max_(i < r') E i <= \max_(i < r') F i)%nat.
Proof.
  elim: r' E F.
   move=> *.
   by rewrite big_ord0.
  move=> r' IH E F H.
  rewrite !big_ord_recr /=.
  rewrite /maxn.
  case: ifP => ?.
   apply: (leq_trans (H _)).
   by rewrite leq_max leqnn orbT.
  apply: (leq_trans (IH _ _ _)).
   move=> ?; apply H.
  by rewrite leq_max leqnn.
Qed.

Local Open Scope ring_scope.
Definition phi' :=
  ('X ^+ n + 'X ^+ m) ^+ (w - r) * ('X ^+ n.-1 + 'X ^+ m.-1) ^+ r
  + \sum_(i < r.-1) a`_i *: ('X ^+ n + 'X ^+ m) ^+ (w - r)
                     * ('X ^+ n.-1 + 'X ^+ m.-1) ^+ (r.-1 - i)
  + \sum_(i < w - r.-1)
     a`_(r.-1 + i) *: ('X ^+ n + 'X ^+ m) ^+ (w - r - i).

Lemma size_phi : (size phi').-1 = p.
Proof.
  rewrite /phi' /=.
  have?:(m.-1.+1 < n.-1.+1)%nat.
   by rewrite ?prednK // ?(esym (lt0n _)) ?(leq_trans _ mn).
  have?: (1 < size ('X^n + 'X^m)%R)%N.
   move=> ?.
   by rewrite size_addl ?size_polyXn // ltnS ?(ltn_trans _ mn).
  have?: (1 < size ('X^n.-1 + 'X^m.-1)%R)%N.
   move=> ?.
   rewrite size_addl ?size_polyXn ?size_polyX //.
   case: n mn => //[][]//.
   by case: m m0.
  have H : ('X^n.-1 + 'X^m.-1 != 0 :> {poly 'F_2})%R.
   by rewrite -size_poly_eq0 size_addl ?size_polyXn.
  have x : ('X^n + 'X^m != 0%R :> {poly 'F_2}).
   by rewrite -size_poly_eq0 size_addl ?size_polyXn.
  have H2: forall n', (('X^n + 'X^m) ^+ n' != 0 :> {poly 'F_2})%R.
   elim => [|? IHn].
    by rewrite GRing.expr0 GRing.oner_neq0.
   by rewrite GRing.exprS GRing.mulf_eq0 negb_or x.
  have H1: forall n', (('X^n.-1 + 'X^m.-1) ^+ n' != 0 :> {poly 'F_2})%R.
   elim => [|? IHn].
    by rewrite GRing.expr0 GRing.oner_neq0.
   by rewrite GRing.exprS GRing.mulf_eq0 negb_or H.
  rewrite !size_addl ?size_polyXn ?size_polyC //.
  + rewrite size_mul //.
    set T' := (_^n.-1 + _)%R.
    rewrite -(@prednK (size (T' ^+ r)%R)); last by rewrite lt0n size_poly_eq0 /T' H1.
    rewrite /T' addnS size_exp size_addl ?size_polyXn {T'}; last by [].
    set T' := (_ + _)%R.
    rewrite -(@prednK (size (T' ^+ (w - r)%nat)%R)); last by rewrite lt0n size_poly_eq0 /T' H2.
    rewrite /T' size_exp size_addl ?size_polyXn {T'}; last by [].
    rewrite mulnBr addSn /= addnBAC; last by apply: leq_mul.
    have H': (n = n.-1 + 1)%nat.
     by rewrite addn1 prednK // ?(ltn_trans _ mn).
    by rewrite [X in (_ + _ - X * r)%nat]H' mulnDl subnDA addnK mul1n.
  + apply: (leq_ltn_trans (size_sum _ _ _)).
    set T := (\max_(i < r.-1) size _%R).
    have/leq_ltn_trans: (T <= \max_(i < r.-1) size ((('X^n + 'X^m) ^+ (w - r)
                * ('X^n.-1 + 'X^m.-1) ^+ (r.-1 - i))%R : {poly 'F_2}))%N.
     subst T; apply: mon_max => i.
     case: a`_i => [][|[]//] H'.
      have->: (Ordinal H' = 0) by apply/val_inj.
      by rewrite !GRing.scale0r GRing.mul0r size_polyC eqxx.
     have->: (Ordinal H' = 1) by apply/val_inj.
     by rewrite !GRing.scale1r leqnn.
    apply.
    case r0': (0 < r.-1)%nat.
     have/eq_bigmax H': (0 < #|'I_r.-1|)%nat by rewrite card_ord.
     rewrite (proj2_sig (H' (fun i => size (('X^n + 'X^m) ^+ (w - r)
                                         * ('X^n.-1 + 'X^m.-1) ^+ (r.-1 - i))%R)))
             !size_mul // {T}.
     set T := size (('X^n + 'X^m) ^+ (w - r)).
     have->: T = T.-1.+1 by rewrite prednK // lt0n size_poly_eq0.
     rewrite !addSn ltn_add2l.
     apply: poly_exp_leq' => //.
      set X := sval _.
      case X0: (X == 0 :> nat)%nat.
       by move/eqP: X0 => ->; rewrite subn0; case: r r0.
      apply: leq_trans.
      apply irreducible.ltn_subr.
       case: X X0 => // ?? X0.
       by rewrite lt0n X0.
      by case: r r0.
    move: r0'; rewrite lt0n => /negP/negP/eqP => ->.
    by rewrite big_ord0 size_mul // -subn1 -addnBA ?ltn_addr // ?lt0n ?size_poly_eq0.
  + apply: (leq_ltn_trans (size_sum _ _ _)).
    set T := (\max_(i < w - r.-1) size _%R).
    have/leq_ltn_trans: (T <= \max_(i < w - r.-1) size (('X^n + 'X^m) ^+ (w - r - i) : {poly 'F_2}))%nat.
     subst T; apply: mon_max => i.
     case: a`_(r.-1 + i) => [][|[]//] H'.
      have->: (Ordinal H' = 0) by apply/val_inj.
      by rewrite !GRing.scale0r size_polyC eqxx.
     have->: (Ordinal H' = 1) by apply/val_inj.
     by rewrite !GRing.scale1r leqnn.
    apply.
    case w0: (w - r.-1 == 0)%nat.
     move/eqP: w0 => ->.
     by rewrite big_ord0 size_mul // -subn1 -addnBA ?ltn_addr // ?lt0n ?size_poly_eq0.
    move/negP/negP: w0; rewrite -lt0n => w0.
    have/eq_bigmax H': (0 < #|'I_(w - r.-1)|)%nat by rewrite card_ord.
    rewrite (proj2_sig (H' (fun i => size (('X^n + 'X^m) ^+ (w - r - i)))))%nat
            !size_mul // {T}.
    set T := sval _.
    case: T => [][?|].
     rewrite /= -subn1 subn0 -[X in (X < _)%nat]addn0 -addnBA
            ?lt0n ?size_poly_eq0 // ltn_add2l.
     rewrite subn1 size_exp size_addl ?size_polyXn ?size_polyX //.
     case: n mn mn m0 => []//[|????]; first by case: m.
     by rewrite mulSn ltn_addr.
    move=> s i.
    rewrite /= -subn1 -addnBA ?lt0n ?size_poly_eq0 // subn1.
    case wr0: (w - r == 0)%nat.
     move/eqP: wr0 => ->.
     rewrite sub0n GRing.expr0 size_polyC /=.
     rewrite -[X in (X < _)%nat]addn0.
     rewrite ltn_add2l size_exp size_addl ?size_polyXn //.
     case: n mn mn m0 => []//[|????]; first by case: m.
     by rewrite mulSn ltn_addr.
    rewrite ltn_addr //.
    apply: poly_exp_leq' => //.
    rewrite /leq -subSn.
     by rewrite subnAC subSnn.
    move: i.
    by rewrite -subn1 subnBA // addn1 subSn //.
  + apply: (leq_ltn_trans (size_sum _ _ _)).
    set T := (\max_(i < r.-1) size _%R).
    have/leq_ltn_trans: (T <= \max_(i < r.-1) size (('X^n + 'X^m) ^+ (w - r) * ('X^n.-1 + 'X^m.-1) ^+ (r.-1 - i) : {poly 'F_2})%R)%nat.
     subst T; apply: mon_max => i.
     case: a`__ => [][|[]//] H'.
      have->: (Ordinal H' = 0) by apply/val_inj.
      by rewrite !GRing.scale0r GRing.mul0r size_polyC eqxx.
     have->: (Ordinal H' = 1) by apply/val_inj.
     by rewrite !GRing.scale1r leqnn.
    apply.
    case r0': (0 < r.-1)%nat.
     have/eq_bigmax H': (0 < #|'I_r.-1|)%nat by rewrite card_ord.
     rewrite (proj2_sig (H' (fun i => size (('X^n + 'X^m) ^+ (w - r)
                                         * ('X^n.-1 + 'X^m.-1) ^+ (r.-1 - i))%R)))
             !size_mul // {T}.
     set T := size (('X^n + 'X^m) ^+ (w - r)).
     have->: T = T.-1.+1 by rewrite prednK // lt0n size_poly_eq0.
     rewrite !addSn ltn_add2l.
     apply: poly_exp_leq' => //.
      set X := sval _.
      case X0: (X == 0 :> nat)%nat.
       by move/eqP: X0 => ->; rewrite subn0; case: r r0.
      apply: leq_trans.
      apply irreducible.ltn_subr.
       case: X X0 => // ?? X0.
       by rewrite lt0n X0.
      by case: r r0.
    move: r0'; rewrite lt0n => /negP/negP/eqP => ->.
    by rewrite big_ord0 size_mul // -subn1 -addnBA ?ltn_addr // ?lt0n ?size_poly_eq0.
Qed.

End phi.

Lemma a32 : size ([:: 1; 0; 0; 1; 1; 0; 0; 1; 0; 0; 0; 0; 1; 0; 0; 0; 1; 0; 1;
                     1; 0; 0; 0; 0; 1; 1; 0; 1; 1; 1; 1; 1]: seq 'F_2)%R == 32.
Proof. by []. Qed.
Definition phi := phi' 624 397 31 (Tuple a32).

(* Local Open Scope term_scope. *)
(* Compute GRing.holds ('X_3 == 'X_3)%R. *)

(* Local Open Scope term_scope. *)
(* Check phi'. *)
(* Check phi'.[0]. *)
(* Set Printing All. *)
(* Check Fp_decFieldType 2. *)
(* Check [decFieldType of {poly 'F_2}]. *)
(* Goal phi' = phi'. *)
(*   apply/eqP. *)
(*   Check GRing.DecidableField.sat (GRing.DecidableField.mixin [decFieldType of 'F_2]). *)
(*   Check GRing.sat. *)
(*   apply/GRing.satP. *)
(* satP *)

(* Check (GRing.Const 0%R). *)
(* Check 'X_1. *)
(* Check 'X_1 : [decFieldType of 'F_2]. *)
(* Print GRing.DecidableField.axiom. *)

(* Compute phi. *)

(* Check GRing.holds. *)
(* Check (@GRing.rterm _ )%R. *)

(* Lemma test : ('X %% 'X == 1)%R. *)
Lemma pm' : prime (2 ^ 19937 - 1).
  Admitted.


Lemma size_phi : (size phi).-1 = 19937.
Proof.
  rewrite /phi /phi' /=.
  have ->: (32 - 31 = 1)%N by []; have ->: (32 - 30 = 2)%N by [].
  rewrite !GRing.expr1; set T := (\sum_(i < 2) _ *: _ ^+ _)%R.
  have ->: T = ('X^624 + 'X^397 + 1)%R.
   by rewrite /T big_ord_recr big_ord1 /= !GRing.scale1r
              subnn subn0 GRing.expr0 GRing.expr1.
  have H : (('X^623 + 'X^396 : poly_ringType [finFieldType of 'F_2])%R != 0%R).
   by rewrite -size_poly_eq0 size_addl ?size_polyXn.
  have x : (('X^624 + 'X^397 : poly_ringType [finFieldType of 'F_2])%R != 0%R).
   by rewrite -size_poly_eq0 size_addl ?size_polyXn.
  have H1: forall n, (('X^623 + 'X^396 : poly_ringType [finFieldType of 'F_2]) ^+ n)%R != 0%R.
   elim => [|n IHn].
    by rewrite GRing.expr0 GRing.oner_neq0.
   by rewrite GRing.exprS GRing.mulf_eq0 negb_or H /=.
  rewrite !size_addl ?size_polyXn ?size_polyC //.
  rewrite size_mul // size_addl ?size_polyXn //.
  set T' := (_ + _)%R.
  rewrite -(@prednK (size (T' ^+ 31)%R)); last by rewrite lt0n size_poly_eq0 /T' H1.
  rewrite /T' size_exp size_addl ?size_polyXn; last by [].
  by native_compute.
  repeat (
  repeat rewrite big_ord_recl /= GRing.scale0r GRing.mul0r GRing.add0r;
  repeat (rewrite big_ord_recl size_addl GRing.scale1r;
    first by rewrite size_mul // [X in _ < X]size_mul // -subn1 -[X in _ < X]subn1
             ltn_sub2r // ?(ltn_add2l, poly_exp_leq') // ?ltn_addr ?size_addl ?size_polyXn)).
  by rewrite big_ord0 size_polyC eqxx lt0n size_poly_eq0 GRing.mulf_eq0 negb_or H1 x.
  rewrite size_mul // size_addl ?size_polyXn //.
  set T' := (_ + _)%R.
  rewrite -(@prednK (size (T' ^+ 31)%R)); last by rewrite lt0n size_poly_eq0 /T' H1.
  by rewrite /T' size_exp size_addl ?size_polyXn.
  repeat (
  repeat rewrite big_ord_recl /= GRing.scale0r GRing.mul0r GRing.add0r;
  repeat (rewrite big_ord_recl size_addl GRing.scale1r;
    first by rewrite size_mul // [X in _ < X]size_mul // -subn1 -[X in _ < X]subn1
             ltn_sub2r // ?(ltn_add2l, poly_exp_leq') // ?ltn_addr ?size_addl ?size_polyXn)).
  by rewrite big_ord0 size_polyC eqxx lt0n size_poly_eq0 GRing.mulf_eq0 negb_or H1 x.
Qed.

(*
from :
https://en.wikipedia.org/wiki/Lucas%E2%80%93Lehmer_primality_test
*)

Definition prime' := 43154247973881626480552355163379198390539350432267115051652505414033306801376580911304513629318584665545269938257648835317902217334584413909528269154609168019007875343741396296801920114486480902661414318443276980300066728104984095451588176077132969843762134621790396391341285205627619600513106646376648615994236675486537480241964350295935168662363909047948347692313978301377820785712419054474332844529183172973242310888265081321626469451077707812282829444775022680488057820028764659399164766265200900561495800344054353690389862894061792872011120833614808447482913547328367277879565648307846909116945866230169702401260240187028746650033445774570315431292996025187780790119375902863171084149642473378986267503308961374905766340905289572290016038000571630875191373979555047468154333253474991046248132504516341796551470575481459200859472614836213875557116864445789750886277996487304308450484223420629266518556024339339190844368921018424844677042727664601852914925277280922697538426770257333928954401205465895610347658855386633902546289962132643282425748035786233580608154696546932563833327670769899439774888526687278527451002963059146963875715425735534475979734463100678367393327402149930968778296741391514599602374213629898720611431410402147238998090962818915890645693934483330994169632295877995848993366747014871763494805549996163051541225403465297007721146231355704081493098663065733677191172853987095748167816256084212823380168625334586431254034670806135273543270714478876861861983320777280644806691125713197262581763151313596429547763576367837019349835178462144294960757190918054625114143666384189433852576452289347652454631535740468786228945885654608562058042468987372436921445092315377698407168198376538237748614196207041548106379365123192817999006621766467167113471632715481795877005382694393400403061700457691135349187874888923429349340145170571716181125795888889277495426977149914549623916394014822985025331651511431278802009056808456506818877266609831636883884905621822262933986548645669080672191704740408891349835685662428063231198520436826329415290752972798343429446509992206368781367154091702655772727391329424277529349082600585884766523150957417077831910016168475685658673192860882070179760307269849987354836042371734660257694347235506301744118874141292438958141549100609752216882230887611431996472330842380137110927449483557815037586849644585749917772869926744218369621137675101083278543794081749094091043084096774144708436324279476892056200427227961638669149805489831121244676399931955371484012886360748706479568669048574782855217054740113945929622177502575565811067452201448981991968635965361551681273982740760138899638820318776303668762730157584640042798880691862640268612686180883874939573818125022279689930267446255773959542469831637863000171279227151406034129902181570659650532600775823677398182129087394449859182749999007223592423334567850671186568839186747704960016277540625331440619019129983789914712515365200336057993508601678807687568562377857095255541304902927192220184172502357124449911870210642694565061384919373474324503966267799038402386781686809962015879090586549423504699190743519551043722544515740967829084336025938225780730880273855261551972044075620326780624448803490998232161231687794715613405793249545509528052518010123087258778974115817048245588971438596754408081313438375502988726739523375296641615501406091607983229239827240614783252892479716519936989519187808681221191641747710902480633491091704827441228281186632445907145787138351234842261380074621914004818152386666043133344875067903582838283562688083236575482068479639546383819532174522502682372441363275765875609119783653298312066708217149316773564340379289724393986744139891855416612295739356668612658271234696438377122838998040199739078061443675415671078463404673702403777653478173367084844734702056866636158138003692253382209909466469591930161626097920508742175670306505139542860750806159835357541032147095084278461056701367739794932024202998707731017692582046210702212514120429322530431789616267047776115123597935404147084870985465426502772057300900333847905334250604119503030001704002887892941404603345869926367501355094942750552591581639980523190679610784993580896683299297681262442314008657033421868094551740506448829039207316711307695131892296593509018623094810557519560305240787163809219164433754514863301000915916985856242176563624771328981678548246297376249530251360363412768366456175077031977457534912806433176539995994343308118470147158712816149394421276614228262909950055746981053206610001560295784656616193252269412026831159508949671513845195883217147982748879261851417819979034417285598607727220866677680426090308754823803345446566305619241308374452754668143015487710877728011086004325892262259413968285283497045571062757701421761565262725153407407625405149931989494459106414660534305378576709862520049864880961144869258603473714363659194013962706366851389299692869491805172556818508298824954954815796063169517658741420159798754273428026723452481263569157307213153739781041627653715078598504154797287663122946711348158529418816432825044466692781137474494898385064375787507376496345148625306383391555145690087891955315994462944493235248817599907119135755933382121706191477185054936632211157222920331148502487563303118018805685073569841580518118710778653953571296014372940865270407021924383167290323231567912289419486240594039074452321678019381871219092155460768444573578559513613304242206151356457513937270939009707237827101245853837678338161023397586854894230696091540249987907453461311923963852950754758058205625956600817743007191746812655955021747670922460866747744520875607859062334750627098328593480067789456169602494392813763495657599847485773553990957557313200809040830036446492219409934096948730547494301216165686750735749555882340303989874672975455060957736921559195480815514035915707129930057027117286252843197413312307617886797506784260195436760305990340708481464607278955495487742140753570621217198252192978869786916734625618430175454903864111585429504569920905636741539030968041471.

Fixpoint S' n :=
  match n with
  | 0 => 4
  | S n' => ((S' n') ^ 2).-2 %% prime'
  end.
Compute S' 19937.-2.

(* Goal prime' = 2 ^ 19937 - 1. *)
(*   done. *)
(* Lemma test : 2 ^ 3 - 1 %| S 3.-2. *)
(* Eval native_compute in (S 19937.-2). *)

Lemma test : 2 ^ 19937 - 1 %| S' 19937.-2.
rewrite /=.

Eval native_compute in (2 ^ 19937 - 1 %| S 19937.-2).

Lemma lucas_test p : prime (2 ^ p - 1) = (2 ^ p - 1 %| S p.-2).
  apply/(iffP idP).

Check dvdn.

Lemma pm : prime (2 ^ (size phi).-1 - 1).
Proof. by rewrite size_phi pm'. Qed.

Lemma X2X : ('X ^ 2 %% phi != 'X %% phi)%R.
Proof.
  rewrite -GRing.subr_eq0 -modp_opp -modp_add.
  apply/negP => /dvdp_leq H.
  have/H: ('X ^ 2 - 'X : {poly 'F_2})%R != 0%R.
   rewrite GRing.subr_eq0.
   apply/negP => /eqP/(f_equal (size : {poly 'F_2} -> nat)).
   by rewrite size_polyXn size_polyX.
  rewrite [X in _ <= X]size_addl ?size_polyXn ?size_opp ?size_polyX //.
  by case: (size phi) size_phi => //= ? ->.
Qed.
(* Fixpoint spliti_iter T i (xs ys : seq T) := *)
(*   match i with *)
(*   | 0 => (rev xs, ys) *)
(*   | S j => *)
(*     match ys with *)
(*     | [::] => (rev xs, ys) *)
(*     | y :: ys' => spliti_iter j (y :: xs) ys' *)
(*     end *)
(*   end. *)

(* Definition spliti T i (xs : seq T) := spliti_iter i [::] xs. *)

Require Import BinNat mt Recdef.

(* Check @irreducible.mulX _ pm. *)
(* Definition init := initialize_random_state 20190820%N. *)
(* Definition zero := next_random_state init. *)
(* Definition one := next_random_state zero.2. *)
(* Compute (state_vector one.2). *)
(* Compute (index zero.2). *)
(* Compute spliti (index one.2).-1 (state_vector one.2). *)
(* Print init. *)
(* Print initialize_random_state . *)
(* Check row. *)
(* Check 'rV__. *)
(* Check head _. *)
(* Compute length *)
(* Compute 3 / 2. *)
(* Check 3 :: [::]. *)
(* Check N.lt. *)
(* Compute N.eqb 3 2. *)
(* Definition piX := locked (irreducible.pi pm 'X)%R. *)

(* Eval simpl in (piX * piX)%R. *)

(* Compute (irreducible.pi pm 'X)%R. *)
(* Compute ('X ^ 2)%R. *)

Definition head_bin (n : N):'F_2 := Ordinal ([eta ltn_pmod n (d:=2)] (leqnSn 1)).

Function binary_of_nat_iter acc (n : N) {measure nat_of_bin n} : list 'F_2 :=
 if N.eqb n 0 then rev acc else binary_of_nat_iter (head_bin n :: acc) (N.div2 n).
Proof.
  move=> _ []// p _.
  apply/ltP.
  case: p => //= p.
   rewrite !natTrecE ltnS.
   elim: (nat_of_pos p) => // n IHn.
   rewrite /= doubleS ltnS ltnW //.
  rewrite !natTrecE -addnn -[X in (X < _ + _)%nat]addn0 ltn_add2l.
  elim: p => //= p IHp.
  by rewrite natTrecE -addnn ltn_addr.
Qed.

Definition binary_of_nat (n : N) := binary_of_nat_iter [::] n.
Definition vector_of_state (x : random_state) :=
  let h := take ((index x + len.-1) %% len) (map binary_of_nat (state_vector x)) in
  let t := drop ((index x + len.-1) %% len) (map binary_of_nat (state_vector x)) in
  let h' := flatten h in
  let t' := flatten t in
  t' ++ take (length h' - 31) h'.

(* Fixpoint state_of_vector (x : seq 'F_2) := *)
(*   let (h, t) := spliti ((index x + len.-1) %% len) (map binary_of_nat (state_vector x)) in *)
(*   let h' := flatten h in *)
(*   let t' := flatten t in *)
(*   t' ++ take (length h' - 31) h'. *)

(* Check 'rV_3. *)
Definition state := { x : seq 'F_2 | size x = 19937 }.
  (* State : forall (x : seq 'F_2), size x = 19937 -> state. *)

Lemma zero_prf : size (map (fun _ => @ord0 1) (iota 0 19937)) = 19937.
Proof. by []. Defined.

Definition zero := @exist _ (fun x => size x = 19937) _ zero_prf.

Lemma add_prf (X Y : state) : size [seq (xy.1 + xy.2)%R | xy <- zip (proj1_sig X) (proj1_sig Y)] = 19937.
Proof.
  case: X Y => []? XH []? YH.
  by rewrite size_map size_zip XH YH.
Qed.

Definition add X Y := @exist _ (fun x => size x = 19937) _ (add_prf X Y).

Lemma asoc_add : associative add.
move=> x y z.
rewrite /add.
rewrite

Check subType .
(* Definition opp := id. *)
  _ : associative add;
  _ : commutative add;
  _ : left_id zero add;
  _ : left_inverse zero opp add
Check val.

Check iota _.
Check _.

Lemma test : lmodType 'F_2.
  apply: (LmodType _ _ _).
  rewrite /=.
  constructor.

  (V :
Check linear.
Check Vector.Axiom.

Check fun x => x.
Check iter .

Compute take 3 [:: 0; 1; 2; 3;4].
Compute drop 3 [:: 0; 1; 2; 3;4].

(* Definition f x := (next_random_state x).2. *)
(* Check irreducible.cycleX_dvdP. *)
(* Check reflect. *)
(* Check irreducible. *)

(* Check read_as_vector. *)
(* Compute spliti 2 (iota 0 3). *)

(* Compute length (state_vector one). *)
(* (624 * 32) - 31 *)

(* 624 * 32 *)
(* Set Printing All. *)

(* Check eigenvalue _ _. *)
(* Compute one. *)
(* Compute zero. *)
(* 0:324445478 *)
(* 1:774197212 *)


From infotheo Require Import f2 ssralg_ext.
Require Import BinNat.

Open Scope N_scope.

Definition mt19937_cycle : nat := 2 ^ 19937 - 1.

Require mt_alg.

Fail Lemma mt_alg_eq_mt : forall seed n,
    mt_alg.nth_random_value seed n = nth_random_value seed n.

Definition cyclic (f : nat -> N) cycle := forall n, f n = f (n + cycle)%nat.

Fail Lemma Mersenne_Twister_Cycle_alg n seed :
  cyclic (mt_alg.nth_random_value seed).

Section mt19937_cyclic.
Variable seed : N.

Lemma Mersenne_Twister_Cycle :
  cyclic (nth_random_value seed) mt19937_cycle.
Abort.

Lemma least_cycle cycle :
  (cycle < mt19937_cycle)%nat -> ~ cyclic (nth_random_value seed) cycle.
Abort.

End mt19937_cyclic.
