module

public import VerifiedGarbage.Impl.Mont.AArch64.P521
public import VerifiedGarbage.Proof.Mont.AArch64.P521.Check
public import VerifiedGarbage.Proof.Framework.Bitslice.Machine
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# P-521's field arithmetic on AArch64: the kernels

The product and the square (`mulOps`, `sqrOps`) are `[a] [b]` and `[a]^2`,
times `2^-576`, modulo `p` (`mul_kernel`, `sqr_kernel`), by the checker
(`Check.lean`): the outputs' functional, run backwards, is the sum of the
products of the words. Their bounds are the checker's too: below
`2^521 + 2^513`, and zero for a zero operand.
-/

-- separate module: the checks of the products, which change only with them
@[expose] public section

namespace VG.Proof.Mont.AArch64.P521

open VG VG.AArch64 VG.Impl.Mont.AArch64.P521

/-! ## Sums -/

/-- `f 0 + … + f (n - 1)`. -/
def sumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo f n + f n

theorem sumTo_congr {f g : Nat → Nat} : ∀ {n : Nat}, (∀ i < n, f i = g i) → sumTo f n = sumTo g n
  | 0, _ => rfl
  | n + 1, h => by
    rw [sumTo, sumTo, sumTo_congr fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)]

theorem sumTo_mul (f : Nat → Nat) (c : Nat) : ∀ n, sumTo (fun i => c * f i) n = c * sumTo f n
  | 0 => rfl
  | n + 1 => by rw [sumTo, sumTo, sumTo_mul f c n, Nat.mul_add]

theorem sumTo_cg {m : Nat} {f g : Nat → Nat} : ∀ {n : Nat}, (∀ i < n, Cg m (f i) (g i)) → Cg m (sumTo f n) (sumTo g n)
  | 0, _ => Cg.refl _ _
  | n + 1, h => (sumTo_cg fun i hi => h i (Nat.lt_succ_of_lt hi)).add (h n (Nat.lt_succ_self n))

/-- The weight of word `i`. -/
def pw (i : Nat) : Nat := 2 ^ (64 * i)

theorem pw_add (i j : Nat) : pw (i + j) = pw i * pw j := by unfold pw; rw [Nat.mul_add, Nat.pow_add]
theorem pw_succ (i : Nat) : pw (i + 1) = 2 ^ 64 * pw i := by rw [pw_add, Nat.mul_comm]; rfl
theorem pw_zero : pw 0 = 1 := rfl
theorem pw_pos (i : Nat) : 0 < pw i := Nat.two_pow_pos _

/-- The number whose words are `f 0`, …, `f (n - 1)`. -/
def num (f : Nat → Nat) (n : Nat) : Nat := sumTo (fun i => pw i * f i) n

theorem num_succ (f : Nat → Nat) (n : Nat) : num f (n + 1) = num f n + pw n * f n := rfl

theorem prime_pos : 0 < prime := by decide +kernel

theorem num_lt {f : Nat → Nat} : ∀ {n : Nat}, (∀ i < n, f i < 2 ^ 64) → num f n < pw n
  | 0, _ => Nat.one_pos
  | n + 1, h => by
    have ih := num_lt fun i hi => h i (Nat.lt_succ_of_lt hi)
    have hn : pw n * (f n + 1) ≤ pw n * 2 ^ 64 := Nat.mul_le_mul_left _ (h n (Nat.lt_succ_self n))
    rw [Nat.mul_add] at hn
    rw [num_succ, pw_succ, Nat.mul_comm (2 ^ 64)]
    omega_using [ih, hn]

theorem num_zero {f : Nat → Nat} {n : Nat} (h : num f n = 0) : ∀ i < n, f i = 0 := by
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    rw [num_succ] at h
    have h1 := Nat.eq_zero_of_add_eq_zero_right h
    have h2 := Nat.eq_zero_of_add_eq_zero_left h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact ih h1 i hi
    · exact (Nat.mul_eq_zero.mp h2).resolve_left (Nat.ne_of_gt (pw_pos _))

/-! ## Products, sorted -/

/-- The order of products. -/
def Pr.key (q : Pr) : Nat := 4194304 * q.a + q.b

/-- A product in its place, with the one of the same factors if there is one. -/
def insP (m : Nat) (g : Pr) : List Pr → List Pr
  | [] => [g]
  | q :: qs =>
    if Nat.beq q.a g.a && Nat.beq q.b g.b then ⟨q.a, q.b, (q.cl + g.cl) % m, (q.ch + g.ch) % m⟩ :: qs
    else if Nat.ble g.key q.key then g :: q :: qs
    else q :: insP m g qs

theorem insP_ok (m : Nat) (inp : Nat → Nat → Nat) (s : St) (g : Pr) : ∀ l,
    Cg m (sumP inp s (insP m g l)) (g.ev inp s + sumP inp s l)
  | [] => Cg.refl _ _
  | q :: qs => by
    rw [insP]
    split
    · rename_i h
      simp only [Bool.and_eq_true, Nat.beq_eq] at h
      simp only [sumP, Pr.ev, h.1, h.2]
      rw [← Nat.add_assoc]
      refine Cg.add ((((Cg.mod m _).mul _).add ((Cg.mod m _).mul _)).trans (Cg.of_eq ?_)) (Cg.refl _ _)
      rw [Nat.add_mul, Nat.add_mul]
      omega_using []
    · split
      · exact Cg.refl _ _
      · simp only [sumP]
        exact ((Cg.refl m _).add (insP_ok m inp s g qs)).trans (Cg.of_eq (by omega_using []))

/-- The products, sorted. -/
def sortP (m : Nat) : List Pr → List Pr
  | [] => []
  | q :: qs => insP m q (sortP m qs)

theorem sortP_ok (m : Nat) (inp : Nat → Nat → Nat) (s : St) : ∀ l, Cg m (sumP inp s (sortP m l)) (sumP inp s l)
  | [] => Cg.refl _ _
  | q :: qs => (insP_ok m inp s q _).trans ((Cg.refl _ _).add (sortP_ok m inp s qs))

/-- The same products. -/
def eqP : List Pr → List Pr → Bool
  | [], [] => true
  | q :: qs, r :: rs => Nat.beq q.a r.a && Nat.beq q.b r.b && Nat.beq q.cl r.cl && Nat.beq q.ch r.ch && eqP qs rs
  | _, _ => false

theorem eqP_eq : ∀ {l r : List Pr}, eqP l r = true → l = r
  | [], [], _ => rfl
  | q :: qs, r :: rs, h => by
    simp only [eqP, Bool.and_eq_true, Nat.beq_eq] at h
    rw [eqP_eq h.2]
    cases q; cases r
    simp only at h
    simp only [h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2]
  | [], _ :: _, h => absurd h (by simp [eqP])
  | _ :: _, [], h => absurd h (by simp [eqP])

theorem sumP_append (inp : Nat → Nat → Nat) (s : St) : ∀ l r, sumP inp s (l ++ r) = sumP inp s l + sumP inp s r
  | [], r => (Nat.zero_add _).symm
  | q :: qs, r => by rw [List.cons_append, sumP, sumP, sumP_append inp s qs r, Nat.add_assoc]

theorem sumL_append (inp : Nat → Nat → Nat) (s : St) : ∀ l r, sumL inp s (l ++ r) = sumL inp s l + sumL inp s r
  | [], r => (Nat.zero_add _).symm
  | q :: qs, r => by rw [List.cons_append, sumL, sumL, sumL_append inp s qs r, Nat.add_assoc]

/-! ## The check -/

/-- Any registers. -/
def anyB : Bd := ⟨List.replicate 29 0, List.replicate 29 (2 ^ 64 - 1), 1⟩

theorem anyB_wf : anyB.wf = true := rfl

theorem getD_replicate (n v : Nat) (i : Nat) : (List.replicate n v).getD i v = v := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem anyB_ok {s : St} (h : Ok s) : anyB.Ok s := by
  refine ⟨fun r => ?_, fun r => ?_, h.c⟩
  · show (List.replicate 29 0).getD (rn r) 0 ≤ _
    rw [getD_replicate]; exact Nat.zero_le _
  · show _ ≤ (List.replicate 29 (2 ^ 64 - 1)).getD (rn r) (2 ^ 64 - 1)
    rw [getD_replicate]; have := h.g r; omega_using [this]

/-- The words of `out` from word `sh` of a number on, modulo `m`. -/
def outFn (m sh : Nat) (out : List Reg) (n : Nat) : Fn :=
  ⟨0, 0, (List.range n).map fun k => full (out.getD k .x8) (pw (k + sh) % m), []⟩

theorem outFn_ev {m sh : Nat} {out : List Reg} {inp : Nat → Nat → Nat} {s : St} (hs : Ok s) (n : Nat) :
    Cg m ((outFn m sh out n).ev inp s) (pw sh * num (fun k => s.g (out.getD k .x8)) n) := by
  have h : ∀ n, Cg m (sumL inp s ((List.range n).map fun k => full (out.getD k .x8) (pw (k + sh) % m)))
      (pw sh * num (fun k => s.g (out.getD k .x8)) n) := by
    intro n
    induction n with
    | zero => exact Cg.refl _ _
    | succ n ih =>
      rw [List.range_succ, List.map_append, sumL_append, num_succ, Nat.mul_add]
      refine ih.add ?_
      rw [List.map_cons, List.map_nil, sumL, sumL, Nat.add_zero, full_ev hs, ← Nat.mul_assoc, ← pw_add, Nat.add_comm sh n]
      exact (Cg.mod m _).mul _
  simp only [Fn.ev, outFn, sumP, Nat.zero_mul, Nat.zero_add, Nat.add_zero]
  exact h n

/-- The words of the operands: below `2^64`, the ninth below `2^9`. -/
def inB (_ i : Nat) : Nat := if Nat.ble i 7 then 2 ^ 64 - 1 else 511

/-- The sequence's output is the sum of the products. -/
def chk (os : List Op) (out : List Reg) (E : List Pr) : Bool :=
  match backs prime inB os anyB (outFn prime 9 out 9) with
  | none => false
  | some F => Nat.beq F.k 0 && Nat.beq F.f 0 && F.l.isEmpty && eqP (sortP prime F.p) E

/-- The operands' words are below their bounds. -/
structure InB (inp : Nat → Nat → Nat) : Prop where
  w : ∀ k i, inp k i < 2 ^ 64
  b : ∀ k i, inp k i ≤ inB k i

theorem chk_ok {os : List Op} {out : List Reg} {E : List Pr} (h : chk os out E = true) {inp : Nat → Nat → Nat}
    (hi : InB inp) {s : St} (hs : Ok s) :
    Cg prime (pw 9 * num (fun k => (run inp os s).g (out.getD k .x8)) 9) (sumP inp s E) := by
  unfold chk at h
  split at h
  · exact absurd h (by simp)
  · rename_i F hF
    simp only [Bool.and_eq_true, Nat.beq_eq, List.isEmpty_iff] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    have hb := backs_ok prime_pos hi.w hi.b os anyB_wf hs (anyB_ok hs) hF
    have hO := (fwds_ok hi.w hi.b os anyB_wf hs (anyB_ok hs)).2
    refine (outFn_ev hO 9).symm.trans (hb.trans ?_)
    simp only [Fn.ev, h1, h2, h3, sumL, Nat.zero_mul, Nat.zero_add]
    rw [← eqP_eq h4]
    exact (sortP_ok prime inp s F.p).symm

/-- The output's top word is at most 512. -/
def chkTop (os : List Op) (out : List Reg) : Bool := Nat.ble ((fwds inB os anyB).u (out.getD 8 .x8)) 512

theorem chkTop_ok {os : List Op} {out : List Reg} (h : chkTop os out = true) {inp : Nat → Nat → Nat} (hi : InB inp)
    {s : St} (hs : Ok s) : (run inp os s).g (out.getD 8 .x8) ≤ 512 :=
  Nat.le_trans ((fwds_ok hi.w hi.b os anyB_wf hs (anyB_ok hs)).1.ub _) (Nat.le_of_ble_eq_true h)

/-- The output is zero if the operands within `ib` are. -/
def chkZero (ib : Nat → Nat → Nat) (os : List Op) (out : List Reg) : Bool :=
  let B := fwds ib os anyB
  (List.range 9).all fun k => Nat.beq (B.u (out.getD k .x8)) 0

theorem chkZero_ok {ib : Nat → Nat → Nat} {os : List Op} {out : List Reg} (h : chkZero ib os out = true)
    {inp : Nat → Nat → Nat} (hw : ∀ k i, inp k i < 2 ^ 64) (hi : ∀ k i, inp k i ≤ ib k i) {s : St} (hs : Ok s) :
    num (fun k => (run inp os s).g (out.getD k .x8)) 9 = 0 := by
  have hB := (fwds_ok hw hi os anyB_wf hs (anyB_ok hs)).1
  have hz : ∀ k < 9, (run inp os s).g (out.getD k .x8) = 0 := fun k hk => by
    have h1 := List.all_eq_true.mp h k (List.mem_range.mpr hk)
    exact Nat.eq_zero_of_le_zero (Nat.le_trans (hB.ub _) (Nat.le_of_eq (Nat.eq_of_beq_eq_true h1)))
  rw [num, sumTo_congr (g := fun _ => 0) fun k hk => by rw [hz k hk, Nat.mul_zero]]
  rfl

/-! ## The check, for the kernel

`backs` run so that the kernel evaluates each functional, and each state's
bounds, before the next: the coefficients by `seqN`
(`Framework/Bitslice/Machine.lean`), everything else to numerals; and what it
runs at every field and product by recursors and the comparisons of numbers
that the kernel evaluates natively. -/

section
open VG.Bitslice.Machine (seqN seqN_eq bool_rec_beq bool_rec_ble)

/-- `c n`, with `n` a numeral. -/
noncomputable def numN {β : Type} (n : Nat) (c : Nat → β) : β :=
  Nat.rec (motive := fun _ => β) (c n) (fun n _ => c n) (Nat.succ n)

theorem numN_eq {β : Type} (n : Nat) (c : Nat → β) : numN n c = c n := rfl

noncomputable def segsN (l : List Seg) (c : List Seg → Bool) : Bool :=
  List.rec (motive := fun _ => (List Seg → Bool) → Bool) (fun c => c [])
    (fun q _ ih c => Seg.rec (fun l lo hi w => numN l fun l => numN lo fun lo => numN hi fun hi => seqN w fun w =>
      ih fun t => c (⟨l, lo, hi, w⟩ :: t)) q) l c

theorem segsN_eq (l : List Seg) (c : List Seg → Bool) : segsN l c = c l := by
  induction l generalizing c with
  | nil => rfl
  | cons q l ih => exact (seqN_eq ..).trans (ih _)

/-- The products' list evaluated, but not its products' numbers, which are the terms they were. -/
noncomputable def prsN (l : List Pr) (c : List Pr → Bool) : Bool :=
  List.rec (motive := fun _ => (List Pr → Bool) → Bool) (fun c => c [])
    (fun q _ ih c => Pr.rec (fun a b cl ch => ih fun t => c (⟨a, b, cl, ch⟩ :: t)) q) l c

theorem prsN_eq (l : List Pr) (c : List Pr → Bool) : prsN l c = c l := by
  induction l generalizing c with
  | nil => rfl
  | cons q l ih => exact ih _

/-- The same, with the factors evaluated. -/
noncomputable def prsF (l : List Pr) (c : List Pr → Bool) : Bool :=
  List.rec (motive := fun _ => (List Pr → Bool) → Bool) (fun c => c [])
    (fun q _ ih c => Pr.rec (fun a b cl ch => numN a fun a => numN b fun b => ih fun t => c (⟨a, b, cl, ch⟩ :: t)) q)
    l c

theorem prsF_eq (l : List Pr) (c : List Pr → Bool) : prsF l c = c l := by
  induction l generalizing c with
  | nil => rfl
  | cons q l ih => exact ih _

/-- What an operation may do to the products: nothing, change coefficients, or rename factors. -/
inductive Chg
  | no
  | coef
  | all

def chg : Op → Chg
  | .ld .. | .lsl .. | .extr .. => .all
  | .mul .. | .umulh .. => .coef
  | _ => .no

/-- `c F`, with `F` evaluated. -/
noncomputable def fnN (p : Chg) (F : Fn) (c : Fn → Bool) : Bool :=
  Fn.rec (fun k f l q => seqN k fun k => seqN f fun f => segsN l fun l =>
    Chg.rec (c ⟨k, f, l, q⟩) (prsN q fun q => c ⟨k, f, l, q⟩) (prsF q fun q => c ⟨k, f, l, q⟩) p) F

theorem fnN_eq (p : Chg) (F : Fn) (c : Fn → Bool) : fnN p F c = c F := by
  show seqN _ _ = _
  rw [seqN_eq, seqN_eq, segsN_eq]
  cases p
  · rfl
  · exact prsN_eq _ _
  · exact prsF_eq _ _

/-- The places in a factor, a bit for each. -/
noncomputable def placeBits (e : Nat) : Nat :=
  Bool.rec
    (Bool.rec
      (Nat.lor (Nat.pow 2 (Nat.div (Nat.sub e 2048) 1024)) (Nat.pow 2 (Nat.mod (Nat.sub e 2048) 1024)))
      (Nat.pow 2 (Nat.sub e 1024)) (Nat.ble (Nat.succ e) 2048))
    (Nat.pow 2 e) (Nat.ble (Nat.succ e) 1024)

theorem testBit_placeBits (d e : Nat) : (placeBits e).testBit d = inE d e := by
  have h (a b : Nat) : (Nat.pow 2 a).testBit b = Nat.beq a b := by
    show (2 ^ a).testBit b = _
    rw [Nat.testBit_two_pow, Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]
  rw [placeBits, bool_rec_ble, bool_rec_ble, inE]
  show _ = if e.succ ≤ 1024 then _ else if e.succ ≤ 2048 then _ else _
  split
  · exact h _ _
  · split
    · exact h _ _
    · exact (Nat.testBit_or ..).trans (by rw [h, h]; rfl)

/-- The places in the products. The kernel evaluates it once for a list, and
for a list with one more product from that of the list without it. -/
noncomputable def placesP (l : List Pr) : Nat :=
  List.rec 0 (fun q _ ih => Nat.lor (Nat.lor (placeBits q.a) (placeBits q.b)) ih) l

/-- `noP`. -/
noncomputable def noPK (d : Nat) (l : List Pr) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight (placesP l) d) 1) 0

theorem noPK_eq (d : Nat) (l : List Pr) : noPK d l = noP d l := by
  have h : ∀ l, (placesP l).testBit d = !noP d l := fun l => by
    induction l with
    | nil => exact Nat.zero_testBit d
    | cons q l ih =>
      show ((placeBits q.a ||| placeBits q.b) ||| placesP l).testBit d = _
      rw [Nat.testBit_or, Nat.testBit_or, testBit_placeBits, testBit_placeBits, ih, noP]
      cases inE d q.a <;> cases inE d q.b <;> cases noP d l <;> rfl
  have e : noPK d l = !(placesP l).testBit d := by
    rw [Nat.testBit, noPK]
    show Nat.beq (placesP l >>> d &&& 1) 0 = _
    rw [Nat.and_comm]
    rw [bne, Bool.not_not, Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq]
  rw [e, h, Bool.not_not]

/-- `subE`. -/
noncomputable def subEK (d l e : Nat) : Nat :=
  Bool.rec
    (Bool.rec
      (Nat.add (Nat.add 2048 (Nat.mul 1024
          (Bool.rec (Nat.div (Nat.sub e 2048) 1024) l (Nat.beq (Nat.div (Nat.sub e 2048) 1024) d))))
        (Bool.rec (Nat.mod (Nat.sub e 2048) 1024) l (Nat.beq (Nat.mod (Nat.sub e 2048) 1024) d)))
      (Bool.rec e (Nat.add 1024 l) (Nat.beq (Nat.sub e 1024) d)) (Nat.ble (Nat.succ e) 2048))
    (Bool.rec e l (Nat.beq e d)) (Nat.ble (Nat.succ e) 1024)

theorem subEK_eq (d l e : Nat) : subEK d l e = subE d l e := by
  simp only [subEK, bool_rec_ble, bool_rec_beq]; rfl

/-- `subP`. -/
noncomputable def subPK (d l : Nat) (p : List Pr) : List Pr :=
  List.rec [] (fun q _ ih => ⟨subEK d l q.a, subEK d l q.b, q.cl, q.ch⟩ :: ih) p

theorem subPK_eq (d l : Nat) (p : List Pr) : subPK d l p = subP d l p := by
  induction p with
  | nil => rfl
  | cons q p ih =>
    show (⟨subEK d l q.a, subEK d l q.b, q.cl, q.ch⟩ : Pr) :: subPK d l p = _
    rw [ih, subEK_eq, subEK_eq]; rfl

/-- `subL`. -/
noncomputable def subLK (d l : Nat) (p : List Seg) : List Seg :=
  List.rec [] (fun q _ ih => ⟨Bool.rec q.l l (Nat.beq q.l d), q.lo, q.hi, q.w⟩ :: ih) p

theorem subLK_eq (d l : Nat) (p : List Seg) : subLK d l p = subL d l p := by
  induction p with
  | nil => rfl
  | cons q p ih =>
    show (⟨Bool.rec q.l l (Nat.beq q.l d), q.lo, q.hi, q.w⟩ : Seg) :: subLK d l p = _
    rw [ih, subL]
    cases Nat.beq q.l d <;> rfl

/-- `putSeg`. -/
noncomputable def putSegK (m : Nat) (g : Seg) (l : List Seg) : List Seg :=
  List.rec [⟨g.l, g.lo, g.hi, Nat.mod g.w m⟩]
    (fun q qs ih => Bool.rec (q :: ih)
      (Bool.rec (q :: ih)
        (Bool.rec (q :: ih) (⟨q.l, q.lo, q.hi, Nat.mod (Nat.add q.w g.w) m⟩ :: qs) (Nat.beq q.hi g.hi))
        (Nat.beq q.lo g.lo))
      (Nat.beq q.l g.l)) l

theorem putSegK_eq (m : Nat) (g : Seg) (l : List Seg) : putSegK m g l = putSeg m g l := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    have e : putSegK m g (q :: l) = Bool.rec (motive := fun _ => List Seg) (q :: putSegK m g l)
      (Bool.rec (motive := fun _ => List Seg) (q :: putSegK m g l)
        (Bool.rec (motive := fun _ => List Seg) (q :: putSegK m g l)
          (⟨q.l, q.lo, q.hi, (q.w + g.w) % m⟩ :: l) (Nat.beq q.hi g.hi))
        (Nat.beq q.lo g.lo)) (Nat.beq q.l g.l) := rfl
    rw [e, ih, putSeg]
    cases Nat.beq q.l g.l <;> cases Nat.beq q.lo g.lo <;> cases Nat.beq q.hi g.hi <;> rfl

/-- `addSeg`. -/
noncomputable def addSegK (m : Nat) (g : Seg) (l : List Seg) : List Seg :=
  Bool.rec (putSegK m g l) l (Nat.beq (Nat.mod g.w m) 0)

theorem addSegK_eq (m : Nat) (g : Seg) (l : List Seg) : addSegK m g l = addSeg m g l := by
  rw [addSegK, putSegK_eq, addSeg]
  exact (bool_rec_beq ..).trans (by simp only [Nat.beq_eq]; rfl)

/-- `part`, each half. -/
noncomputable def partK (d : Nat) (l : List Seg) : List Seg × List Seg :=
  ⟨List.rec [] (fun q _ ih => Bool.rec ih (q :: ih) (Nat.beq q.l d)) l,
    List.rec [] (fun q _ ih => Bool.rec (q :: ih) ih (Nat.beq q.l d)) l⟩

theorem partK_eq (d : Nat) (l : List Seg) : partK d l = part d l := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    have e : partK d (q :: l) = ⟨Bool.rec (motive := fun _ => List Seg) (partK d l).1 (q :: (partK d l).1) (Nat.beq q.l d),
      Bool.rec (motive := fun _ => List Seg) (q :: (partK d l).2) (partK d l).2 (Nat.beq q.l d)⟩ := rfl
    rw [e, ih, part]
    cases Nat.beq q.l d <;> rfl

/-- `take`. -/
noncomputable def takeK (m d : Nat) (l : List Seg) : Option (Nat × List Seg) :=
  let r := partK d l
  match r.1 with
  | [] => some (0, r.2)
  | es@(_ :: _) =>
    match pick 0 es with
    | none => none
    | some (q, _) => if tile m q.w 8 0 es then some (q.w, r.2) else none

theorem takeK_eq (m d : Nat) (l : List Seg) : takeK m d l = take m d l := by
  rw [takeK, partK_eq]; rfl

/-- `putPr`. -/
noncomputable def addPrK (m : Nat) (g : Pr) (l : List Pr) : List Pr :=
  List.rec [⟨g.a, g.b, Nat.mod g.cl m, Nat.mod g.ch m⟩]
    (fun q qs ih => Bool.rec (q :: ih)
      (Bool.rec (q :: ih) (⟨q.a, q.b, Nat.mod (Nat.add q.cl g.cl) m, Nat.mod (Nat.add q.ch g.ch) m⟩ :: qs)
        (Nat.beq q.b g.b)) (Nat.beq q.a g.a)) l

theorem addPrK_eq (m : Nat) (g : Pr) (l : List Pr) : addPrK m g l = addPr m g l := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    have e : addPrK m g (q :: l) = Bool.rec (motive := fun _ => List Pr) (q :: addPrK m g l)
      (Bool.rec (motive := fun _ => List Pr) (q :: addPrK m g l)
        (⟨q.a, q.b, (q.cl + g.cl) % m, (q.ch + g.ch) % m⟩ :: l) (Nat.beq q.b g.b)) (Nat.beq q.a g.a) := rfl
    rw [e, ih, addPr]
    cases Nat.beq q.a g.a <;> cases Nat.beq q.b g.b <;> rfl

noncomputable def hasPrK (g : Pr) (l : List Pr) : Bool :=
  List.rec false (fun q _ ih => Bool.rec ih (Bool.rec ih true (Nat.beq q.b g.b)) (Nat.beq q.a g.a)) l

theorem hasPrK_eq (g : Pr) (l : List Pr) : hasPrK g l = hasPr g l := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    have e : hasPrK g (q :: l) = Bool.rec (motive := fun _ => Bool) (hasPrK g l)
      (Bool.rec (motive := fun _ => Bool) (hasPrK g l) true (Nat.beq q.b g.b)) (Nat.beq q.a g.a) := rfl
    rw [e, ih, hasPr]
    cases Nat.beq q.a g.a <;> cases Nat.beq q.b g.b <;> rfl

noncomputable def putPrK (m : Nat) (g : Pr) (l : List Pr) : List Pr :=
  Bool.rec (⟨g.a, g.b, Nat.mod g.cl m, Nat.mod g.ch m⟩ :: l) (addPrK m g l) (hasPrK g l)

theorem putPrK_eq (m : Nat) (g : Pr) (l : List Pr) : putPrK m g l = putPr m g l := by
  rw [putPrK, hasPrK_eq, addPrK_eq, putPr]
  cases hasPr g l <;> rfl

/-- `insP`. -/
noncomputable def insPK (m : Nat) (g : Pr) (l : List Pr) : List Pr :=
  List.rec [g]
    (fun q qs ih => Bool.rec (Bool.rec (q :: ih) (g :: q :: qs) (Nat.ble g.key q.key))
      (Bool.rec (Bool.rec (q :: ih) (g :: q :: qs) (Nat.ble g.key q.key))
        (⟨q.a, q.b, Nat.mod (Nat.add q.cl g.cl) m, Nat.mod (Nat.add q.ch g.ch) m⟩ :: qs)
        (Nat.beq q.b g.b)) (Nat.beq q.a g.a)) l

theorem insPK_eq (m : Nat) (g : Pr) (l : List Pr) : insPK m g l = insP m g l := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    have e : insPK m g (q :: l) = Bool.rec (motive := fun _ => List Pr)
      (Bool.rec (motive := fun _ => List Pr) (q :: insPK m g l) (g :: q :: l) (Nat.ble g.key q.key))
      (Bool.rec (motive := fun _ => List Pr)
        (Bool.rec (motive := fun _ => List Pr) (q :: insPK m g l) (g :: q :: l) (Nat.ble g.key q.key))
        (⟨q.a, q.b, (q.cl + g.cl) % m, (q.ch + g.ch) % m⟩ :: l) (Nat.beq q.b g.b)) (Nat.beq q.a g.a) := rfl
    rw [e, ih, insP]
    cases Nat.beq q.a g.a <;> cases Nat.beq q.b g.b <;> cases Nat.ble g.key q.key <;> rfl

/-- `sortP`, each list evaluated before the next. -/
noncomputable def sortPK (m : Nat) (l : List Pr) (c : List Pr → Bool) : Bool :=
  List.rec (motive := fun _ => (List Pr → Bool) → Bool) (fun c => c [])
    (fun q _ ih c => ih fun t => prsN (insPK m q t) c) l c

theorem sortPK_eq (m : Nat) (l : List Pr) (c : List Pr → Bool) : sortPK m l c = c (sortP m l) := by
  induction l generalizing c with
  | nil => rfl
  | cons q l ih =>
    refine (ih _).trans ?_
    rw [prsN_eq, insPK_eq]; rfl

/-- `back`. -/
noncomputable def backK (m : Nat) (B : Bd) : Op → Fn → Option Fn
  | .ld k i d, F =>
    if Nat.ble i 15 && Nat.ble k 3 then some ⟨F.k, F.f, subLK (rn d) (inpLoc k i) F.l, subPK (rn d) (inpLoc k i) F.p⟩
    else none
  | .lsl d n k, F =>
    match pullShl m (rn d) (rn n) k F.l, (if Nat.beq k 1 then renP (rn d) (1024 + rn n) F.p else if noPK (rn d) F.p then some F.p else none) with
    | some l, some p => if Nat.ble k 63 then some ⟨F.k, F.f, l, p⟩ else none
    | _, _ => none
  | .extr d n q k, F =>
    match pullExtr m (rn d) (rn n) (rn q) k F.l, (if Nat.beq k 63 then renP (rn d) (2048 + 1024 * rn n + rn q) F.p else if noPK (rn d) F.p then some F.p else none) with
    | some l, some p => if Nat.ble k 63 then some ⟨F.k, F.f, l, p⟩ else none
    | _, _ => none
  | o, F =>
    if noPK (rn o.dst) F.p then
      match takeK m (rn o.dst) F.l with
      | none => none
      | some (w, l) =>
        let both (f : Nat) (n q : Reg) (k : Nat) : Option Fn := some ⟨k, f, addSegK m (full n w) (addSegK m (full q w) l), F.p⟩
        let diff (f : Nat) (n q : Reg) (k : Nat) : Option Fn :=
          some ⟨k, f, addSegK m (full n w) (addSegK m (full q (m - w % m)) l), F.p⟩
        match o with
        | .mul _ n q => some ⟨F.k, F.f, l, putPrK m ⟨rn n, rn q, w, 0⟩ F.p⟩
        | .umulh _ n q => some ⟨F.k, F.f, l, putPrK m ⟨rn n, rn q, 0, w⟩ F.p⟩
        | .add _ n q => if Nat.ble (B.u n + B.u q) (2 ^ 64 - 1) then both F.f n q F.k else none
        | .adc _ n q => if Nat.ble (B.u n + B.u q + B.c) (2 ^ 64 - 1) then both ((F.f + w) % m) n q F.k else none
        | .adds _ n q =>
          if Nat.beq (F.f % m) (w * 2 ^ 64 % m) || Nat.ble (B.u n + B.u q) (2 ^ 64 - 1) then both 0 n q F.k else none
        | .adcs _ n q =>
          if Nat.beq (F.f % m) (w * 2 ^ 64 % m) || Nat.ble (B.u n + B.u q + B.c) (2 ^ 64 - 1) then both w n q F.k else none
        | .subs _ n q =>
          if Nat.beq (rn n) (rn q) then some ⟨(F.k + F.f) % m, 0, l, F.p⟩
          else if Nat.beq (F.f % m) (w * 2 ^ 64 % m) then diff 0 n q ((F.k + w * 2 ^ 64) % m) else none
        | .sbcs _ n q => if Nat.beq (F.f % m) (w * 2 ^ 64 % m) then diff w n q ((F.k + w * (2 ^ 64 - 1)) % m) else none
        | .lsr _ n k => if Nat.ble k 63 then some ⟨F.k, F.f, addSegK m ⟨rn n, k, 64, w⟩ l, F.p⟩ else none
        | .movz _ v => some ⟨(F.k + w * (v % 2 ^ 16)) % m, F.f, l, F.p⟩
        | .low _ n q k =>
          if Nat.beq (B.lb.getD (rn q) 0) (2 ^ k - 1) && Nat.beq (B.u q) (2 ^ k - 1) && Nat.ble k 64 then
            some ⟨F.k, F.f, addSegK m ⟨rn n, 0, k, w⟩ l, F.p⟩
          else none
        | _ => none
    else none

theorem backK_eq (m : Nat) (B : Bd) (o : Op) (F : Fn) : backK m B o F = back m B o F := by
  cases o <;> simp only [backK, back, subLK_eq, subPK_eq, noPK_eq, takeK_eq, addSegK_eq, putPrK_eq] <;> rfl

/-- `backs`, then `c`. -/
noncomputable def backsK (m : Nat) (ib : Nat → Nat → Nat) (os : List Op) : Bd → Fn → (Fn → Bool) → Bool :=
  List.rec (motive := fun _ => Bd → Fn → (Fn → Bool) → Bool) (fun _ F c => c F)
    (fun o _ ih B F c => ih (fwd ib o B) F fun G =>
      Option.rec false (fun G => fnN (chg o) G c) (backK m B o G)) os

theorem backsK_eq {m : Nat} {ib : Nat → Nat → Nat} {os : List Op} {B : Bd} {F : Fn} {c : Fn → Bool} :
    backsK m ib os B F c = match backs m ib os B F with | none => false | some G => c G := by
  induction os generalizing B F c with
  | nil => rfl
  | cons o os ih =>
    refine ih.trans ?_
    rw [backs]
    cases backs m ib os (fwd ib o B) F with
    | none => rfl
    | some G =>
      show Option.rec (motive := fun _ => Bool) false (fun G => fnN (chg o) G c) (backK m B o G) = _
      rw [backK_eq]
      show _ = match back m B o G with | none => false | some G => c G
      cases back m B o G with
      | none => rfl
      | some G => exact fnN_eq ..

/-- `chk`. -/
noncomputable def chkK (os : List Op) (out : List Reg) (E : List Pr) : Bool :=
  backsK prime inB os anyB (outFn prime 9 out 9) fun F =>
    Nat.beq F.k 0 && Nat.beq F.f 0 && F.l.isEmpty && sortPK prime F.p fun p => eqP p E

theorem chkK_eq (os : List Op) (out : List Reg) (E : List Pr) : chkK os out E = chk os out E := by
  rw [chkK, backsK_eq, chk]
  cases backs prime inB os anyB (outFn prime 9 out 9) with
  | none => rfl
  | some F => exact congrArg (fun b => Nat.beq F.k 0 && Nat.beq F.f 0 && F.l.isEmpty && b) (sortPK_eq ..)

end

/-! ## The product -/

/-- A product of two places at word `e`. -/
def pr (a b e : Nat) : Pr := ⟨a, b, pw e % prime, pw (e + 1) % prime⟩

theorem pr_ev (a b e : Nat) (inp : Nat → Nat → Nat) (s : St) :
    Cg prime ((pr a b e).ev inp s) (pw e * (ev inp s a * ev inp s b)) := by
  unfold Pr.ev pr
  refine (((Cg.mod prime _).mul _).add ((Cg.mod prime _).mul _)).trans (Cg.of_eq ?_)
  dsimp only
  generalize ev inp s a * ev inp s b = x
  rw [pw_succ, Nat.mul_comm (2 ^ 64), Nat.mul_assoc, ← Nat.mul_add, Nat.add_comm, Nat.div_add_mod]

/-- A product below `2^64` at word `e`. -/
def prLow (a b e : Nat) : Pr := ⟨a, b, pw e % prime, 0⟩

theorem prLow_ev (a b e : Nat) (inp : Nat → Nat → Nat) (s : St) (h : ev inp s a * ev inp s b < 2 ^ 64) :
    Cg prime ((prLow a b e).ev inp s) (pw e * (ev inp s a * ev inp s b)) := by
  unfold Pr.ev prLow
  dsimp only
  rw [Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt h]
  exact (Cg.mod prime _).mul _

theorem sumP_map_range (f : Nat → Pr) (g : Nat → Nat) (inp : Nat → Nat → Nat) (s : St) :
    ∀ n, (∀ i < n, Cg prime ((f i).ev inp s) (g i)) → Cg prime (sumP inp s ((List.range n).map f)) (sumTo g n)
  | 0, _ => Cg.refl _ _
  | n + 1, h => by
    rw [List.range_succ, List.map_append, sumP_append, sumTo]
    refine (sumP_map_range f g inp s n fun i hi => h i (Nat.lt_succ_of_lt hi)).add ?_
    simp only [List.map_cons, List.map_nil, sumP, Nat.add_zero]
    exact h n (Nat.lt_succ_self n)

theorem sumP_flatMap_range (f : Nat → List Pr) (g : Nat → Nat) (inp : Nat → Nat → Nat) (s : St) :
    ∀ n, (∀ i < n, Cg prime (sumP inp s (f i)) (g i)) → Cg prime (sumP inp s ((List.range n).flatMap f)) (sumTo g n)
  | 0, _ => Cg.refl _ _
  | n + 1, h => by
    rw [List.range_succ, List.flatMap_append, sumP_append, sumTo]
    refine (sumP_flatMap_range f g inp s n fun i hi => h i (Nat.lt_succ_of_lt hi)).add ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact h n (Nat.lt_succ_self n)

/-- The products of the words. -/
def mulE : List Pr :=
  ((List.range 8).flatMap fun i => (List.range 9).map fun j => pr (inpLoc 0 i) (inpLoc 1 j) (i + j)) ++
    (((List.range 8).map fun j => pr (inpLoc 0 8) (inpLoc 1 j) (8 + j)) ++ [prLow (inpLoc 0 8) (inpLoc 1 8) 16])

theorem ev_inp (inp : Nat → Nat → Nat) (s : St) {k i : Nat} (hk : k < 4) (hi : i < 16) :
    ev inp s (inpLoc k i) = inp k i := by
  rw [ev, ite_eq_left (by unfold inpLoc; omega_using [hk, hi]), lv_inp inp s hi]

theorem top_lt {inp : Nat → Nat → Nat} (hi : InB inp) (k q : Nat) : inp k 8 * inp q 8 < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul (hi.b k 8) (hi.b q 8)) (by show 511 * 511 < 2 ^ 64; decide)

theorem mulE_ev {inp : Nat → Nat → Nat} (hi : InB inp) (s : St) :
    Cg prime (sumP inp s mulE) (num (inp 0) 9 * num (inp 1) 9) := by
  have one : ∀ i < 9, ∀ j < 9, pw (i + j) * (ev inp s (inpLoc 0 i) * ev inp s (inpLoc 1 j)) =
      (pw i * inp 0 i) * (pw j * inp 1 j) := fun i hi j hj => by
    rw [ev_inp inp s (by decide) (by omega_using [hi]), ev_inp inp s (by decide) (by omega_using [hj]), pw_add]
    ac_rfl
  have rows : ∀ i < 9, ∀ n ≤ 9, Cg prime (sumP inp s ((List.range n).map fun j => pr (inpLoc 0 i) (inpLoc 1 j) (i + j)))
      ((pw i * inp 0 i) * num (inp 1) n) := fun i hi n hn =>
    (sumP_map_range _ (fun j => (pw i * inp 0 i) * (pw j * inp 1 j)) inp s n fun j hj =>
      (pr_ev _ _ _ inp s).trans (Cg.of_eq (one i hi j (by omega_using [hj, hn])))).trans (Cg.of_eq (sumTo_mul _ _ n))
  have last : Cg prime (sumP inp s (((List.range 8).map fun j => pr (inpLoc 0 8) (inpLoc 1 j) (8 + j)) ++
      [prLow (inpLoc 0 8) (inpLoc 1 8) 16])) ((pw 8 * inp 0 8) * num (inp 1) 9) := by
    rw [sumP_append, num_succ _ 8, Nat.mul_add]
    refine (rows 8 (by decide) 8 (by decide)).add ?_
    rw [sumP, sumP, Nat.add_zero]
    refine (prLow_ev _ _ _ inp s ?_).trans (Cg.of_eq (one 8 (by decide) 8 (by decide)))
    rw [ev_inp inp s (by decide) (by decide), ev_inp inp s (by decide) (by decide)]
    exact top_lt hi 0 1
  rw [mulE, sumP_append]
  refine ((sumP_flatMap_range _ (fun i => (pw i * inp 0 i) * num (inp 1) 9) inp s 8 fun i h =>
    rows i (by omega_using [h]) 9 (Nat.le_refl _)).add last).trans (Cg.of_eq ?_)
  rw [sumTo_congr (g := fun i => num (inp 1) 9 * (pw i * inp 0 i)) fun i _ => Nat.mul_comm _ _, sumTo_mul,
    Nat.mul_comm (pw 8 * inp 0 8), ← Nat.mul_add, Nat.mul_comm]
  rfl

/-- The product's number is `[a] [b] 2^-576` modulo `p`. -/
theorem mul_kernel {inp : Nat → Nat → Nat} (hi : InB inp) {s : St} (hs : Ok s) :
    Cg prime (pw 9 * num (fun k => (run inp mulOps s).g (mulOut.getD k .x8)) 9)
      (num (inp 0) 9 * num (inp 1) 9) :=
  (chk_ok ((chkK_eq ..).symm.trans (by decide +kernel)) hi hs).trans (mulE_ev hi s)

theorem mul_top {inp : Nat → Nat → Nat} (hi : InB inp) {s : St} (hs : Ok s) :
    (run inp mulOps s).g (mulOut.getD 8 .x8) ≤ 512 := chkTop_ok (by decide +kernel) hi hs

/-- Bounds with operand `k` zero. -/
def zeroB (k q i : Nat) : Nat := if Nat.beq q k then 0 else inB q i

theorem zeroB_le {inp : Nat → Nat → Nat} (hi : InB inp) {k : Nat} (hz : ∀ i, inp k i = 0) (q i : Nat) :
    inp q i ≤ zeroB k q i := by
  unfold zeroB
  cases hb : Nat.beq q k with
  | true => rw [Nat.eq_of_beq_eq_true hb, hz]; exact Nat.zero_le _
  | false => exact hi.b q i

theorem mul_zero {inp : Nat → Nat → Nat} (hi : InB inp) {s : St} (hs : Ok s)
    (hz : (∀ i, inp 0 i = 0) ∨ ∀ i, inp 1 i = 0) :
    num (fun k => (run inp mulOps s).g (mulOut.getD k .x8)) 9 = 0 := by
  rcases hz with hz | hz
  · exact chkZero_ok (ib := zeroB 0) (by decide +kernel) hi.w (zeroB_le hi hz) hs
  · exact chkZero_ok (ib := zeroB 1) (by decide +kernel) hi.w (zeroB_le hi hz) hs

/-! ## The square -/

/-- The products of row `i` of the square. -/
def sqrRow (i : Nat) : List Pr :=
  pr (inpLoc 0 i) (inpLoc 0 i) (2 * i) :: pr (inpLoc 0 i) (1024 + inpLoc 0 (i + 1)) (2 * i + 1) ::
    (List.range (7 - i)).map fun j =>
      pr (inpLoc 0 i) (2048 + 1024 * inpLoc 0 (i + 2 + j) + inpLoc 0 (i + 1 + j)) (2 * i + 2 + j)

/-- The products of the square. -/
def sqrE : List Pr := ((List.range 8).flatMap sqrRow) ++ [prLow (inpLoc 0 8) (inpLoc 0 8) 16]

theorem ev_dbl (inp : Nat → Nat → Nat) (s : St) {i : Nat} (hi : i < 16) :
    ev inp s (1024 + inpLoc 0 i) = inp 0 i * 2 % 2 ^ 64 := by
  have : inpLoc 0 i < 1024 := by unfold inpLoc; omega_using [hi]
  rw [ev, ite_eq_right (by omega_using []), ite_eq_left (by omega_using [this]), Nat.add_sub_cancel_left, lv_inp inp s hi]

theorem ev_ext (inp : Nat → Nat → Nat) (s : St) {i j : Nat} (hi : i < 16) (hj : j < 16) :
    ev inp s (2048 + 1024 * inpLoc 0 i + inpLoc 0 j) = (inp 0 i * 2 ^ 64 + inp 0 j) / 2 ^ 63 % 2 ^ 64 := by
  have h1 : inpLoc 0 j < 1024 := by unfold inpLoc; omega_using [hj]
  have e1 : (2048 + 1024 * inpLoc 0 i + inpLoc 0 j - 2048) / 1024 = inpLoc 0 i := by omega_using [h1]
  have e2 : (2048 + 1024 * inpLoc 0 i + inpLoc 0 j - 2048) % 1024 = inpLoc 0 j := by omega_using [h1]
  rw [ev, ite_eq_right (by omega_using []), ite_eq_right (by omega_using []), e1, e2, lv_inp inp s hi, lv_inp inp s hj]

/-- Word of `2 [a]` above `a_i`: twice `a_(i+1)`, then words of `2 [a]`. -/
def dw (a : Nat → Nat) (i j : Nat) : Nat :=
  if j = 0 then a (i + 1) * 2 % 2 ^ 64 else (a (i + 1 + j) * 2 ^ 64 + a (i + j)) / 2 ^ 63 % 2 ^ 64

/-- `n` words of `2 [a]` above `a_i`, and what they carry. -/
theorem dw_sum (a : Nat → Nat) (ha : ∀ i, a i < 2 ^ 64) (i : Nat) : ∀ n,
    num (dw a i) (n + 1) + pw (n + 1) * (a (i + 1 + n) / 2 ^ 63) = 2 * num (fun j => a (i + 1 + j)) (n + 1)
  | 0 => by
    have h := ha (i + 1)
    simp only [num, sumTo, dw, ite_true, pw_succ, pw_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.mul_one]
    omega_using [h]
  | n + 1 => by
    have ih := dw_sum a ha i n
    rw [num_succ _ (n + 1), num_succ (fun j => a (i + 1 + j)) (n + 1), Nat.mul_add, ← ih, pw_succ (n + 1)]
    have h1 := ha (i + 1 + n)
    have h2 := ha (i + 1 + (n + 1))
    have e : dw a i (n + 1) + 2 ^ 64 * (a (i + 1 + (n + 1)) / 2 ^ 63) = a (i + 1 + n) / 2 ^ 63 + 2 * a (i + 1 + (n + 1)) := by
      rw [dw, ite_eq_right (by omega_using []), show i + (n + 1) = i + 1 + n by omega_using []]
      omega_using [h1, h2]
    generalize pw (n + 1) = P
    have e3 : P * dw a i (n + 1) + P * (2 ^ 64 * (a (i + 1 + (n + 1)) / 2 ^ 63)) =
      P * (a (i + 1 + n) / 2 ^ 63) + P * (2 * a (i + 1 + (n + 1))) := by rw [← Nat.mul_add, e, Nat.mul_add]
    have e4 : 2 * (P * a (i + 1 + (n + 1))) = P * (2 * a (i + 1 + (n + 1))) := Nat.mul_left_comm ..
    have e5 : 2 ^ 64 * P * (a (i + 1 + (n + 1)) / 2 ^ 63) = P * (2 ^ 64 * (a (i + 1 + (n + 1)) / 2 ^ 63)) := by ac_rfl
    rw [e4, e5]
    omega_using [e3]

private theorem mul4 (a b c d : Nat) : a * b * (c * d) = a * c * (b * d) := by ac_rfl

private theorem mul4' (a c : Nat) : a * a * (c * c) = a * c * (a * c) := by ac_rfl

/-- Row `i` of the square, as its words. -/
theorem sqrRow_words {inp : Nat → Nat → Nat} (s : St) {i : Nat} (h8 : i < 8) :
    Cg prime (sumP inp s (sqrRow i))
      (pw (2 * i) * (inp 0 i * inp 0 i) + (pw (2 * i + 1) * (inp 0 i * dw (inp 0) i 0) +
        sumTo (fun j => (pw (2 * i + 1) * inp 0 i) * (pw (j + 1) * dw (inp 0) i (j + 1))) (7 - i))) := by
  unfold sqrRow
  rw [sumP, sumP]
  refine Cg.add ((pr_ev _ _ _ inp s).trans (Cg.of_eq ?_)) (Cg.add ((pr_ev _ _ _ inp s).trans (Cg.of_eq ?_)) ?_)
  · rw [ev_inp inp s (by decide) (by omega_using [h8])]
  · rw [ev_inp inp s (by decide) (by omega_using [h8]), ev_dbl inp s (by omega_using [h8]), dw, ite_eq_left rfl]
  · refine sumP_map_range _ _ inp s _ fun j hj => (pr_ev _ _ _ inp s).trans (Cg.of_eq ?_)
    rw [ev_inp inp s (by decide) (by omega_using [h8]), ev_ext inp s (by omega_using [hj, h8]) (by omega_using [hj, h8]),
      dw, ite_eq_right (by omega_using []), show i + 1 + (j + 1) = i + 2 + j by omega_using [],
      show i + (j + 1) = i + 1 + j by omega_using [],
      show 2 * i + 2 + j = (2 * i + 1) + (j + 1) by omega_using [], pw_add]
    exact mul4 _ _ _ _

private theorem row_eq (P Q a X : Nat) :
    P * P * (a * a) + P * Q * a * (2 * X) = P * a * (P * a + 2 * (Q * X)) := by
  rw [Nat.mul_add]
  congr 1 <;> ac_rfl

/-- Row `i` of the square. -/
theorem sqrRow_ev {inp : Nat → Nat → Nat} (hi : InB inp) (s : St) {i : Nat} (h8 : i < 8) :
    Cg prime (sumP inp s (sqrRow i))
      ((pw i * inp 0 i) * ((pw i * inp 0 i) + 2 * (pw (i + 1) * num (fun j => inp 0 (i + 1 + j)) (8 - i)))) := by
  have hd := dw_sum (inp 0) (hi.w 0) i (7 - i)
  have top : inp 0 (i + 1 + (7 - i)) / 2 ^ 63 = 0 := by
    rw [show i + 1 + (7 - i) = 8 by omega_using [h8]]
    have := hi.b 0 8
    rw [show inB 0 8 = 511 from rfl] at this
    omega_using [this]
  rw [top, Nat.mul_zero, Nat.add_zero, show 7 - i + 1 = 8 - i by omega_using [h8]] at hd
  refine (sqrRow_words s h8).trans (Cg.of_eq ?_)
  have sh : ∀ n, sumTo (fun j => pw (j + 1) * dw (inp 0) i (j + 1)) n + dw (inp 0) i 0 = num (dw (inp 0) i) (n + 1) := by
    intro n
    induction n with
    | zero => simp only [sumTo, num, pw_zero, Nat.one_mul, Nat.zero_add]
    | succ n ih => rw [num_succ _ (n + 1), ← ih, sumTo]; omega_using []
  have hs := sh (7 - i)
  rw [show 7 - i + 1 = 8 - i by omega_using [h8], hd] at hs
  rw [sumTo_mul, ← Nat.mul_assoc (pw (2 * i + 1)) (inp 0 i) (dw (inp 0) i 0), ← Nat.mul_add,
    Nat.add_comm (dw (inp 0) i 0), hs, show 2 * i = i + i by omega_using [], show i + i + 1 = i + (i + 1) by omega_using [],
    pw_add i i, pw_add i (i + 1)]
  exact row_eq _ _ _ _

/-- A number's words from the `i`-th on. -/
theorem num_split (a : Nat → Nat) : ∀ m i, num (fun j => a (i + j)) (m + 1) = a i + 2 ^ 64 * num (fun j => a (i + 1 + j)) m
  | 0, i => by simp only [num, sumTo, pw_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.mul_zero]
  | m + 1, i => by
    rw [num_succ _ (m + 1), num_split a m i, num_succ _ m, Nat.mul_add, show i + (m + 1) = i + 1 + m by omega_using [],
      pw_succ, Nat.mul_assoc, Nat.add_assoc]

private theorem sq_eq (X Y : Nat) : X * (X + 2 * Y) + Y * Y = (X + Y) * (X + Y) := by
  rw [Nat.mul_add, Nat.add_mul X Y, Nat.mul_add, Nat.mul_add]
  have e1 : X * (2 * Y) = 2 * (X * Y) := Nat.mul_left_comm ..
  have e2 : Y * X = X * Y := Nat.mul_comm ..
  omega_using [e1, e2]

/-- A square, word by word. -/
theorem sq_rows (a : Nat → Nat) : ∀ n, n ≤ 8 →
    sumTo (fun i => (pw i * a i) * ((pw i * a i) + 2 * (pw (i + 1) * num (fun j => a (i + 1 + j)) (8 - i)))) n +
      (pw n * num (fun j => a (n + j)) (9 - n)) * (pw n * num (fun j => a (n + j)) (9 - n)) =
    num a 9 * num a 9
  | 0, _ => by simp only [sumTo, pw_zero, Nat.one_mul, Nat.zero_add, Nat.sub_zero]
  | n + 1, hn => by
    rw [← sq_rows a n (Nat.le_of_succ_le hn), sumTo, Nat.add_assoc]
    congr 1
    have h := num_split a (8 - n) n
    rw [show 8 - n + 1 = 9 - n by omega_using [hn]] at h
    rw [h, show 9 - (n + 1) = 8 - n by omega_using [hn], Nat.mul_add (pw n) (a n), ← Nat.mul_assoc (pw n) (2 ^ 64),
      Nat.mul_comm (pw n) (2 ^ 64), ← pw_succ]
    exact sq_eq _ _

theorem sqrE_ev {inp : Nat → Nat → Nat} (hi : InB inp) (s : St) :
    Cg prime (sumP inp s sqrE) (num (inp 0) 9 * num (inp 0) 9) := by
  rw [← sq_rows (inp 0) 8 (Nat.le_refl _), sqrE, sumP_append]
  refine (sumP_flatMap_range _ _ inp s 8 fun i h => sqrRow_ev hi s h).add ?_
  rw [sumP, sumP, Nat.add_zero]
  refine (prLow_ev _ _ _ inp s ?_).trans (Cg.of_eq ?_)
  · rw [ev_inp inp s (by decide) (by decide)]; exact top_lt hi 0 0
  · have e : num (fun j => inp 0 (8 + j)) (9 - 8) = inp 0 8 := by
      show 0 + pw 0 * inp 0 (8 + 0) = _
      rw [Nat.zero_add, pw_zero, Nat.one_mul]
    rw [e, ev_inp inp s (by decide) (by decide), show pw 16 = pw 8 * pw 8 from pw_add 8 8]
    exact mul4' _ _

/-- The square's number is `[a]^2 2^-576` modulo `p`. -/
theorem sqr_kernel {inp : Nat → Nat → Nat} (hi : InB inp) {s : St} (hs : Ok s) :
    Cg prime (pw 9 * num (fun k => (run inp sqrOps s).g (sqrOut.getD k .x8)) 9)
      (num (inp 0) 9 * num (inp 0) 9) :=
  (chk_ok ((chkK_eq ..).symm.trans (by decide +kernel)) hi hs).trans (sqrE_ev hi s)

theorem sqr_top {inp : Nat → Nat → Nat} (hi : InB inp) {s : St} (hs : Ok s) :
    (run inp sqrOps s).g (sqrOut.getD 8 .x8) ≤ 512 := chkTop_ok (by decide +kernel) hi hs

theorem sqr_zero {inp : Nat → Nat → Nat} (hi : InB inp) {s : St} (hs : Ok s) (hz : ∀ i, inp 0 i = 0) :
    num (fun k => (run inp sqrOps s).g (sqrOut.getD k .x8)) 9 = 0 :=
  chkZero_ok (ib := zeroB 0) (by decide +kernel) hi.w (zeroB_le hi hz) hs

end VG.Proof.Mont.AArch64.P521
