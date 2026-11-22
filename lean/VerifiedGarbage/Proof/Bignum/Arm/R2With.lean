module

public import VerifiedGarbage.Impl.Bignum.Arm.R2Normalized
public import VerifiedGarbage.Proof.Bignum.Arm.R2
public import VerifiedGarbage.Proof.Bignum.Arm.R2CT
import VerifiedGarbage.Proof.Bignum.Arm.R2PublicCT
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
import VerifiedGarbage.Proof.Bignum.Arm.R2Init
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopSteps
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopCT
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Impl.Bignum.Arm.R2Normalized
meta import VerifiedGarbage.Proof.Bignum.Arm.R2
meta import VerifiedGarbage.Proof.Bignum.Arm.R2CT
meta import VerifiedGarbage.Proof.Bignum.Arm.R2PublicCT
meta import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
meta import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
meta import VerifiedGarbage.Proof.Bignum.Arm.R2Init
meta import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopSteps
meta import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopCT
meta import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
meta import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.Block

/-! # `R² mod m`'s squarings by any Montgomery product

`r2SquaresWith op`, `r2With op` and `r2PublicWith op` are `r2Squares`, `r2`
and `r2Public` with their squarings `op 4 4 4`, still in one loop: for the
product of a `TwoExp.Montgomery` `K` (a call of a shared product,
`MontBackend.callOp`), they do what those do (`R2.lean`, `R2CT.lean`,
`R2PublicCT.lean`), keep `K`'s predicate and write only `K`'s regions. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest)

section
variable {base : BitVec 32} {len w : Nat} {Q : State → Prop} {regions : List Region}
  (K : TwoExp.Montgomery base len w Q regions)

/-- `sqC_square_ok`, by `K`'s product. -/
theorem sqC_squareWith_ok (s : State) {m k c : Nat} {P : Prop} (h : SqC base len w m P k c s) (q : Q s) :
    WP isa (K.op 4 4 4) s fun t => SqC base len w m P (2 * k) c t ∧ Q t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  obtain hw : 2 ≤ w := h.ready.width ▸ h.ready.layout.1
  obtain fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  obtain size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  obtain op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  obtain op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  obtain odd : m % 2 = 1 := h.modulus ▸ numAt_odd_of_inverse s.mem _ (by omega_using [hw]) h.ready.inverse
  refine WP.mono (K.op_ok s 4 4 4 h.ready q op4 op4 op4 (by decide) (by rw [h.modulus]; exact h.operand)) ?_
  rintro t ⟨ready, modulus, bound, value, keeps, qt, frame, rest⟩
  rw [h.modulus] at modulus bound value
  refine ⟨⟨ready, modulus, bound, fun p => r2_square_value odd (h.value p) value, ?_, ?_⟩, qt, frame, rest⟩
  · have := keeps_array_word (d := 0) (bits := 32) keeps fits op7 (by decide) (by omega_using [])
    simp only [Nat.add_zero] at this
    change (t.mem.readW (off (State.addr base) (arrAt w 7)) 32).toNat = 2
    rw [this]; exact h.two
  · rw [keeps_header_readW keeps size (d := 208) (bits := 32) (by decide)]; exact h.counter

/-- `sqC_step_ok`, by `K`'s product. -/
theorem sqC_stepWith_ok (s : State) {m k c : Nat} {P : Prop} (h : SqC base len w m P k c s) (q : Q s)
    (hc : 0 < c) (hc' : c < 2 ^ 32) :
    WP isa (r2SquareStepWith K.op) s fun t => SqC base len w m P (2 * k) (c - 1) t ∧ t.z = decide (c = 1) ∧
      Q t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [r2SquareStepWith, WP.seq_iff]
  refine WP.mono (sqC_squareWith_ok K s h q) ?_
  rintro u ⟨hu, qu, frameU, restU⟩
  obtain fits := hu.ready.layout.2.2.1
  obtain size : 212 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  refine WP.mono (doubleCount_ok u hu.ready.workspace size hu.ready.ptr hc hc' hu.counter) ?_
  rintro t ⟨mem, zero, keep⟩
  obtain ⟨ht, frameT⟩ := hu.after_count mem keep
  obtain restT : Rest roundClobbers u t := keep.mono (by decide)
  exact ⟨ht, zero, K.stable frameT restT qu,
    frameU.trans (frameT.mono fun r hr => by have er := List.mem_singleton.mp hr; subst r; exact K.workspace),
    restU.trans restT⟩

/-- `sqC_loop_ok`, by `K`'s product. -/
theorem sqC_loopWith_ok (s : State) {m k c : Nat} {P : Prop} (h : SqC base len w m P k c s) (q : Q s)
    (hc : 0 < c) (hc' : c < 2 ^ 32) :
    WP isa (.loop (r2SquareStepWith K.op) .ne) s fun t => SqC base len w m P (2 ^ c * k) 0 t ∧ Q t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  let inv := fun j t => ∃ i, i + j = c ∧ 0 < j ∧ SqC base len w m P (2 ^ i * k) j t ∧ Q t ∧
    Frame regions s.mem t.mem ∧ Rest roundClobbers s t
  refine WP.loop (M := isa) inv ?_ c s ⟨0, by omega_using [], hc, by rw [Nat.pow_zero, Nat.one_mul]; exact h, q,
    Frame.refl _ _, Rest.refl _ _⟩
  intro j t hi
  obtain ⟨i, hij, hj, ht, qt, frame, rest⟩ := hi
  refine WP.mono (sqC_stepWith_ok K t ht qt hj (by omega_using [hc', hij])) ?_
  rintro u ⟨hu, zero, qu, frameU, restU⟩
  rw [show 2 * (2 ^ i * k) = 2 ^ (i + 1) * k by rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm]] at hu
  by_cases exit : j = 1
  · left
    refine ⟨?_, ?_, qu, frame.trans frameU, rest.trans restU⟩
    · change some (!u.z) = some false
      simp only [zero, exit, decide_true, Bool.not_true]
    · rw [show c = i + 1 by omega_using [hij, exit]]
      simpa only [exit, Nat.sub_self] using hu
  · right
    refine ⟨?_, j - 1, by omega_using [hj], i + 1, by omega_using [hij, hj], by omega_using [hj, exit], hu, qu,
      frame.trans frameU, rest.trans restU⟩
    change some (!u.z) = some true
    simp only [zero, exit, decide_false, Bool.not_false]

/-- `sqC_squares_ok`, by `K`'s product. -/
theorem sqC_squaresWith_ok (s : State) {m k : Nat} {P : Prop} (h : SqC base len w m P k 0 s) (q : Q s) :
    WP isa (r2SquaresWith K.op) s fun t => SqC base len w m P (64 * k) 0 t ∧ Q t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [r2SquaresWith, WP.seq_iff]
  refine WP.mono (r2SquareCount_ok s h) ?_
  rintro u ⟨hu, frameU, restU⟩
  obtain restU' : Rest roundClobbers s u := restU.mono (by decide)
  refine WP.mono (sqC_loopWith_ok K u hu (K.stable frameU restU' q) (by decide) (by decide)) ?_
  rintro t ⟨ht, qt, frameT, restT⟩
  rw [show (2 : Nat) ^ 6 = 64 from rfl] at ht
  exact ⟨ht, qt, (frameU.mono fun r hr => by have er := List.mem_singleton.mp hr; subst r; exact K.workspace).trans
    frameT, restU'.trans restT⟩

/-- `r2Squares_ok`, by `K`'s product. -/
theorem r2SquaresWith_ok (s : State) {m : Nat} (h : R2Sq base len w m w s) (q : Q s) :
    WP isa (r2SquaresWith K.op) s fun t => R2Sq base len w m (64 * w) t ∧ Q t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t :=
  WP.mono (sqC_squaresWith_ok K s h.toC q) fun _ ⟨ht, qt, frame, rest⟩ => ⟨ht.toR2Sq, qt, frame, rest⟩

/-- The end of `r2With` and `r2PublicWith`: the squarings, from the doublings' `2^(64 w + w)`. -/
theorem r2SquaresWith_done (s : State) {m : Nat} (h : R2Sq base len w m w s) (q : Q s) :
    WP isa (r2SquaresWith K.op) s fun t => DoubleLoopReady base len w 0 t ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % m ∧ numAt t.mem (State.addr base) w 0 = m ∧
      Q t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (r2SquaresWith_ok K s h q) ?_
  rintro t ⟨fin, qt, frameT, restT⟩
  obtain exact : numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % m := by
    rw [← Nat.mod_eq_of_lt fin.operand, fin.value, show 64 * w + 64 * w = 128 * w by omega_using []]
  exact ⟨⟨fin.ready.workspace, fin.ready.layout, fin.ready.width, fin.ready.ptr, fin.ready.inverse,
      by rw [fin.modulus]; exact fin.operand, fin.two, fin.counter, fin.ready.stackRead,
      fin.ready.stackSep, fin.ready.saved⟩, exact, fin.modulus, qt, frameT, restT⟩

/-- `r2_ok`, by `K`'s product. -/
theorem r2With_ok (s : State) (h : ArithmeticReady base len w s) (q : Q s) (countFits : 128 * w < 2 ^ 32) :
    WP isa (r2With K.op) s fun t => DoubleLoopReady base len w 0 t ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Q t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [r2With, WP.seq_iff]
  refine WP.mono (r2Init_ok s h) ?_
  rintro u ⟨ready, one, modulus, frame, rest⟩
  rw [WP.seq_iff]
  refine WP.mono (r2Loop_ok u ready one (by rw [modulus]; exact h.modulus) countFits) ?_
  rintro v ⟨sq, frameV, restV⟩
  rw [modulus] at sq
  refine WP.mono (r2SquaresWith_done K v sq (K.stable frameV restV (K.stable frame rest q))) ?_
  rintro t ⟨done, value, mod, qt, frameT, restT⟩
  exact ⟨done, value, mod, qt,
    ((frame.trans frameV).mono fun r hr => by have er := List.mem_singleton.mp hr; subst r; exact K.workspace).trans
      frameT, rest.trans (restV.trans restT)⟩

/-- `r2Public_ok`, by `K`'s product. -/
theorem r2PublicWith_ok (s : State) (h : ArithmeticReady base len w s) (q : Q s) (countFits : 128 * w < 2 ^ 32) :
    WP isa (r2PublicWith K.op) s fun t => DoubleLoopReady base len w 0 t ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Q t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [r2PublicWith, WP.seq_iff]
  refine WP.mono (r2PublicInit_ok s h rfl) ?_
  rintro u ⟨ready, frame, rest⟩
  rw [WP.seq_iff]
  refine WP.mono (r2PublicLoop_ok u ready countFits) ?_
  rintro v ⟨sq, frameV, restV⟩
  refine WP.mono (r2SquaresWith_done K v sq (K.stable frameV restV (K.stable frame rest q))) ?_
  rintro t ⟨done, value, mod, qt, frameT, restT⟩
  exact ⟨done, value, mod, qt,
    ((frame.trans frameV).mono fun r hr => by have er := List.mem_singleton.mp hr; subst r; exact K.workspace).trans
      frameT, rest.trans (restV.trans restT)⟩

/-! ## Timing -/

/-- The squarings' loop states in two runs, each for its own modulus, with `K`'s predicate. -/
def SqCRelWith (P : Prop) (k c : Nat) (s t : State) : Prop :=
  ((∃ m, SqC base len w m P k c s) ∧ Q s) ∧ ((∃ m, SqC base len w m P k c t) ∧ Q t) ∧ s.sp = t.sp

variable {K} in
theorem sqC_squareWith_ct (ct : TwoExp.MontgomeryTiming K) {k c : Nat} {P : Prop} :
    RelCT isa (SqCRelWith (base := base) (len := len) (w := w) (Q := Q) P k c) (K.op 4 4 4)
      (SqCRelWith (base := base) (len := len) (w := w) (Q := Q) P (2 * k) c) := by
  obtain op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have opCT := relCT_keep_sp ((ct.op_ct 4 4 4 op4 op4 op4).mono
    (P' := SqCRelWith (base := base) (len := len) (w := w) (Q := Q) P k c)
    (fun _ _ h => by
      obtain ⟨⟨⟨m1, h1⟩, q1⟩, ⟨⟨m2, h2⟩, q2⟩, sp⟩ := h
      exact ⟨⟨h1.ready, q1, by rw [h1.modulus]; exact h1.operand⟩,
        ⟨h2.ready, q2, by rw [h2.modulus]; exact h2.operand⟩, sp⟩)
    (fun _ _ _ => trivial)) (fun _ _ h => h.2.2)
  have post (s : State) (h : (∃ m, SqC base len w m P k c s) ∧ Q s) :
      WP isa (K.op 4 4 4) s fun t => (∃ m, SqC base len w m P (2 * k) c t) ∧ Q t := by
    obtain ⟨⟨m, hm⟩, q⟩ := h
    exact WP.mono (sqC_squareWith_ok K s hm q) fun t ht => ⟨⟨m, ht.1⟩, ht.2.1⟩
  exact (opCT.wp (fun s t h => ⟨post s h.1, post t h.2.1⟩)).mono (fun _ _ h => h)
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩)

variable {K} in
theorem sqC_stepWith_ct (ct : TwoExp.MontgomeryTiming K) {k c : Nat} {P : Prop} :
    RelCT isa (SqCRelWith (base := base) (len := len) (w := w) (Q := Q) P k c) (r2SquareStepWith K.op)
      (fun _ _ => True) := by
  rw [r2SquareStepWith]
  exact (sqC_squareWith_ct ct).seq ((sqC_block_ct (k := 2 * k) (c := c) (by taint_decide)).mono
    (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial))

variable {K} in
theorem sqC_loopWith_ct (ct : TwoExp.MontgomeryTiming K) {k c : Nat} {P : Prop} (hc : 0 < c)
    (hc' : c < 2 ^ 32) :
    RelCT isa (SqCRelWith (base := base) (len := len) (w := w) (Q := Q) P k c)
      (.loop (r2SquareStepWith K.op) .ne) (fun _ _ => True) := by
  let I := fun j (s t : State) => 0 < j ∧ j < 2 ^ 32 ∧
    ∃ i, SqCRelWith (base := base) (len := len) (w := w) (Q := Q) P i j s t
  have step : ∀ j, RelCT isa (I j) (r2SquareStepWith K.op) fun s t => isa.eval .ne s = isa.eval .ne t ∧
      (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ j' < j, I j' s t) := by
    intro j s t tr1 tr2 u v h e1 e2
    obtain ⟨hj, hj', i, ⟨⟨m1, hs⟩, qs⟩, ⟨⟨m2, ht⟩, qt⟩, sp⟩ := h
    obtain ⟨trace, _⟩ := sqC_stepWith_ct ct (k := i) (c := j) s t tr1 tr2 u v
      ⟨⟨⟨m1, hs⟩, qs⟩, ⟨⟨m2, ht⟩, qt⟩, sp⟩ e1 e2
    obtain ⟨_, u', eu, hu, zu, qu, _, ru⟩ := sqC_stepWith_ok K s hs qs hj hj'
    obtain ⟨_, v', ev, hv, zv, qv, _, rv⟩ := sqC_stepWith_ok K t ht qt hj hj'
    obtain ⟨-, rfl⟩ := Exec.det e1 eu
    obtain ⟨-, rfl⟩ := Exec.det e2 ev
    refine ⟨trace, ?_, fun _ => trivial, ?_⟩
    · change some (!u.z) = some (!v.z)
      rw [zu, zv]
    · intro branch
      have ne : j ≠ 1 := by
        intro eq
        change some (!u.z) = some true at branch
        simp only [zu, eq, decide_true, Bool.not_true] at branch
        cases branch
      exact ⟨j - 1, by omega_using [hj], by omega_using [hj, ne], by omega_using [hj'],
        2 * i, ⟨⟨m1, hu⟩, qu⟩, ⟨⟨m2, hv⟩, qv⟩, ru.sp.trans (sp.trans rv.sp.symm)⟩
  exact (RelCT.loop I step c).mono (fun _ _ h => ⟨hc, hc', k, h⟩) (fun _ _ h => h)

variable {K} in
/-- `sqC_squares_ct`, by `K`'s product. -/
theorem sqC_squaresWith_ct (ct : TwoExp.MontgomeryTiming K) {k : Nat} {P : Prop} :
    RelCT isa (SqCRelWith (base := base) (len := len) (w := w) (Q := Q) P k 0) (r2SquaresWith K.op)
      (fun _ _ => True) := by
  have post (s : State) (h : (∃ m, SqC base len w m P k 0 s) ∧ Q s) :
      WP isa (.block r2SquareCount) s fun t => (∃ m, SqC base len w m P k 6 t) ∧ Q t := by
    obtain ⟨⟨m, hm⟩, q⟩ := h
    exact WP.mono (r2SquareCount_ok s hm) fun _ x => ⟨⟨m, x.1⟩, K.stable x.2.1 (x.2.2.mono (by decide)) q⟩
  have count := (relCT_keep_sp ((sqC_block_ct (base := base) (len := len) (w := w) (P := P) (k := k) (c := 0)
    (l := r2SquareCount) (by taint_decide)).mono
    (P' := SqCRelWith (base := base) (len := len) (w := w) (Q := Q) P k 0)
    (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial)) (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨post s h.1, post t h.2.1⟩)
  rw [r2SquaresWith]
  exact (count.mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩)).seq
    (sqC_loopWith_ct ct (by decide) (by decide))

variable {K} in
/-- `r2Squares_ct`, by `K`'s product. -/
theorem r2SquaresWith_ct (ct : TwoExp.MontgomeryTiming K) :
    RelCT isa (fun s t => ((∃ m, R2Sq base len w m w s) ∧ Q s) ∧ ((∃ m, R2Sq base len w m w t) ∧ Q t) ∧
      s.sp = t.sp) (r2SquaresWith K.op) (fun _ _ => True) :=
  (sqC_squaresWith_ct ct (P := True)).mono
    (fun _ _ h => ⟨⟨h.1.1.elim fun m hm => ⟨m, hm.toC⟩, h.1.2⟩, ⟨h.2.1.1.elim fun m hm => ⟨m, hm.toC⟩, h.2.1.2⟩,
      h.2.2⟩) (fun _ _ _ => trivial)

variable {K} in
/-- `r2_ct`, by `K`'s product. -/
theorem r2With_ct (ct : TwoExp.MontgomeryTiming K) (countFits : 128 * w < 2 ^ 32) :
    RelCT isa (fun s t => (ArithmeticReady base len w s ∧ Q s) ∧ (ArithmeticReady base len w t ∧ Q t) ∧
      s.sp = t.sp) (r2With K.op) (fun _ _ => True) := by
  have initPost (s : State) (h : ArithmeticReady base len w s ∧ Q s) :
      WP isa r2Init s fun t => R2LoopReady base len w t ∧ Q t :=
    WP.mono (r2Init_ok s h.1) fun _ x => ⟨⟨x.1, x.2.1, by rw [x.2.2.1]; exact h.1.modulus⟩,
      K.stable x.2.2.2.1 x.2.2.2.2 h.2⟩
  have init := (relCT_keep_sp ((r2Init_ct (base := base) (len := len) (w := w)).mono
    (P' := fun (s t : State) => (ArithmeticReady base len w s ∧ Q s) ∧ (ArithmeticReady base len w t ∧ Q t) ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h))
    (fun _ _ h => h.2.2)).wp (fun s t h => ⟨initPost s h.1, initPost t h.2.1⟩)
  refine init.seq ?_
  have loopPost (s : State) (h : R2LoopReady base len w s ∧ Q s) :
      WP isa doubleLoop s fun v => (∃ m, R2Sq base len w m w v) ∧ Q v :=
    WP.mono (r2Loop_ok s h.1.1 h.1.2.1 h.1.2.2 countFits) fun v x => ⟨⟨_, x.1⟩, K.stable x.2.1 x.2.2 h.2⟩
  have loop : RelCT isa (fun s t => s.sp = t.sp ∧ (R2LoopReady base len w s ∧ Q s) ∧ (R2LoopReady base len w t ∧ Q t))
      doubleLoop (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    have hw : 2 ≤ w := h.2.1.1.1.width ▸ h.2.1.1.1.layout.1
    exact doubleLoop_ct (by omega_using [hw]) (by omega_using [countFits]) s t tr1 tr2 u v
      ⟨h.2.1.1.1, h.2.2.1.1, h.1⟩ e1 e2
  have loopCT := (relCT_keep_sp loop (fun _ _ h => h.1)).wp
    (fun s t h => ⟨loopPost s h.2.1, loopPost t h.2.2⟩)
  exact loopCT.seq ((r2SquaresWith_ct ct).mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h))

variable {K} in
/-- `r2Public_ct`, by `K`'s product. -/
theorem r2PublicWith_ct (ct : TwoExp.MontgomeryTiming K) {M : Nat} (countFits : 128 * w < 2 ^ 32) :
    RelCT isa (fun s t =>
      ((ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w 0 = M) ∧ Q s) ∧
      ((ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w 0 = M) ∧ Q t) ∧ s.sp = t.sp)
      (r2PublicWith K.op) (fun _ _ => True) := by
  let P := fun (s : State) => R2PublicInitialized base len w M s ∧ Q s
  have initPost (s : State) (h : (ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w 0 = M) ∧ Q s) :
      WP isa r2PublicInit s P :=
    WP.mono (r2PublicInit_ok s h.1.1 h.1.2) (fun _ j => ⟨j.1, K.stable j.2.1 j.2.2 h.2⟩)
  have initialized := (relCT_keep_sp ((r2PublicInit_ct (base := base) (len := len) (w := w) (M := M)).mono
    (P' := fun (s t : State) => ((ArithmeticReady base len w s ∧ numAt s.mem (State.addr base) w 0 = M) ∧ Q s) ∧
      ((ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w 0 = M) ∧ Q t) ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h))
    (fun _ _ h => h.2.2)).wp (fun s t h => ⟨initPost s h.1, initPost t h.2.1⟩)
  have loop : RelCT isa (fun s t => s.sp = t.sp ∧ P s ∧ P t) doubleLoop (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    have hw : 2 ≤ w := h.2.1.1.ready.width ▸ h.2.1.1.ready.layout.1
    obtain ⟨cpos, cle⟩ := r2PublicCount_le (w := w) (M := M) (by omega_using [hw])
    exact doubleLoop_ct cpos (by omega_using [countFits, cle]) s t tr1 tr2 u v
      ⟨h.2.1.1.ready, h.2.2.1.ready, h.1⟩ e1 e2
  have post (s : State) (h : P s) : WP isa doubleLoop s fun t => (∃ m, R2Sq base len w m w t) ∧ Q t :=
    WP.mono (r2PublicLoop_ok s h.1 countFits) (fun _ j => ⟨⟨M, j.1⟩, K.stable j.2.1 j.2.2 h.2⟩)
  have powered := (relCT_keep_sp loop (fun _ _ h => h.1)).wp (fun s t h => ⟨post s h.2.1, post t h.2.2⟩)
  exact initialized.seq ((powered.mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩)).seq
    ((r2SquaresWith_ct ct).mono (fun _ _ h => h) (fun _ _ h => h)))

end

end VG.Proof.Bignum.Arm
