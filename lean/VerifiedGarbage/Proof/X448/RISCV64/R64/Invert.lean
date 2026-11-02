module

public import VerifiedGarbage.Proof.X448.RISCV64.R64.Ladder
public import VerifiedGarbage.Proof.X448.Invert
public import VerifiedGarbage.Proof.X448.RISCV64.Invert
import VerifiedGarbage.Proof.X25519.RISCV64.Instr

/-!
# X448 on RISC-V, 64-bit limbs: the inversion

`invert` of `Impl/X448/RISCV64/R64.lean` computes `z^(p-2)` into `R` for the
element `z` at `Z2` by the addition chain of `Proof/X448/Invert.lean`
(`invertQ_ok`): runs of squarings (`sqn_ok`, a loop on `t1` after the first),
the chain as far as `z^(2²²³ - 1)` in `R` and `z^(2²²² - 1)` in `T6`
(`chain223_ok`, which Ed448's square root shares), then its two final
factors. The chain's slots `T0`–`T6` are separate from the slots `qs` the
caller keeps (`TempsOk`), whose elements it keeps.
-/

@[expose] public section

namespace VG.Proof.X448.RISCV64.R64
section

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X448.RISCV64.R64 VG.Proof.X25519 VG.Proof.X25519.RISCV64
open VG.Impl.X448.RISCV64 (X2 Z2 R ACC)
open VG.Proof.X448.RISCV64 (FS SlotsOk SlotsOk.mono SlotsOk.congr upd upd_self upd_of_ne IQ Sep1 sep1_get)
open VG.Spec.X448 (P Fe)

/-! ## Separate slots -/

/-- The chain's temporaries. -/
abbrev TQ : List Nat := [T0, T1, T2, T3, T4, T5, T6]

/-- The temporaries are separate from the slots `qs`, and not among them. -/
def TempsOk (qs : List Nat) : Bool := TQ.all fun t => Sep8 t qs && !qs.contains t

theorem temps_get {qs : List Nat} (h : TempsOk qs = true) {t : Nat} (ht : t ∈ TQ) :
    Sep8 t qs = true ∧ t ∉ qs := by
  have := List.all_eq_true.mp h t ht
  simp only [Bool.and_eq_true] at this
  refine ⟨this.1, fun hm => ?_⟩
  have h2 := this.2
  rw [List.contains_iff_mem.mpr hm] at h2
  contradiction

theorem sep8_cons {o x : Nat} {l : List Nat} (h1 : Sep8 o [x] = true) (h2 : Sep8 o l = true) :
    Sep8 o (x :: l) = true := by
  simp only [Sep8, Sep1, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h1 h2 ⊢
  exact ⟨⟨⟨h1.1.1.1, h1.1.1.2, h2.1.1.2⟩, h2.1.2⟩, h1.2, h2.2⟩

/-- `Sep8 o` of a list of literal slots in front of `qs`, from `Sep8 o qs`. -/
macro "sep8" : tactic =>
  `(tactic| repeat (first | with_reducible assumption | refine sep8_cons (by decide) ?_))

theorem upd_upd (v : Nat → Fe) (o : Nat) (x y : Fe) : upd (upd v o x) o y = upd v o y := by
  funext q; by_cases h : q = o
  · subst h; rw [upd_self, upd_self]
  · rw [upd_of_ne _ _ h, upd_of_ne _ _ h, upd_of_ne _ _ h]

section
variable {b : Addr} {s0 : State} {a : BitVec 64}

theorem Cur.congr {s : State} {c : BitVec 64} {qs qs' : List Nat} {v w : Nat → Fe}
    (h : Cur b s0 a c qs v s) (hq : ∀ q ∈ qs', q ∈ qs) (hv : ∀ q ∈ qs', v q = w q) :
    Cur b s0 a c qs' w s :=
  ⟨h.ctx, h.stp, h.t2, h.t1, (h.slots.mono hq).congr hv⟩

/-- `Cur` with any counter in `t1`. -/
abbrev CurE (b : Addr) (s0 : State) (a : BitVec 64) (qs : List Nat) (v : Nat → Fe) (s : State) : Prop :=
  ∃ c, Cur b s0 a c qs v s

theorem opMulE {o x y : Nat} {qs : List Nat} {v : Nat → Fe} (hq : Sep8 o qs = true)
    (ho : o + 56 ≤ ACC) (hx : x ∈ qs) (hy : y ∈ qs) {s : State} (h : CurE b s0 a qs v s) :
    WP isa (mul o x y) s (CurE b s0 a (o :: qs) (upd v o (v x * v y))) :=
  let ⟨c, h⟩ := h
  WP.mono (opMul hq ho hx hy h) fun _ h' => ⟨c, h'⟩

/-! ## Runs of squarings -/

/-- The loop of `sqn o x n` from `sL`, before the iteration that leaves `m - 1`
squarings to do. -/
abbrev SqInv (b : Addr) (s0 : State) (a : BitVec 64) (o n : Nat) (qs : List Nat) (v : Nat → Fe) (y : Fe)
    (m : Nat) (s : State) : Prop :=
  Cur b s0 a (BitVec.ofNat 64 m) (o :: qs) (upd v o (VG.Proof.X448.sqn y (n - m))) s

theorem sep8_self {o : Nat} {qs : List Nat} (hq : Sep8 o qs = true) (ho : o + 56 ≤ ACC) :
    Sep8 o (o :: qs) = true := by
  refine sep8_cons ?_ hq
  have h8 := sep8_o hq
  have hA : ACC = 952 := rfl
  simp only [Sep8, Sep1, List.all_cons, List.all_nil, Bool.and_true, beq_self_eq_true,
    Bool.true_or, Bool.true_and, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  omega

theorem sqStep_ok {o n : Nat} {qs : List Nat} {v : Nat → Fe} {y : Fe} (hq : Sep8 o qs = true)
    (ho : o + 56 ≤ ACC) {m : Nat} (hm : 1 ≤ m) (hmn : m < n) (hn : n ≤ 2048) {s : State}
    (h : SqInv b s0 a o n qs v y m s) :
    WP isa (sqStep o) s fun s' => SqInv b s0 a o n qs v y (m - 1) s' ∧
      (s'.gpr .t1 != 0) = decide (m - 1 ≠ 0) := by
  unfold sqStep
  refine WP.seq (wp_subi (by decide) fun s1 u1 => WP.block_nil ?_)
  have h1 : Cur b s0 a (BitVec.ofNat 64 (m - 1)) (o :: qs) (upd v o (VG.Proof.X448.sqn y (n - m))) s1 :=
    ⟨h.ctx.of_rest (u1.rest (ws := [.t1]) (by decide)) (by decide),
      h.stp.trans (Stp.of_rest (u1.rest (ws := [.t1]) (by decide)) (by decide) u1.mem),
      by rw [u1.other _ (by decide), h.t2],
      by rw [u1.gpr, h.t1, ofNat_sub_one hm (by omega)],
      by rw [u1.mem]; exact h.slots⟩
  refine WP.mono (opMul (o := o) (x := o) (y := o) (sep8_self hq ho) ho List.mem_cons_self
    List.mem_cons_self h1) fun s2 h2 => ⟨h2.congr (fun q hq => List.mem_cons_of_mem _ hq) fun q _ => ?_, ?_⟩
  · rw [upd_upd, upd_self, show n - (m - 1) = n - m + 1 by omega]; rfl
  · rw [h2.t1, ofNat_ne_zero (by omega)]

/-- `[o] = [x]^(2^n)`. -/
theorem sqn_ok {o x n : Nat} {qs : List Nat} {v : Nat → Fe} (hn1 : 1 ≤ n) (hn : n ≤ 2048)
    (hq : Sep8 o qs = true) (ho : o + 56 ≤ ACC) (hx : x ∈ qs) {s : State} (h : CurE b s0 a qs v s) :
    WP isa (Impl.X448.RISCV64.R64.sqn o x n) s (CurE b s0 a (o :: qs) (upd v o (VG.Proof.X448.sqn (v x) n))) := by
  unfold Impl.X448.RISCV64.R64.sqn
  by_cases h1 : n = 1
  · subst h1
    exact opMulE hq ho hx hx h
  · simp only [h1, ↓reduceIte]
    refine WP.seq (WP.mono (opMulE hq ho hx hx h) fun s1 ⟨c1, h1'⟩ => ?_)
    refine WP.seq (wp_li (by omega) fun s2 u2 => WP.block_nil ?_)
    have h2 : SqInv b s0 a o n qs v (v x) (n - 1) s2 :=
      ⟨h1'.ctx.of_rest (u2.rest (ws := [.t1]) (by decide)) (by decide),
        h1'.stp.trans (Stp.of_rest (u2.rest (ws := [.t1]) (by decide)) (by decide) u2.mem),
        by rw [u2.other _ (by decide), h1'.t2], by rw [u2.gpr],
        by rw [u2.mem, show n - (n - 1) = 1 by omega]; exact h1'.slots⟩
    refine WP.mono (Q := SqInv b s0 a o n qs v (v x) 0) (WP.loop (M := isa)
      (fun m s' => 1 ≤ m ∧ m < n ∧ SqInv b s0 a o n qs v (v x) m s') ?_ (n - 1) s2
        ⟨by omega, by omega, h2⟩) fun s' h' => ⟨_, by
          have := h'.slots; rw [Nat.sub_zero] at this; exact ⟨h'.ctx, h'.stp, h'.t2, h'.t1, this⟩⟩
    rintro m s' ⟨hm1, hm2, hl⟩
    refine WP.mono (sqStep_ok hq ho hm1 hm2 hn hl) fun s'' ⟨hl', hz⟩ => ?_
    by_cases hm : m - 1 = 0
    · exact .inl ⟨by rw [eval_nonzero, hz]; simp [hm], by rw [hm] at hl'; exact hl'⟩
    · exact .inr ⟨by rw [eval_nonzero, hz]; simp [hm], m - 1, by omega, by omega, by omega, hl'⟩

/-! ## The chain

Each slot of the chain holds a power `pw z e` of `z`, its exponent a closed
expression, so that each step reads its operands' exponents off the
previous slots (`look`) and the exponents are checked by `decide`. -/

/-- `[o] = [x] · [y]` for powers of `z`. -/
theorem opMulP {o x y : Nat} {qs : List Nat} {F : Nat → Fe} {z : Fe} {ea eb ee : Nat}
    (hq : Sep8 o qs = true) (ho : o + 56 ≤ ACC) (hx : x ∈ qs) (hy : y ∈ qs)
    (hFx : F x = VG.Proof.X448.pw z ea) (hFy : F y = VG.Proof.X448.pw z eb) (he : ea + eb = ee)
    {s : State} (h : CurE b s0 a qs F s) :
    WP isa (mul o x y) s (CurE b s0 a (o :: qs) (upd F o (VG.Proof.X448.pw z ee))) :=
  WP.mono (opMulE hq ho hx hy h) fun _ ⟨c, h'⟩ => ⟨c, h'.congr (fun _ hq => hq) fun _ _ => by
    rw [hFx, hFy, VG.Proof.X448.pw_mul, he]⟩

/-- `[o] = [x]^(2^n)` for a power of `z`. -/
theorem sqnP {o x n : Nat} {qs : List Nat} {F : Nat → Fe} {z : Fe} {ea : Nat} (hn1 : 1 ≤ n)
    (hn : n ≤ 2048) (hq : Sep8 o qs = true) (ho : o + 56 ≤ ACC) (hx : x ∈ qs)
    (hFx : F x = VG.Proof.X448.pw z ea) {s : State} (h : CurE b s0 a qs F s) :
    WP isa (Impl.X448.RISCV64.R64.sqn o x n) s
      (CurE b s0 a (o :: qs) (upd F o (VG.Proof.X448.pw z (ea * 2 ^ n)))) :=
  WP.mono (sqn_ok hn1 hn hq ho hx h) fun _ ⟨c, h'⟩ => ⟨c, h'.congr (fun _ hq => hq) fun _ _ => by
    rw [hFx, VG.Proof.X448.sqn_pw]⟩

/-- The elements after `chain223 Z2`: `z^(2²²³ - 1)` in `R` and
`z^(2²²² - 1)` in `T6`, for `z` in `Z2`. -/
def chainV (v : Nat → Fe) : Nat → Fe :=
  upd (upd v T6 (VG.Proof.X448.pw (v Z2) (2 ^ 222 - 1))) R (VG.Proof.X448.pw (v Z2) (2 ^ 223 - 1))

/-- A slot's element, read through the updates of literal slots. -/
macro "look" : tactic => `(tactic| simp (disch := decide) only [chainV, upd_self, upd_of_ne])

theorem chain223_ok {qs : List Nat} {v : Nat → Fe} (hR : Sep8 R qs = true) (hZ : Z2 ∈ qs)
    (hT : TempsOk qs = true) {s : State} (h : CurE b s0 a qs v s) :
    WP isa (chain223 Z2) s (CurE b s0 a (R :: T6 :: qs) (chainV v)) := by
  obtain ⟨q0, n0⟩ := temps_get hT (t := T0) (by decide)
  obtain ⟨q1, n1⟩ := temps_get hT (t := T1) (by decide)
  obtain ⟨q2, n2⟩ := temps_get hT (t := T2) (by decide)
  obtain ⟨q3, n3⟩ := temps_get hT (t := T3) (by decide)
  obtain ⟨q4, n4⟩ := temps_get hT (t := T4) (by decide)
  obtain ⟨q5, n5⟩ := temps_get hT (t := T5) (by decide)
  obtain ⟨q6, n6⟩ := temps_get hT (t := T6) (by decide)
  -- `z` as the power `z^1` in its slot.
  have hZ0 : Z2 ∈ Z2 :: qs := List.mem_cons_self
  have h0 : CurE b s0 a (Z2 :: qs) (upd v Z2 (VG.Proof.X448.pw (v Z2) 1)) s :=
    let ⟨c, h⟩ := h
    ⟨c, h.congr (fun q hq => by
      simp only [List.mem_cons] at hq; rcases hq with rfl | hq
      · exact hZ
      · exact hq) fun q _ => by
      by_cases e : q = Z2
      · subst e; rw [upd_self, VG.Proof.X448.pw_one]
      · rw [upd_of_ne _ _ e]⟩
  have hRZ : Sep8 R (Z2 :: qs) = true := sep8_cons (by decide) hR
  have g0 : Sep8 T0 (Z2 :: qs) = true := sep8_cons (by decide) q0
  have g1 : Sep8 T1 (Z2 :: qs) = true := sep8_cons (by decide) q1
  have g2 : Sep8 T2 (Z2 :: qs) = true := sep8_cons (by decide) q2
  have g3 : Sep8 T3 (Z2 :: qs) = true := sep8_cons (by decide) q3
  have g4 : Sep8 T4 (Z2 :: qs) = true := sep8_cons (by decide) q4
  have g5 : Sep8 T5 (Z2 :: qs) = true := sep8_cons (by decide) q5
  have g6 : Sep8 T6 (Z2 :: qs) = true := sep8_cons (by decide) q6
  unfold chain223
  refine WP.seq (WP.mono (sqnP (z := v Z2) (ea := 1) (by decide) (by decide) (by sep8) (by decide) hZ0 (by look) h0) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (opMulP (z := v Z2) (ea := 1 * 2 ^ 1) (eb := 1) (ee := 2 ^ 2 - 1) (by sep8) (by decide) (by simp) (by simp [hZ0])
    (by look) (by look) (by decide) h1) fun s2 h2 => ?_)
  refine WP.seq (WP.mono (sqnP (z := v Z2) (ea := 2 ^ 2 - 1) (by decide) (by decide) (by sep8) (by decide) (by simp) (by look) h2) fun s3 h3 => ?_)
  refine WP.seq (WP.mono (opMulP (z := v Z2) (ea := (2 ^ 2 - 1) * 2 ^ 2) (eb := 2 ^ 2 - 1) (ee := 2 ^ 4 - 1) (by sep8) (by decide) (by simp) (by simp)
    (by look) (by look) (by decide) h3) fun s4 h4 => ?_)
  refine WP.seq (WP.mono (sqnP (z := v Z2) (ea := 2 ^ 4 - 1) (by decide) (by decide) (by sep8) (by decide) (by simp) (by look) h4) fun s5 h5 => ?_)
  refine WP.seq (WP.mono (opMulP (z := v Z2) (ea := (2 ^ 4 - 1) * 2 ^ 4) (eb := 2 ^ 4 - 1) (ee := 2 ^ 8 - 1) (by sep8) (by decide) (by simp) (by simp)
    (by look) (by look) (by decide) h5) fun s6 h6 => ?_)
  refine WP.seq (WP.mono (sqnP (z := v Z2) (ea := 2 ^ 8 - 1) (by decide) (by decide) (by sep8) (by decide) (by simp) (by look) h6) fun s7 h7 => ?_)
  refine WP.seq (WP.mono (opMulP (z := v Z2) (ea := (2 ^ 8 - 1) * 2 ^ 8) (eb := 2 ^ 8 - 1) (ee := 2 ^ 16 - 1) (by sep8) (by decide) (by simp) (by simp)
    (by look) (by look) (by decide) h7) fun s8 h8 => ?_)
  refine WP.seq (WP.mono (sqnP (z := v Z2) (ea := 2 ^ 16 - 1) (by decide) (by decide) (by sep8) (by decide) (by simp) (by look) h8) fun s9 h9 => ?_)
  refine WP.seq (WP.mono (opMulP (z := v Z2) (ea := (2 ^ 16 - 1) * 2 ^ 16) (eb := 2 ^ 16 - 1) (ee := 2 ^ 32 - 1) (by sep8) (by decide) (by simp) (by simp)
    (by look) (by look) (by decide) h9) fun s10 h10 => ?_)
  refine WP.seq (WP.mono (sqnP (z := v Z2) (ea := 2 ^ 32 - 1) (by decide) (by decide) (by sep8) (by decide) (by simp) (by look) h10) fun s11 h11 => ?_)
  refine WP.seq (WP.mono (opMulP (z := v Z2) (ea := (2 ^ 32 - 1) * 2 ^ 32) (eb := 2 ^ 32 - 1) (ee := 2 ^ 64 - 1) (by sep8) (by decide) (by simp) (by simp)
    (by look) (by look) (by decide) h11) fun s12 h12 => ?_)
  refine WP.seq (WP.mono (sqnP (z := v Z2) (ea := 2 ^ 64 - 1) (by decide) (by decide) (by sep8) (by decide) (by simp) (by look) h12) fun s13 h13 => ?_)
  refine WP.seq (WP.mono (opMulP (z := v Z2) (ea := (2 ^ 64 - 1) * 2 ^ 64) (eb := 2 ^ 64 - 1) (ee := 2 ^ 128 - 1) (by sep8) (by decide) (by simp) (by simp)
    (by look) (by look) (by decide) h13) fun s14 h14 => ?_)
  refine WP.seq (WP.mono (sqnP (z := v Z2) (ea := 2 ^ 128 - 1) (by decide) (by decide) (by sep8) (by decide) (by simp) (by look) h14) fun s15 h15 => ?_)
  refine WP.seq (WP.mono (opMulP (z := v Z2) (ea := (2 ^ 128 - 1) * 2 ^ 64) (eb := 2 ^ 64 - 1) (ee := 2 ^ 192 - 1) (by sep8) (by decide) (by simp) (by simp)
    (by look) (by look) (by decide) h15) fun s16 h16 => ?_)
  refine WP.seq (WP.mono (sqnP (z := v Z2) (ea := 2 ^ 192 - 1) (by decide) (by decide) (by sep8) (by decide) (by simp) (by look) h16) fun s17 h17 => ?_)
  refine WP.seq (WP.mono (opMulP (z := v Z2) (ea := (2 ^ 192 - 1) * 2 ^ 16) (eb := 2 ^ 16 - 1) (ee := 2 ^ 208 - 1) (by sep8) (by decide) (by simp) (by simp)
    (by look) (by look) (by decide) h17) fun s18 h18 => ?_)
  refine WP.seq (WP.mono (sqnP (z := v Z2) (ea := 2 ^ 208 - 1) (by decide) (by decide) (by sep8) (by decide) (by simp) (by look) h18) fun s19 h19 => ?_)
  refine WP.seq (WP.mono (opMulP (z := v Z2) (ea := (2 ^ 208 - 1) * 2 ^ 8) (eb := 2 ^ 8 - 1) (ee := 2 ^ 216 - 1) (by sep8) (by decide) (by simp) (by simp)
    (by look) (by look) (by decide) h19) fun s20 h20 => ?_)
  refine WP.seq (WP.mono (sqnP (z := v Z2) (ea := 2 ^ 216 - 1) (by decide) (by decide) (by sep8) (by decide) (by simp) (by look) h20) fun s21 h21 => ?_)
  refine WP.seq (WP.mono (opMulP (z := v Z2) (ea := (2 ^ 216 - 1) * 2 ^ 4) (eb := 2 ^ 4 - 1) (ee := 2 ^ 220 - 1) (by sep8) (by decide) (by simp) (by simp)
    (by look) (by look) (by decide) h21) fun s22 h22 => ?_)
  refine WP.seq (WP.mono (sqnP (z := v Z2) (ea := 2 ^ 220 - 1) (by decide) (by decide) (by sep8) (by decide) (by simp) (by look) h22) fun s23 h23 => ?_)
  refine WP.seq (WP.mono (opMulP (z := v Z2) (ea := (2 ^ 220 - 1) * 2 ^ 2) (eb := 2 ^ 2 - 1) (ee := 2 ^ 222 - 1) (by sep8) (by decide) (by simp) (by simp)
    (by look) (by look) (by decide) h23) fun s24 h24 => ?_)
  refine WP.seq (WP.mono (sqnP (z := v Z2) (ea := 2 ^ 222 - 1) (by decide) (by decide) (by sep8) (by decide) (by simp) (by look) h24) fun s25 h25 => ?_)
  refine WP.mono (opMulP (z := v Z2) (ea := (2 ^ 222 - 1) * 2 ^ 1) (eb := 1) (ee := 2 ^ 223 - 1) (by sep8) (by decide) (by simp) (by simp [hZ0])
    (by look) (by look) (by decide) h25) fun s26 ⟨c26, h26⟩ => ⟨c26,
    h26.congr (fun q hq => ?_) fun q hq => ?_⟩
  · simp only [List.mem_cons] at hq ⊢
    rcases hq with rfl | rfl | hq
    · exact .inl rfl
    · simp
    · simp [hq]
  · simp only [List.mem_cons] at hq
    rcases hq with rfl | rfl | hq
    · simp (disch := decide) only [chainV, upd_self]
    · simp (disch := decide) only [chainV, upd_self, upd_of_ne]
    · have e0 : q ≠ T0 := fun e => n0 (e ▸ hq)
      have e1 : q ≠ T1 := fun e => n1 (e ▸ hq)
      have e2 : q ≠ T2 := fun e => n2 (e ▸ hq)
      have e3 : q ≠ T3 := fun e => n3 (e ▸ hq)
      have e4 : q ≠ T4 := fun e => n4 (e ▸ hq)
      have e5 : q ≠ T5 := fun e => n5 (e ▸ hq)
      have e6 : q ≠ T6 := fun e => n6 (e ▸ hq)
      by_cases eR : q = R
      · subst eR
        simp (disch := decide) only [chainV, upd_self]
      · simp only [chainV, upd_of_ne _ _ e0, upd_of_ne _ _ e1, upd_of_ne _ _ e2, upd_of_ne _ _ e3,
          upd_of_ne _ _ e4, upd_of_ne _ _ e5, upd_of_ne _ _ e6, upd_of_ne _ _ eR]
        by_cases eZ : q = Z2
        · subst eZ; rw [upd_self, VG.Proof.X448.pw_one]
        · rw [upd_of_ne _ _ eZ]

/-- The exponent of the inversion's chain. -/
theorem inv_exp : (2 ^ 223 - 1) * 2 ^ 225 + ((2 ^ 222 - 1) * 2 ^ 2 + 1) = P - 2 := by decide +kernel

/-- The slots other than `R`, whose element the chain overwrites. -/
theorem drop_R {qs : List Nat} (hq : Sep8 R qs = true) (hT : TempsOk qs = true) {a : BitVec 64}
    {v : Nat → Fe} {s : State} (hc : Ctx b s) (hS : ∀ q ∈ qs, q ≠ R → FS s.mem b q = v q)
    (h0 : s.gpr .t2 = a) :
    Sep8 R (qs.filter (· ≠ R)) = true ∧ TempsOk (qs.filter (· ≠ R)) = true ∧
      CurE b s a (qs.filter (· ≠ R)) v s := by
  -- `R`'s element is whatever is there; the chain overwrites it.
  have hC : CurE b s a (qs.filter (· ≠ R)) v s :=
    ⟨_, hc, Stp.refl _ _, h0, rfl, fun q hq => by
      simp only [List.mem_filter, decide_eq_true_eq] at hq; exact hS q hq.1 hq.2⟩
  have hfR : Sep8 R (qs.filter (· ≠ R)) = true := by
    simp only [Sep8, Sep1, Bool.and_eq_true, List.all_eq_true] at hq ⊢
    exact ⟨⟨⟨hq.1.1.1, fun q hq' => hq.1.1.2 q (List.mem_filter.mp hq').1⟩, hq.1.2⟩,
      fun q hq' => hq.2 q (List.mem_filter.mp hq').1⟩
  have hfT : TempsOk (qs.filter (· ≠ R)) = true := by
    refine List.all_eq_true.mpr fun t ht => ?_
    obtain ⟨h1, h2⟩ := temps_get hT ht
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨?_, ?_⟩
    · simp only [Sep8, Sep1, Bool.and_eq_true, List.all_eq_true] at h1 ⊢
      exact ⟨⟨⟨h1.1.1.1, fun q hq' => h1.1.1.2 q (List.mem_filter.mp hq').1⟩, h1.1.2⟩,
        fun q hq' => h1.2 q (List.mem_filter.mp hq').1⟩
    · rw [Bool.eq_false_iff]
      intro hc
      exact h2 (List.mem_filter.mp (List.contains_iff_mem.mp hc)).1
  exact ⟨hfR, hfT, hC⟩

/-- The inversion of the element at `Z2` into `R`, keeping the slots `qs`
other than `R` (which may be any slots separate from `R` and the chain's
temporaries). -/
theorem invertQ_ok {qs : List Nat} (hq : Sep8 R qs = true) (hZ : Z2 ∈ qs)
    (hT : TempsOk qs = true) {a : BitVec 64} {v : Nat → Fe} {s : State} (hc : Ctx b s)
    (hS : ∀ q ∈ qs, q ≠ R → FS s.mem b q = v q) (h0 : s.gpr .t2 = a) :
    WP isa Impl.X448.RISCV64.R64.invert s fun s' => Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b qs (upd v R (VG.Proof.X448.pw (v Z2) (P - 2))) := by
  have hZR : Z2 ≠ R := by decide
  obtain ⟨hfR, hfT, hC⟩ := drop_R hq hT hc hS h0
  have hZf : Z2 ∈ qs.filter (· ≠ R) := by simp [hZ, hZR]
  obtain ⟨f6, _⟩ := temps_get hfT (t := T6) (by decide)
  unfold Impl.X448.RISCV64.R64.invert invTail
  refine WP.seq (WP.mono (chain223_ok hfR hZf hfT hC) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (sqnP (z := v Z2) (ea := 2 ^ 223 - 1) (by decide) (by decide) (by sep8)
    (by decide) (by simp) (by look) h1) fun s2 h2 => ?_)
  refine WP.seq (WP.mono (sqnP (z := v Z2) (ea := 2 ^ 222 - 1) (by decide) (by decide) (by sep8)
    (by decide) (by simp) (by look) h2) fun s3 h3 => ?_)
  refine WP.seq (WP.mono (opMulP (z := v Z2) (ea := (2 ^ 222 - 1) * 2 ^ 2) (eb := 1)
    (ee := (2 ^ 222 - 1) * 2 ^ 2 + 1) (by sep8) (by decide) (by simp)
    (by repeat (first | exact hZf | apply List.mem_cons_of_mem))
    (by look) (by look; exact (VG.Proof.X448.pw_one _).symm) rfl h3) fun s4 h4 => ?_)
  refine WP.mono (opMulP (z := v Z2) (ea := (2 ^ 223 - 1) * 2 ^ 225)
    (eb := (2 ^ 222 - 1) * 2 ^ 2 + 1) (ee := P - 2) (by sep8) (by decide) (by simp) (by simp)
    (by look) (by look) inv_exp h4) fun s5 ⟨c5, h5⟩ => ⟨h5.stp, h5.ctx, fun q hq => ?_⟩
  by_cases eR : q = R
  · subst eR
    rw [h5.slots _ List.mem_cons_self, upd_self, upd_self]
  · have hq' : q ∈ qs.filter (· ≠ R) := by simp [hq, eR]
    have e6 : q ≠ T6 := fun e => (temps_get hT (t := T6) (by decide)).2 (e ▸ hq)
    rw [h5.slots q (by repeat (first | exact hq' | apply List.mem_cons_of_mem)), upd_of_ne _ _ eR]
    simp only [chainV, upd_of_ne _ _ e6, upd_of_ne _ _ eR]

/-- The inversion in X448: `z` at `Z2`, and `x2` at `X2` kept. -/
theorem invert_ok {a : BitVec 64} {v : Nat → Fe} {s : State} (hc : Ctx b s)
    (hS : SlotsOk s.mem b [Z2, X2] v) (h0 : s.gpr .t2 = a) :
    WP isa Impl.X448.RISCV64.R64.invert s fun s' => Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b IQ (upd v R (VG.Proof.X448.pw (v Z2) (P - 2))) :=
  invertQ_ok (by decide) (by decide) (by decide) hc (fun q hq hqR => hS q (by
    simp only [IQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · decide
    · exact absurd rfl hqR
    · decide)) h0

end

end

end VG.Proof.X448.RISCV64.R64
