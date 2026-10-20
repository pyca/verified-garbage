module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeMul
meta import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeMul
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.ByteWords
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeBase
meta import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeBase
public import VerifiedGarbage.Proof.Bignum.X86.ExponentBits
meta import VerifiedGarbage.Proof.Bignum.X86.ExponentBits
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.MulEnv
meta import VerifiedGarbage.Proof.Bignum.X86.PublicRt.MulEnv
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Stages
meta import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Stages
public import VerifiedGarbage.Proof.Mont.X86.ExponentShift
meta import VerifiedGarbage.Proof.Mont.X86.ExponentShift

/-! # The trace of the exponentiation, in public RSA at a run-time width

Its pieces between calls are checked by the taint analysis (`τA`), its
multiplications related by `mul_relCT`; what each needs of a run (`St`:
`Env`, the base and one below the modulus, what is left of the exponent at
128) each keeps (`bit_st`, `mulSt_ok`, `tail_st`), so the runs of a round
(`sparseRound_relCT`) and of the loop (`sparseLoop_relCT`) from the same
exponent leak the same traces, the exponent being public.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Mont.X86.Dynamic

/-- Two runs, each meeting `F`. -/
abbrev Both (F : State → Prop) (s t : State) : Prop := F s ∧ F t

theorem relCT_both {P F : State → Prop} {c : Prog isa} (hct : RelCT isa (Both P) c fun _ _ => True)
    (hw : ∀ s, P s → WP isa c s F) : RelCT isa (Both P) c (Both F) :=
  (hct.wp (F₁ := F) (F₂ := F) fun s t h => ⟨hw s h.1, hw t h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

theorem taint_both {P F : State → Prop} {c : Prog isa} (hag : ∀ s t, P s → P t → VG.X86.Taint.Agree τA s t)
    (hc : VG.Taint.Hint VG.X86.Taint.T) (hT : (VG.Taint.check taint τA c hc).isSome = true)
    (hw : ∀ s, P s → WP isa c s F) : RelCT isa (Both P) c (Both F) :=
  relCT_both (RelCT.taint (A := taint) τA (fun s t h => hag s t h.1 h.2) hT) hw

section
variable {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- What the exponentiation keeps of a run: `Env` with the modulus `M`, the arguments apart, `esp`, the
base (number 1) and one (number 3) below `M`, and what is left `k` of the exponent at 128. -/
def St (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (M k : Nat) (s : State) : Prop :=
  Env base bytes len args M s ∧ ArgsOk s ∧ s.gpr .esp = sp ∧
    val32 s.mem base (numAt len 1) (nw len) < M ∧ val32 s.mem base (numAt len 3) (nw len) < M ∧
    val32 s.mem base 128 2 = k

theorem St.agree {sp : BitVec 32} {M₁ M₂ k₁ k₂ : Nat} {s t : State} (S₁ : St base bytes len args sp M₁ k₁ s)
    (S₂ : St base bytes len args sp M₂ k₂ t) : VG.X86.Taint.Agree τA s t :=
  agreeA S₁.1.pi S₂.1.pi S₁.2.1 S₂.2.1 (S₁.2.2.1.trans S₂.2.2.1.symm)

/-- A multiplication in `Env`: what it keeps. -/
theorem mulKeep_ok {s : State} {M : Nat} (E : Env base bytes len args M s) (A : ArgsOk s)
    (hbytes : bytes = (args 9).toNat * 8) {o a b : Nat} (ho : 1 ≤ o) (ho4 : o ≤ 4) (ha : a ≤ 4) (hb : b ≤ 4)
    (hB : val32 s.mem base (numAt len b) (nw len) < M) :
    WP isa (PublicRt.mul o a b) s fun u =>
      Env base bytes len args M u ∧ ArgsOk u ∧ Keeps [.eax, .ecx, .edx] s u ∧
      val32 u.mem base (numAt len o) (nw len) < M ∧
      (∀ j ≤ 4, j ≠ o → val32 u.mem base (numAt len j) (nw len) = val32 s.mem base (numAt len j) (nw len)) ∧
      val32 u.mem base 128 2 = val32 s.mem base 128 2 := by
  have h := E.pi
  have nw' := h.scratch.nowrap
  have wbe := wb_eq len
  have f5 := (h.fits (j := 5) (by decide)).2
  have fo := (h.fits (j := o) (by omega)).1
  have n0 : numOff = 256 := rfl
  refine WP.mono (mulRaw_ok E hbytes ho ho4 ha hb hB) fun u ⟨Eu, _, K, F, L, _⟩ =>
    ⟨Eu, A.keep K (by decide), K, L, fun j hj hjo => ?_, ?_⟩
  · have h5 : numAt len j + 4 * nw len ≤ numAt len 5 := by
      have := Nat.mul_le_mul_right (wb len) (show j + 1 ≤ 5 by omega)
      simp only [numAt]; rw [Nat.add_mul, Nat.one_mul] at this; omega
    refine mulFrame_val32 E.room nw' F ?_ h5 (by omega) fo f5
    rcases Nat.lt_or_gt_of_ne hjo with hl | hl
    · left
      have := Nat.mul_le_mul_right (wb len) (show j + 1 ≤ o by omega)
      simp only [numAt] at this ⊢; rw [← wbe]; rw [Nat.add_mul, Nat.one_mul] at this; omega
    · right
      have := Nat.mul_le_mul_right (wb len) (show o + 1 ≤ j by omega)
      simp only [numAt] at this ⊢; rw [Nat.add_mul, Nat.one_mul] at this; omega
  · have f0 := (h.fits (j := 0) (by decide)).1
    simp only [numAt, numOff] at f0
    rw [← read_eq_val32, ← read_eq_val32, mulFrame_hdr E.room nw' F (by decide) (by omega) fo f5]

variable (sp : BitVec 32)

theorem bit_st {M k : Nat} {s : State} (S : St base bytes len args sp M k s) :
    WP isa (.block PublicContext.bitTest) s fun u =>
      St base bytes len args sp M k u ∧ u.zf = some (decide (k % 2 = 0)) := by
  obtain ⟨E, A, sp₀, X, O, c₀⟩ := S
  have h := E.pi
  have f0 := (h.fits (j := 0) (by decide)).1
  simp only [numAt, numOff] at f0
  refine WP.mono (PublicContext.bitTest_ok h.scratch (by omega)) fun u ⟨M₁, K₁, Z₁⟩ => ?_
  refine ⟨⟨E.keep K₁ (by decide) (by decide) (by rw [M₁]; exact Frame.refl _ _), A.keep K₁ (by decide),
    (K₁.1 _ (by decide)).trans sp₀, by rw [M₁]; exact X, by rw [M₁]; exact O, by rw [M₁]; exact c₀⟩, ?_⟩
  rw [Z₁, ← c₀, val32_parity]

theorem mulSt_ok (hbytes : bytes = (args 9).toNat * 8) {o a b : Nat} (ho : 1 ≤ o) (ho4 : o ≤ 4) (ha : a ≤ 4)
    (hb : b ≤ 4) (h1 : o ≠ 3) (h3 : o ≠ 1 ∨ b = 1) {M k : Nat} {s : State} (S : St base bytes len args sp M k s)
    (hB : val32 s.mem base (numAt len b) (nw len) < M) :
    WP isa (PublicRt.mul o a b) s (St base bytes len args sp M k) := by
  obtain ⟨E, A, sp₀, X, O, c₀⟩ := S
  refine WP.mono (mulKeep_ok E A hbytes ho ho4 ha hb hB) fun u ⟨Eu, Au, K, L, V, W⟩ =>
    ⟨Eu, Au, (K.1 _ (by decide)).trans sp₀, ?_, by rw [V 3 (by decide) (Ne.symm h1)]; exact O, W.trans c₀⟩
  by_cases o1 : o = 1
  · subst o1; exact L
  · rw [V 1 (by decide) (Ne.symm o1)]; exact X

theorem tail_st {M k : Nat} {s : State} (S : St base bytes len args sp M k s) :
    WP isa (.block (VG.Impl.Mont.X86.Dynamic.shiftExponent 2 PublicContext.exponentOffset ++
        PublicContext.exponentLeft)) s fun u =>
      St base bytes len args sp M (k / 2) u ∧ u.zf = some (decide (k / 2 = 0)) := by
  obtain ⟨E, A, sp₀, X, O, c₀⟩ := S
  have h := E.pi
  have nw' := h.scratch.nowrap
  have wbe := wb_eq len
  have f5 := (h.fits (j := 5) (by decide)).2
  have e1 : numAt len 1 = 256 + wb len := by simp only [numAt, numOff] <;> omega
  have e3 : numAt len 3 = 256 + 3 * wb len := by simp only [numAt, numOff] <;> omega
  have e5 : numAt len 5 = 256 + 5 * wb len := by simp only [numAt, numOff] <;> omega
  refine WP.block_append (WP.mono (shiftExponent_ok h.scratch 2 128 (by omega)) fun u₆ ⟨O₆, V₆, K₆⟩ => ?_)
  have E₆ := E.keep K₆ (by decide) (by decide) (Outside.chg O₆ (.inl ⟨by decide, by decide⟩))
  refine WP.mono (PublicContext.exponentLeft_ok E₆.pi.scratch (by omega)) fun t ⟨M₇, K₇, Z₇⟩ => ?_
  have W : val32 u₆.mem base 128 2 = k / 2 := by rw [V₆, c₀]
  exact ⟨⟨E₆.keep K₇ (by decide) (by decide) (by rw [M₇]; exact Frame.refl _ _),
    (A.keep K₆ (by decide)).keep K₇ (by decide), (K₇.1 _ (by decide)).trans ((K₆.1 _ (by decide)).trans sp₀),
    by rw [M₇, O₆.val32 (.inr (by omega)) (by omega)]; exact X,
    by rw [M₇, O₆.val32 (.inr (by omega)) (by omega)]; exact O, by rw [M₇, W]⟩, by rw [Z₇, W]⟩

theorem sparseRound_relCT (hbytes : bytes = (args 9).toNat * 8) (k : Nat) :
    RelCT isa (Both fun s => ∃ M, St base bytes len args sp M k s) sparseRound
      (Both fun s => (∃ M, St base bytes len args sp M (k / 2) s) ∧ s.zf = some (decide (k / 2 = 0))) := by
  have mul : ∀ {o a b : Nat} (ho : 1 ≤ o) (ho4 : o ≤ 4) (ha : a ≤ 4) (hb : b ≤ 4) (h1 : o ≠ 3)
      (h3 : o ≠ 1 ∨ b = 1) (hb13 : b = 1 ∨ b = 3)
      (hT : (VG.Taint.check taint τF (.block (mulArgs o a b)) (.block [])).isSome = true),
      RelCT isa (Both fun s => ∃ M, St base bytes len args sp M k s) (PublicRt.mul o a b)
        (Both fun s => ∃ M, St base bytes len args sp M k s) := by
    intro o a b ho ho4 ha hb h1 h3 hb13 hT
    have lt : ∀ {M : Nat} {s : State}, St base bytes len args sp M k s →
        val32 s.mem base (numAt len b) (nw len) < M := by
      intro M s S; rcases hb13 with rfl | rfl
      · exact S.2.2.2.1
      · exact S.2.2.2.2.1
    exact relCT_both ((mul_relCT hbytes sp ho4 ha hb (by omega) hT).mono (fun _ _ ⟨⟨_, S₁⟩, ⟨_, S₂⟩⟩ =>
        ⟨S₁.2.2.1, S₂.2.2.1, ⟨⟨_, S₁.1, lt S₁⟩, S₁.2.1⟩, ⟨⟨_, S₂.1, lt S₂⟩, S₂.2.1⟩⟩) fun _ _ h => h)
      fun _ ⟨M, S⟩ => WP.mono (mulSt_ok sp hbytes ho ho4 ha hb h1 h3 S (lt S)) fun _ h => ⟨M, h⟩
  unfold sparseRound
  refine VG.RelCT.seq (R := Both fun s => ∃ M, St base bytes len args sp M k s) ?_ ?_
  · refine VG.RelCT.seq (taint_both (F := fun s => (∃ M, St base bytes len args sp M k s) ∧
        s.zf = some (decide (k % 2 = 0))) (fun _ _ ⟨_, S₁⟩ ⟨_, S₂⟩ => S₁.agree S₂) (.block [])
      (by taint_decide) fun _ ⟨M, S⟩ => WP.mono (bit_st sp S) fun _ ⟨h, z⟩ => ⟨⟨M, h⟩, z⟩) ?_
    refine VG.RelCT.ite (M := isa) (c := .e) (fun _ _ h => h.1.2.trans h.2.2.symm) ?_ ?_
    · exact RelCT.nil fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩
    · exact (mul (o := 2) (a := 2) (b := 1) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by taint_decide)).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
  refine VG.RelCT.seq (mul (o := 1) (a := 1) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by taint_decide)) ?_
  exact taint_both (fun _ _ ⟨_, S₁⟩ ⟨_, S₂⟩ => S₁.agree S₂) (.block []) (by taint_decide)
    fun _ ⟨M, S⟩ => WP.mono (tail_st sp S) fun _ ⟨h, z⟩ => ⟨⟨M, h⟩, z⟩

theorem sparseLoop_relCT (hbytes : bytes = (args 9).toNat * 8) (k : Nat) :
    RelCT isa (Both fun s => ∃ M, St base bytes len args sp M k s) (.loop sparseRound .ne)
      (Both fun s => ∃ M, St base bytes len args sp M 0 s) := by
  refine VG.RelCT.loop (M := isa) (I := fun k s t => Both (fun s => ∃ M, St base bytes len args sp M k s) s t)
    (fun k => ?_) k
  refine (sparseRound_relCT sp hbytes k).mono (fun _ _ h => h) ?_
  rintro s t ⟨⟨S₁, z₁⟩, ⟨S₂, z₂⟩⟩
  have e₁ : isa.eval .ne s = some (!decide (k / 2 = 0)) := by show s.zf.map (!·) = _; rw [z₁]; rfl
  have e₂ : isa.eval .ne t = some (!decide (k / 2 = 0)) := by show t.zf.map (!·) = _; rw [z₂]; rfl
  refine ⟨e₁.trans e₂.symm, fun h => ?_, fun h => ?_⟩
  · rw [e₁] at h
    have d : k / 2 = 0 := by simpa using h
    rw [d] at S₁ S₂
    exact ⟨S₁, S₂⟩
  · rw [e₁] at h
    have : k / 2 ≠ 0 := by simpa using h
    exact ⟨k / 2, by omega, S₁, S₂⟩

end

end VG.Proof.Bignum.X86.PublicRt
