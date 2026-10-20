module

public import VerifiedGarbage.Proof.Bignum.X86.SparseStep
public import VerifiedGarbage.Proof.Bignum.X86.PublicTiming
public import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Framework.X86.RelCT

import VerifiedGarbage.Proof.Bignum.X86.PublicLayout

/-! # The exponentiation's trace depends on the public exponent alone

Two runs whose exponents (the two words at header offset 128) agree take the
same branches: each iteration's product is taken for the same bits, and the
loop ends after the same number of iterations. Everything else is checked by
the taint analysis, with only the workspace pointer public.
-/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicContext

/-- The runs' workspace pointers agree. -/
abbrev Public (s t : State) : Prop := VG.X86.Taint.Agree (workspaceTaint false) s t

/-- What a run of the loop needs of its state: a modulus, and the result and
the base reduced by it. -/
def SparseReady (n bytes : Nat) (base : Addr) (s : State) : Prop :=
  ∃ m, PublicContext.Context n m base bytes s ∧
    wordsVal s.mem base (slot n 7) n < m ∧ wordsVal s.mem base (slot n 6) n < m

theorem multiply_relCT (n o a b : Nat) : RelCT isa Public (multiply n o a b) Public :=
  checkedProgramChange (mul_check false _ _ _ _ _ _) (by rfl)

theorem bitTest_relCT {bytes : Nat} {base : Addr} :
    RelCT isa (fun s t => Public s t ∧ Scr s base bytes ∧ Scr t base bytes ∧ 128 + 4 ≤ bytes ∧
        w32 s.mem base 128 % 2 = w32 t.mem base 128 % 2) (.block bitTest)
      (fun s t => Public s t ∧ s.zf = t.zf) := by
  intro s t tr ur sf tf ⟨A, hs, ht, hb, eq⟩ E F
  obtain ⟨T, A'⟩ := (checkedProgramChange (hint := .block []) (σ := workspaceTaint false) rfl rfl :
    RelCT isa Public (.block bitTest) Public) _ _ _ _ _ _ A E F
  obtain ⟨-, -, Zs⟩ := wp_result (PublicContext.bitTest_ok hs hb) E
  obtain ⟨-, -, Zt⟩ := wp_result (PublicContext.bitTest_ok ht hb) F
  exact ⟨T, A', by rw [Zs, Zt, eq]⟩

theorem sparseRoundBody_relCT (n bytes : Nat) (base : Addr) :
    RelCT isa (fun s t => Public s t ∧ Scr s base bytes ∧ Scr t base bytes ∧ 128 + 4 ≤ bytes ∧
        w32 s.mem base 128 % 2 = w32 t.mem base 128 % 2) (sparseRound n) Public := by
  have Tail : RelCT isa Public (.block (VG.Impl.Mont.X86.Dynamic.shiftExponent 2 exponentOffset ++ exponentLeft)) Public :=
    checkedProgramChange (hint := .block []) (σ := workspaceTaint false) rfl rfl
  unfold sparseRound sparseProduct
  refine VG.RelCT.seq (VG.RelCT.seq bitTest_relCT ?_) (VG.RelCT.seq (multiply_relCT n 6 6 6) Tail)
  refine RelCT.ite (fun s t H => H.2) ?_ ?_
  · exact RelCT.nil fun _ _ H => H.1.1
  · exact (multiply_relCT n 7 7 6).mono (fun _ _ H => H.1.1) fun _ _ h => h

theorem sparseRound_relCT (n bytes : Nat) (base : Addr) (k : Nat) :
    RelCT isa (fun s t => Public s t ∧ SparseReady n bytes base s ∧ SparseReady n bytes base t ∧
        val32 s.mem base 128 2 = k ∧ val32 t.mem base 128 2 = k) (sparseRound n)
      (fun s t => Public s t ∧ SparseReady n bytes base s ∧ SparseReady n bytes base t ∧
        val32 s.mem base 128 2 = k / 2 ∧ val32 t.mem base 128 2 = k / 2 ∧
        s.zf = some (decide (k / 2 = 0)) ∧ t.zf = some (decide (k / 2 = 0))) := by
  intro s t tr ur sf tf ⟨A, Rs, Rt, Ks, Kt⟩ E F
  obtain ⟨m₁, C₁, y₁, b₁⟩ := Rs
  obtain ⟨m₂, C₂, y₂, b₂⟩ := Rt
  have hb : 128 + 4 ≤ bytes := by
    have := C₁.size_le; have := PublicContext.slot_header n 8; change slot n 8 ≤ bytes at *; omega
  have T := sparseRoundBody_relCT n bytes base _ _ _ _ _ _
    ⟨A, C₁.scr, C₂.scr, hb, by rw [← val32_parity, ← val32_parity, Ks, Kt]⟩ E F
  obtain ⟨y, Y₁⟩ := mont_representation C₁.coprime y₁
  obtain ⟨b, B₁⟩ := mont_representation C₁.coprime b₁
  obtain ⟨y', Y₂⟩ := mont_representation C₂.coprime y₂
  obtain ⟨b', B₂⟩ := mont_representation C₂.coprime b₂
  obtain ⟨Cs, Vs, Ws, Es, Zs, -, -⟩ := wp_result (PublicContext.sparseRound_ok C₁ Y₁ B₁) E
  obtain ⟨Ct, Vt, Wt, Et, Zt, -, -⟩ := wp_result (PublicContext.sparseRound_ok C₂ Y₂ B₂) F
  have pos₁ : 0 < m₁ := by have := C₁.gt_one; omega
  have pos₂ : 0 < m₂ := by have := C₂.gt_one; omega
  refine ⟨T.1, T.2, ⟨m₁, Cs, by rw [Vs]; exact Nat.mod_lt _ pos₁, by rw [Ws]; exact Nat.mod_lt _ pos₁⟩,
    ⟨m₂, Ct, by rw [Vt]; exact Nat.mod_lt _ pos₂, by rw [Wt]; exact Nat.mod_lt _ pos₂⟩,
    by rw [Es, Ks], by rw [Et, Kt], by rw [Zs, Ks], by rw [Zt, Kt]⟩

theorem sparseLoop_relCT (n bytes : Nat) (base : Addr) (k : Nat) :
    RelCT isa (fun s t => Public s t ∧ SparseReady n bytes base s ∧ SparseReady n bytes base t ∧
        val32 s.mem base 128 2 = k ∧ val32 t.mem base 128 2 = k)
      (.loop (sparseRound n) .ne) Public := by
  refine VG.RelCT.loop (M := isa) (fun k (s t : State) => Public s t ∧ SparseReady n bytes base s ∧
    SparseReady n bytes base t ∧ val32 s.mem base 128 2 = k ∧ val32 t.mem base 128 2 = k) ?_ k
  intro k
  refine (sparseRound_relCT n bytes base k).mono (fun _ _ h => h) ?_
  rintro s t ⟨A, Rs, Rt, Es, Et, Zs, Zt⟩
  have ev : isa.eval .ne s = isa.eval .ne t := by
    change s.zf.map (!·) = t.zf.map (!·)
    rw [Zs, Zt]
  refine ⟨ev, fun _ => A, fun cont => ⟨k / 2, ?_, A, Rs, Rt, Es, Et⟩⟩
  change s.zf.map (!·) = some true at cont
  rw [Zs] at cont
  by_cases h : k / 2 = 0
  · rw [decide_eq_true h] at cont; cases cont
  · omega

/-- What a run of the exponentiation needs of its state: a modulus, and
`one` and `R²` (or any value) reduced by it. -/
def SparseStart (n bytes : Nat) (base : Addr) (s : State) : Prop :=
  ∃ m, PublicContext.Context n m base bytes s ∧
    wordsVal s.mem base (slot n 4) n < m ∧ wordsVal s.mem base (slot n 5) n < m

theorem sparseExponentiate_relCT (n bytes : Nat) (base : Addr) :
    RelCT isa (fun s t => Public s t ∧ SparseStart n bytes base s ∧ SparseStart n bytes base t ∧
        val32 s.mem base 128 2 = val32 t.mem base 128 2)
      (sparseExponentiate n) Public := by
  intro s t tr ur sf tf ⟨A, Rs, Rt, Ex⟩ E F
  obtain ⟨m₁, C₁, o₁, r₁⟩ := Rs
  obtain ⟨m₂, C₂, o₂, r₂⟩ := Rt
  unfold sparseExponentiate at E F
  cases E with | seq E₁ E' => cases F with | seq F₁ F' =>
  cases E' with | seq E₂ E'' => cases F' with | seq F₂ F'' =>
  cases E'' with | seq E₃ E₄ => cases F'' with | seq F₃ F₄ =>
  have T₁ := multiply_relCT n 7 5 4 _ _ _ _ _ _ A E₁ F₁
  have T₂ := multiply_relCT n 6 6 5 _ _ _ _ _ _ T₁.2 E₂ F₂
  have mul₁ {m : Nat} {σ : State} (C : PublicContext.Context n m base bytes σ) (o : wordsVal σ.mem base (slot n 4) n < m) :=
    PublicContext.multiply_ok C (o := 7) (a := 5) (b := 4)
      (by unfold operand; decide) (by unfold operand; decide) (by unfold operand; decide)
      (by decide) (by decide) (by decide) (by decide) o
  obtain ⟨Cs₁, Ks₁, ys₁, -⟩ := wp_result (mul₁ C₁ o₁) E₁
  obtain ⟨Ct₁, Kt₁, yt₁, -⟩ := wp_result (mul₁ C₂ o₂) F₁
  have mul₂ {m : Nat} {σ : State} (C : PublicContext.Context n m base bytes σ) (r : wordsVal σ.mem base (slot n 5) n < m) :=
    PublicContext.multiply_ok C (o := 6) (a := 6) (b := 5)
      (by unfold operand; decide) (by unfold operand; decide) (by unfold operand; decide)
      (by decide) (by decide) (by decide) (by decide) r
  have keep5 {m : Nat} {σ τ : State} (C : PublicContext.Context n m base bytes σ) (K : OpKeep (modulus n) base (slot n 2) (slot n 7) σ τ) :=
    PublicContext.slot_value (i := 5) C (by unfold operand; decide) (by decide) (by decide) K
  have keep7 {m : Nat} {σ τ : State} (C : PublicContext.Context n m base bytes σ) (K : OpKeep (modulus n) base (slot n 2) (slot n 6) σ τ) :=
    PublicContext.slot_value (i := 7) C (by unfold operand; decide) (by decide) (by decide) K
  obtain ⟨Cs₂, Ks₂, bs₂, -⟩ := wp_result (mul₂ Cs₁ (by rw [keep5 C₁ Ks₁]; exact r₁)) E₂
  obtain ⟨Ct₂, Kt₂, bt₂, -⟩ := wp_result (mul₂ Ct₁ (by rw [keep5 C₂ Kt₁]; exact r₂)) F₂
  have T₃ := sparseLoop_relCT n bytes base (val32 s.mem base 128 2) _ _ _ _ _ _
    ⟨T₂.2, ⟨m₁, Cs₂, by rw [keep7 Cs₁ Ks₂]; exact ys₁, bs₂⟩,
      ⟨m₂, Ct₂, by rw [keep7 Ct₁ Kt₂]; exact yt₁, bt₂⟩,
      by rw [PublicContext.header_value (by decide) Ks₂, PublicContext.header_value (by decide) Ks₁],
      by rw [PublicContext.header_value (by decide) Kt₂, PublicContext.header_value (by decide) Kt₁, Ex]⟩
    E₃ F₃
  have T₄ := multiply_relCT n 7 7 4 _ _ _ _ _ _ T₃.2 E₄ F₄
  rw [T₁.1, T₂.1, T₃.1, T₄.1]
  exact ⟨rfl, T₄.2⟩

end VG.Proof.Bignum.X86
