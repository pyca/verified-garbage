module
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming

public import VerifiedGarbage.Proof.Bignum.X86.PublicDataTiming
public import VerifiedGarbage.Proof.Bignum.X86.PublicTiming
public import VerifiedGarbage.Proof.Bignum.X86.SparseTiming
public import VerifiedGarbage.Proof.Bignum.X86.PublicPower
public import VerifiedGarbage.Proof.Bignum.X86.AcceptSave

/-! # Input acceptance and exponentiation have no secret-dependent trace -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicContext

/-- What a run of the public exponentiation needs of its state: the modulus
is odd and above one. -/
def PublicReady (n bytes : Nat) (base : Addr) (s : State) : Prop :=
  Scr s base bytes ∧ 0 < n ∧ 128 * n < 2 ^ 32 ∧ size n ≤ bytes ∧
    ∃ m, wordsVal s.mem base (slot n 0) n = m ∧ 1 < m ∧ m % 2 = 1

theorem publicPower_relCT (n bytes : Nat) (base : Addr) :
    RelCT isa (fun s t => Public s t ∧ PublicReady n bytes base s ∧ PublicReady n bytes base t ∧
        val32 s.mem base 128 2 = val32 t.mem base 128 2)
      (publicPower n) Public := by
  have Setup : RelCT isa Public (setup n) Public :=
    checkedProgramChange (PublicContext.setup_check n) (by rfl)
  have ready {s u : State} {tr : List Leak} (R : PublicReady n bytes base s)
      (E : Exec isa (setup n) s tr u) :
      SparseStart n bytes base u ∧ val32 u.mem base 128 2 = val32 s.mem base 128 2 := by
    obtain ⟨hs, hn, hn32, hz, m, hv, hm1, hodd⟩ := R
    obtain ⟨C, One, R2, O, -⟩ := wp_result (PublicContext.setup_ok hs hn hn32 hz hv hm1 hodd) E
    exact ⟨⟨m, C, by rw [One]; exact hm1, by rw [R2]; exact Nat.mod_lt _ (by omega)⟩,
      PublicContext.setup_exponent O⟩
  intro s t tr ur sf tf ⟨A, Rs, Rt, Ex⟩ E F
  unfold publicPower at E F
  cases E with | seq E₁ E₂ => cases F with | seq F₁ F₂ =>
  have T₁ := Setup _ _ _ _ _ _ A E₁ F₁
  obtain ⟨Ss, Es⟩ := ready Rs E₁
  obtain ⟨St, Et⟩ := ready Rt F₁
  have T₂ := sparseExponentiate_relCT n bytes base _ _ _ _ _ _ ⟨T₁.2, Ss, St, by rw [Es, Et, Ex]⟩ E₂ F₂
  rw [T₁.1, T₂.1]
  exact ⟨rfl, T₂.2⟩

theorem acceptAndPower_relCT (n bytes : Nat) (base : Addr) :
    RelCT isa (fun s t => Public s t ∧ PublicReady n bytes base s ∧ PublicReady n bytes base t ∧
        val32 s.mem base 128 2 = val32 t.mem base 128 2)
      (PublicFn.acceptAndPower n) Public := by
  have Save : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (.block [.store (VG.Impl.Mont.X86.sc PublicFn.acceptanceOffset) .ecx])
      (VG.X86.Taint.Agree (workspaceTaint false)) := checkedBlockInvariant rfl rfl
  have ready {s u v : State} {tr ur : List Leak} (R : PublicReady n bytes base s)
      (E : Exec isa (inputCompare n) s tr u)
      (F : Exec isa (.block [.store (VG.Impl.Mont.X86.sc PublicFn.acceptanceOffset) .ecx]) u ur v) :
      PublicReady n bytes base v ∧ val32 v.mem base 128 2 = val32 s.mem base 128 2 := by
    obtain ⟨hs, hn, hn32, hz, m, hv, hm1, hodd⟩ := R
    obtain ⟨hv', N, -, -, X, -⟩ := wp_result (wp_result (PublicContext.acceptSave_ok hs hn hz) E) F
    exact ⟨⟨hv', hn, hn32, hz, m, by rw [N, hv], hm1, hodd⟩, X⟩
  intro s t tr ur sf tf ⟨A, Rs, Rt, Ex⟩ E F
  unfold PublicFn.acceptAndPower at E F
  cases E with | seq E₁ E' => cases F with | seq F₁ F' =>
  cases E' with | seq E₂ E₃ => cases F' with | seq F₂ F₃ =>
  have T₁ := inputCompare_relCT n _ _ _ _ _ _ A E₁ F₁
  have T₂ := Save _ _ _ _ _ _ T₁.2 E₂ F₂
  obtain ⟨Rs', Es⟩ := ready Rs E₁ E₂
  obtain ⟨Rt', Et⟩ := ready Rt F₁ F₂
  have T₃ := publicPower_relCT n bytes base _ _ _ _ _ _ ⟨T₂.2, Rs', Rt', by rw [Es, Et, Ex]⟩ E₃ F₃
  rw [T₁.1, T₂.1, T₃.1]
  exact ⟨rfl, T₃.2⟩

end VG.Proof.Bignum.X86
