module

public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedFn
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Bignum.X86.PublicTiming
public import VerifiedGarbage.Proof.Bignum.X86.PublicApplyTiming
public import VerifiedGarbage.Proof.Bignum.X86.SparseTiming
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedApply

import VerifiedGarbage.Proof.Bignum.X86.PublicDataTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedSetup
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedSetupFrame

/-! # Stored-power arithmetic and public key checks have fixed instruction traces -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicContext

theorem precomputedSetup_check (n : Nat) :
    VG.Taint.check taint (workspaceTaint false) (precomputedSetup n)
      (.seq (workspaceTaint false) (.block []) (oneHint false)) = some (zerosTaint false) := by
  unfold precomputedSetup
  exact exponent_check_seq taint (setupInverse_taint false (slot n 0) inverseOffset) (by rfl)
    (one_check false n (slot n 4))

/-- What a run of the stored-power exponentiation needs of its state: the
modulus is odd and above one, and the stored power below it. -/
def PowerReady (n bytes : Nat) (base : Addr) (s : State) : Prop :=
  Scr s base bytes ∧ 0 < n ∧ size n ≤ bytes ∧
    ∃ m, wordsVal s.mem base (slot n 0) n = m ∧ 1 < m ∧ m % 2 = 1 ∧
      wordsVal s.mem base (slot n 5) n < m

theorem precomputedPower_relCT (n bytes : Nat) (base : Addr) :
    RelCT isa (fun s t => Public s t ∧ PowerReady n bytes base s ∧ PowerReady n bytes base t ∧
        val32 s.mem base 128 2 = val32 t.mem base 128 2)
      (precomputedPower n) Public := by
  have Setup : RelCT isa Public (precomputedSetup n) Public :=
    checkedProgramChange (precomputedSetup_check n) (by rfl)
  have ready {s u : State} {tr : List Leak} (R : PowerReady n bytes base s)
      (E : Exec isa (precomputedSetup n) s tr u) :
      SparseStart n bytes base u ∧ val32 u.mem base 128 2 = val32 s.mem base 128 2 := by
    obtain ⟨hs, hn, hz, m, hv, hm1, hodd, hr⟩ := R
    obtain ⟨C, One, O, -⟩ := wp_result (PublicContext.precomputedSetup_ok hs hn hz hv hm1 hodd) E
    have bound : size n ≤ 2 ^ 64 := by have := hs.nowrap; omega
    refine ⟨⟨m, C, by rw [One]; exact hm1, ?_⟩, ?_⟩
    · rw [PublicContext.precomputedSetup_value O (by decide : 5 < 8) (by decide) bound]; exact hr
    · exact PublicContext.setup_exponent (PublicContext.precomputedSetup_ranges O)
  intro s t tr ur sf tf ⟨A, Rs, Rt, Ex⟩ E F
  unfold precomputedPower at E F
  cases E with | seq E₁ E₂ => cases F with | seq F₁ F₂ =>
  have T₁ := Setup _ _ _ _ _ _ A E₁ F₁
  obtain ⟨Ss, Es⟩ := ready Rs E₁
  obtain ⟨St, Et⟩ := ready Rt F₁
  have T₂ := sparseExponentiate_relCT n bytes base _ _ _ _ _ _ ⟨T₁.2, Ss, St, by rw [Es, Et, Ex]⟩ E₂ F₂
  rw [T₁.1, T₂.1]
  exact ⟨rfl, T₂.2⟩

theorem precomputedAcceptAndPower_relCT (n bytes : Nat) (base : Addr) :
    RelCT isa (fun s t => Public s t ∧ PowerReady n bytes base s ∧ PowerReady n bytes base t ∧
        val32 s.mem base 128 2 = val32 t.mem base 128 2)
      (PrecomputedFn.acceptAndPower n) Public := by
  have Save : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (.block [.store (VG.Impl.Mont.X86.sc PublicFn.acceptanceOffset) .ecx])
      (VG.X86.Taint.Agree (workspaceTaint false)) := checkedBlockInvariant rfl rfl
  have ready {s u v : State} {tr ur : List Leak} (R : PowerReady n bytes base s)
      (E : Exec isa (inputCompare n) s tr u)
      (F : Exec isa (.block [.store (VG.Impl.Mont.X86.sc PublicFn.acceptanceOffset) .ecx]) u ur v) :
      PowerReady n bytes base v ∧ val32 v.mem base 128 2 = val32 s.mem base 128 2 := by
    obtain ⟨hs, hn, hz, m, hv, hm1, hodd, hr⟩ := R
    obtain ⟨hv', N, Q, -, X, -⟩ := wp_result (wp_result (PublicContext.acceptSave_ok hs hn hz) E) F
    exact ⟨⟨hv', hn, hz, m, by rw [N, hv], hm1, hodd, by rw [Q]; exact hr⟩, X⟩
  intro s t tr ur sf tf ⟨A, Rs, Rt, Ex⟩ E F
  unfold PrecomputedFn.acceptAndPower at E F
  cases E with | seq E₁ E' => cases F with | seq F₁ F' =>
  cases E' with | seq E₂ E₃ => cases F' with | seq F₂ F₃ =>
  have T₁ := inputCompare_relCT n _ _ _ _ _ _ A E₁ F₁
  have T₂ := Save _ _ _ _ _ _ T₁.2 E₂ F₂
  obtain ⟨Rs', Es⟩ := ready Rs E₁ E₂
  obtain ⟨Rt', Et⟩ := ready Rt F₁ F₂
  have T₃ := precomputedPower_relCT n bytes base _ _ _ _ _ _ ⟨T₂.2, Rs', Rt', by rw [Es, Et, Ex]⟩ E₃ F₃
  rw [T₁.1, T₂.1, T₃.1]
  exact ⟨rfl, T₃.2⟩

theorem precomputedChecks_relCT (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (precomputedChecks n)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply erased_relCT (precomputedChecks n) (precomputedChecks 1)
    (VG.Taint.hintOf taint (workspaceTaint false) (precomputedChecks 1)) rfl rfl rfl
  rfl

end VG.Proof.Bignum.X86
