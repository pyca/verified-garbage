module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Base
public import VerifiedGarbage.Proof.Aes.PPC64LE.CodeLit
import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Ctr32
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector

meta import VerifiedGarbage.Proof.Aes.PPC64LE.Base
meta import VerifiedGarbage.Proof.Aes.PPC64LE.CodeLit
meta import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Ctr32
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
public import VerifiedGarbage.Proof.Gcm.Contract

/-! # Baseline POWER8 AES CTR contract -/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE
open VG VG.PPC64LE

theorem ctr32_correct (s : State) (hs : Proof.Aes.ctr32PPC64LE.pre s) :
    ∃ t s', Exec isa Impl.Aes.PPC64LE.ctr32 s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.ctr32PPC64LE.post s s' := by
  obtain ⟨t, s', he, hk, hp⟩ := Crypto.ctr32_ok s hs
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by lit_decide)
    (by rw [← Code.allInstrs_eq]; lit_decide), hp⟩

theorem ctr32_ct : ConstantTime isa Proof.Aes.ctr32PPC64LE.pre Proof.Aes.ctr32PPC64LE.pub
    Impl.Aes.PPC64LE.ctr32 := by
  refine VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem ctr32To_correct (s : State) (hs : Proof.Aes.ctr32ToPPC64LE.pre s) :
    ∃ t s', Exec isa Impl.Aes.PPC64LE.ctr32To s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.ctr32ToPPC64LE.post s s' := by
  obtain ⟨t, s', he, hk, hp⟩ := Crypto.ctr32To_ok s hs
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by lit_decide)
    (by rw [← Code.allInstrs_eq]; lit_decide), hp⟩

theorem ctr32To_ct : ConstantTime isa Proof.Aes.ctr32ToPPC64LE.pre Proof.Aes.ctr32ToPPC64LE.pub
    Impl.Aes.PPC64LE.ctr32To := by
  refine VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption


end VG.Proof.Aes.PPC64LE
