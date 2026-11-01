module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Base
public import VerifiedGarbage.Proof.Aes.PPC64LE.CodeLit
import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.ExpandKey
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector

meta import VerifiedGarbage.Proof.Aes.PPC64LE.Base
meta import VerifiedGarbage.Proof.Aes.PPC64LE.CodeLit
meta import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.ExpandKey
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
public import VerifiedGarbage.Proof.Aes.Contract

/-! # Baseline POWER8 AES key-expansion contracts -/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE
open VG VG.PPC64LE

/-- A state satisfying the precondition. -/
def ekSatState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 16 | .r5 => 0x2000 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 240⟩, ⟨0x3000, 512⟩]

theorem expandKey_correct (s : State) (hs : Proof.Aes.expandKeyPPC64LE.pre s) :
    ∃ t s', Exec isa Impl.Aes.PPC64LE.expandKey s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.expandKeyPPC64LE.post s s' := by
  obtain ⟨hr, hw, hd, _, _, hlen⟩ := hs
  have hc : Crypto.KeyConfig s (s.gpr .r3) (s.gpr .r5) (s.gpr .r4).toNat :=
    ⟨hlen, by rw [hr, hw]; simp, by rw [hw]; simp, hd⟩
  obtain ⟨t, s', he, hk, hp⟩ := Crypto.expandKey_ok s hc
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by lit_decide)
    (by rw [← Code.allInstrs_eq]; lit_decide), hp⟩

theorem expandKey_ct_of (pre : State → Prop) (pub : State → State → Prop)
    (hp : ∀ s₁ s₂, pub s₁ s₂ → s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
      s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.sp = s₂.sp) :
    ConstantTime isa pre pub Impl.Aes.PPC64LE.expandKey := by
  refine VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hpub
  obtain ⟨h1, h2, h3, hsp⟩ := hp s₁ s₂ hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> with_reducible assumption

theorem expandKey_ct : ConstantTime isa Proof.Aes.expandKeyPPC64LE.pre Proof.Aes.expandKeyPPC64LE.pub
    Impl.Aes.PPC64LE.expandKey :=
  expandKey_ct_of _ _ fun _ _ ⟨h1, h2, h3, _, hsp⟩ => ⟨h1, h2, h3, hsp⟩

theorem expandKey_verified :
    Verified PPC64LE.target Impl.Aes.PPC64LE.expandKey (Proof.Aes.expandKeyScratchContract PPC64LE.abi) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Proof.Aes.expandKeyScratchContract, Proof.Aes.expandKeyScratchSig,
      Proof.Aes.expandKeyPPC64LE, PPC64LE.abi, PPC64LE.argRegs] [ekSatState] using ekSatState)

/-- A direct call needs only the key and the output schedule. -/
def expandKeyDirectSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 16 | .r5 => 0x2000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 240⟩]

theorem expandKey_direct_correct (s : State) (hs : Proof.Aes.expandKeyDirectPPC64LE.pre s) :
    ∃ t s', Exec isa Impl.Aes.PPC64LE.expandKey s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.expandKeyDirectPPC64LE.post s s' := by
  obtain ⟨hr, hw, hd, hlen⟩ := hs
  have hc : Crypto.KeyConfig s (s.gpr .r3) (s.gpr .r5) (s.gpr .r4).toNat :=
    ⟨hlen, by rw [hr, hw]; simp, by rw [hw]; simp, hd⟩
  obtain ⟨t, s', he, hk, hp⟩ := Crypto.expandKey_ok s hc
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by lit_decide)
    (by rw [← Code.allInstrs_eq]; lit_decide), hp⟩

theorem expandKey_direct_ct : ConstantTime isa Proof.Aes.expandKeyDirectPPC64LE.pre
    Proof.Aes.expandKeyDirectPPC64LE.pub Impl.Aes.PPC64LE.expandKey :=
  expandKey_ct_of _ _ fun _ _ hp => hp

theorem expandKey_direct_verified :
    Verified PPC64LE.target Impl.Aes.PPC64LE.expandKey (Spec.Aes.expandKeyContract PPC64LE.abi) :=
  Verified.of_correct expandKey_direct_correct expandKey_direct_ct (by
    sig_implies [Spec.Aes.expandKeyContract, Spec.Aes.expandKeySig, Spec.Aes.expandKeyPre, Spec.Aes.expandKeyPost,
      Proof.Aes.expandKeyDirectPPC64LE, Proof.Aes.expandKeyPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [expandKeyDirectSat] using expandKeyDirectSat)

end VG.Proof.Aes.PPC64LE
