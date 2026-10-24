module

public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# SEC 1 point compression on PPC64LE: the contract the proof is written against

The facts of `Spec.EcKey.Instance.compressPublicKeyContract` on PPC64LE, by
name, for any curve: `vg_ec_<curve>_compress_public_key(out, public,
scratch)`, with the arguments in `r3`–`r5` and the result in `r3` (ELFv2).
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE

open VG VG.PPC64LE

def compressContract (C : Spec.Weierstrass.Curve) : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, C.len + 1⟩
    let pk : Region := ⟨s.gpr .r4, 2 * C.len + 1⟩
    let ws : Region := ⟨s.gpr .r5, 8192⟩
    s.rd = [pk] ∧ s.wr = [out, ws] ∧
      pk.Disjoint out ∧ pk.Disjoint ws ∧ out.Disjoint ws ∧
      (s.gpr .r3).toNat + (C.len + 1) ≤ 2 ^ 64 ∧
      (s.gpr .r4).toNat + (2 * C.len + 1) ≤ 2 ^ 64 ∧
      (s.gpr .r5).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match Spec.EcKey.compressPublicKey C (Spec.EcKey.bytesAt s.mem (s.gpr .r4) (2 * C.len + 1)) with
    | some bs => s'.gpr .r3 = 1 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .r3) (C.len + 1) = bs
    | none => s'.gpr .r3 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .r3) (C.len + 1) = List.replicate (C.len + 1) 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5

theorem compress_implies (I : Spec.EcKey.Instance)
    (hsat : ∃ s, (I.compressPublicKeyContract abi 0).pre s) :
    (compressContract I.curve).Implies (I.compressPublicKeyContract abi 0) where
  pre := by
    sig_implies_pre [Spec.EcKey.Instance.compressPublicKeyContract,
      Spec.EcKey.Instance.compressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, compressContract]
  post := by
    intro s s' _ h
    sig_post [Spec.EcKey.Instance.compressPublicKeyContract,
      Spec.EcKey.Instance.compressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, compressContract]
    simp only [compressContract] at h
    revert h
    generalize Spec.EcKey.compressPublicKey _ _ = q
    rcases q with _ | z <;> exact fun h => ⟨by rw [h.1]; rfl, h.2⟩
  pub := by
    sig_implies_pub [Spec.EcKey.Instance.compressPublicKeyContract,
      Spec.EcKey.Instance.compressPublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, compressContract]
  sat := hsat

/-- A state satisfying the precondition, for encodings of `len` bytes. -/
def satState (len : Nat) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 2 * len + 1⟩]
  wr := [⟨0x1000, len + 1⟩, ⟨0x8000, 8192⟩]

end VG.Proof.EcKey.Compressed.PPC64LE
