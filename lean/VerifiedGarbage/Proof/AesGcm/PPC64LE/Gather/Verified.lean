module

public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Groups
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Gather.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Impl.AesGcm.PPC64LE.SealGather
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Gather.Verified
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Gather.CT
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Gather.Fn
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Frame

/-!
# AES-GCM encryption out of place, from a list of slices, PPC64LE: the shared contract

Untrusted: everything here is checked by Lean. The shared contract of
`vg_aes_gcm_seal_gather`, with the 2832 bytes of stack below the stack
pointer that its frame and its call use (`Proof.AesGcm.sealGatherRoundsContract`):
its postcondition from the one the proof is written against
(`gatherPost_of`), its public arguments as `gatherPub` (`gatherPub_of`), and
a state that satisfies its precondition (`gatherSat`), for
`GatherSplit/Verified.lean`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE.Gather

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE.SealGather
open VG.Proof.ChaCha20Poly1305.PPC64LE.Gather (filter_true' filter_false' filterMap_some' filterMap_none' pairFacts_ro)

theorem stackArgs_three (s : State) :
    List.map (stackArg s) (List.range 3) = [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

theorem gatherPost_of {s s' : State} (h : gatherPost s s') :
    (Proof.AesGcm.sealGatherRoundsContract PPC64LE.abi 2832).post s s' := by
  sig_post [Proof.AesGcm.sealGatherRoundsContract, Spec.Gcm.sealGatherSig, Proof.AesGcm.sealGatherRoundsPost, PPC64LE.abi,
    PPC64LE.argRegs, stackArgs_three, List.append_eq]
  exact fun _ _ => h

theorem gatherPub_of {s₁ s₂ : State} (hp : (Proof.AesGcm.sealGatherRoundsContract PPC64LE.abi 2832).pub s₁ s₂) :
    gatherPub s₁ s₂ := by
  sig_pub [Proof.AesGcm.sealGatherRoundsContract, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPre, PPC64LE.abi,
    PPC64LE.argRegs, stackArgs_three, List.append_eq] at hp
  obtain ⟨qsp, q3, q4, q5, q6, q7, q8, q9, q10, a0, a1, a2, hd⟩ := hp
  exact ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, a0, a1, a2, hd⟩

/-- A state satisfying the precondition of `vg_aes_gcm_seal_gather`: no
slices, nonce, additional data or text; the tag at `0x5000`, its address
the third stack argument, at `sp + 112`. -/
def gatherSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r7 => 0x3000 | .r9 => 0x4000 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9071 then 0x50 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x9060, 24⟩]
  wr := [⟨0, 0⟩, ⟨0x5000, 16⟩]

end VG.Proof.AesGcm.PPC64LE.Gather
