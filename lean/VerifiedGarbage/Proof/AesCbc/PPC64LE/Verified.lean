module

public import VerifiedGarbage.Impl.AesCbc.PPC64LE
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Call
public import VerifiedGarbage.Spec.Cbc.Contract
import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# AES-CBC on PPC64LE: `Verified`

Correctness and constant time, a state satisfying the precondition, and the
shared contracts of `Spec/Cbc/Contract.lean` (with no stack: a call stores
nothing in memory).
-/

@[expose] public section

namespace VG.Proof.AesCbc.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCbc.PPC64LE

theorem encrypt_correct (s : State) (hs : (cbcPPC64LE true).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (cbcPPC64LE true).post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := whole_wp encBody_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (cbcPPC64LE false).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (cbcPPC64LE false).post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := whole_wp decBody_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

/-- A state satisfying the precondition (with no blocks). -/
def sat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r6 => 0x3000 | .r8 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩]

theorem encrypt_verified : Verified PPC64LE.target encrypt (Spec.Cbc.aesEncryptContract PPC64LE.abi) :=
  Verified.of_correct encrypt_correct (whole_ct encBody_ok encBody_ct) (by
    sig_implies [Spec.Cbc.aesEncryptContract, Spec.Cbc.aesSig, cbcPPC64LE, modePPC64LE, cbcMode,
      ciphOf, cbc, cts, PPC64LE.abi, PPC64LE.argRegs] [sat] using sat)

theorem decrypt_verified : Verified PPC64LE.target decrypt (Spec.Cbc.aesDecryptContract PPC64LE.abi) :=
  Verified.of_correct decrypt_correct (whole_ct decBody_ok decBody_ct) (by
    sig_implies [Spec.Cbc.aesDecryptContract, Spec.Cbc.aesSig, cbcPPC64LE, modePPC64LE, cbcMode,
      ciphOf, cbc, cts, PPC64LE.abi, PPC64LE.argRegs] [sat] using sat)

end VG.Proof.AesCbc.PPC64LE
