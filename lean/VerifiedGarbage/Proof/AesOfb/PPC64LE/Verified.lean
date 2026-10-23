module

public import VerifiedGarbage.Impl.AesOfb.PPC64LE
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Call
public import VerifiedGarbage.Proof.AesOfb.Spec
public import VerifiedGarbage.Spec.Ofb.Contract
import VerifiedGarbage.Proof.AesOfb.PPC64LE.Body
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# AES-OFB on PPC64LE: `Verified`

Correctness and constant time, from the loop AES-CBC's proofs share, a state
satisfying the precondition, and the shared contract of
`Spec/Ofb/Contract.lean` (with no stack: a call stores nothing in memory).
-/

@[expose] public section

namespace VG.Proof.AesOfb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOfb.PPC64LE
open VG.Proof.AesCbc.PPC64LE

theorem crypt_correct (s : State) (hs : (modePPC64LE ofbMode).pre s) :
    ∃ t s', Exec isa crypt s t s' ∧ abiPreserved s s' ∧ (modePPC64LE ofbMode).post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := whole_wp body_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem crypt_verified : Verified PPC64LE.target crypt (Spec.Ofb.aesContract PPC64LE.abi) :=
  Verified.of_correct crypt_correct (whole_ct body_ok body_ct)
    { pre := by sig_implies_pre [Spec.Ofb.aesContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modePPC64LE,
        PPC64LE.abi, PPC64LE.argRegs]
      -- `ofbMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Spec.Ofb.aesContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modePPC64LE, ofbMode, PPC64LE.abi,
          PPC64LE.argRegs]
        sig_reduce [Spec.Ofb.aesContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modePPC64LE, ofbMode, PPC64LE.abi,
          PPC64LE.argRegs] at h
        sig_simp [Spec.Ofb.aesContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modePPC64LE, ofbMode, PPC64LE.abi,
          PPC64LE.argRegs] [] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by sig_implies_pub [Spec.Ofb.aesContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modePPC64LE,
        PPC64LE.abi, PPC64LE.argRegs]
      sat := by sig_implies_sat [Spec.Ofb.aesContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modePPC64LE,
        PPC64LE.abi, PPC64LE.argRegs] [sat] using sat }

end VG.Proof.AesOfb.PPC64LE
