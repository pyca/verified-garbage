import VerifiedGarbage.Proof.AesCbc.AArch64.Verified
import VerifiedGarbage.Proof.AesOfb.AArch64.Body

/-!
# AES-OFB on AArch64: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), from the loop AES-CBC's proofs share, a state satisfying the
precondition, and the shared contract of `Spec/Ofb/Contract.lean` (with no
stack: the call keeps the return address in `x30`, which the function saves
in the scratch buffer).
-/

namespace VG.Proof.AesOfb.AArch64

open VG VG.AArch64 VG.Impl.AesOfb.AArch64
open VG.Impl.AesCbc.AArch64 (whole)
open VG.Proof.AesCbc.AArch64
open VG.Proof.Aes.AArch64 (BlocksImpl)

theorem crypt_keepsV (v : BlocksImpl) : (crypt v.enc).allInstrs keepsV = true := by
  simp only [crypt, whole, body, Code.allInstrs, v.encKeepsV]; decide +kernel

theorem crypt_correct (v : BlocksImpl) (s : State) (hs : (modeAArch64 ofbMode).pre s) :
    ∃ t s', Exec isa (crypt v.enc) s t s' ∧ abiPreserved s s' ∧ (modeAArch64 ofbMode).post s s' :=
  WP.withPreservedV (whole_wp (body_ok v) hs) (crypt_keepsV v)

theorem crypt_verified (v : BlocksImpl) :
    Verified AArch64.target (crypt v.enc) (Spec.Ofb.aesContract AArch64.abi) :=
  Verified.of_correct (crypt_correct v) (whole_ct (body_ok v) (body_ct v))
    { pre := by sig_implies_pre [Spec.Ofb.aesContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modeAArch64,
        AArch64.abi, AArch64.argRegs]
      -- `ofbMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Spec.Ofb.aesContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modeAArch64, ofbMode, AArch64.abi,
          AArch64.argRegs]
        sig_reduce [Spec.Ofb.aesContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modeAArch64, ofbMode, AArch64.abi,
          AArch64.argRegs] at h
        sig_simp [Spec.Ofb.aesContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modeAArch64, ofbMode, AArch64.abi,
          AArch64.argRegs] [] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by sig_implies_pub [Spec.Ofb.aesContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modeAArch64,
        AArch64.abi, AArch64.argRegs]
      sat := by sig_implies_sat [Spec.Ofb.aesContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modeAArch64,
        AArch64.abi, AArch64.argRegs] [sat] using sat }

end VG.Proof.AesOfb.AArch64
