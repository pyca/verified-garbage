module
public import VerifiedGarbage.Impl.AesXts.X86_64Vaes
public import VerifiedGarbage.Proof.AesCbc.X86_64.Call
public import VerifiedGarbage.Proof.AesXts.Spec
public import VerifiedGarbage.Spec.Xts.Contract
public import VerifiedGarbage.Proof.Xts.Contract
meta import VerifiedGarbage.Proof.Xts.Contract

import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Dec
import VerifiedGarbage.Proof.AesCbc.X86_64.Verified
import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Enc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.AesXts.X86_64Vaes
meta import VerifiedGarbage.Proof.AesCbc.X86_64.Call
meta import VerifiedGarbage.Proof.AesXts.Spec
meta import VerifiedGarbage.Spec.Xts.Contract
meta import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Dec
meta import VerifiedGarbage.Proof.AesCbc.X86_64.Verified
meta import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Enc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# One-pass XTS-AES on x86-64: `Verified`

Correctness from `encrypt_wp` and `decrypt_wp`; constant time by the taint analysis of the
whole function, from the public arguments (pointers, `rounds` and `n`); and
the shared contract of `Spec/Xts/Contract.lean`, with the 8 bytes of stack
of `vg_aes_xts_encrypt`'s (the precondition `UPre` the proofs share with it
includes them; this function writes none).
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Vaes

open VG VG.X86_64
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.X86_64

theorem encrypt_mx : Impl.AesXts.X86_64Vaes.encrypt.allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel

theorem encrypt_spSafe : Impl.AesXts.X86_64Vaes.encrypt.all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel

theorem encrypt_correct (s : State) (hs : (modeX86_64 (AesXts.xtsMode true)).pre s) :
    ∃ t s', Exec isa Impl.AesXts.X86_64Vaes.encrypt s t s' ∧ abiPreserved s s' ∧
      (modeX86_64 (AesXts.xtsMode true)).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := encrypt_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec encrypt_mx he hg, hp⟩

theorem encrypt_ct : ConstantTime isa (modeX86_64 (AesXts.xtsMode true)).pre (modeX86_64 (AesXts.xtsMode true)).pub
    Impl.AesXts.X86_64Vaes.encrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem encrypt_verified :
    Verified X86_64.target Impl.AesXts.X86_64Vaes.encrypt (Proof.Xts.aesEncryptContract X86_64.abi 8) :=
  Verified.of_correct encrypt_correct encrypt_ct
    { pre := by sig_implies_pre [Proof.Xts.aesEncryptContract, Proof.Xts.aesSig, modeX86_64, X86_64.abi,
        X86_64.argRegs]
      -- `xtsMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Proof.Xts.aesEncryptContract, Proof.Xts.aesSig, modeX86_64, AesXts.xtsMode, ciphOf, X86_64.abi,
          X86_64.argRegs]
        sig_reduce [Proof.Xts.aesEncryptContract, Proof.Xts.aesSig, modeX86_64, AesXts.xtsMode, ciphOf,
          X86_64.abi, X86_64.argRegs] at h
        sig_simp [Proof.Xts.aesEncryptContract, Proof.Xts.aesSig, modeX86_64, AesXts.xtsMode, ciphOf, X86_64.abi,
          X86_64.argRegs] [] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by sig_implies_pub [Proof.Xts.aesEncryptContract, Proof.Xts.aesSig, modeX86_64, X86_64.abi,
        X86_64.argRegs]
      sat := by sig_implies_sat [Proof.Xts.aesEncryptContract, Proof.Xts.aesSig, modeX86_64, X86_64.abi,
        X86_64.argRegs] [sat] using sat }

theorem decrypt_mx : Impl.AesXts.X86_64Vaes.decrypt.allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel

theorem decrypt_spSafe : Impl.AesXts.X86_64Vaes.decrypt.all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel

theorem decrypt_correct (s : State) (hs : (modeX86_64 (AesXts.xtsMode false)).pre s) :
    ∃ t s', Exec isa Impl.AesXts.X86_64Vaes.decrypt s t s' ∧ abiPreserved s s' ∧
      (modeX86_64 (AesXts.xtsMode false)).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := decrypt_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec decrypt_mx he hg, hp⟩

theorem decrypt_ct : ConstantTime isa (modeX86_64 (AesXts.xtsMode false)).pre (modeX86_64 (AesXts.xtsMode false)).pub
    Impl.AesXts.X86_64Vaes.decrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem decrypt_verified :
    Verified X86_64.target Impl.AesXts.X86_64Vaes.decrypt (Proof.Xts.aesDecryptContract X86_64.abi 8) :=
  Verified.of_correct decrypt_correct decrypt_ct
    { pre := by sig_implies_pre [Proof.Xts.aesDecryptContract, Proof.Xts.aesSig, modeX86_64, X86_64.abi,
        X86_64.argRegs]
      -- `xtsMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Proof.Xts.aesDecryptContract, Proof.Xts.aesSig, modeX86_64, AesXts.xtsMode, ciphOf, X86_64.abi,
          X86_64.argRegs]
        sig_reduce [Proof.Xts.aesDecryptContract, Proof.Xts.aesSig, modeX86_64, AesXts.xtsMode, ciphOf,
          X86_64.abi, X86_64.argRegs] at h
        sig_simp [Proof.Xts.aesDecryptContract, Proof.Xts.aesSig, modeX86_64, AesXts.xtsMode, ciphOf, X86_64.abi,
          X86_64.argRegs] [] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by sig_implies_pub [Proof.Xts.aesDecryptContract, Proof.Xts.aesSig, modeX86_64, X86_64.abi,
        X86_64.argRegs]
      sat := by sig_implies_sat [Proof.Xts.aesDecryptContract, Proof.Xts.aesSig, modeX86_64, X86_64.abi,
        X86_64.argRegs] [sat] using sat }

end VG.Proof.AesXts.X86_64.Vaes
