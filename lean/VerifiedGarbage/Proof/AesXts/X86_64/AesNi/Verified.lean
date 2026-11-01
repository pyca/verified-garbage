module
public import VerifiedGarbage.Impl.AesXts.X86_64AesNi
public import VerifiedGarbage.Proof.AesCbc.X86_64.Call
public import VerifiedGarbage.Proof.AesXts.Spec
public import VerifiedGarbage.Spec.Xts.Contract
public import VerifiedGarbage.Proof.Xts.Contract
meta import VerifiedGarbage.Proof.Xts.Contract

import VerifiedGarbage.Proof.AesXts.X86_64.AesNi.Loop
import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Dec
import VerifiedGarbage.Proof.AesCbc.X86_64.Verified
import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Enc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.AesXts.X86_64AesNi
meta import VerifiedGarbage.Proof.AesCbc.X86_64.Call
meta import VerifiedGarbage.Proof.AesXts.Spec
meta import VerifiedGarbage.Spec.Xts.Contract
meta import VerifiedGarbage.Proof.AesXts.X86_64.AesNi.Loop
meta import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Dec
meta import VerifiedGarbage.Proof.AesCbc.X86_64.Verified
meta import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Enc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# One-pass XTS-AES with AES-NI on x86-64: correctness and `Verified`

`encrypt_wp` and `decrypt_wp`: `crypt_wp` (`Vaes/Top.lean`) with this loop
(`loop8_ok`), the AES-NI round code on `xmm0`–`xmm7` and on `xmm0`, and what
the rounds need as for the VAES functions (`KPe`, `KPd`, `kpe_pre`,
`imc_pre`). Constant time by the taint analysis of the whole function, from
the public arguments (pointers, `rounds` and `n`); the contract is the shared
one of `Spec/Xts/Contract.lean`, with the 8 bytes of stack of
`vg_aes_xts_encrypt`'s (the precondition the proofs share with it includes
them; this function writes none).
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.OnePassNi

open VG VG.X86_64
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.X86_64
open VG.Proof.AesXts.X86_64.Vaes (crypt_wp KPe KPd kpe_stable kpd_stable kpe_pre imc_pre)
open VG.Impl.Aes.X86_64.AesNi (regs8)

theorem encrypt_wp {s₀ : State} (h0 : (modeX86_64 (AesXts.xtsMode true)).pre s₀) :
    WP isa Impl.AesXts.X86_64AesNi.encrypt s₀ fun s' =>
      gprPreserved s₀ s' ∧ (modeX86_64 (AesXts.xtsMode true)).post s₀ s' := by
  refine crypt_wp (KP := KPe) h0 (fun s₁ hp₁ => kpe_stable hp₁)
    (fun s₁ hp₁ => loop8_ok hp₁ (kpe_stable hp₁) ?_) (fun s₁ hp₁ => ?_)
    (fun s₁ hp₁ s h => WP.block_nil ⟨h, kpe_pre hp₁ h⟩)
  · intro s ⟨hK, hrdi, hrsi, hr10⟩
    exact Aes.X86_64.AesNi.aes_ok regs8 (by decide) (by decide) hp₁.rounds s hK (by rw [hrsi, rsi_ofNat]) hr10
  · intro s ⟨hK, hrdi, hrsi, hr10⟩
    exact WP.mono (Aes.X86_64.AesNi.aes_ok [.xmm0] (by decide) (by decide) hp₁.rounds s hK
      (by rw [hrsi, rsi_ofNat]) hr10) fun s' ⟨e, f⟩ => ⟨e _ List.mem_cons_self, f⟩

theorem decrypt_wp {s₀ : State} (h0 : (modeX86_64 (AesXts.xtsMode false)).pre s₀) :
    WP isa Impl.AesXts.X86_64AesNi.decrypt s₀ fun s' =>
      gprPreserved s₀ s' ∧ (modeX86_64 (AesXts.xtsMode false)).post s₀ s' := by
  refine crypt_wp (KP := KPd) h0 (fun s₁ hp₁ => kpd_stable hp₁)
    (fun s₁ hp₁ => loop8_ok hp₁ (kpd_stable hp₁) ?_) (fun s₁ hp₁ => ?_)
    (fun s₁ hp₁ s h => imc_pre hp₁ h)
  · intro s ⟨hK, hrdi, hrsi, hr8, hr10⟩
    exact Aes.X86_64.AesNi.aesDec_ok regs8 (by decide) (by decide) hp₁.rounds s hK (by rw [hrsi, rsi_ofNat]) hr10
  · intro s ⟨hK, hrdi, hrsi, hr8, hr10⟩
    exact WP.mono (Aes.X86_64.AesNi.aesDec_ok [.xmm0] (by decide) (by decide) hp₁.rounds s hK
      (by rw [hrsi, rsi_ofNat]) hr10) fun s' ⟨e, f⟩ => ⟨e _ List.mem_cons_self, f⟩

theorem encrypt_mx : Impl.AesXts.X86_64AesNi.encrypt.allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel

theorem encrypt_spSafe : Impl.AesXts.X86_64AesNi.encrypt.all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel

theorem encrypt_correct (s : State) (hs : (modeX86_64 (AesXts.xtsMode true)).pre s) :
    ∃ t s', Exec isa Impl.AesXts.X86_64AesNi.encrypt s t s' ∧ abiPreserved s s' ∧
      (modeX86_64 (AesXts.xtsMode true)).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := encrypt_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec encrypt_mx he hg, hp⟩

theorem encrypt_ct : ConstantTime isa (modeX86_64 (AesXts.xtsMode true)).pre (modeX86_64 (AesXts.xtsMode true)).pub
    Impl.AesXts.X86_64AesNi.encrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem encrypt_verified :
    Verified X86_64.target Impl.AesXts.X86_64AesNi.encrypt (Proof.Xts.aesEncryptContract X86_64.abi 8) :=
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

theorem decrypt_mx : Impl.AesXts.X86_64AesNi.decrypt.allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel

theorem decrypt_spSafe : Impl.AesXts.X86_64AesNi.decrypt.all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel

theorem decrypt_correct (s : State) (hs : (modeX86_64 (AesXts.xtsMode false)).pre s) :
    ∃ t s', Exec isa Impl.AesXts.X86_64AesNi.decrypt s t s' ∧ abiPreserved s s' ∧
      (modeX86_64 (AesXts.xtsMode false)).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := decrypt_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec decrypt_mx he hg, hp⟩

theorem decrypt_ct : ConstantTime isa (modeX86_64 (AesXts.xtsMode false)).pre (modeX86_64 (AesXts.xtsMode false)).pub
    Impl.AesXts.X86_64AesNi.decrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem decrypt_verified :
    Verified X86_64.target Impl.AesXts.X86_64AesNi.decrypt (Proof.Xts.aesDecryptContract X86_64.abi 8) :=
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

end VG.Proof.AesXts.X86_64.OnePassNi
