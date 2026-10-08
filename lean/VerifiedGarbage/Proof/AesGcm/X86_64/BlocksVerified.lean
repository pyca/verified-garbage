import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.CT
import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES-GCM on whole blocks, x86-64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
of `vg_aes_gcm_encrypt_blocks` and `vg_aes_gcm_decrypt_blocks` (for any
implementations `v` of `vg_aes_ctr32` and `vg_ghash`, with or without the
interleaved loops), a state satisfying their precondition, and the shared
contracts of `Spec/Gcm/Contract.lean` (with 8 bytes of stack, for the return
address of a call: the functions called make no calls).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64

open Gcm.X86_64.Stitch (CtxMode)

/-- The loops `st` for any kind of key context are the same code. -/
theorem map_code_enc (st : Option StitchImpl) (M : CtxMode) : (st.map (·.code M)).map (·.enc) = st.map (·.enc) := by
  cases st <;> rfl

theorem map_code_dec (st : Option StitchImpl) (M : CtxMode) : (st.map (·.code M)).map (·.dec) = st.map (·.dec) := by
  cases st <;> rfl

section
variable (v : GcmImpl) {M : CtxMode} {aligned : Bool} (st : Option (StitchCode M aligned))

theorem encryptBlocks_mx :
    (Blocks.encrypt v.callees.ctr v.callees.gh (st.map (·.enc)) aligned).allInstrs (fun i => !loadsMxcsr i) = true := by
  have hh := StitchImpl.head_mxcsr st fun i => i.encP
  simp only [Blocks.encrypt, Blocks.blocks, Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.allInstrs,
    GcmImpl.callees, hh, v.ctr.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true, Bool.false_eq_true, ite_false,
    ite_true]; decide +kernel

theorem decryptBlocks_mx :
    (Blocks.decrypt v.callees.ctr v.callees.gh (st.map (·.dec)) aligned).allInstrs (fun i => !loadsMxcsr i) = true := by
  have hh := StitchImpl.head_mxcsr st fun i => i.decP
  simp only [Blocks.decrypt, Blocks.blocks, Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.allInstrs,
    GcmImpl.callees, hh, v.ctr.mxcsr, v.gh.mxcsr, Bool.true_and, Bool.and_true, Bool.false_eq_true, ite_false,
    ite_true]; decide +kernel

theorem encryptBlocks_spSafe :
    (Blocks.encrypt v.callees.ctr v.callees.gh (st.map (·.enc)) aligned).all (fun i => !X86_64.isa.writesSp i) = true := by
  have hh := StitchImpl.head_spSafe st fun i => i.encP
  simp only [Blocks.encrypt, Blocks.blocks, Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.all,
    GcmImpl.callees, hh, v.ctr.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true, Bool.false_eq_true, ite_false,
    ite_true]; decide +kernel

theorem decryptBlocks_spSafe :
    (Blocks.decrypt v.callees.ctr v.callees.gh (st.map (·.dec)) aligned).all (fun i => !X86_64.isa.writesSp i) = true := by
  have hh := StitchImpl.head_spSafe st fun i => i.decP
  simp only [Blocks.decrypt, Blocks.blocks, Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.all,
    GcmImpl.callees, hh, v.ctr.spSafe, v.gh.spSafe, Bool.true_and, Bool.and_true, Bool.false_eq_true, ite_false,
    ite_true]; decide +kernel

theorem encryptBlocks_xdepth :
    (Blocks.encrypt v.callees.ctr v.callees.gh (st.map (·.enc)) aligned).x86_64Depth ≤ 8 := by
  have hh := StitchImpl.head_xdepth st fun i => i.encP
  simp only [Blocks.encrypt, Blocks.blocks, Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.x86_64Depth,
    GcmImpl.callees, hh, v.ctr.noStack, v.gh.noStack, Nat.max_le]
  decide +kernel

theorem decryptBlocks_xdepth :
    (Blocks.decrypt v.callees.ctr v.callees.gh (st.map (·.dec)) aligned).x86_64Depth ≤ 8 := by
  have hh := StitchImpl.head_xdepth st fun i => i.decP
  simp only [Blocks.decrypt, Blocks.blocks, Blocks.tail, Blocks.ctrCall, Blocks.ghCall, Code.x86_64Depth,
    GcmImpl.callees, hh, v.ctr.noStack, v.gh.noStack, Nat.max_le]
  decide +kernel

theorem encryptBlocksM_correct (s : State) (hs : (Proof.AesGcm.encryptBlocksX86_64M M).pre s) :
    ∃ t s', Exec isa (Blocks.encrypt v.callees.ctr v.callees.gh (st.map (·.enc)) aligned) s t s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.encryptBlocksX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := Blocks.encrypt_wp v st hs
  exact ⟨t, s', he, abiPreserved_of_exec (encryptBlocks_mx v st) he hg, hp⟩

theorem decryptBlocksM_correct (s : State) (hs : (Proof.AesGcm.decryptBlocksX86_64M M).pre s) :
    ∃ t s', Exec isa (Blocks.decrypt v.callees.ctr v.callees.gh (st.map (·.dec)) aligned) s t s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.decryptBlocksX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := Blocks.decrypt_wp v st hs
  exact ⟨t, s', he, abiPreserved_of_exec (decryptBlocks_mx v st) he hg, hp⟩

end

section
variable (v : GcmImpl) (st : Option StitchImpl)

/-! The key context of `vg_aes_gcm_init` (`CtxMode.base`). -/

theorem encryptBlocks_correct (s : State) (hs : Proof.AesGcm.encryptBlocksX86_64.pre s) :
    ∃ t s', Exec isa (Blocks.encrypt v.callees.ctr v.callees.gh (st.map (·.enc))) s t s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.encryptBlocksX86_64.post s s' := by
  have h := encryptBlocksM_correct v (st.map (·.code CtxMode.base)) s (Proof.AesGcm.blocksPreM_base hs)
  rwa [map_code_enc] at h

theorem decryptBlocks_correct (s : State) (hs : Proof.AesGcm.decryptBlocksX86_64.pre s) :
    ∃ t s', Exec isa (Blocks.decrypt v.callees.ctr v.callees.gh (st.map (·.dec))) s t s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.decryptBlocksX86_64.post s s' := by
  have h := decryptBlocksM_correct v (st.map (·.code CtxMode.base)) s (Proof.AesGcm.blocksPreM_base hs)
  rwa [map_code_dec] at h

theorem Blocks.encrypt_ctB :
    ConstantTime isa Proof.AesGcm.encryptBlocksX86_64.pre Proof.AesGcm.encryptBlocksX86_64.pub
      (Blocks.encrypt v.callees.ctr v.callees.gh (st.map (·.enc))) := by
  have h := Blocks.encrypt_ct v (st.map (·.code CtxMode.base))
  rw [map_code_enc] at h
  exact fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ => h s₁ s₂ t₁ t₂ s₁' s₂' (Proof.AesGcm.blocksPreM_base h₁)
    (Proof.AesGcm.blocksPreM_base h₂)

theorem Blocks.decrypt_ctB :
    ConstantTime isa Proof.AesGcm.decryptBlocksX86_64.pre Proof.AesGcm.decryptBlocksX86_64.pub
      (Blocks.decrypt v.callees.ctr v.callees.gh (st.map (·.dec))) := by
  have h := Blocks.decrypt_ct v (st.map (·.code CtxMode.base))
  rw [map_code_dec] at h
  exact fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ => h s₁ s₂ t₁ t₂ s₁' s₂' (Proof.AesGcm.blocksPreM_base h₁)
    (Proof.AesGcm.blocksPreM_base h₂)

theorem encryptBlocks_mxB :
    (Blocks.encrypt v.callees.ctr v.callees.gh (st.map (·.enc))).allInstrs (fun i => !loadsMxcsr i) = true := by
  have h := encryptBlocks_mx v (st.map (·.code CtxMode.base)); rwa [map_code_enc] at h

theorem encryptBlocks_xdepthB :
    (Blocks.encrypt v.callees.ctr v.callees.gh (st.map (·.enc))).x86_64Depth ≤ 8 := by
  have h := encryptBlocks_xdepth v (st.map (·.code CtxMode.base)); rwa [map_code_enc] at h

theorem decryptBlocks_xdepthB :
    (Blocks.decrypt v.callees.ctr v.callees.gh (st.map (·.dec))).x86_64Depth ≤ 8 := by
  have h := decryptBlocks_xdepth v (st.map (·.code CtxMode.base)); rwa [map_code_dec] at h

theorem decryptBlocks_mxB :
    (Blocks.decrypt v.callees.ctr v.callees.gh (st.map (·.dec))).allInstrs (fun i => !loadsMxcsr i) = true := by
  have h := decryptBlocks_mx v (st.map (·.code CtxMode.base)); rwa [map_code_dec] at h

theorem encryptBlocks_spSafeB :
    (Blocks.encrypt v.callees.ctr v.callees.gh (st.map (·.enc))).all (fun i => !X86_64.isa.writesSp i) = true := by
  have h := encryptBlocks_spSafe v (st.map (·.code CtxMode.base)); rwa [map_code_enc] at h

theorem decryptBlocks_spSafeB :
    (Blocks.decrypt v.callees.ctr v.callees.gh (st.map (·.dec))).all (fun i => !X86_64.isa.writesSp i) = true := by
  have h := decryptBlocks_spSafe v (st.map (·.code CtxMode.base)); rwa [map_code_dec] at h

end

/-- A state satisfying the precondition of `vg_aes_gcm_encrypt_blocks` and `_decrypt_blocks` (with no
data, and `scratch` at 0). -/
def blocksSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 0x3000 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x8008, 8⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0x4000, 0⟩, ⟨0, 2112⟩]

theorem encryptBlocks_verified (v : GcmImpl) (st : Option StitchImpl) :
    Verified X86_64.target (Blocks.encrypt v.callees.ctr v.callees.gh (st.map (·.enc)))
      (Spec.Gcm.encryptBlocksContract X86_64.abi 8) :=
  Verified.of_correct (encryptBlocks_correct v st) (Blocks.encrypt_ctB v st) (by
    sig_implies [Spec.Gcm.encryptBlocksContract, Spec.Gcm.cryptBlocksSig, Proof.AesGcm.encryptBlocksX86_64,
      Proof.AesGcm.blocksPre, Proof.AesGcm.blocksPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
      Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [blocksSat] using blocksSat)

theorem decryptBlocks_verified (v : GcmImpl) (st : Option StitchImpl) :
    Verified X86_64.target (Blocks.decrypt v.callees.ctr v.callees.gh (st.map (·.dec)))
      (Spec.Gcm.decryptBlocksContract X86_64.abi 8) :=
  Verified.of_correct (decryptBlocks_correct v st) (Blocks.decrypt_ctB v st) (by
    sig_implies [Spec.Gcm.decryptBlocksContract, Spec.Gcm.cryptBlocksSig, Proof.AesGcm.decryptBlocksX86_64,
      Proof.AesGcm.blocksPre, Proof.AesGcm.blocksPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
      Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [blocksSat] using blocksSat)

end VG.Proof.AesGcm.X86_64
