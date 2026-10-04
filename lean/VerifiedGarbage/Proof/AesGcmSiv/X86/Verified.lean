import VerifiedGarbage.Proof.AesGcmSiv.X86.FnCT
import VerifiedGarbage.Proof.GcmSiv.Polyval
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.GcmSiv.Contract

/-!
# AES-GCM-SIV on x86: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementations `v` of `vg_aes_ctr32`, `vg_aes_expand_key` and
`vg_ghash`), with the tag input computed with GHASH equal to the RFC's
(`tagInput_eq`, from `Proof.GcmSiv.Polyval`, imported here only so that the
other proofs need not import its algebra), a state satisfying each
precondition, and the shared contracts of `Spec/GcmSiv/Contract.lean`, with
28 bytes of stack: a call of `vg_aes_ctr32` (its six arguments and return
address), which makes no calls.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.Impl.AesGcmSiv.X86
open VG.Proof.AesGcm.X86 (GcmImpl)

/-- RFC 8452 Appendix A: POLYVAL with `H` is GHASH with `H · x`. -/
theorem tagInput_eq : TagInputEq := fun a n pt d => by
  rw [GcmSiv.tagInput_eq, Spec.GcmSiv.polyval, GcmSiv.Polyval.polyvalFrom_eq]
  rfl

/-- The return value: the low word of `edx:eax`. -/
theorem setWidth_ret (a b : BitVec 32) : (a ++ b).setWidth 32 = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_append]
  have := b.isLt
  rw [Nat.shiftLeft_eq, Nat.or_mod_two_pow, Nat.mul_mod_left, Nat.zero_or, Nat.mod_eq_of_lt this]

section
variable (v : GcmImpl)

theorem seal_spSafe : («seal» v.callees).all (fun i => !isa.writesSp i) = true := by
  simp only [«seal», sivEntry, Impl.AesGcm.X86.entry, keys, derive, deriveBlock, derivePost, expand, hkey, polyval,
    absorb, chunk, absTail, absTailPre, lens, onStr, tag, crypt, cryptBlock, cryptTail, callCtr, callKey, callGh,
    Impl.AesGcm.X86.ctrCall, Impl.AesGcm.X86.keyCall, Impl.AesGcm.X86.ghCall, GcmImpl.callees, Code.all, v.ctr.spSafe, v.ctr.expandSpSafe, v.gh.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem open_spSafe : («open» v.callees).all (fun i => !isa.writesSp i) = true := by
  simp only [«open», sivEntry, Impl.AesGcm.X86.entry, keys, derive, deriveBlock, derivePost, expand, hkey, polyval,
    absorb, chunk, absTail, absTailPre, lens, onStr, tag, crypt, cryptBlock, cryptTail, mask, callCtr, callKey,
    callGh, Impl.AesGcm.X86.ctrCall, Impl.AesGcm.X86.keyCall, Impl.AesGcm.X86.ghCall, GcmImpl.callees, Code.all,
    v.ctr.spSafe, v.ctr.expandSpSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

end

/-- A state satisfying the precondition of `vg_aes_gcm_siv_seal` and
`vg_aes_gcm_siv_open`: the key schedule at `0x1000`, 10 rounds, the nonce at
`0x2000`, no additional data (at `0x2100`), no data (at `0x3000`) and `work`
at `0x5000`, as stack arguments at `0x8004`. -/
def sealSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800d then 0x20
    else if a = 0x8011 then 0x21 else if a = 0x8019 then 0x30 else if a = 0x8021 then 0x50 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x2100, 0⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x5000, 4096⟩, ⟨0x8004, 32⟩]

theorem sealSat_args : arg sealSat 0 = 0x1000 ∧ arg sealSat 1 = 10 ∧ arg sealSat 2 = 0x2000 ∧
    arg sealSat 3 = 0x2100 ∧ arg sealSat 4 = 0 ∧ arg sealSat 5 = 0x3000 ∧ arg sealSat 6 = 0 ∧
    arg sealSat 7 = 0x5000 ∧ argAddr sealSat 0 = 0x8004 := by
  decide

theorem seal_verified (v : GcmImpl) :
    Verified X86.target («seal» v.callees) (Spec.GcmSiv.sealContract X86.abi 28) :=
  Verified.of_correct (fun _ hs => seal_wp v tagInput_eq hs) (seal_ct v) (by
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, e⟩ := sealSat_args
    have esp : sealSat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.GcmSiv.sealContract, Spec.GcmSiv.sealSig, sealX86, onePre, onePub, schR, nonceR, aadR,
      dataR, workR, argsR', retR, stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, e, esp] using sealSat)

theorem open_verified (v : GcmImpl) :
    Verified X86.target («open» v.callees) (Spec.GcmSiv.openContract X86.abi 28) :=
  Verified.of_correct (fun _ hs => open_wp v tagInput_eq hs) (open_ct v)
    { pre := by
        sig_implies_pre [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, openX86, openResult, openPost, onePre,
          onePub, schR, nonceR, aadR, dataR, workR, argsR', retR, stackR, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes]
      post := by
        intro s s' _ h
        sig_post [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, openX86, openResult, openPost, onePre,
          onePub, schR, nonceR, aadR, dataR, workR, argsR', retR, stackR, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, setWidth_ret]
        sig_reduce [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, openX86, openResult, openPost, onePre,
          onePub, schR, nonceR, aadR, dataR, workR, argsR', retR, stackR, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, setWidth_ret] at h
        sig_simp [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, openX86, openResult, openPost, onePre,
          onePub, schR, nonceR, aadR, dataR, workR, argsR', retR, stackR, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, setWidth_ret] [] at h
        split at h <;> rename_i heq <;> rw [heq] <;> exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, openX86, openResult, openPost, onePre,
          onePub, schR, nonceR, aadR, dataR, workR, argsR', retR, stackR, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes] at h
        sig_split h
        sig_reduce [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, openX86, openResult, openPost, onePre,
          onePub, schR, nonceR, aadR, dataR, workR, argsR', retR, stackR, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes]
        sig_simp [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, openX86, openResult, openPost, onePre,
          onePub, schR, nonceR, aadR, dataR, workR, argsR', retR, stackR, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
      sat := by
        obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, e⟩ := sealSat_args
        have esp : sealSat.gpr .esp = 0x8000 := rfl
        sig_implies_sat [Spec.GcmSiv.openContract, Spec.GcmSiv.openSig, openX86, openResult, openPost, onePre,
          onePub, schR, nonceR, aadR, dataR, workR, argsR', retR, stackR, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes] [a0, a1, a2, a3, a4, a5, a6, a7, e, esp] using sealSat }

end VG.Proof.AesGcmSiv.X86
