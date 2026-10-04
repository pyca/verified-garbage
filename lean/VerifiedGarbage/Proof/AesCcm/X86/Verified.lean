import VerifiedGarbage.Proof.AesCcm.X86.SealCT
import VerifiedGarbage.Proof.AesCcm.X86.OpenCT
import VerifiedGarbage.Proof.CmacAes.X86.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ccm.Contract
import VerifiedGarbage.Proof.AesCcm.Scratch

/-!
# AES-CCM on x86: `Verified`

Untrusted: everything here is checked by Lean. Correctness (`seal_wp'`,
`open_wp'`) and constant time (`seal_ct`, `open_ct`) for any implementation
`v` of `vg_aes_ctr32`, a state satisfying the precondition, and the shared
contracts with the working space as a last argument
(`Proof/AesCcm/Scratch.lean`), with 56 bytes of stack: a call of
`vg_cmac_aes_update` (its six arguments and return address) and its own
calls of `vg_aes_ctr32`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Proof.AesGcm.X86 (ofNat_toNat32)

theorem seal_correct (v : Ctr32Impl) (s : State) (hs : sealX86.pre s) :
    ∃ t s', Exec isa («seal» v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ sealX86.post s s' := by
  obtain ⟨t, s', e, abi, h⟩ := seal_wp' v (args_of_seal hs) rfl rfl (ofNat_toNat32 _).symm rfl
    (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl
    (tag_wr hs)
  exact ⟨t, s', e, abi, h⟩

/-- The return value: the low word of `edx:eax`. -/
theorem setWidth_ret (a b : BitVec 32) : (a ++ b).setWidth 32 = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_append]
  have := b.isLt
  rw [Nat.shiftLeft_eq, Nat.or_mod_two_pow, Nat.mul_mod_left, Nat.zero_or, Nat.mod_eq_of_lt this]

theorem open_correct (v : Ctr32Impl) (s : State) (hs : openX86.pre s) :
    ∃ t s', Exec isa («open» v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ openX86.post s s' := by
  obtain ⟨t, s', e, abi, h⟩ := open_wp' v (args_of_open hs) rfl rfl (ofNat_toNat32 _).symm rfl
    (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl
  refine ⟨t, s', e, abi, ?_⟩
  simp only [openX86, setWidth_ret]
  exact h

theorem seal_spSafe (v : Ctr32Impl) : («seal» v.callee v.suffix).all (fun i => !isa.writesSp i) = true := by
  simp only [«seal», ccmEntry, Impl.AesGcm.X86.entry, ctrs, mac, b0, aad, aadHead, header, absorbPad, updBlock,
    updCall, Impl.CmacAes.Stream.X86.call6, tag, ctr, ctrCall, tagOut, Code.all, Proof.CmacAes.X86.update_spSafe v,
    v.spSafe, Bool.and_true]
  decide +kernel

theorem open_spSafe (v : Ctr32Impl) : («open» v.callee v.suffix).all (fun i => !isa.writesSp i) = true := by
  simp only [«open», ccmEntry, Impl.AesGcm.X86.entry, ctrs, mac, b0, aad, aadHead, header, absorbPad, updBlock,
    updCall, Impl.CmacAes.Stream.X86.call6, tag, ctr, ctrCall, mask, Impl.AesGcm.X86.recv, Impl.AesGcm.X86.cmp,
    Code.all, Proof.CmacAes.X86.update_spSafe v, v.spSafe, Bool.and_true]
  decide +kernel

/-- A state satisfying the precondition of `vg_aes_ccm_seal`: the key
schedule at `0x1000`, 10 rounds, a 7-byte nonce at `0x2000`, no associated
data (at `0x2100`), no data (at `0x3000`), a 4-byte tag at `0x4000` and
`work` at `0x5000`, as stack arguments at `0x8004`. -/
def sealSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800d then 0x20
    else if a = 0x8010 then 7 else if a = 0x8015 then 0x21 else if a = 0x801d then 0x30
    else if a = 0x8025 then 0x40 else if a = 0x8028 then 4 else if a = 0x802d then 0x50 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 4⟩, ⟨0x5000, 2560⟩, ⟨0x8004, 44⟩]

/-- As `sealSat`, with the tag read only. -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩, ⟨0x4000, 4⟩],
                 wr := [⟨0x3000, 0⟩, ⟨0x5000, 2560⟩, ⟨0x8004, 44⟩] }

theorem sealSat_args : arg sealSat 0 = 0x1000 ∧ arg sealSat 1 = 10 ∧ arg sealSat 2 = 0x2000 ∧ arg sealSat 3 = 7 ∧
    arg sealSat 4 = 0x2100 ∧ arg sealSat 5 = 0 ∧ arg sealSat 6 = 0x3000 ∧ arg sealSat 7 = 0 ∧
    arg sealSat 8 = 0x4000 ∧ arg sealSat 9 = 4 ∧ arg sealSat 10 = 0x5000 ∧ argAddr sealSat 0 = 0x8004 := by
  decide

theorem openSat_args : arg openSat 0 = 0x1000 ∧ arg openSat 1 = 10 ∧ arg openSat 2 = 0x2000 ∧ arg openSat 3 = 7 ∧
    arg openSat 4 = 0x2100 ∧ arg openSat 5 = 0 ∧ arg openSat 6 = 0x3000 ∧ arg openSat 7 = 0 ∧
    arg openSat 8 = 0x4000 ∧ arg openSat 9 = 4 ∧ arg openSat 10 = 0x5000 ∧ argAddr openSat 0 = 0x8004 :=
  sealSat_args

theorem seal_verified (v : Ctr32Impl) :
    Verified X86.target («seal» v.callee v.suffix) (Proof.AesCcm.sealScratchContract X86.abi 56) :=
  Verified.of_correct (seal_correct v) (seal_ct v) (by
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e⟩ := sealSat_args
    have esp : sealSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre,
      Spec.Ccm.sealPost, sealX86, sealPre, oneLay, onePub, schR, nonceR, aadR, dataR, tagR, workR, argsR', retR,
      stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e, esp] using sealSat)

theorem open_verified (v : Ctr32Impl) :
    Verified X86.target («open» v.callee v.suffix) (Proof.AesCcm.openScratchContract X86.abi 56) :=
  Verified.of_correct (open_correct v) (open_ct v)
    { pre := by
        sig_implies_pre [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
          Spec.Ccm.openLeak, openX86, openLeak, openRes, openPre, oneLay, onePub, schR, nonceR, aadR, dataR, tagR, workR, argsR', retR,
          stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      post := by
        sig_implies_post [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
          Spec.Ccm.openPost, Spec.Ccm.openLeak, openX86, openLeak, openRes, openPre, oneLay, onePub, schR, nonceR, aadR, dataR, tagR,
          workR, argsR', retR, stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
          Spec.Ccm.openLeak, openX86, openLeak, openRes, openPre, oneLay, onePub, schR, nonceR, aadR, dataR, tagR, workR, argsR', retR,
          stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
        sig_split h
        sig_reduce [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
          Spec.Ccm.openLeak, openX86, openLeak, openRes, openPre, oneLay, onePub, schR, nonceR, aadR, dataR, tagR, workR, argsR', retR,
          stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
        sig_simp [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
          Spec.Ccm.openLeak, openX86, openLeak, openRes, openPre, oneLay, onePub, schR, nonceR, aadR, dataR, tagR, workR, argsR', retR,
          stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [Nat.forall_lt_succ_right, Nat.not_lt_zero,
          false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by
        obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e⟩ := openSat_args
        have esp : openSat.gpr .esp = 0x8000 := rfl
        sig_implies_sat [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
          Spec.Ccm.openPost, Spec.Ccm.openLeak, openX86, openLeak, openRes, openPre, oneLay, onePub, schR, nonceR, aadR, dataR, tagR,
          workR, argsR', retR, stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
          [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e, esp] using openSat }

end VG.Proof.AesCcm.X86
