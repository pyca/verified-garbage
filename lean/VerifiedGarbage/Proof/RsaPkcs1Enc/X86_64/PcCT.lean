module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.PcContract
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCT
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.PcCall
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Alloc
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.PcContract
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCT
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.PcCall
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Alloc
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86-64: constant time

The pieces of `vg_rsa_pkcs1_encrypt` (`EncCT`), for entry states related to
the anchor by `contract` (`PR`), and the call of the precomputed public
operation, constant time for its contract, which makes `pre`'s words public
too. Nothing after the call branches on its result.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.PcCT

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Encrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa.X86_64 (PublicImpl pdChkContract)
open Pc

/-- An entry state meeting the precondition with the anchor's public data. -/
def PR (a s : State) : Prop := contract.pre s ∧ contract.pub a s

theorem pr_sib : ∀ a s, PR a s → Sib a s := fun _ _ h => ⟨(pre_of h.1).toEPre, h.2.1⟩

theorem pub_refl (s : State) : contract.pub s s := ⟨X86_64.pub_refl s, rfl, rfl, rfl⟩

theorem callArgs_two : RelCT isa (Two (At PR PreCall)) (.block Impl.RsaPkcs1Enc.X86_64.Precomputed.callArgs)
    (Two (At PR Pc.J5)) :=
  two_piece [.rsp] (pins (J := PreCall) pr_sib [(.rsp, fb)] (by
        simp only [List.mem_singleton]; rintro p rfl s t h; exact h.rsp) (by
        simp only [List.mem_singleton]; rintro p rfl; exact fb_pin)) (by taint_decide)
    fun _ _ ⟨s, S, h⟩ => WP.mono (callArgs_ok (pre_of S.1) h) fun _ hh => ⟨s, S, hh.1⟩

/-- What the precomputed public operation's contract makes public. -/
theorem pub_view {a s t : State} (S : PR a s) (h : Pc.J5 s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (callRd s) (pubWr s)).gpr =
      [a.gpr .rdi, a.gpr .rcx, stackArg a 6, stackArg a 7, a.gpr .r8, a.gpr .r9, fb a - 8] ∧
    stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 0 = off (fb a) oEM ∧
    stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 1 = a.gpr .rcx ∧
    stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 2 = stackArg a 4 ∧
    stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 3 = stackArg a 5 ∧
    Spec.Rsa.wordsAt (t.callEntry.withRegions (callRd s) (pubWr s)).mem
      ((t.callEntry.withRegions (callRd s) (pubWr s)).gpr .rdx)
      ((t.callEntry.withRegions (callRd s) (pubWr s)).gpr .rcx).toNat =
      Spec.Rsa.wordsAt a.mem (stackArg a 6) (stackArg a 7).toNat ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (callRd s) (pubWr s)).mem
      ((t.callEntry.withRegions (callRd s) (pubWr s)).gpr .r8)
      ((t.callEntry.withRegions (callRd s) (pubWr s)).gpr .r9).toNat = eB a := by
  obtain ⟨hpc, hdi, hsi, hdx, hcx, h8, h9⟩ := h
  have hp := pre_of S.1
  have S' := pr_sib _ _ S
  have rcx := S'.gpr (r := .rcx) (by decide)
  have hfE : Frame [stkR s, outR s, scrR s] s.mem t.callEntry.mem :=
    frame_call (frame_of_outside hpc.out) (callEntry_frame hpc.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (ret_sub s)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [entry_regs, hdi, hsi, hdx, hcx, h8, h9, hpc.rsp, S'.fb, rcx, S'.gpr (r := .rdi) (by decide),
      S.2.2.1, S.2.2.2.1, S'.gpr (r := .r8) (by decide), S'.gpr (r := .r9) (by decide)]
  · rw [stackArg_entry hpc.rsp _ _ (by decide), ← S'.fb]
    have := hpc.slots.a0; simp only [Bignum.word, off_zero, Nat.mul_zero]; exact this
  · rw [stackArg_entry hpc.rsp _ _ (by decide), ← rcx]; exact hpc.slots.a1
  · rw [stackArg_entry hpc.rsp _ _ (by decide), ← S'.arg (by decide)]; exact hpc.slots.a2
  · rw [stackArg_entry hpc.rsp _ _ (by decide), ← S'.arg (by decide)]; exact hpc.slots.a3
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx]
    rw [State.withRegions_mem, pre_words hp hfE, S.2.2.2.2]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h8, h9]
    rw [entryBytes hpc _ _ hp.dKe (by have := hp.dOe; rw [outR]; exact this) hp.des.symm
      (by have := hp.wE; omega)]
    exact S'.e

theorem call_ct (v : PublicImpl) : RelCT isa (Two (At PR Pc.J5)) (.call v.name v.code) fun _ _ => True := by
  refine RelCT.callEx (k := pdChkContract) v.ok v.ct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨r₁, a0₁, a1₁, a2₁, a3₁, n₁, e₁⟩ := pub_view S₁ j₁
  obtain ⟨r₂, a0₂, a1₂, a2₂, a3₂, n₂, e₂⟩ := pub_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := call_covers (pre_of S₁.1) j₁.1
  obtain ⟨c₂, w₂⟩ := call_covers (pre_of S₂.1) j₂.1
  have hpub : pdChkContract.pub (t₁.callEntry.withRegions (callRd s₁) (pubWr s₁))
      (t₂.callEntry.withRegions (callRd s₂) (pubWr s₂)) :=
    ⟨regs_eq (r₁.trans r₂.symm), a0₁.trans a0₂.symm, a1₁.trans a1₂.symm, a2₁.trans a2₂.symm,
      a3₁.trans a3₂.symm, n₁.trans n₂.symm, e₁.trans e₂.symm⟩
  have p₁ := call_pre (pre_of S₁.1) j₁
  have p₂ := call_pre (pre_of S₂.1) j₂
  exact ⟨callRd s₁, pubWr s₁, callRd s₂, pubWr s₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂, by rw [j₁.1.rsp, j₂.1.rsp, (pr_sib _ _ S₁).fb, (pr_sib _ _ S₂).fb]⟩

theorem call_two (v : PublicImpl) : RelCT isa (Two (At PR Pc.J5)) (.call v.name v.code) (Two (At PR AfterCall)) :=
  two_post (call_ct v) fun _ _ ⟨s, S, h⟩ =>
    WP.mono (call_ok v (pre_of S.1) h) fun _ h => ⟨s, S, h.1.toAfterCall⟩

theorem body_ct (v : PublicImpl) : RelCT isa (Two (At PR J0))
    (Impl.RsaPkcs1Enc.X86_64.Precomputed.body v.name v.code) fun _ _ => True := by
  rw [Pc.body_eq]
  exact RelCT.seq (setup_two pr_sib) (RelCT.seq (ps_two pr_sib) (RelCT.seq (sep_two pr_sib)
    (RelCT.seq (copy_two pr_sib) (RelCT.seq callArgs_two (RelCT.seq (call_two v)
      (RelCT.seq (maskArgs_two pr_sib) (mask_ct pr_sib)))))))

theorem code_constantTime (v : PublicImpl) :
    ConstantTime isa contract.pre contract.pub (Impl.RsaPkcs1Enc.X86_64.Precomputed.code v.name v.code) :=
  RelCT.constantTime (relCT_alloc ((body_ct v).mono
    (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, e₁, e₂⟩ => ⟨s₁, ⟨s₁, ⟨h₁, pub_refl s₁⟩, e₁⟩, ⟨s₂, ⟨h₂, hpub⟩, e₂⟩⟩)
    fun _ _ h => h))

/-! ## `Verified` -/

/-- `vg_rsa_pkcs1_encrypt_precomputed`, calling the implementation `v` of
`vg_rsa_public_precomputed_checked`, meets the shared contract. -/
theorem code_verified (v : PublicImpl) :
    Verified target (Impl.RsaPkcs1Enc.X86_64.Precomputed.code v.name v.code)
      (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi encStack) :=
  Verified.of_correct (k := contract) (code_correct v) (code_constantTime v) implies

/-- It writes `rsp` only in its frame's push and pop. -/
theorem code_spSafe (v : PublicImpl) :
    (Impl.RsaPkcs1Enc.X86_64.Precomputed.code v.name v.code).all (fun i => !isa.writesSp i) = true := by
  simp only [Impl.RsaPkcs1Enc.X86_64.Precomputed.code, Impl.RsaPkcs1Enc.X86_64.Precomputed.body, Code.all,
    v.spSafe, Bool.true_and]
  decide +kernel

end VG.Proof.RsaPkcs1Enc.X86_64.PcCT
