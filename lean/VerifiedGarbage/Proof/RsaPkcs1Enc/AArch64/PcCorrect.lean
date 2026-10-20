module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.PcCall
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on AArch64: correctness

As `vg_rsa_pkcs1_encrypt`'s (`enc_ok`), with `pre` loaded for the call
(`callArgs_inv`) and the precomputed public operation (`pd_call`): the
registers the ABI keeps whatever `pre` holds, and, if `pre` holds the values
for `n`, `encK`'s postcondition.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Enc.Pc

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Encrypt
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked)

/-- `encK`'s postcondition, if `pre` holds the values for `n`. -/
def post (P : Nat) (s s' : State) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 4) (stackArg s 5).toNat) → (encK P).post s s'

theorem body_eq (n : String) (c : Prog isa) :
    Impl.RsaPkcs1Enc.AArch64.Precomputed.body n c = .seq (.block setup) (.seq psLoop (.seq (.block sep)
      (.seq msgCopy (.seq (.block Impl.RsaPkcs1Enc.AArch64.Precomputed.callArgs)
      (.seq (.call n c) (.seq (.block maskArgs) maskLoop)))))) := rfl

theorem consistent_iff (P : Nat) (s : State) :
    Consistent (layP P s) s.mem ↔ Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) =
      some (Spec.Rsa.wordsAt s.mem (stackArg s 4) (stackArg s 5).toNat) := by
  rw [Consistent, preW_layP, prlW_layP]; rfl

theorem code_ok (c : PdChecked) {s : State}
    (h : (Spec.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (c.stack + 1088)).pre s) :
    WP isa (Impl.RsaPkcs1Enc.AArch64.Precomputed.code c.name c.code) s fun s' =>
      abiPreserved s s' ∧ post c.stack s s' := by
  obtain ⟨hL, hrd, hwr, hpl, hsp⟩ := pre_of h
  refine WP.frame (by omega) (WP.alloc (by decide) ?_ ?_)
  · show 1072 ≤ (s.sp - 16).toNat
    rw [BitVec.toNat_sub_of_le (by show 16 ≤ s.sp.toNat; omega)]
    show 1072 ≤ s.sp.toNat - 16
    omega
  · show WP isa (Impl.RsaPkcs1Enc.AArch64.Precomputed.body c.name c.code) (entered s) _
    rw [body_eq]
    refine WP.seq (WP.mono (entry_okX hL hrd hwr) fun t ⟨hc, hs⟩ => ?_)
    refine WP.seq (WP.mono (psLoop_ok hL (setup_inv hc hs)) fun t₁ h₁ => ?_)
    refine WP.seq (WP.mono (sep_inv hL ⟨rfl, rfl⟩ h₁) fun t₂ h₂ => ?_)
    refine WP.seq (WP.mono (msgCopy_ok hL h₂) fun t₃ h₃ => ?_)
    refine WP.seq (WP.mono (callArgs_inv hL (preOk_of hpl) (regsOf _ s) h₃) fun t₄ h₄ => ?_)
    refine WP.seq (WP.mono (pd_call c hL rfl h₄) fun t₅ h₅ => ?_)
    refine WP.seq (WP.mono (maskArgs_inv h₅.toCalledF) fun t₆ h₆ => ?_)
    refine WP.mono (maskLoop_ok hL h₆) fun u hu => ?_
    have hc := hu.ctx
    have hsp' : (freed frameBytes u).sp = (layP c.stack s).Q + BitVec.ofNat 64 1072 := by rw [freed_sp, hc.sp]; rfl
    refine ⟨⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, fun hq => ?_⟩
    · by_cases h30 : r = .x30
      · subst r
        rw [popped_gpr_self, freed_mem, hsp']; exact hc.kept.lr
      · rw [popped_gpr_ne _ h30, freed_gpr]
        exact hc.cs r hr h30
    · rw [popped_sp, hsp']
      show (layP c.stack s).Q + BitVec.ofNat 64 1072 + BitVec.ofNat 64 16 = s.sp
      rw [add_add]; exact lay_Q _ s _ _
    · rw [popped_v, freed_v]
      exact hc.vs r hr
    · refine result_ok hL.mlk hL.plk (y := t₅.mem) (r := t₅.gpr .x0)
        (h₅.out ((consistent_iff c.stack s).2 hq)) ?_ fun i hi => ?_
      · rw [popped_gpr_ne _ (by decide), freed_gpr]
        exact hu.x0
      · rw [popped_mem, freed_mem]
        exact hu.done i hi

end VG.Proof.RsaPkcs1Enc.AArch64.Enc.Pc
