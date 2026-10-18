module

public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCheck
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivPcTail
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT

/-!
# `vg_rsa_private_checked_precomputed` on x86-64: what follows the CRT

`checkP_ok` runs everything after the call of the CRT, from any state the
frame allows: whatever `M` holds and whatever the CRT returned (`r₁`), when
`pre`'s first words are `n`'s values, it returns and releases what
`vg_rsa_private_checked`'s check does (`check_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivCheckedPc
open VG.Impl.Rsa.X86_64.PrivChecked (sp lea oM)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa (gOf checkResult released check_logic bytesAt_length')

theorem checkP_eq (pdName : String) (pd : Prog isa) :
    seqs (([.block pdArgs, .call pdName pd] : List (Prog isa)) ++ PrivCheckedPc.tail) =
      .seq (.block pdArgs) (.seq (.call pdName pd) (seqs PrivCheckedPc.tail)) := rfl

/-- Everything after the CRT, from any state the frame allows: whatever `M`
holds and the CRT returned. -/
theorem checkP_ok (P : PublicImpl) (pdName : String) {s t : State} (hp : PreFPc s) (he : EnvP s t) :
    WP isa (seqs (([.block pdArgs, .call pdName (P.code)] : List (Prog isa)) ++ PrivCheckedPc.tail)) t fun t' =>
      EnvP s t' ∧
      (Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) =
          some (Spec.Rsa.wordsAt s.mem (stackArg s 14) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)) →
        t'.gpr .rax = checkResult (t.gpr .rax) (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt t.mem (off (fbP s) oM) (s.gpr .rcx).toNat) ∧
        Spec.Rsa.bytesAt t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
          (if released (t.gpr .rax) (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
              (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
              (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat)
              (Spec.Rsa.bytesAt t.mem (off (fbP s) oM) (s.gpr .rcx).toNat)
            then Spec.Rsa.bytesAt t.mem (off (fbP s) oM) (s.gpr .rcx).toNat
            else List.replicate (s.gpr .rcx).toNat 0)) ∧
      Spec.Rsa.bytesAt t'.mem (off (fbP s) oM) (s.gpr .rcx).toNat = List.replicate (s.gpr .rcx).toNat 0 ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  have hk2 := hp.k2
  have csk : ∀ {rs : List Reg} {a b : State}, Keep rs a b → (∀ r ∈ calleeSaved, r ∉ rs) →
      ∀ r ∈ calleeSaved, b.gpr r = a.gpr r := fun k h r hr => k.gpr (h r hr)
  rw [checkP_eq]
  refine WP.seq (WP.mono_mx (by decide +kernel)
    (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (pdArgsP_ok hp he) rfl)
    fun t₃ ⟨⟨he₃, hm₃, hdi₃, hsi₃, hdx₃, hcx₃, h8₃, h9₃⟩, k₃⟩ hmx₃ => ?_)
  have hw : ∀ {d : Nat}, d < 4 → word t₃.mem (fbP s) (8 * d) =
      [off (fbP s) oM, s.gpr .rcx, stackArg s 12, stackArg s 13].getD d 0 := fun {d} hd => by
    rw [hm₃]
    rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 by omega) with rfl | rfl | rfl | rfl
    · simp (disch := decide) only [word_wo, word_self0, Nat.mul_zero]
      rfl
    · simp (disch := decide) only [word_wo, word_writeW_self, Nat.mul_one]; rfl
    · simp (disch := decide) only [word_wo, word_writeW_self]; rfl
    · simp (disch := decide) only [word_writeW_self]; rfl
  refine WP.seq (WP.mono (pdP_call P pdName hp he₃ (hw (d := 0) (by decide))
    (hw (d := 1) (by decide)) (hw (d := 2) (by decide)) (hw (d := 3) (by decide)) hdi₃ hsi₃ hdx₃ hcx₃ h8₃ h9₃)
    fun t₄ ⟨he₄, hpd, hM₄, hR1₄, hcs₄, hmx₄⟩ => ?_)
  refine WP.mono_mx (by decide +kernel)
    (WP.keep [.rax, .r11, .rdi, .rsi, .rcx, .r10, .rdx, .r9, .r8] (tailP_ok hp he₄) (by decide +kernel))
    fun t' ⟨⟨hax, hout, hM', he'⟩, k₅⟩ hmx₅ => ⟨he', fun hpc => ?_, hM',
      fun r hr => by rw [csk k₅ (by decide) r hr, hcs₄ r hr, csk k₃ (by decide) r hr],
      by rw [hmx₅, hmx₄, hmx₃]⟩
  clear hM'
  -- The values the tail reads.
  have hr1 : word t₄.mem (fbP s) oR1 = t.gpr .rax := by
    rw [hR1₄, hm₃]
    simp (disch := decide) only [word_wo, word_wo0, word_writeW_self]
  have hmb : Spec.Rsa.bytesAt t₃.mem (off (fbP s) oM) (s.gpr .rcx).toNat =
      Spec.Rsa.bytesAt t.mem (off (fbP s) oM) (s.gpr .rcx).toNat := by
    rw [hm₃]
    simp (disch := first | decide | (simp only [oM, oR1]; omega)) only [bytes_wo, bytes_wo0]
  rw [hr1] at hax hout
  rw [hM₄, hmb] at hout
  simp only [hmb] at hpd
  have h3 : match Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) with
      | some _ => (1 : BitVec 64).setWidth 32 = 1
      | none => (1 : BitVec 64).setWidth 32 = 0 := by
    rw [hpc]; rfl
  have hl := check_logic (r₁ := t.gpr .rax) (r₂ := t₄.gpr .rax) (r₃ := 1)
    (eB := Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
    (mB := Spec.Rsa.bytesAt t.mem (off (fbP s) oM) (s.gpr .rcx).toNat)
    (outB := Spec.Rsa.bytesAt t₄.mem (s.gpr .rdi) (s.gpr .rcx).toNat)
    (xB := Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat) h3 (fun _ => by
      have := hpd _ (bytesAt_length' _ _ _) hpc
      cases hpo : Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          (Spec.Rsa.bytesAt t.mem (off (fbP s) oM) (s.gpr .rcx).toNat) <;>
        simp only [hpo, Spec.Rsa.written] at this ⊢
      · exact this.1
      · exact this)
  exact ⟨by rw [hax]; exact hl.1, by rw [hout]; exact if_congr hl.2 rfl rfl⟩

end VG.Proof.Rsa.X86_64
