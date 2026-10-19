module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptMacStart
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptMacUpdate

/-! # The rejection-key HMAC absorbs the entire ciphertext -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem kdkUpdateArguments {g : Geometry} {s : State}
    (a : Arguments g (fun j => (kdkUpdatePlan j).valueAt g) 6 s) :
    Arguments g (updateValues g (g.sources 3) g.length 64) 6 s := by
  intro j hj
  rw [a j hj]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl
  · change g.workspace + BitVec.ofNat 32 sSt = g.workspace
    exact BitVec.add_zero _
  all_goals rfl

theorem kdkAbsorb_ok (v : VG.Proof.Sha256.X86.Variants.Backend)
    {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {key : List Byte}
    (h : Context g bs s) (keyFits : key.length ≤ 64) (repr : MacRepr g key [] s) :
    WP isa (callAfter kdkUpdArgs (hashFns v).updN (hashFns v).updC) s fun t => Context g bs t ∧
      Frame (hashWrites g) s.mem t.mem ∧ Keeps callClobbers s t ∧ MacRepr g key (bs 3) t := by
  unfold callAfter
  refine WP.seq (WP.mono (kdkUpdArgs_ok h) ?_)
  rintro a ⟨ha, args, Fa, Ka⟩
  have sourceEq : (⟨byteAddr (g.sources 3), g.length⟩ : Region) = g.sourceRegion 3 := rfl
  refine WP.mono (macUpdate_call v ha (kdkUpdateArguments args)
    (ha.valid.sourceFits 3) (by have := ha.valid.maxLength; omega)
    ?_ ?_ ?_ ?_ (ha.sources 3).read keyFits (macRepr_args h Fa repr)) ?_
  · rw [sourceEq]
    exact (ha.valid.sourcesWorkspace 3).sub_right (ha.valid.scratchSub (by decide : sSt + 96 ≤ 8448))
  · rw [sourceEq]
    exact (ha.valid.sourcesWorkspace 3).sub_right (ha.valid.scratchSub (by decide : sHash + 608 ≤ 8448))
  · rw [sourceEq]
    exact (ha.valid.stackSources 3).sub_left ha.valid.calleeSub
  · rw [sourceEq]
    simpa only [BitVec.add_zero] using ((ha.valid.stackSources 3).sub_left (fun x hx => ha.valid.innerSub x
      (Offset.sub_base (d := 0) (n := 24) _ (by decide : 0 + 24 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes) x hx))).symm
  · rintro t ⟨ht, F, _, K, rt⟩
    refine ⟨ht, (argsFrame_hash Fa).trans F, (Ka.mono (by decide)).trans K, ?_⟩
    change MacRepr g key (Spec.Rsa.bytesAt a.mem (byteAddr (g.sources 3)) g.length) t at rt
    have cipherBytes : Spec.Rsa.bytesAt a.mem (byteAddr (g.sources 3)) g.length = bs 3 := (ha.sources 3).bytes
    rw [cipherBytes] at rt
    exact rt

end VG.Proof.RsaPkcs1Enc.X86.Dec
