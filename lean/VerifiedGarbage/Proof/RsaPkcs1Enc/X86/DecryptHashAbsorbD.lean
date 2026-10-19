module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptHashStartD
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptHashUpdate

/-! # Absorb the complete padded private exponent into SHA-256 -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem shaUpdateArguments {g : Geometry} {s : State}
    (a : Arguments g (fun j => (shaUpdatePlan j).valueAt g) 6 s) :
    Arguments g (updateValues g (g.workspace + BitVec.ofNat 32 sD) g.length 0) 6 s := by
  intro j hj
  rw [a j hj]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl
  · change g.workspace + BitVec.ofNat 32 sSt = g.workspace
    exact BitVec.add_zero _
  all_goals rfl

theorem hashAbsorbD_ok (v : VG.Proof.Sha256.X86.Variants.Backend)
    {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {D : List Byte}
    (h : Context g bs s) (bytes : Spec.Rsa.bytesAt s.mem (g.scratch sD g.length).base g.length = D)
    (repr : Spec.Sha256.Repr s.mem (g.scratch sSt 96).base []) :
    WP isa (callAfter shaUpdArgs (hashFns v).updN (hashFns v).updC) s fun t => Context g bs t ∧
      Frame (hashWrites g) s.mem t.mem ∧ Keeps callClobbers s t ∧
      Spec.Sha256.Repr t.mem (g.scratch sSt 96).base D := by
  have fit : sD + g.length ≤ 8448 := by have := h.valid.maxLength; unfold sD; omega
  have addr : byteAddr (g.workspace + BitVec.ofNat 32 sD) = (g.scratch sD g.length).base :=
    h.valid.scratchAddress (by decide : sD < 8448)
  have region : (⟨byteAddr (g.workspace + BitVec.ofNat 32 sD), g.length⟩ : Region) = g.scratch sD g.length := by
    rw [addr]
    rfl
  unfold callAfter
  refine WP.seq (WP.mono (shaUpdArgs_ok h) ?_)
  rintro a ⟨ha, args, Fa, Ka⟩
  have bytesA := (scratchBytes_args h fit Fa).trans bytes
  have reprA := repr_args h Fa repr
  refine WP.mono (shaUpdate_call v ha (shaUpdateArguments args)
    (ha.valid.scratchFit fit (by decide)) (by have := ha.valid.maxLength; omega) (by decide : 0 < 2 ^ 32)
    ?_ ?_ ?_ ?_ ?_ reprA rfl) ?_
  · rw [region]
    exact scratchDisjoint g (Or.inr (by decide : sSt + 96 ≤ sD)) fit (by decide : sSt + 96 ≤ 8448)
  · rw [region]
    exact scratchDisjoint g (Or.inl (by have := h.valid.maxLength; unfold sD sHash; omega)) fit (by decide : sHash + 608 ≤ 8448)
  · rw [region]
    exact ha.calleeScratch fit
  · rw [region]
    exact (ha.argsScratch (by decide : 24 ≤ 160) fit).symm
  · rw [addr]
    exact ha.scratchRead fit
  · rintro t ⟨ht, F, _, K, rt⟩
    refine ⟨ht, (argsFrame_hash Fa).trans F, (Ka.mono (by decide)).trans K, ?_⟩
    change Spec.Sha256.Repr t.mem (g.scratch sSt 96).base
      (Spec.Rsa.bytesAt a.mem (byteAddr (g.workspace + BitVec.ofNat 32 sD)) g.length) at rt
    rw [addr, bytesA] at rt
    exact rt

end VG.Proof.RsaPkcs1Enc.X86.Dec
