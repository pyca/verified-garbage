module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptMacUpdate

/-! # Absorb one complete PRF message from its scratch buffer -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem prfUpdateArguments {g : Geometry} {s : State} {len : Nat}
    (a : Arguments g (fun j => (prfUpdatePlan len j).valueAt g) 6 s) :
    Arguments g (updateValues g (g.workspace + BitVec.ofNat 32 sMsg) len 64) 6 s := by
  intro j hj
  rw [a j hj]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact BitVec.add_zero _
  all_goals rfl

theorem prfAbsorb_ok (v : VG.Proof.Sha256.X86.Variants.Backend)
    {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {key text : List Byte} {len : Nat}
    (h : Context g bs s) (keyFits : key.length ≤ 64) (repr : MacRepr g key [] s)
    (lengthBound : len ≤ 16) (bytes : Spec.Rsa.bytesAt s.mem (g.scratch sMsg len).base len = text) :
    WP isa (callAfter (prfUpdArgs len) (hashFns v).updN (hashFns v).updC) s fun t => Context g bs t ∧
      Frame (hashWrites g) s.mem t.mem ∧
      Frame ((updateWr g ++ [g.calleeRegion]) ++ [⟨byteAddr g.stack, 80⟩]) s.mem t.mem ∧
      Keeps callClobbers s t ∧ MacRepr g key text t := by
  have fit : sMsg + len ≤ 8448 := by unfold sMsg; omega
  have addr : byteAddr (g.workspace + BitVec.ofNat 32 sMsg) = (g.scratch sMsg len).base :=
    h.valid.scratchAddress (by decide)
  have region : (⟨byteAddr (g.workspace + BitVec.ofNat 32 sMsg), len⟩ : Region) = g.scratch sMsg len := by
    rw [addr]
    rfl
  unfold callAfter
  refine WP.seq (WP.mono (prfUpdArgs_ok h len) ?_)
  rintro a ⟨ha, args, Fa, Ka⟩
  refine WP.mono (macUpdate_call v ha (prfUpdateArguments args)
    (ha.valid.scratchFit fit (by decide)) (by omega) ?_ ?_ ?_ ?_
    ?_ keyFits (macRepr_args h Fa repr)) ?_
  · rw [region]
    exact scratchDisjoint g (Or.inr (by decide : sSt + 96 ≤ sMsg)) fit (by decide)
  · rw [region]
    exact scratchDisjoint g (Or.inl (by unfold sMsg sHash; omega)) fit (by decide)
  · rw [region]
    exact ha.calleeScratch fit
  · rw [region]
    exact (ha.argsScratch (by decide : 24 ≤ 160) fit).symm
  · rw [addr]
    exact ha.scratchRead fit
  · rintro t ⟨ht, F, Ffine, K, rt⟩
    refine ⟨ht, (argsFrame_hash Fa).trans F, ?_, (Ka.mono (by decide)).trans K, ?_⟩
    · exact (Fa.sub (by
        intro r hr
        exact ⟨r, List.mem_append_right _ hr, fun _ hx => hx⟩)).trans
          (Ffine.sub (by
            intro r hr
            exact ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩))
    · change MacRepr g key (Spec.Rsa.bytesAt a.mem (byteAddr (g.workspace + BitVec.ofNat 32 sMsg)) len) t at rt
      rw [addr, (scratchBytes_args h fit Fa).trans bytes] at rt
      exact rt

end VG.Proof.RsaPkcs1Enc.X86.Dec
