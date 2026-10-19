module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptHashFinalizePre
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Word32

/-! # Finish SHA-256 of the private exponent in DH -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem shaFinalize_call (v : VG.Proof.Sha256.X86.Variants.Backend)
    {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {msg : List Byte}
    (h : Context g bs s) (a : Arguments g (fun j => (shaFinalizePlan j).valueAt g) 5 s)
    (repr : Spec.Sha256.Repr s.mem (g.scratch sSt 96).base msg) (msgLength : msg.length = g.length) :
    WP isa (.call (hashFns v).finN (hashFns v).finC) s fun t => Context g bs t ∧
      Frame (hashWrites g) s.mem t.mem ∧ Frame (finalizeWr g ++ [g.calleeRegion]) s.mem t.mem ∧
      Keeps callClobbers s t ∧
      Spec.Rsa.bytesAt t.mem (g.scratch sDH 32).base 32 = Spec.Sha256.hash msg := by
  have argsWrite : InRegions s.wr (callArgsRegion g 20).base 20 := by
    have raw := h.inner.write (d := 0) (n := 20) (by decide)
    simpa only [BitVec.add_zero, callArgsRegion] using raw
  have W : Covers (finalizeWr g) s.wr := (Covers.one (h.scratchWrite (by decide : sSt + 96 ≤ 8448))).cons
    ((Covers.one (h.scratchWrite (by decide : sDH + 32 ≤ 8448))).cons
      ((Covers.one (h.scratchWrite (by decide : sHash + 608 ≤ 8448))).pair (Covers.one argsWrite)))
  refine WP.mono (hash_call_ok h (finalize_verified v)
    (Nat.le_trans v.stream.finSU (by decide)) v.stream.finSp (shaFinalize_pre h a) W.right W ?_) ?_
  · intro r hr
    simp only [finalizeWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨g.workspaceRegion, by simp [hashWrites], h.valid.scratchSub (by decide : sSt + 96 ≤ 8448)⟩
    · exact ⟨g.workspaceRegion, by simp [hashWrites], h.valid.scratchSub (by decide : sDH + 32 ≤ 8448)⟩
    · exact ⟨g.workspaceRegion, by simp [hashWrites], h.valid.scratchSub (by decide : sHash + 608 ≤ 8448)⟩
    · exact ⟨_, by simp [hashWrites], Region.sub_prefix (by decide : 20 ≤ 80)⟩
  · rintro t ⟨ht, F, Ffine, K, u, M, _, post⟩
    refine ⟨ht, F, Ffine, K, ?_⟩
    sig_post [Spec.Sha256.finalizeScratchContract, Spec.Sha256.finalizeScratchSig, Spec.Sha256.finalizePost,
      abi, argSlots, argVal, argBytes] at post
    have sa := fun {j : Nat} (hj : j < 5) => callArgument_value h a (by decide : 5 ≤ 20) hj [] (finalizeWr g)
    have v0 : (shaFinalizePlan 0).valueAt g = g.workspace := by simp [shaFinalizePlan, CallArg.valueAt, sSt]
    have v1 : (shaFinalizePlan 1).valueAt g = BitVec.ofNat 32 g.length := rfl
    have v2 : (shaFinalizePlan 2).valueAt g = 0 := rfl
    have v3 : (shaFinalizePlan 3).valueAt g = g.workspace + BitVec.ofNat 32 sDH := rfl
    simp only [sa (by decide : 0 < 5), sa (by decide : 1 < 5), sa (by decide : 2 < 5),
      sa (by decide : 3 < 5), v0, v1, v2, v3, M] at post
    have stateEq : (g.scratch sSt 96).base = byteAddr g.workspace := by simp [Geometry.scratch, sSt]
    have entryRepr : Spec.Sha256.Repr s.callEntry.mem (g.scratch sSt 96).base msg := by
      apply repr_frame h.callFrame ?_ repr
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact (h.calleeScratch (by decide : sSt + 96 ≤ 8448)).symm
    rw [stateEq] at entryRepr
    have out := post Spec.Sha256.H0 msg entryRepr
      (by rw [Word32.count_eq (by have := h.valid.maxLength; omega), msgLength])
    change Spec.Rsa.bytesAt t.mem (byteAddr (g.workspace + BitVec.ofNat 32 sDH)) 32 = Spec.Sha256.hash msg at out
    rw [h.valid.scratchAddress (by decide : sDH < 8448)] at out
    exact out

end VG.Proof.RsaPkcs1Enc.X86.Dec
