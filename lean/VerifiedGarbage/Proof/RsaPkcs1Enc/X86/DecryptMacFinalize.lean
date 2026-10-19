module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptMacFinalizePre
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptMacState
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Word32

/-! # Finalize the rejection-key and PRF HMACs -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem macFinalize_call (v : VG.Proof.Sha256.X86.Variants.Backend)
    {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {dst : Nat} {key text : List Byte}
    (h : Context g bs s) (a : Arguments g (macFinalizeValues g dst (64 + text.length)) 6 s)
    (dstLow : 192 ≤ dst) (dstHigh : dst + 32 ≤ sHash)
    (keyFits : key.length ≤ 64) (textFits : text.length ≤ 1024) (repr : MacRepr g key text s) :
    WP isa (.call (hashFns v).hfN (hashFns v).hfC) s fun t => Context g bs t ∧
      Frame (hashWrites g) s.mem t.mem ∧ Frame (macFinalizeWr g dst ++ [g.calleeRegion]) s.mem t.mem ∧
      Keeps callClobbers s t ∧
      Spec.Rsa.bytesAt t.mem (g.scratch dst 32).base 32 = Spec.Hmac.hmac Spec.Hmac.sha256 key text := by
  have dstFit : dst + 32 ≤ 8448 := by unfold sHash at dstHigh; omega
  have argsWrite : InRegions s.wr (callArgsRegion g 24).base 24 := by
    have raw := h.inner.write (d := 0) (n := 24) (by decide)
    simpa only [BitVec.add_zero, callArgsRegion] using raw
  have W : Covers (macFinalizeWr g dst) s.wr := (Covers.one (h.scratchWrite (by decide : sSt + 96 ≤ 8448))).cons
    ((Covers.one (h.scratchWrite dstFit)).cons
      ((Covers.one (h.scratchWrite (by decide : sHash + 832 ≤ 8448))).pair (Covers.one argsWrite)))
  have R : Covers (macFinalizeRd g) (s.rd ++ s.wr) := Covers.one (h.scratchRead (by decide : sOuter + 96 ≤ 8448))
  refine WP.mono (hash_call_ok h (hmacFinalize_verified v)
    (Nat.le_trans v.finalizeStack (by decide)) v.finalizeNoSp (macFinalize_pre h a dstLow dstHigh)
    (Covers.append_left R W.right) W ?_) ?_
  · intro r hr
    simp only [macFinalizeWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨g.workspaceRegion, by simp [hashWrites], h.valid.scratchSub (by decide : sSt + 96 ≤ 8448)⟩
    · exact ⟨g.workspaceRegion, by simp [hashWrites], h.valid.scratchSub dstFit⟩
    · exact ⟨g.workspaceRegion, by simp [hashWrites], h.valid.scratchSub (by decide : sHash + 832 ≤ 8448)⟩
    · exact ⟨_, by simp [hashWrites], Region.sub_prefix (by decide : 24 ≤ 80)⟩
  · rintro t ⟨ht, F, Ffine, K, u, M, _, post⟩
    refine ⟨ht, F, Ffine, K, ?_⟩
    sig_post [Spec.Hmac.Instance.finalizeScratchContract, Spec.Hmac.finalizeScratchContract, Spec.Hmac.finalizeScratchSig,
      Spec.Hmac.finalizePost, Spec.Hmac.finalizeSig, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256,
      abi, argSlots, argVal, argBytes] at post
    have sa := fun {j : Nat} (hj : j < 6) => callArgument_value h a (by decide : 6 ≤ 20) hj (macFinalizeRd g) (macFinalizeWr g dst)
    have v0 : macFinalizeValues g dst (64 + text.length) 0 = g.workspace := rfl
    have v1 : macFinalizeValues g dst (64 + text.length) 1 = g.workspace + BitVec.ofNat 32 sOuter := rfl
    have v2 : macFinalizeValues g dst (64 + text.length) 2 = BitVec.ofNat 32 (64 + text.length) := rfl
    have v3 : macFinalizeValues g dst (64 + text.length) 3 = 0 := rfl
    have v4 : macFinalizeValues g dst (64 + text.length) 4 = g.workspace + BitVec.ofNat 32 dst := rfl
    simp only [sa (by decide : 0 < 6), sa (by decide : 1 < 6), sa (by decide : 2 < 6),
      sa (by decide : 3 < 6), sa (by decide : 4 < 6), v0, v1, v2, v3, v4, M] at post
    have entryInner := repr_frame h.callFrame (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact (h.calleeScratch (by decide : sSt + 96 ≤ 8448)).symm) repr.1
    have entryOuter := repr_frame h.callFrame (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact (h.calleeScratch (by decide : sOuter + 96 ≤ 8448)).symm) repr.2
    have stateEq : (g.scratch sSt 96).base = byteAddr g.workspace := by simp [Geometry.scratch, sSt]
    have outerAddr : byteAddr (g.workspace + BitVec.ofNat 32 sOuter) = (g.scratch sOuter 96).base := h.valid.scratchAddress (by decide)
    rw [stateEq] at entryInner
    have out := post (macKey key) text (macKey_length keyFits)
      (by rw [macKey_length keyFits]; omega) entryInner
      (Word32.count_eq (by omega)) (by
        change Spec.Sha256.Repr s.callEntry.mem (byteAddr (g.workspace + BitVec.ofNat 32 sOuter)) _
        rw [outerAddr]; exact entryOuter)
    change Spec.Rsa.bytesAt t.mem (byteAddr (g.workspace + BitVec.ofNat 32 dst)) 32 =
      Spec.Hmac.hmac Spec.Hmac.sha256 key text at out
    have dstAddr : byteAddr (g.workspace + BitVec.ofNat 32 dst) = (g.scratch dst 32).base :=
      h.valid.scratchAddress (by omega)
    rw [dstAddr] at out
    exact out

end VG.Proof.RsaPkcs1Enc.X86.Dec
