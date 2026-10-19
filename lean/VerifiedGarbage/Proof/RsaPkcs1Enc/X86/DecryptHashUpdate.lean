module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptHashUpdatePre
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Word32

/-! # A verified SHA-256 update preserves the other decryption buffers -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem shaUpdate_call (v : VG.Proof.Sha256.X86.Variants.Backend)
    {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {data : BitVec 32} {len count : Nat}
    (h : Context g bs s) (a : Arguments g (updateValues g data len count) 6 s)
    (dataFit : data.toNat + len ≤ 2 ^ 32) (lengthBound : len < 2 ^ 32) (countBound : count < 2 ^ 32)
    (dataState : (⟨byteAddr data, len⟩ : Region).Disjoint (g.scratch sSt 96))
    (dataScratch : (⟨byteAddr data, len⟩ : Region).Disjoint (g.scratch sHash 608))
    (calleeData : g.calleeRegion.Disjoint ⟨byteAddr data, len⟩)
    (dataArgs : (⟨byteAddr data, len⟩ : Region).Disjoint ⟨byteAddr g.stack, 24⟩)
    (dataRead : InRegions (s.rd ++ s.wr) (byteAddr data) len)
    {iv : Spec.Sha256.HashValue} {msg : List Byte}
    (repr : Spec.Sha256.ReprFrom iv s.mem (g.scratch sSt 96).base msg) (msgLength : msg.length = count) :
    WP isa (.call (hashFns v).updN (hashFns v).updC) s fun t => Context g bs t ∧
      Frame (hashWrites g) s.mem t.mem ∧ Frame (updateWr g ++ [g.calleeRegion]) s.mem t.mem ∧
      Keeps callClobbers s t ∧
      Spec.Sha256.ReprFrom iv t.mem (g.scratch sSt 96).base
        (msg ++ Spec.Rsa.bytesAt s.mem (byteAddr data) len) := by
  have argsWrite : InRegions s.wr (byteAddr g.stack) 24 := by
    have raw := h.inner.write (d := 0) (n := 24) (by decide)
    simpa only [BitVec.add_zero] using raw
  have W : Covers (updateWr g) s.wr := (Covers.one (h.scratchWrite (by decide : sSt + 96 ≤ 8448))).cons
    ((Covers.one (h.scratchWrite (by decide : sHash + 608 ≤ 8448))).pair (Covers.one argsWrite))
  have R : Covers (updateRd g data len) (s.rd ++ s.wr) := Covers.one dataRead
  refine WP.mono (hash_call_ok h (update_verified v)
    (Nat.le_trans v.stream.updSU (by decide)) v.stream.updSp
    (shaUpdate_pre h a dataFit lengthBound dataState dataScratch calleeData dataArgs)
    (Covers.append_left R W.right) W ?_) ?_
  · intro r hr
    simp only [updateWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨g.workspaceRegion, by simp [hashWrites], h.valid.scratchSub (by decide : sSt + 96 ≤ 8448)⟩
    · exact ⟨g.workspaceRegion, by simp [hashWrites], h.valid.scratchSub (by decide : sHash + 608 ≤ 8448)⟩
    · exact ⟨_, by simp [hashWrites], Region.sub_prefix (by decide : 24 ≤ 80)⟩
  · rintro t ⟨ht, F, Ffine, K, u, M, _, post⟩
    refine ⟨ht, F, Ffine, K, ?_⟩
    sig_post [Spec.Sha256.updateScratchContract, Spec.Sha256.updateScratchSig, Spec.Sha256.updatePost,
      abi, argSlots, argVal, argBytes] at post
    have sa := fun {j : Nat} (hj : j < 6) => callArgument_value h a (by decide : 6 ≤ 20) hj (updateRd g data len) (updateWr g)
    have v0 : updateValues g data len count 0 = g.workspace := rfl
    have v1 : updateValues g data len count 1 = BitVec.ofNat 32 count := rfl
    have v2 : updateValues g data len count 2 = 0 := rfl
    have v3 : updateValues g data len count 3 = data := rfl
    have v4 : updateValues g data len count 4 = BitVec.ofNat 32 len := rfl
    simp only [sa (by decide : 0 < 6), sa (by decide : 1 < 6), sa (by decide : 2 < 6),
      sa (by decide : 3 < 6), sa (by decide : 4 < 6), v0, v1, v2, v3, v4,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt lengthBound, M] at post
    have stateEq : (g.scratch sSt 96).base = byteAddr g.workspace := by simp [Geometry.scratch, sSt]
    have entryRepr : Spec.Sha256.ReprFrom iv s.callEntry.mem (g.scratch sSt 96).base msg := by
      apply repr_frame h.callFrame ?_ repr
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ((h.valid.stackWorkspace.sub_left h.valid.calleeSub).sub_right
        (h.valid.scratchSub (by decide : sSt + 96 ≤ 8448))).symm
    have dataBytes : Spec.Rsa.bytesAt s.callEntry.mem (byteAddr data) len = Spec.Rsa.bytesAt s.mem (byteAddr data) len := by
      apply VG.Proof.Rsa.rsa_bytes_frame h.callFrame (by omega)
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact calleeData.symm
    rw [stateEq] at entryRepr ⊢
    have out := post iv msg entryRepr (by rw [Word32.count_eq countBound, msgLength])
    change Spec.Sha256.ReprFrom iv t.mem (byteAddr g.workspace)
      (msg ++ Spec.Rsa.bytesAt s.callEntry.mem (byteAddr data) len) at out
    rw [dataBytes] at out
    exact out

end VG.Proof.RsaPkcs1Enc.X86.Dec
