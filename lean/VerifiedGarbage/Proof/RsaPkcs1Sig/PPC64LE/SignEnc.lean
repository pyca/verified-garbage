module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.SignSetup
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_rsa_pkcs1_sign` on PPC64LE: the encoding

`encode` (`Proof/RsaPkcs1Sig/PPC64LE/Encode.lean`) from `AtEnc`: its
precondition (`AtEnc.epre`) and what follows it (`enc_ok`, into `AtAft`):
`EM` in the frame and 1, or 0, as the encoding of the hash value succeeds
(`encOut`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Sign

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.Sign
open VG.Proof.RsaPkcs1Sig.PPC64LE (EPre EPost EOut encodeId encode_ok)

/-- `EM`, in the frame. -/
abbrev emR (s : State) : Region := ⟨fb s + BitVec.ofNat 64 oEM, (s.gpr .r6).toNat⟩

theorem em_sub {s : State} (h : SPre s) : Region.Sub (emR s) (kR s) :=
  frame_sub s (by have := h.k2; unfold oEM frameBytes; omega)

/-- The hash value. -/
abbrev hashOf (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat

/-- The encoding of the hash value, if it succeeds. -/
abbrev encOut (s : State) : Option (List Byte) :=
  encodeId ((s.gpr .r9).setWidth 32) (hashOf s) (s.gpr .r6).toNat

/-- A byte of `EM` is in the local variable space. -/
theorem em_in {s : State} (h : SPre s) (rs : List Region) {i : Nat} (hi : i < (s.gpr .r6).toNat) :
    InRegions (fr s :: rs) (fb s + BitVec.ofNat 64 oEM + BitVec.ofNat 64 i) 1 := by
  rw [Offset.add_add]; exact in_fr s rs (by unfold oEM; omega) (by have := h.k2; unfold oEM frameBytes; omega)

theorem bytes_of_frame {s : State} {rs : List Region} {m : Mem} (hf : Frame rs s.mem m) {p : Addr}
    {len : Nat} (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, len⟩ r) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) hd hl (List.mem_range.mp hi)

theorem AtEnc.epre {s t : State} (h : SPre s) (A : AtEnc s t) :
    EPre t ((s.gpr .r9).setWidth 32) (s.gpr .r6).toNat := by
  refine ⟨by rw [A.r6, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq], by rw [A.r5], h.k2, fun i hi => ?_, fun j hj => ?_, fun j hj i hi e => ?_⟩
  · rw [A.r4, A.wr]; exact em_in h _ hi
  · rw [A.r7, A.rd, h.hrd]
    rw [A.r8] at hj
    exact ⟨dR s, List.mem_append_left _ (by simp), Offset.contains_base _ (by omega) (by have := h.wd; omega)⟩
  · rw [A.r8] at hj
    rw [A.r7, A.r4] at e
    have c1 : (dR s).Contains (s.gpr .r10 + BitVec.ofNat 64 j) 1 :=
      Offset.contains_base _ (by omega) (by have := h.wd; omega)
    have c2 : (kR s).Contains (s.gpr .r10 + BitVec.ofNat 64 j) 1 := by
      rw [e, Offset.add_add]; exact frame_contains s (by have := h.k2; unfold oEM frameBytes; omega)
    exact h.kd _ c2 c1

theorem encodeId_len {x : BitVec 32} {H em : List Byte} {k : Nat} (h : encodeId x H k = some em) :
    em.length = k := by
  unfold encodeId at h
  split at h
  · exact Proof.RsaPkcs1Sig.encode_length h
  · cases h

/-- After `encode`. -/
structure AtAft (s u : State) : Prop extends Fr s u where
  r12 : u.gpr .r12 = fb s
  r26 : u.gpr .r26 = s.gpr .r3
  r27 : u.gpr .r27 = s.gpr .r5
  r28 : u.gpr .r28 = s.gpr .r6
  r29 : u.gpr .r29 = s.gpr .r7
  r30 : u.gpr .r30 = s.gpr .r8
  enc : match encOut s with
    | some em => u.gpr .r3 = 1 ∧ Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oEM) (s.gpr .r6).toNat = em
    | none => u.gpr .r3 = 0

/-- The frame's words below `EM` are apart from it. -/
theorem below_em {s : State} (h : SPre s) {d : Nat} (hd : d + 8 ≤ oEM) {r : Region} (hr : r ∈ [emR s]) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r := by
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint _ (.inl hd) (by unfold oEM at hd; omega) (by have := h.k2; unfold oEM; omega)

theorem enc_ok {s t : State} (h : SPre s) (A : AtEnc s t) :
    WP isa Impl.RsaPkcs1Sig.PPC64LE.encode t (AtAft s) := by
  have hk := h.k2
  have hH : Spec.Rsa.bytesAt t.mem (t.gpr .r7) (t.gpr .r8).toNat = hashOf s := by
    rw [A.r7, A.r8]
    exact bytes_of_frame A.mem (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.kd.symm)
      (by have := h.wd; omega)
  refine WP.mono (encode_ok (A.epre h)) fun u ⟨kp, eo⟩ => ?_
  rw [hH] at eo
  have hf : Frame [emR s] t.mem u.mem ∧ (match encOut s with
      | some em => u.gpr .r3 = 1 ∧ Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oEM) (s.gpr .r6).toNat = em
      | none => u.gpr .r3 = 0) := by
    show Frame _ _ _ ∧ match encOut s with | some em => _ | none => _
    unfold encOut
    revert eo
    cases he : encodeId ((s.gpr .r9).setWidth 32) (hashOf s) (s.gpr .r6).toNat with
    | none => intro eo; simp only [EOut] at eo; exact ⟨eo.2 ▸ Frame.refl _ _, eo.1⟩
    | some em =>
      intro eo
      have hl := encodeId_len he
      simp only [EOut] at eo
      rw [A.r4] at eo
      refine ⟨eo.2 ▸ VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _), eo.1, ?_⟩
      rw [eo.2, ← hl]; exact Proof.RsaPkcs1Sig.bytesAt_writeBytes _ _ _ (by omega)
  obtain ⟨hf, he⟩ := hf
  refine ⟨⟨kp.sp.trans A.sp, kp.rd.trans A.rd, kp.wr.trans A.wr, kp.lr.trans A.lr,
    fun r hr => (kp.gpr r (by revert r; decide)).trans (A.hi r hr),
    A.mem.trans (hf.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, em_sub h⟩),
    A.sv.frame hf fun p hp r hr => below_em h (by have := saved_offs p hp; unfold oSave oEM at *; omega) hr, ?_⟩,
    (kp.gpr _ (by decide)).trans A.r12, (kp.gpr _ (by decide)).trans A.r26, (kp.gpr _ (by decide)).trans A.r27,
    (kp.gpr _ (by decide)).trans A.r28, (kp.gpr _ (by decide)).trans A.r29, (kp.gpr _ (by decide)).trans A.r30, he⟩
  rw [hf.readW (Region.contains_self _ _) (fun r hr => below_em h (by decide) hr) (by decide)]; exact A.ls

end VG.Proof.RsaPkcs1Sig.PPC64LE.Sign
