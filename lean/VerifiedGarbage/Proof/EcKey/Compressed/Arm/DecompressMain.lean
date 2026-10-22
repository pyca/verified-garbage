module

public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.DecompressContract
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.DecompressMiddle
import VerifiedGarbage.Proof.EcKey.Compressed.Arm.DecompressFinish
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.EcKey.Compressed.Decode

/-! # Decompression meets the merged API contract -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Ecdsa.Arm
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm Spec.Weierstrass

theorem decompress_key (c : Cfg) (root : Fe c.C → Fe c.C) (s : State) :
    Impl.EcKey.Compressed.decode c.C root
      (Spec.EcKey.bytesAt s.mem (ptr s .r1) (c.C.len + 1)) =
    if CompressedAccept c root s then
      some (.affine (Fin.ofNat c.C.p (keyX c s)) (keyRoot c root s)) else none := by
  have hb : Spec.Ecdsa.bytesAt s.mem (ptr s .r1) (c.C.len + 1) =
      s.mem (ptr s .r1) :: Spec.Ecdsa.bytesAt s.mem (ptr s .r1 + 1) c.C.len := by
    rw [Nat.add_comm c.C.len 1, bytesAt_add]
    simp only [Spec.Ecdsa.bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero,
      List.cons_append, List.nil_append]
    rfl
  apply decode_checked_eq root (length_bytesAt _ _ _)
    (by change (Spec.Ecdsa.bytesAt _ _ _).head? = _; rw [hb]; rfl)
    (by change ofBytes ((Spec.Ecdsa.bytesAt _ _ _).drop 1) = _; rw [hb]; rfl)

theorem decompress_correct (c : Cfg) (hc : CfgOk c)
    (root : Fe c.C → Fe c.C) (hroot : CandidateCorrect c root)
    (s : State) (hs : (decompressContract c.C root).pre s) :
    ∃ t s', Exec isa (Impl.EcKey.Compressed.Arm.decompress c) s t s' ∧
      abiPreserved s s' ∧ (decompressContract c.C root).post s s' := by
  obtain ⟨hrd, hwr, hpo, hpw, how, hfit, hpkfit, hwfit⟩ := hs
  have hp : InputPre c (1 + c.C.len) s :=
    ⟨by rw [hrd]; simp [Nat.add_comm], by rw [hwr]; simp,
      by simpa only [Nat.add_comm] using hpw, by omega, hwfit⟩
  have hrun : WP isa (Impl.EcKey.Compressed.Arm.decompress c) s fun s' =>
      (decompressContract c.C root).post s s' ∧
      (∀ rd ∈ Cfg.saved, s'.gpr rd.1 = s.gpr rd.1) ∧ s'.sp = s.sp := by
    apply decompressFront_ok hc hp
    intro t F
    refine WP.seq (WP.mono (decompressMiddle_ok hc hroot F) fun u U => ?_)
    refine WP.mono (decompressFinish_ok hc U.scr U.out (by omega)
      (by rw [U.wr, hwr, show 1 + 2 * c.C.len = 2 * c.C.len + 1 by omega]; simp)
      (by simpa only [Nat.add_comm] using how.sub_right (Region.sub_prefix (by decide : size ≤ 8192)))
      U.saved (decide (CompressedAccept c root s)) (by simp only [U.flag, decide_eq_true_eq]))
      fun s' ⟨hout, hret, hsave, K, _⟩ => ?_
    refine ⟨?_, hsave, K.sp.trans U.sp⟩
    dsimp only [decompressContract]
    rw [decompress_key]
    rw [U.x, U.y] at hout
    change Spec.EcKey.bytesAt s'.mem (ptr s .r0) (1 + 2 * c.C.len) = _ at hout
    simp only [decide_eq_true_eq] at hret hout
    simp only [BitVec.setWidth_append_eq_right]
    by_cases hk : CompressedAccept c root s
    · rw [ite_eq_left hk] at hret hout ⊢
      refine ⟨hret, ?_⟩
      change Spec.EcKey.bytesAt s'.mem (ptr s .r0) (2 * c.C.len + 1) =
        4 :: (toBytes c.C.len (Fin.ofNat c.C.p (keyX c s)).val ++ toBytes c.C.len (keyRoot c root s).val)
      simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt hk.1.2, Nat.add_comm] using hout
    · rw [ite_eq_right hk] at hret hout ⊢
      exact ⟨hret, by simpa only [Nat.add_comm] using hout⟩
  obtain ⟨t, s', he, hpost, hsave, hsp⟩ := hrun
  refine ⟨t, s', he, ⟨?_, hsp⟩, hpost⟩
  intro r hr
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsave (.r4, 0) (by decide)
  · exact hsave (.r5, 4) (by decide)
  · exact hsave (.r6, 8) (by decide)
  · exact hsave (.r7, 12) (by decide)
  · exact hsave (.r8, 16) (by decide)
  · exact hsave (.r9, 20) (by decide)
  · exact hsave (.r10, 24) (by decide)
  · exact hsave (.r11, 28) (by decide)
  · exact hsave (.lr, 32) (by decide)

end VG.Proof.EcKey.Compressed.Arm
