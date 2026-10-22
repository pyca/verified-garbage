module

public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Contract
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Front
import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Finish
import VerifiedGarbage.Proof.EcKey.Compressed.Encode
import VerifiedGarbage.Proof.Ecdh.Arm.Main

/-! # Compression meets the merged API contract -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Ecdsa.Arm
open VG.Proof.Ecdsa.Arm VG.Proof.Mont.Arm VG.Proof.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.Ecdh.Arm Spec.Weierstrass

theorem compress_key (c : Cfg) (s : State) :
    Spec.EcKey.compressPublicKey c.C
      (Spec.EcKey.bytesAt s.mem (ptr s .r1) (2 * c.C.len + 1)) =
    if KeyOk c s then some (BitVec.ofNat 8 (2 + keyY c s % 2) :: toBytes c.C.len (keyX c s)) else none := by
  have hlen : (Spec.Ecdsa.bytesAt s.mem (ptr s .r1) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]
    omega
  have hhead : (Spec.Ecdsa.bytesAt s.mem (ptr s .r1) (1 + 2 * c.C.len)).head? =
      some (s.mem (ptr s .r1)) := by rw [peer_bytes]; rfl
  have hx : ofBytes (((Spec.Ecdsa.bytesAt s.mem (ptr s .r1) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      keyX c s := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
    rfl
  have hy : ofBytes ((Spec.Ecdsa.bytesAt s.mem (ptr s .r1) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      keyY c s := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
  have hv : Proof.Ecdh.Valid c.C (s.mem (ptr s .r1)) (keyX c s) (keyY c s) ↔ KeyOk c s := by
    constructor
    · rintro ⟨h4, hx, hy, he⟩
      exact ⟨⟨⟨h4, hx⟩, hy⟩, he⟩
    · rintro ⟨⟨⟨h4, hx⟩, hy⟩, he⟩
      exact ⟨h4, hx, hy, he⟩
  change Spec.EcKey.compressPublicKey c.C
    (Spec.Ecdsa.bytesAt s.mem (ptr s .r1) (2 * c.C.len + 1)) = _
  rw [show 2 * c.C.len + 1 = 1 + 2 * c.C.len by omega, compress_eq hlen hhead hx hy]
  simp only [hv]

theorem compress_correct (c : Cfg) (hc : CfgOk c)
    (s : State) (hs : (compressContract c.C).pre s) :
    ∃ t s', Exec isa (Impl.EcKey.Compressed.Arm.compress c) s t s' ∧
      abiPreserved s s' ∧ (compressContract c.C).post s s' := by
  obtain ⟨hrd, hwr, hpo, hpw, how, hfit, hpkfit, hwfit⟩ := hs
  have hp : InputPre c (1 + 2 * c.C.len) s :=
    ⟨by rw [hrd, show 1 + 2 * c.C.len = 2 * c.C.len + 1 by omega]; simp,
      by rw [hwr]; simp, by simpa only [Nat.add_comm] using hpw,
      by omega, hwfit⟩
  have hrun : WP isa (Impl.EcKey.Compressed.Arm.compress c) s fun s' =>
      (compressContract c.C).post s s' ∧
      (∀ rd ∈ Cfg.saved, s'.gpr rd.1 = s.gpr rd.1) ∧ s'.sp = s.sp := by
    apply front_ok hc hp
    intro t F
    refine WP.mono (finish_ok hc F.scr F.out
      (by omega) (by rw [F.wr, hwr]; simp [Nat.add_comm])
      (by simpa only [Nat.add_comm] using
        how.sub_right (by simpa using Region.sub_prefix (by decide : size ≤ 8192)))
      F.saved (decide (KeyOk c s)) (by simp only [F.flag, decide_eq_true_eq]))
      fun s' ⟨hout, hret, hsave, K, _⟩ => ?_
    refine ⟨?_, hsave, K.sp.trans F.sp⟩
    change (match Spec.EcKey.compressPublicKey c.C
      (Spec.EcKey.bytesAt s.mem (ptr s .r1) (2 * c.C.len + 1)) with
      | some bs => _ | none => _)
    rw [compress_key]
    rw [F.x, F.y] at hout
    change Spec.EcKey.bytesAt s'.mem (ptr s .r0) (1 + c.C.len) = _ at hout
    simp only [decide_eq_true_eq] at hret hout
    simp only [BitVec.setWidth_append_eq_right]
    by_cases hk : KeyOk c s
    · rw [ite_eq_left hk] at hret hout ⊢
      exact ⟨hret, by simpa only [Nat.add_comm] using hout⟩
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
