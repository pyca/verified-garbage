module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawWitness
public import VerifiedGarbage.Proof.Dsa.X86.Generation.RememberDraw
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ControlKeeps
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Offset

/-! Consume one complete padded draw and retain its exact next cursor and length. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86

def DrawFrame (base : Addr) (len : Nat) (s t : State) : Prop :=
  Frame [⟨off base Layout.witness, len⟩, ⟨off base Layout.control, 512⟩] s.mem t.mem

def DrawWrites (base : Addr) (len : Nat) (s t : State) : Prop :=
  Frame [⟨off base Layout.witness, len⟩, ⟨off base witnessCursor, 4⟩,
    ⟨off base witnessRemaining, 4⟩] s.mem t.mem

theorem draw_control_before {s t : State} {base : Addr} {len d : Nat}
    (F : DrawWrites base len s t) (length : len ≤ 384)
    (lo : Layout.control ≤ d) (hi : d + 4 ≤ Layout.control + 32) :
    t.mem.readW (off base d) 32 = s.mem.readW (off base d) 32 := by
  apply F.readW (r := ⟨off base d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint base (.inr (by simp only [Layout.witness, Layout.control] at lo ⊢; omega))
      (by unfold Layout.control at hi; omega) (by unfold Layout.witness; omega)
  · exact Offset.disjoint base (.inl hi) (by unfold Layout.control at hi; omega) (by decide)
  · exact Offset.disjoint base (.inl (Nat.le_trans hi (by decide)))
      (by unfold Layout.control at hi; omega) (by decide)

theorem draw_from_tape {s : State} {base : Addr} {bytes len drawBytes remaining : Nat} {src : BitVec 32}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (positive : 0 < len) (length : len ≤ drawBytes) (upper : len ≤ 384)
    (cursor : s.mem.readW (off base witnessCursor) 32 = src)
    (value : s.mem.readW (off base witnessRemaining) 32 = BitVec.ofNat 32 remaining)
    (room : drawBytes ≤ remaining) (bound : remaining < 2 ^ 32)
    (sourceFit : src.toNat + drawBytes ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (byteAddr src) drawBytes)
    (apart : Region.Disjoint ⟨byteAddr src, drawBytes⟩ ⟨base, bytes⟩) :
    WP isa (drawFromTape len drawBytes) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base Layout.witness) len =
        Spec.Rsa.bytesAt s.mem (off (byteAddr src) (drawBytes - len)) len ∧
      t.mem.readW (off base witnessCursor) 32 = src + BitVec.ofNat 32 drawBytes ∧
      t.mem.readW (off base witnessRemaining) 32 = BitVec.ofNat 32 (remaining - drawBytes) ∧
      DrawFrame base len s t ∧ DrawWrites base len s t ∧ Keeps [.eax, .ebx, .ecx, .esi] s t := by
  unfold drawFromTape
  refine WP.seq (wp_movS (readSrc_sc scr (d := witnessCursor) (by
    have : witnessCursor + 4 ≤ 40960 := by decide
    omega)) fun a A _ => WP.block_nil ?_)
  have Sa := scr.of_keeps A.keeps (by decide)
  refine WP.seq (WP.mono (draw_copy Sa capacity positive length upper (A.gpr.trans cursor) sourceFit
    (by rw [A.rd, A.wr]; exact read) apart) fun b ⟨copy, next, Fb, Kb⟩ => ?_)
  have Sb := Sa.of_keeps Kb (by decide)
  have remainingB : b.mem.readW (off base witnessRemaining) 32 = BitVec.ofNat 32 remaining := by
    rw [buffer_control Fb upper witnessRemaining (by decide) (by decide), A.mem, value]
  refine WP.mono (remember_draw Sb capacity room bound remainingB) fun t ⟨memory, Kt⟩ => ?_
  have Fc : Frame [⟨off base Layout.control, 512⟩] b.mem t.mem := by
    rw [memory]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains base (by decide : Layout.control ≤ witnessCursor) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains base (by decide : Layout.control ≤ witnessRemaining) (by decide) (by decide))
  refine ⟨?_, ?_, ?_, ?_, ?_, ((A.keeps.mono (by decide)).trans Kb).trans (Kt.mono (by decide))⟩
  · have unchanged := VG.Proof.Dsa.Generation.frame_bytesAt Fc (p := off base Layout.witness) (len := len)
      (by
        intro r hr
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint base (.inl (by simp only [Layout.witness, Layout.control]; omega))
          (by unfold Layout.witness; omega) (by decide)) (by omega)
    rw [unchanged, copy, A.mem]
  · rw [memory, Mem.readW_writeW_sep (Offset.sep base (.inl (by decide : witnessCursor + 4 ≤ witnessRemaining))
      (by decide) (by decide)) (by decide), Mem.readW_writeW_self32, next]
  · rw [memory, Mem.readW_writeW_self32]
  · have first : DrawFrame base len s b := by
      unfold DrawFrame
      rw [← A.mem]
      exact Fb.mono (by simp)
    exact first.trans (Fc.mono (by simp))
  · have first : DrawWrites base len s b := by
      unfold DrawWrites
      rw [← A.mem]
      exact Fb.mono (by simp)
    apply first.trans
    rw [memory]
    exact ((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW
      (by simp) _ (Region.contains_self _ _)

end VG.Proof.Dsa.X86.Generation
