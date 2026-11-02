module

public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivResult
import VerifiedGarbage.Proof.Rsa.RISCV64.PrivFinal
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_private_checked` on RISC-V: correctness

The restores (`restore_ok`), then the blocks and calls in order
(`code_correct`), from the frame's `alloc` to its `free`, to the outcome
(`final_ok`), on the registers and the stack (`fnPost`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Priv

open VG VG.RISCV64 VG.Impl.Rsa.RISCV64.Priv VG.RISCV64.RegUpd

theorem Late.keep {s t u : State} (L : Late s t) {rs : List Reg} (k : Keep rs t u) (hsp : u.sp = t.sp)
    (hm : u.mem = t.mem) (hrs : ∀ r ∈ preserved, r ∉ rs := by decide) : Late s u :=
  ⟨hsp.trans L.sp, k.2.1.trans L.rd, k.2.2.trans L.wr, (k.gpr (hrs _ (by decide))).trans L.s1,
    (k.gpr (hrs _ (by decide))).trans L.s2, (k.gpr (hrs _ (by decide))).trans L.s3,
    (k.gpr (hrs _ (by decide))).trans L.s4, (k.gpr (hrs _ (by decide))).trans L.s5,
    (k.gpr (hrs _ (by decide))).trans L.s6,
    fun r hr => (k.gpr (hrs r (by revert r; decide))).trans (L.hi r hr), hm ▸ L.mem, hm ▸ L.sv⟩

/-- The frame's words are apart from `out` and `m`. -/
theorem slot_apart {s : State} (h : PreP s) {d : Nat} (hd : d + 8 ≤ oM) {r : Region} (hr : r ∈ [oR s, mR s]) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.ko.sub_left (frame_sub s (by unfold oM frameBytes at *; omega))
  · exact Offset.disjoint _ (.inl hd) (by unfold oM at hd; omega) (by have := h.k2; unfold oM; omega)

theorem Late.release {s t u : State} (h : PreP s) (L : Late s t) (k : Keep [.a1, .a2, .t2, .t3, .t5] t u)
    (hsp : u.sp = t.sp) (hf : Frame [oR s, mR s] t.mem u.mem) : Late s u := by
  refine ⟨hsp.trans L.sp, k.2.1.trans L.rd, k.2.2.trans L.wr, (k.gpr (by decide)).trans L.s1,
    (k.gpr (by decide)).trans L.s2, (k.gpr (by decide)).trans L.s3, (k.gpr (by decide)).trans L.s4,
    (k.gpr (by decide)).trans L.s5, (k.gpr (by decide)).trans L.s6,
    fun r hr => (k.gpr (by revert r; decide)).trans (L.hi r hr), L.mem.trans (hf.sub fun r hr => ?_),
    L.sv.frame hf fun p hp r hr => slot_apart h (by have := saved_offs p hp; unfold oSave oM at *; omega) hr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
  · exact ⟨_, List.mem_cons_self .., mR_sub h⟩

/-- The restores. -/
theorem restore_ok {s w : State} (h : PreP s) (L : Late s w) :
    WP isa (.block restore) w fun v =>
      (∀ r ∈ preserved, v.gpr r = s.gpr r) ∧ v.gpr .ra = s.gpr .ra ∧ v.sp = fb s ∧ v.mem = w.mem ∧
        v.gpr .a0 = w.gpr .a0 := by
  rw [restore_eq]
  refine WP.block_append_iff.mpr (WP.block_cons_iff.mpr ⟨_, exec_addSp (imm := 0) (by decide),
    WP.block_nil ?_⟩)
  refine WP.mono (Spill.restore_wp (b := .t0) (B := fb s) (by have := fb_al h; omega)
    (by rw [gpr_write_self, L.sp]; exact BitVec.add_zero _) restored_offs restorable (fun p hp => by
      have := saved_offs p (restored_saved p hp)
      show InRegions (w.rd ++ w.wr) _ 8
      rw [L.wr]
      exact ⟨kR s, List.mem_append_right _ (List.mem_cons_self ..),
        frame_contains s (by unfold oSave frameBytes at *; omega)⟩)
    (L.sv.sub restored_saved)) fun v R => ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rcases preserved_split hr with hs | hs
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
      exact R.gpr p ((by decide : ∀ p ∈ saved, p ∈ restored) p hp)
    · have : r ∉ restored.map Prod.fst := by revert r; decide
      rw [R.other r this, gpr_write_of_ne _ _ (by revert r; decide)]
      exact L.hi r hs
  · exact R.gpr (.ra, oRa) (by decide)
  · rw [R.sp]; exact L.sp
  · rw [R.mem]; rfl
  · rw [R.other _ (by decide), gpr_write_of_ne _ _ (by decide)]

/-- The outcome, on the registers and the stack. -/
def fnPost (s s' : State) : Prop :=
  Spec.Rsa.writtenOutcome s'.mem (s.gpr .a0) (s.gpr .a3).toNat ((s'.gpr .a0).setWidth 32)
    (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat))

theorem code_correct (s : State) (hpre : (Spec.Rsa.privateCheckedContract RISCV64.abi frameBytes).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ fnPost s t := by
  show WP isa code s fun t => abiPreserved s t ∧ fnPost s t
  have h := preP_of hpre
  have hk := h.k2
  unfold code
  refine WP.allocLe ⟨by decide, by decide, by decide⟩ h.sp1 ?_
  unfold body
  refine WP.seq (WP.mono (setup_ok h) fun t₁ A => ?_)
  refine WP.seq (crtCall_ok h A fun t₂ M C => ?_)
  refine WP.seq (WP.mono (preArgs_ok h M C) fun t₃ P => ?_)
  refine WP.seq (preCall_ok h P fun t₄ Q4 => ?_)
  refine WP.seq (WP.mono (pubArgs_ok h Q4) fun t₅ R => ?_)
  refine WP.seq (pubCall_ok h R fun t₆ C6 => ?_)
  refine WP.seq (WP.mono (cmpArgs_ok h C6) fun t₇ L => ?_)
  refine WP.seq (WP.mono (WP.rdwr (compare_ok h L)) fun t₈ ⟨⟨a8, m8, k8⟩, _, _, sp8⟩ => ?_)
  have L8 : Late s t₈ := L.toLate.keep k8 sp8 m8
  have iSt : InRegions (t₈.rd ++ t₈.wr) (fb s + BitVec.ofNat 64 152) 8 := by
    rw [L8.wr]; exact ⟨kR s, List.mem_append_right _ (List.mem_cons_self ..), frame_contains s (by decide)⟩
  have iEs : InRegions (t₈.rd ++ t₈.wr) (fb s + BitVec.ofNat 64 160) 8 := by
    rw [L8.wr]; exact ⟨kR s, List.mem_append_right _ (List.mem_cons_self ..), frame_contains s (by decide)⟩
  refine WP.seq (WP.mono (WP.rdwr (result_ok (cs := t₇.mem.readW (fb s + BitVec.ofNat 64 oSt) 64)
    (es := t₇.mem.readW (fb s + BitVec.ofNat 64 oEs) 64) h L8.sp iSt iEs (by rw [m8]) (by rw [m8]) a8
    (cmpAcc_lt _ _ _ _) L8.s1 L8.s3))
    fun t₉ ⟨⟨⟨r0, r3, r5, r2, r3', m9⟩, k9⟩, _, _, sp9⟩ => ?_)
  have L9 : Late s t₉ := L8.keep k9 sp9 m9
  refine WP.seq (WP.mono (WP.rdwr (release_ok h L9 (fun b => Proof.Rsa.low_and_mask b _ _) r5 r2 r3' r3))
    fun t₁₀ ⟨⟨hout, f10, k10⟩, _, _, sp10⟩ => ?_)
  have L10 := L9.release h k10 sp10 f10
  refine WP.mono (restore_ok h L10) fun v ⟨vp, vra, vs, vm, v0⟩ => ?_
  have fs : (freed frameBytes v).sp = v.sp + BitVec.ofNat 64 frameBytes := by simp only [freed]
  have fg : (freed frameBytes v).gpr = v.gpr := by simp only [freed]
  have fm : (freed frameBytes v).mem = v.mem := by simp only [freed]
  refine ⟨⟨fun r hr => by rw [fg]; exact vp r hr, ?_, by rw [fg]; exact vra⟩, ?_⟩
  · rw [fs, vs]; exact BitVec.sub_add_cancel _ _
  · unfold fnPost
    rw [fm, fg, vm, v0, k10.gpr (by decide), r0]
    have m97 : t₉.mem = t₇.mem := m9.trans m8
    rw [m97] at hout
    have hx : Spec.Rsa.bytesAt t₇.mem (s.gpr .a6) (s.gpr .a3).toNat =
        Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a3).toNat :=
      bytes_of_frame L.mem (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rw [iR_eq h]
        rcases hr with rfl | rfl | rfl
        · exact h.ki.symm
        · exact h.oi.symm
        · exact h.is) (by have := h.wi; rw [h.h7] at this; omega)
    refine final_ok (Proof.Rsa.bytesAt_length' _ _ _) (Proof.Rsa.bytesAt_length' _ _ _) L.crt L.pub ?_ hout
    rw [cmpAcc_eq_zero, ← hx, Proof.Rsa.bytesAt_eq_iff]

end VG.Proof.Rsa.RISCV64.Priv
