module

import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivResult
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPubCall
public import VerifiedGarbage.Proof.Rsa.PrivCheck

/-!
# `vg_rsa_private_checked` on PPC64LE: the restores

`Late` through the blocks after the public operation (`Late.keep`,
`Late.release`), and the restores of our caller's registers and return
address (`restore_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv
open VG.Proof.Bignum.PPC64LE (Keep)

theorem Late.keep {s t u : State} (L : Late s t) {rs : List Reg} (k : Keep rs t u) (hm : u.mem = t.mem)
    (hrs : ∀ r ∈ preserved, r ∉ rs := by decide) : Late s u :=
  ⟨k.sp.trans L.sp, k.rd.trans L.rd, k.wr.trans L.wr, (k.gpr _ (hrs _ (by decide))).trans L.r24,
    (k.gpr _ (hrs _ (by decide))).trans L.r25, (k.gpr _ (hrs _ (by decide))).trans L.r26,
    (k.gpr _ (hrs _ (by decide))).trans L.r27, (k.gpr _ (hrs _ (by decide))).trans L.r28,
    (k.gpr _ (hrs _ (by decide))).trans L.r29,
    fun r hr => (k.gpr r (hrs r (by revert r; decide))).trans (L.hi r hr), hm ▸ L.mem, hm ▸ L.sv, hm ▸ L.ls⟩

/-- The frame's words are apart from `out` and `m`. -/
theorem slot_apart {s : State} (h : PreP s) {d : Nat} (hd : d + 8 ≤ oM) {r : Region} (hr : r ∈ [oR s, mR s]) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.ko.sub_left (frame_sub s (by unfold oM frameBytes at *; omega))
  · exact Offset.disjoint _ (.inl hd) (by unfold oM at hd; omega) (by have := h.k2; unfold oM; omega)

theorem Late.release {s t u : State} (h : PreP s) (L : Late s t) (k : Keep [.r0, .r6, .r7, .r8] t u)
    (hf : Frame [oR s, mR s] t.mem u.mem) : Late s u := by
  have mk : Region.Sub (mR s) (kR s) := frame_sub s (by have := h.k2; unfold oM frameBytes; omega)
  refine ⟨k.sp.trans L.sp, k.rd.trans L.rd, k.wr.trans L.wr, (k.gpr _ (by decide)).trans L.r24,
    (k.gpr _ (by decide)).trans L.r25, (k.gpr _ (by decide)).trans L.r26, (k.gpr _ (by decide)).trans L.r27,
    (k.gpr _ (by decide)).trans L.r28, (k.gpr _ (by decide)).trans L.r29,
    fun r hr => (k.gpr r (by revert r; decide)).trans (L.hi r hr), L.mem.trans (hf.sub fun r hr => ?_),
    L.sv.frame hf fun p hp r hr => slot_apart h (by have := saved_offs p hp; unfold oSave oM at *; omega) hr, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self .., mk⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => slot_apart h (by decide) hr) (by decide)]; exact L.ls

/-- The restores. -/
theorem restore_ok {s w : State} (L : Late s w) :
    WP isa (.block restore) w fun v =>
      (∀ r ∈ preserved, v.gpr r = s.gpr r) ∧ v.lr = s.lr ∧ v.sp = fb s ∧ v.mem = w.mem ∧ v.gpr .r3 = w.gpr .r3 := by
  have iLr : InRegions (w.rd ++ w.wr) (fb s + BitVec.ofNat 64 oLr) 8 := by
    rw [L.wr]; exact in_fr' s _ _ (by decide) (by decide)
  have c1 : oLr < 2 ^ 15 := by decide
  have c2 : oLr % 4 = 0 := by decide
  rw [restore_eq]
  refine WP.block_append_iff.mpr (WP.mono (Q := fun v => v = { ((w.write .r12 w.sp).write .r0
      (w.mem.readW (fb s + BitVec.ofNat 64 oLr) 64)) with lr := w.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 })
    ?_ fun v e => ?_)
  · prun [exec_addSp0, L.sp, iLr, c1, c2, exec_mtlr]
  · subst e
    refine WP.mono (Spill.restore_wp (b := .r12) (B := fb s) (by decide) (by simp [State.write, L.sp])
      saved_ho (by decide) (fun p hp => by
        have := saved_offs p hp
        show InRegions (w.rd ++ w.wr) _ 8
        rw [L.wr]; exact in_fr' s _ _ (by unfold oSave at this; omega) (by unfold oSave at this; unfold frameBytes; omega))
      L.sv) fun v R => ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · rcases preserved_split hr with hs | hs
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
        exact R.gpr p hp
      · have : r ∉ saved.map Prod.fst := by revert r; decide
        rw [R.other r this]
        have h12 : r ≠ .r12 := by revert r; decide
        have h0 : r ≠ .r0 := by revert r; decide
        simp only [State.write, h12, h0, ite_false]
        exact L.hi r hs
    · rw [R.lr]; exact L.ls
    · rw [R.sp]; exact L.sp
    · rw [R.mem]; rfl
    · rw [R.other _ (by decide)]; simp [State.write]
