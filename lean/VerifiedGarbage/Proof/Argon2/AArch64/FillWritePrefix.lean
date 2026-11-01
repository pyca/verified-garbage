module

public import VerifiedGarbage.Proof.Argon2.AArch64.Finish
public import VerifiedGarbage.Impl.Argon2.AArch64.FillWrite
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
public import VerifiedGarbage.Proof.Argon2.Contract

/-! Merged from `Proof.Argon2.AArch64.FillWriteWord`. -/

@[expose] public section

section
/-! One output word, keeping register writes folded during execution. -/

namespace VG.Proof.Argon2.AArch64.FillWrite

open VG VG.AArch64 VG.Impl.Argon2.AArch64.FillWrite
open VG.Impl.Argon2.AArch64

/-- Registers preserved while copying/XORing matrix words and testing the pass. -/
def CopyKeeps (s t : State) : Prop :=
  (∀ r, r ≠ .x8 → r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → t.gpr r = s.gpr r) ∧
    t.rd = s.rd ∧ t.wr = s.wr

theorem CopyKeeps.refl (s : State) : CopyKeeps s s := ⟨fun _ _ _ _ _ => rfl, rfl, rfl⟩
theorem CopyKeeps.trans {s t u : State} (h : CopyKeeps s t) (k : CopyKeeps t u) : CopyKeeps s u :=
  ⟨fun r h8 h13 h14 h15 => (k.1 r h8 h13 h14 h15).trans (h.1 r h8 h13 h14 h15),
    k.2.1.trans h.2.1, k.2.2.trans h.2.2⟩

def value (xorOld : Bool) (m : Mem) (src dest : Addr) (i : Nat) : Addr :=
  let next := m.readW (off src (8 * i)) 64
  if xorOld then next ^^^ m.readW (off dest (8 * i)) 64 else next

/-- The source is readable and the destination writable; its old contents
are read only on later passes. -/
theorem pair_ok (xorOld : Bool) (s : State) (i : Nat) (hi : i < 64)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .x1) (16 * i)) 16)
    (hw : InRegions s.wr (off (s.gpr .x0) (16 * i)) 16)
    (ho : InRegions (s.rd ++ s.wr) (off (s.gpr .x0) (16 * i)) 16) :
    WP isa (.block (Impl.Argon2.AArch64.FillWrite.pair xorOld i)) s fun t =>
      t.mem = (s.mem.writeW (off (s.gpr .x0) (8 * (2 * i)))
          (value xorOld s.mem (s.gpr .x1) (s.gpr .x0) (2 * i))).writeW
        (off (s.gpr .x0) (8 * (2 * i + 1)))
          (value xorOld s.mem (s.gpr .x1) (s.gpr .x0) (2 * i + 1)) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have e : (16 * i) % 16 = 0 ∧ 16 * i < 65536 := by omega
  simp only [off] at hr hw ho
  have a0 : 8 * (2 * i) = 16 * i := by omega
  have a1 : 8 * (2 * i + 1) = 16 * i + 8 := by omega
  cases xorOld
  · refine WP.block_cons_iff.mpr ⟨_, exec_ldrq_dwords e hr, ?_⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_strq_write e hw, ?_⟩
    refine WP.block_nil ⟨?_, rfl, rfl, rfl, rfl⟩
    simp only [RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.v_setV_self, write16_dwords,
      Offset.add_add, value, off, a0, a1, Bool.false_eq_true, ite_false]
  · refine WP.block_cons_iff.mpr ⟨_, exec_ldrq_dwords e hr, ?_⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_ldrq_dwords e ho, ?_⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_eor_v, ?_⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_strq_write e hw, ?_⟩
    refine WP.block_nil ⟨?_, rfl, rfl, rfl, rfl⟩
    simp only [RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.v_setV_self,
      RegUpd.v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v1), ofVDwords_xor, write16_dwords,
      Offset.add_add, value, off, a0, a1, ite_true]

end VG.Proof.Argon2.AArch64.FillWrite
end

/-! Compose the pair writes without re-executing a long load/store block. -/

namespace VG.Proof.Argon2.AArch64.FillWrite

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.FillWrite

def result (xorOld : Bool) (m : Mem) (src dest : Addr) : Block :=
  if xorOld then xorBlock (blockAt m src) (blockAt m dest) else blockAt m src

theorem result_get (xorOld : Bool) (m : Mem) (src dest : Addr) (i : Fin 128) :
    (result xorOld m src dest)[i] = value xorOld m src dest i.val := by
  cases xorOld <;> simp only [result, value, Bool.false_eq_true, ite_false, ite_true,
    xorBlock_get, blockAt_get]

theorem frame_extend {m m' : Mem} {dest : Addr} {n k : Nat}
    (hf : Frame [⟨dest, 8 * n⟩] m m') (h : n ≤ k) : Frame [⟨dest, 8 * k⟩] m m' := by
  apply hf.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨_, by simp, Region.sub_prefix (Nat.mul_le_mul_left 8 h)⟩

theorem source_read {m m' : Mem} {src dest : Addr} {n : Nat}
    (hf : Frame [⟨dest, 8 * n⟩] m m') (hn : n ≤ 128)
    (hd : (⟨src, 1024⟩ : Region).Disjoint ⟨dest, 1024⟩) (i : Fin 128) :
    m'.readW (off src (8 * i.val)) 64 = m.readW (off src (8 * i.val)) 64 := by
  have full := frame_extend hf hn
  exact full.readW (r := ⟨src, 1024⟩)
    (Offset.contains_base src (by omega) (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)

theorem old_read {m m' : Mem} {dest : Addr} {n k : Nat}
    (hf : Frame [⟨dest, 8 * n⟩] m m') (hk : n ≤ k) (hk' : k < 128) :
    m'.readW (off dest (8 * k)) 64 = m.readW (off dest (8 * k)) 64 :=
  hf.readW (r := ⟨off dest (8 * k), 8⟩) (Region.contains_self _ _)
    (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact Offset.disjoint_base dest (by omega) (by omega)) (by decide)

theorem prefix_ok (xorOld : Bool) (n : Nat) (hn : n ≤ 64) (s : State)
    (hs : (⟨s.gpr .x1, 1024⟩ : Region) ∈ s.rd ++ s.wr)
    (hw : (⟨s.gpr .x0, 1024⟩ : Region) ∈ s.wr)
    (hd : (⟨s.gpr .x1, 1024⟩ : Region).Disjoint ⟨s.gpr .x0, 1024⟩) :
    WP isa (.block (words xorOld n)) s fun t =>
      Written t.mem (s.gpr .x0) (result xorOld s.mem (s.gpr .x1) (s.gpr .x0)) (2 * n) ∧
      Frame [⟨s.gpr .x0, 8 * (2 * n)⟩] s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.sp = s.sp := by
  induction n with
  | zero => exact WP.block_nil ⟨fun i hi => by omega, Frame.refl _ _, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    simp only [words, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro t ⟨written, frame, gpr, rd, wr, mx⟩
    have hn' : n < 64 := by omega
    have src : t.gpr .x1 = s.gpr .x1 := congrFun gpr .x1
    have dest : t.gpr .x0 = s.gpr .x0 := congrFun gpr .x0
    have write : InRegions t.wr (off (t.gpr .x0) (16 * n)) 16 := by
      rw [dest, wr]
      exact ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩
    have read : InRegions (t.rd ++ t.wr) (off (t.gpr .x1) (16 * n)) 16 := by
      rw [src, rd, wr]
      exact ⟨_, hs, Offset.contains_base _ (by omega) (by omega)⟩
    have old : InRegions (t.rd ++ t.wr) (off (t.gpr .x0) (16 * n)) 16 := by
      obtain ⟨r, hr, hc⟩ := write
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    refine (pair_ok xorOld t n hn' read write old).mono ?_
    rintro u ⟨mem, gpr', rd', wr', mx'⟩
    have v (k : Nat) (hk : k < 128) (hk' : 2 * n ≤ k) :
        value xorOld t.mem (t.gpr .x1) (t.gpr .x0) k =
          (result xorOld s.mem (s.gpr .x1) (s.gpr .x0))[(⟨k, hk⟩ : Fin 128)] := by
      rw [result_get, src, dest]
      unfold value
      rw [source_read frame (by omega) hd ⟨k, hk⟩]
      cases xorOld
      · rfl
      · rw [old_read frame hk' hk]
    refine ⟨?_, ?_, gpr'.trans gpr, rd'.trans rd, wr'.trans wr, mx'.trans mx⟩
    · rw [mem, v (2 * n) (by omega) (by omega), v (2 * n + 1) (by omega) (by omega), dest,
        show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
      exact written_step (by omega) (written_step (by omega) written)
    · rw [mem, dest]
      exact ((frame_extend frame (by omega : 2 * n ≤ 2 * (n + 1))).writeW
        (r := ⟨s.gpr .x0, 8 * (2 * (n + 1))⟩) (by simp) _
        (Offset.contains_base _ (by omega) (by omega))).writeW
        (r := ⟨s.gpr .x0, 8 * (2 * (n + 1))⟩) (by simp) _
        (Offset.contains_base _ (by omega) (by omega))


