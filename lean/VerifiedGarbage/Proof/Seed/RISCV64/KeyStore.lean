module
public import VerifiedGarbage.Impl.Seed.RISCV64.ExpandKey
public import VerifiedGarbage.Proof.Seed.RISCV64.Lanes

import VerifiedGarbage.Proof.Seed.RISCV64.Round
import VerifiedGarbage.Proof.Seed.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Copying `G`'s outputs on RISC-V

As on PPC64LE (`Proof/Seed/PPC64LE/KeyStore.lean`): `keyStore_ok`:
`keyStore k` copies the sixteen lanes of `G`'s words to the schedule's words
from `k`, a byte at a time (`storeLE32`); `keyMove_ok`: `keyMove` copies the
second sixteen inputs of `G` to its words.
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Seed.RISCV64 VG.Proof.Seed
open VG.Impl.Aes.RISCV64 (sb)

/-- The schedule's words from `k`. -/
def outR (s : State) (k : Nat) : Region := ⟨s.gpr .a1 + BitVec.ofNat 64 (4 * k), 64⟩

theorem keyStore_ok (k : Nat) (hk : k ≤ 16) {s : State} (h : Room s)
    (hw : ∀ w < 16, InRegions s.wr (s.gpr .a1 + BitVec.ofNat 64 (4 * (k + w))) 4)
    (hsep : (outR s k).Disjoint (scratchR s)) :
    ∀ n ≤ 16, ∃ t, runBlock isa ((List.range n).flatMap fun w =>
        ldW .t0 (tSlot 0) w :: Impl.Words.RISCV64.storeLE32 .t0 .t1 .a1 (4 * (k + w))) s = some t ∧
      (∀ w < n, t.mem.readW (s.gpr .a1 + BitVec.ofNat 64 (4 * (k + w))) 32 = lv s (tSlot 0) w) ∧
      (∀ r, r ≠ .t0 → r ≠ .t1 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Frame [outR s k] s.mem t.mem
  | 0, _ => ⟨s, runBlock_nil, fun w hw => by omega, fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | n + 1, hn => by
    obtain ⟨t, ht, hv, hg, hrd, hwr, hsp, hf⟩ := keyStore_ok k hk h hw hsep n (by omega)
    have sbt : t.gpr sb = s.gpr sb := hg _ (by decide) (by decide)
    have a1t : t.gpr .a1 = s.gpr .a1 := hg _ (by decide) (by decide)
    have room : Room t := room_congr h sbt hwr
    have hlane : lv t (tSlot 0) n = lv s (tSlot 0) n := by
      simp only [lv, laneA, sbt]
      refine hf.readW (r := ⟨s.gpr sb + BitVec.ofNat 64 (8 * tSlot 0 + 4 * n), 4⟩) (Region.contains_self _ _) ?_
        (by decide)
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      refine (hsep.sub_right ?_).symm
      show Region.Sub ⟨s.gpr sb + BitVec.ofNat 64 (8 * tSlot 0 + 4 * n), 4⟩ ⟨s.gpr sb, 8 * scratchSlots⟩
      exact Offset.sub_base _ (by unfold scratchSlots tSlot; omega)
    let t1 := t.write .t0 ((lv t (tSlot 0) n).setWidth 64)
    have e1 : exec (ldW .t0 (tSlot 0) n) t = some t1 := exec_ldW_lane room mem_tA (by omega) .t0
    have hw1 : InRegions t1.wr (t1.gpr .a1 + BitVec.ofNat 64 (4 * (k + n))) 4 := by
      simp only [t1, wr_write, gpr_write_of_ne _ _ (show ¬ Reg.a1 = .t0 by decide), hwr, a1t]
      exact hw n (by omega)
    obtain ⟨t2, e2, h2⟩ := run_of_wp (ByteLoad.storeLE32_ok (s := t1) (v := .t0) (tmp := .t1) (n := .a1)
      (off := 4 * (k + n)) (by decide) (by decide) (by omega) hw1)
    have m2 : t2.mem = t.mem.writeW (s.gpr .a1 + BitVec.ofNat 64 (4 * (k + n))) (lv s (tSlot 0) n) := by
      rw [h2, mem_write]
      show t1.mem.writeW _ _ = _
      simp only [t1, gpr_write_self, gpr_write_of_ne _ _ (show ¬ Reg.a1 = .t0 by decide), a1t,
        mem_write, lo32_ext, hlane]
    refine ⟨t2, ?_, fun w hw' => ?_, fun r h1 h2' => ?_, by rw [h2]; exact hrd, by rw [h2]; exact hwr,
      by rw [h2]; exact hsp, ?_⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact runBlock_trans ht (by rw [runBlock_cons, e1, runStep_some]; exact e2)
    · rw [m2]
      by_cases hwn : w = n
      · subst hwn; rw [Mem.readW_writeW_self32]
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
        exact hv w (by omega)
    · rw [h2, gpr_write_of_ne _ _ h2']
      show t1.gpr r = s.gpr r
      simp only [t1, gpr_write_of_ne _ _ h1]; exact hg r h1 h2'
    · rw [m2]
      exact hf.writeW List.mem_cons_self _ (Offset.contains _ (by omega) (by omega) (by omega))

/-- Moving lane `b` of `uSlot` to `G`'s words. -/
def spMove : LaneSpec := [(tSlot 0, fun x => x uSlot)]

theorem keyMove_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa keyMove s = some s' ∧ Room s' ∧
      (∀ k ∈ arrays, ∀ b < 16, lv s' k b = newVal spMove k (fun k' => lv s k' b)) ∧
      Frame [arraysR s] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ (∀ r, r ≠ .t0 → r ≠ .t1 → s'.gpr r = s.gpr r) := by
  refine lanes16_room (f := fun w => [ldW .t0 uSlot w, stW (tSlot 0) w .t0])
    (by decide) ?_ (fun b hb s h => ?_) h
  · intro kv hkv x y hxy
    simp only [spMove, List.mem_singleton] at hkv; subst hkv
    exact hxy uSlot (by decide)
  · rw [runBlock_cons, exec_ldW_lane h (by decide) hb, runStep_some, runBlock_cons,
      exec_stW_lane ?h1 (by decide) hb, runStep_some, runBlock_nil]
    case h1 => exact room_congr h rfl rfl
    refine ⟨_, rfl, ?_, rfl, rfl, rfl, fun r h1 h2 => ?_⟩
    · simp only [laneWrites, spMove, List.foldl_cons, List.foldl_nil, gpr_write_self,
        setWidth_setWidth_32, mem_setMem, mem_write,
        laneA_write _ _ (show ¬ sb = .t0 by decide)]
    · simp only [gpr_write_of_ne _ _ h1, gpr_setMem]

end VG.Proof.Seed.RISCV64
