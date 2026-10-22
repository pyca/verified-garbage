module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Save
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Impl.AesGcm.AArch64
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Mem

/-!
# SM4-GCM on AArch64: saving and restoring our caller's registers

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/AArch64/Save.lean`, whose definitions and lemmas on the slots
this uses), for SM4-GCM's 768-byte working space.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.Proof.AesGcm.AArch64

theorem save_ok (s : State) (b : Reg) {W : Addr} (hb : s.gpr b = W) (hw : Covers [⟨W, 768⟩] s.wr) :
    ∃ s', runBlock isa (save b) s = some s' ∧ s'.gpr = s.gpr ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = savedMem s.mem W s.gpr := by
  have w (d : Nat) (h : d + 8 ≤ 768) : InRegions s.wr (W + BitVec.ofNat 64 d) 8 := in_off hw h (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, ↓reduceDIte, Nat.reduceLT, Nat.reduceGT, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reducePow, BitVec.reduceEq, not_false_eq_true, not_true_eq_false, Bool.not_true, Bool.not_false, and_self, false_implies, implies_true, Nat.reduceBEq, Nat.reduceBNe, decide_true, decide_false, BitVec.reduceSignExtend, save, saved, List.map, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, Size.bytes,
      Size.bits, State.read, gpr_write, ite_true, ite_false, Option.bind_some, hb,
      w 128 (by decide), w 136 (by decide), w 144 (by decide), w 152 (by decide), w 160 (by decide),
      w 168 (by decide), w 176 (by decide), w 184 (by decide), w 192 (by decide), w 200 (by decide),
      w 208 (by decide)]
    rfl, ?_⟩
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  simp only [savedMem, saved, List.foldl, Mem.writeW, BitVec.setWidth_eq]

theorem restore_ok (s : State) {W : Addr} (h19 : s.gpr .x19 = W) (hr : Covers [⟨W, 768⟩] (s.rd ++ s.wr)) :
    ∃ s', runBlock isa restore s = some s' ∧
      (∀ p ∈ saved, s'.gpr p.1 = s.mem.readW (W + BitVec.ofNat 64 p.2) 64) ∧
      (∀ r, r ∉ saved.map (·.1) → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have r (d : Nat) (h : d + 8 ≤ 768) : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) 8 := in_off hr h (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, ↓reduceDIte, Nat.reduceLT, Nat.reduceGT, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reducePow, BitVec.reduceEq, not_false_eq_true, not_true_eq_false, Bool.not_true, Bool.not_false, and_self, false_implies, implies_true, Nat.reduceBEq, Nat.reduceBNe, decide_true, decide_false, BitVec.reduceSignExtend, restore, saved, List.map, runBlock_cons, runStep_some,
      runBlock_nil, exec, addr, State.load, Size.bytes, Size.bits, gpr_write, mem_write, rd_write,
      wr_write, ite_true, ite_false, Option.bind_some, Option.map_some, h19,
      r 128 (by decide), r 136 (by decide), r 144 (by decide), r 152 (by decide), r 160 (by decide),
      r 168 (by decide), r 176 (by decide), r 184 (by decide), r 192 (by decide), r 200 (by decide),
      r 208 (by decide)]
    rfl, ?_⟩
  refine ⟨fun p h => ?_, fun r h => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [gpr_write, Mem.readW]
  · simp only [saved, List.map, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    simp [gpr_write, h]

/-- The end of every function: our caller's registers restored. -/
theorem exit_ok {s s₀ : State} {W : Addr} (h19 : s.gpr .x19 = W) (hsp : s.sp = s₀.sp)
    (hr : Covers [⟨W, 768⟩] (s.rd ++ s.wr)) (hs : SavedAt s.mem W s₀) :
    WP isa (.block restore) s fun s' => GprAbi s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .x0 = s.gpr .x0 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', run, hsv, hother, sp', hm, rd', wr'⟩ := restore_ok s h19 hr
  refine WP.of_runBlock ⟨s', run, ⟨fun r hr' => ?_, by rw [sp', hsp]⟩, hm, hother .x0 (by decide), rd', wr'⟩
  have hin : r ∈ saved.map (·.1) := (by decide : ∀ r ∈ preserved, r ∈ saved.map (·.1)) r hr'
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hin
  rw [hsv p hp, hs p hp]

end VG.Proof.Sm4Gcm.AArch64
