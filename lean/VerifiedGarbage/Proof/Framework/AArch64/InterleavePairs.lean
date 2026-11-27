module

-- separate module: for any code with pairs, and `Interleave` is what many proofs import.

public import VerifiedGarbage.Proof.Framework.AArch64.Interleave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Reduce

/-!
# AArch64: interleaving code with loads and stores of pairs

Untrusted: everything here is checked by Lean. `ldp` and `stp` are two loads
and two stores (`exec_expand`), so code with them, woven with other code,
runs as the one and then the other if it does so with them split
(`WP.weavePairs`).
-/

@[expose] public section

namespace VG.AArch64.Interleave

open VG

/-- `ldp` and `stp` as two loads and two stores. -/
def expand : Instr → List Instr
  | .ldp a b n o => if a ≠ b ∧ a ≠ n ∧ o % 8 = 0 ∧ o ≤ 504 then [.ldr .x a n o, .ldr .x b n (o + 8)] else [.ldp a b n o]
  | .stp a b n o => if o % 8 = 0 ∧ o ≤ 504 then [.str .x a n o, .str .x b n (o + 8)] else [.stp a b n o]
  | i => [i]

theorem exec_ldp_two {a b n : Reg} {o : Nat} (h : a ≠ b ∧ a ≠ n ∧ o % 8 = 0 ∧ o ≤ 504) (s : State) :
    (exec (.ldr .x a n o) s).bind (exec (.ldr .x b n (o + 8))) = exec (.ldp a b n o) s := by
  obtain ⟨hab, han, h8, hb⟩ := h
  have e : s.gpr n + BitVec.ofNat 64 o + 8 = s.gpr n + BitVec.ofNat 64 (o + 8) := Offset.add_add ..
  have l1 : o < 4096 * 8 := by omega_using [hb]
  have l2 : (o + 8) % 8 = 0 := by omega_using [h8]
  have l3 : o + 8 < 4096 * 8 := by omega_using [hb]
  simp only [reduceExec, addr, Size.bytes, h8, l1, hab, hb, ne_eq, not_false_eq_true, and_self, ite_true, Option.bind_some, e]
  cases h1 : s.load (s.gpr n + BitVec.ofNat 64 o) 8 with
  | none => rfl
  | some v =>
    simp only [Option.map_some, Option.bind_some, reduceExec, addr, Size.bytes, l2, l3, and_self, ite_true,
      RegUpd.gpr_write_of_ne s .x _ (Ne.symm han), State.load, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write]
    rfl

theorem exec_stp_two {a b n : Reg} {o : Nat} (h : o % 8 = 0 ∧ o ≤ 504) (s : State) :
    (exec (.str .x a n o) s).bind (exec (.str .x b n (o + 8))) = exec (.stp a b n o) s := by
  obtain ⟨h8, hb⟩ := h
  have e : s.gpr n + BitVec.ofNat 64 o + 8 = s.gpr n + BitVec.ofNat 64 (o + 8) := Offset.add_add ..
  have l1 : o < 4096 * 8 := by omega_using [hb]
  have l2 : (o + 8) % 8 = 0 := by omega_using [h8]
  have l3 : o + 8 < 4096 * 8 := by omega_using [hb]
  simp only [reduceExec, addr, Size.bytes, h8, l1, hb, and_self, ite_true, Option.bind_some, e]
  cases h1 : s.store (s.gpr n + BitVec.ofNat 64 o) 8 (BitVec.setWidth (8 * 8) (s.read .x a)) with
  | none => rfl
  | some t =>
    have g : t.gpr = s.gpr := by
      simp only [State.store] at h1
      split at h1
      · cases h1; rfl
      · cases h1
    simp only [Option.bind_some, reduceExec, addr, Size.bytes, l2, l3, and_self, ite_true, g, State.read]

theorem exec_expand (i : Instr) (s : State) : runBlock isa (expand i) s = exec i s := by
  have one : ∀ j, runBlock isa [j] s = exec j s := fun j => by
    show (exec j s).bind some = _
    exact Option.bind_fun_some _
  have two : ∀ j k, runBlock isa [j, k] s = (exec j s).bind (exec k) := fun j k => by
    show (exec j s).bind (fun u => (exec k u).bind some) = _
    refine congrArg _ (funext fun u => Option.bind_fun_some _)
  cases i
  case ldp a b n o =>
    simp only [expand]
    split
    · rw [two]; exact exec_ldp_two ‹_› s
    · exact one _
  case stp a b n o =>
    simp only [expand]
    split
    · rw [two]; exact exec_stp_two ‹_› s
    · exact one _
  all_goals exact one _

theorem runBlock_expand : ∀ (is : List Instr) (s : State), runBlock isa (is.flatMap expand) s = runBlock isa is s
  | [], _ => rfl
  | i :: is, s => by
    rw [List.flatMap_cons, runBlock_append, exec_expand]
    show (exec i s).bind _ = (exec i s).bind _
    exact congrArg _ (funext fun u => runBlock_expand is u)

theorem Merge.append_left {c a b : List Instr} (l : List Instr) (h : Merge c a b) : Merge (l ++ c) (l ++ a) b := by
  induction l with
  | nil => exact h
  | cons x l ih => exact .left ih

theorem Merge.append_right {c a b : List Instr} (l : List Instr) (h : Merge c a b) : Merge (l ++ c) a (l ++ b) := by
  induction l with
  | nil => exact h
  | cons x l ih => exact .right ih

theorem Merge.expand {c a b : List Instr} (h : Merge c a b) :
    Merge (c.flatMap expand) (a.flatMap expand) (b.flatMap expand) := by
  induction h with
  | nil => exact .nil
  | left _ ih => simp only [List.flatMap_cons]; exact ih.append_left _
  | right _ ih => simp only [List.flatMap_cons]; exact ih.append_right _

/-- Blocks that are independent when their `ldp` and `stp` are split, interleaved, run as the first and then the second. -/
theorem WP.weavePairs {xb : Reg} {a b : List Instr} (hind : Indeps xb (a.flatMap expand) (b.flatMap expand)) {s : State}
    {Q : State → Prop} (h : WP isa (.block a) s fun t => WP isa (.block b) t Q) :
    WP isa (.block (VG.Impl.AArch64Weave.weave a b)) s Q := by
  obtain ⟨s', h', hq⟩ := runBlock_of_WP (WP.block_append_iff.mpr h)
  refine WP.of_runBlock ⟨s', ?_, hq⟩
  rw [← runBlock_expand, run_merge (weave_merge a b).expand hind, ← List.flatMap_append, runBlock_expand]
  exact h'

end VG.AArch64.Interleave
