module

import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.Sm3.AArch64.Sm4.Spec
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Sm3.AArch64.Compress
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm3.AArch64.Sm4.Lit
public import VerifiedGarbage.Impl.Sm3.AArch64.Sm4
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Sm3.AArch64.Sm4.Spec
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Sm3.AArch64.Compress
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Reduce
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Sm3.AArch64.Sm4.Lit
meta import VerifiedGarbage.Impl.Sm3.AArch64.Sm4
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# SM3 compression with the AArch64 SM3 instructions: correctness

`compress_verified`: `Impl.Sm3.AArch64.Sm4.compress` (`vg_sm3_compress_sm4`)
meets the contract of the compression function
(`Proof.Sm3.compressAArch64`), so the streaming proofs apply to it as to
`vg_sm3_compress`.
-/

@[expose] public section

namespace VG.Proof.Sm3.AArch64.Sm4

open VG VG.AArch64 VG.Impl.Sm3.AArch64.Sm4
open VG.Spec.Sm3 (HashValue Word Block W stateAt blockAt compressBlocks)

/-! ## The instructions -/

theorem exec_vop (s : State) (op : VOp) :
    exec (.vop op) s = (VOp.eval s op).map (fun p => s.setV p.1 p.2) := rfl

theorem eval_ss1 (s : State) (d n m a : VReg) :
    VOp.eval s (.sm3ss1 d n m a) = some (d, sm3Ss1 (s.v n) (s.v m) (s.v a)) := rfl

theorem eval_shl (s : State) (d n : VReg) :
    VOp.eval s (.shift .shl .s4 d n 1) =
      some (d, VArr.s4.map2 (fun w x y => VShiftOp.shl.eval 1 w x y) (s.v d) (s.v n)) := rfl

theorem eval_sri (s : State) (d n : VReg) :
    VOp.eval s (.shift .sri .s4 d n 31) =
      some (d, VArr.s4.map2 (fun w x y => VShiftOp.sri.eval 31 w x y) (s.v d) (s.v n)) := rfl

theorem eval_tt1 (s : State) (b : Bool) (d n m : VReg) {i : Nat} (hi : i < 4) :
    VOp.eval s (.sm3tt (tt1 b) d n m i) = some (d, sm3Tt1 b (s.v d) (s.v n) (vword (s.v m) i)) := by
  cases b <;> simp only [tt1, VOp.eval, hi, ite_true, Bool.false_eq_true, ite_false]

theorem eval_tt2 (s : State) (b : Bool) (d n m : VReg) {i : Nat} (hi : i < 4) :
    VOp.eval s (.sm3tt (tt2 b) d n m i) = some (d, sm3Tt2 b (s.v d) (s.v n) (vword (s.v m) i)) := by
  cases b <;> simp only [tt2, VOp.eval, hi, ite_true, Bool.false_eq_true, ite_false]

theorem eval_ext3 (s : State) (d n m : VReg) :
    VOp.eval s (.ext d n m 12) = some (d, extW 3 (s.v n) (s.v m)) := rfl

theorem eval_ext2 (s : State) (d n m : VReg) :
    VOp.eval s (.ext d n m 8) = some (d, extW 2 (s.v n) (s.v m)) := rfl

theorem eval_partw1 (s : State) (d n m : VReg) :
    VOp.eval s (.sm3partw1 d n m) = some (d, sm3PartW1 (s.v d) (s.v n) (s.v m)) := rfl

theorem eval_partw2 (s : State) (d n m : VReg) :
    VOp.eval s (.sm3partw2 d n m) = some (d, sm3PartW2 (s.v d) (s.v n) (s.v m)) := rfl

theorem eval_eor (s : State) (d n m : VReg) :
    VOp.eval s (.logic .eor d n m) = some (d, s.v n ^^^ s.v m) := rfl

theorem eval_rev (s : State) (op : VRevOp) (d n : VReg) :
    VOp.eval s (.rev op d n) = some (d, op.eval (s.v n)) := rfl

theorem eval_mov (s : State) (d n : VReg) : VOp.eval s (.mov d n) = some (d, s.v n) := rfl

theorem eval_dup (s : State) (d : VReg) (n : Reg) :
    VOp.eval s (.dup .s4 d n) = some (d, ofVWords ((s.gpr n).setWidth 32) ((s.gpr n).setWidth 32)
      ((s.gpr n).setWidth 32) ((s.gpr n).setWidth 32)) := rfl

theorem extW_self (x : BitVec 128) : extW 2 x x = swap8 x := rfl

/-! ## The registers -/

theorem treg_cases (j : Nat) :
    (treg j = .v17 ∧ treg (j + 1) = .v18) ∨ (treg j = .v18 ∧ treg (j + 1) = .v17) := by
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · exact .inl ⟨by simp only [treg, h, ite_true], by
      simp only [treg, show (j + 1) % 2 = 1 by omega_using [h], Nat.one_ne_zero, ite_false]⟩
  · exact .inr ⟨by simp only [treg, h, Nat.one_ne_zero, ite_false], by
      simp only [treg, show (j + 1) % 2 = 0 by omega_using [h], ite_true]⟩

/-- The registers of five consecutive groups' message words, and those with a fixed use. -/
theorem msg_nodup (n : Nat) :
    [msg n, msg (n + 1), msg (n + 2), msg (n + 3), msg (n + 4), .v5, .v6, .v7, .v16, .v17, .v18, .v19,
      .v20, .v21, .v22].Nodup := by
  have key : ∀ c < 5, [msg c, msg (c + 1), msg (c + 2), msg (c + 3), msg (c + 4), .v5, .v6, .v7, .v16,
      .v17, .v18, .v19, .v20, .v21, .v22].Nodup := by decide
  have e : ∀ k, msg (n + k) = msg (n % 5 + k) := fun k => by
    simp only [msg]; rw [show (n % 5 + k) % 5 = (n + k) % 5 by omega_arith]
  rw [show msg n = msg (n % 5) by simp only [msg, Nat.mod_mod], e 1, e 2, e 3, e 4]
  exact key _ (Nat.mod_lt _ (by decide))

/-- A message register is none of those with a fixed use. -/
theorem msg_other (n : Nat) : ∀ r ∈ [VReg.v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22], msg n ≠ r := by
  have key : ∀ c < 5, ∀ r ∈ [VReg.v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22], msg c ≠ r := by
    decide
  rw [show msg n = msg (n % 5) by simp only [msg, Nat.mod_mod]]
  exact key _ (Nat.mod_lt _ (by decide))

/-! ## An iteration -/

theorem round_ok (j : Nat) (s : State) (v : HashValue) (w w₄ : Word)
    (h5 : s.v .v5 = abcd v) (h6 : s.v .v6 = efgh v) (ht : vword (s.v (treg j)) 3 = tRot j)
    (hw : vword (s.v (msg (j / 4))) (j % 4) = w) (hw' : vword (s.v .v16) (j % 4) = w ^^^ w₄) :
    WP isa (.block (round j)) s fun s' =>
      s'.v .v5 = abcd (roundW v j w w₄) ∧ s'.v .v6 = efgh (roundW v j w w₄) ∧
      vword (s'.v (treg (j + 1))) 3 = rot1 (tRot j) ∧
      (∀ r, r ≠ .v5 → r ≠ .v6 → r ≠ .v7 → r ≠ .v17 → r ≠ .v18 → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hx := msg_other (j / 4)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
  obtain ⟨x5, -, x7, -, x17, x18, -⟩ := hx
  have hi : j % 4 < 4 := Nat.mod_lt j (by decide)
  have hc := treg_cases j
  apply WP.of_runBlock
  simp only [round]
  generalize msg (j / 4) = x at *
  generalize treg j = t at *
  generalize treg (j + 1) = u at *
  have e1 := round_abcd v j w w₄ (s.v t) ht
  have e2 := round_efgh v j w w₄ (s.v t) ht
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · simp only [reduceCtorEq, ↓reduceIte, and_self, runBlock_cons, runStep_some, runBlock_nil,
      exec_vop, eval_ss1, eval_shl, eval_sri, eval_tt1 _ _ _ _ _ hi, eval_tt2 _ _ _ _ _ hi, isa,
      RegUpd.v_setV, RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV, Option.map_some,
      x5, x7, x17, x18, h5, h6, hw, hw', e1, e2, Option.some.injEq, exists_eq_left',
      vword_map2 _ _ _ (show 3 < 4 by decide)]
    refine ⟨trivial, trivial, ?_, fun r r5 r6 r7 r17 r18 => ?_, trivial⟩
    · rw [ht]; rfl
    · simp only [r5, r6, r7, r17, r18, ite_false]

theorem round_four {n i : Nat} (hi : i < 4) : (4 * n + i) / 4 = n ∧ (4 * n + i) % 4 = i := by
  omega_using [hi]

/-- Iteration `4 n + i`, of group `n`. -/
theorem round_ok' (H : HashValue) (M : Block) (n i : Nat) (hi : i < 4) (s : State)
    (h5 : s.v .v5 = abcd (Spec.Sm3.rounds H M (4 * n + i)))
    (h6 : s.v .v6 = efgh (Spec.Sm3.rounds H M (4 * n + i)))
    (ht : vword (s.v (treg (4 * n + i))) 3 = tRot (4 * n + i))
    (hq : s.v (msg n) = quad M n) (hq' : s.v .v16 = quad M n ^^^ quad M (n + 1)) :
    WP isa (.block (round (4 * n + i))) s fun s' =>
      s'.v .v5 = abcd (Spec.Sm3.rounds H M (4 * n + i + 1)) ∧
      s'.v .v6 = efgh (Spec.Sm3.rounds H M (4 * n + i + 1)) ∧
      vword (s'.v (treg (4 * n + i + 1))) 3 = rot1 (tRot (4 * n + i)) ∧
      (∀ r, r ≠ .v5 → r ≠ .v6 → r ≠ .v7 → r ≠ .v17 → r ≠ .v18 → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := round_four (n := n) hi
  have h := round_ok (4 * n + i) s _ (W M (4 * n + i)) (W M (4 * n + i + 4)) h5 h6 ht
    (by rw [e.1, e.2, hq, vword_quad M n hi])
    (by rw [e.2, hq', vword_xor, vword_quad M n hi, vword_quad M (n + 1) hi]
        exact congrArg (fun k => W M (4 * n + i) ^^^ W M k) (by omega_arith))
  rw [rounds_succ, round_eq]
  exact h

theorem treg_even (n : Nat) : treg (4 * n) = .v17 := by
  simp only [treg, show 4 * n % 2 = 0 by omega_arith, ite_true]

/-! ## A group of four iterations -/

theorem msg_ne (n k : Nat) (h₁ : n ≤ k) (h₂ : k < n + 4) : msg k ≠ msg (n + 4) := by
  have hd := msg_nodup n
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  rcases (by omega_arith : k = n ∨ k = n + 1 ∨ k = n + 2 ∨ k = n + 3) with rfl | rfl | rfl | rfl
  · exact hd.1.2.2.2.1
  · exact hd.2.1.2.2.1
  · exact hd.2.2.1.2.1
  · exact hd.2.2.2.1.1

/-- A register with a fixed use is no message register. -/
theorem fixed_ne {r : VReg} (hr : r ∈ [VReg.v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22]) (k : Nat) :
    r ≠ msg k := Ne.symm (msg_other k r hr)

theorem tset_ok (c : Word) (s : State) :
    WP isa (.block (tset c)) s fun s' =>
      vword (s'.v .v17) 3 = c ∧ (∀ r, r ≠ .v17 → s'.v r = s.v r) ∧
      (∀ r, r ≠ .x4 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e : ∀ x : BitVec 32, BitVec.setWidth 32 (BitVec.setWidth 64 x) = x := fun x => by
    rw [BitVec.setWidth_setWidth_of_le x (by decide), BitVec.setWidth_eq]
  apply WP.of_runBlock
  simp only [tset, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec_movz_w, exec_movk_w, exec_vop,
    eval_dup, isa, Option.map_some, RegUpd.gpr_write_self, RegUpd.v_setV, RegUpd.gpr_setV, RegUpd.mem_setV,
    RegUpd.rd_setV, RegUpd.wr_setV, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.v_write,
    Option.some.injEq, exists_eq_left', vword_ofVWords_3, e, movzk]
  exact ⟨trivial, fun r hr => by simp only [hr, ite_false],
    fun r hr => by simp only [RegUpd.gpr_write_of_ne, hr, not_false_eq_true], trivial, trivial, trivial⟩

theorem tinit_ok (n : Nat) (s : State) (ht : n ≠ 0 → n ≠ 4 → vword (s.v .v17) 3 = tRot (4 * n)) :
    WP isa (.block (tinit n)) s fun s' =>
      vword (s'.v .v17) 3 = tRot (4 * n) ∧ (∀ r, r ≠ .v17 → s'.v r = s.v r) ∧
      (∀ r, r ≠ .x4 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  by_cases h : n = 0 ∨ n = 4
  · simp only [tinit, h, ite_true]
    exact tset_ok _ s
  · simp only [tinit, h, ite_false]
    exact WP.block_nil (M := isa) ⟨ht (fun e => h (.inl e)) (fun e => h (.inr e)), fun _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, rfl⟩

theorem expand_run (n : Nat) (hn : n ≤ 12) (s : State) (a b c d : BitVec 128)
    (ha : s.v (msg n) = a) (hb : s.v (msg (n + 1)) = b) (hc : s.v (msg (n + 2)) = c)
    (hd' : s.v (msg (n + 3)) = d) :
    WP isa (.block (expand n)) s fun s' =>
      s'.v (msg (n + 4)) = sm3PartW2 (sm3PartW1 (extW 3 b c) a d) (extW 2 c d) (extW 3 a b) ∧
      (∀ r, r ≠ msg (n + 4) → r ≠ .v19 → r ≠ .v20 → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hd := msg_nodup n
  have hd'' := VG.nodup_reverse hd
  apply WP.of_runBlock
  simp only [expand, hn, ite_true]
  generalize msg n = x₀ at *
  generalize msg (n + 1) = x₁ at *
  generalize msg (n + 2) = x₂ at *
  generalize msg (n + 3) = x₃ at *
  generalize msg (n + 4) = x₄ at *
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hd hd''
  simp only [↓reduceIte, and_self, runBlock_cons, runStep_some, runBlock_nil, exec_vop, eval_ext3, eval_ext2,
    eval_partw1, eval_partw2, isa, RegUpd.v_setV, RegUpd.gpr_setV, RegUpd.mem_setV,
    RegUpd.rd_setV, RegUpd.wr_setV, hd, hd'', ha, hb, hc, hd',
    Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr h19 h20 => by simp only [hr, h19, h20, ite_false], trivial⟩

/-- The message words of group `n + 4`, where a group reads them. -/
theorem expand_ok (M : Block) (n : Nat) (s : State)
    (hm : ∀ k, n ≤ k → k < n + 4 → k ≤ 16 → s.v (msg k) = quad M k) (hn : n < 16) :
    WP isa (.block (expand n)) s fun s' =>
      (∀ k, n ≤ k → k < n + 5 → k ≤ 16 → s'.v (msg k) = quad M k) ∧
      (∀ r, (∀ k, r ≠ msg k) → r ≠ .v19 → r ≠ .v20 → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  by_cases h : n ≤ 12
  · refine WP.mono (expand_run n h s _ _ _ _ (hm n (by omega_arith) (by omega_arith) (by omega_arith))
      (hm (n + 1) (by omega_arith) (by omega_arith) (by omega_arith))
      (hm (n + 2) (by omega_arith) (by omega_arith) (by omega_arith))
      (hm (n + 3) (by omega_arith) (by omega_arith) (by omega_arith)))
      fun s' ⟨e, hv, hg, hmm, hrd, hwr⟩ => ⟨fun k h₁ h₂ h₃ => ?_, fun r hr => hv r (hr _), hg, hmm, hrd, hwr⟩
    by_cases hk : k = n + 4
    · rw [hk, e, expand_eq]
    · have o := msg_other k
      rw [hv _ (msg_ne n k h₁ (by omega_arith)) (o _ (by decide)) (o _ (by decide))]
      exact hm k h₁ (by omega_arith) h₃
  · simp only [expand, h, ite_false]
    exact WP.block_nil (M := isa) ⟨fun k h₁ h₂ h₃ => hm k h₁ (by omega_arith) h₃, fun _ _ _ _ => rfl,
      rfl, rfl, rfl, rfl⟩

theorem wprime_ok (n : Nat) (s : State) (a b : BitVec 128) (ha : s.v (msg n) = a) (hb : s.v (msg (n + 1)) = b) :
    WP isa (.block (wprime n)) s fun s' =>
      s'.v .v16 = a ^^^ b ∧ (∀ r, r ≠ .v16 → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [wprime, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec_vop, eval_eor, isa,
    RegUpd.v_setV, RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV, ha, hb,
    Option.map_some, Option.some.injEq, exists_eq_left', and_self]
  exact ⟨trivial, fun r hr => by simp only [hr, ite_false], trivial⟩

/-- What holds after `n` groups of a block, from the state `sB`. -/
structure RInv (H : HashValue) (M : Block) (sB : State) (n : Nat) (s : State) : Prop where
  v5 : s.v .v5 = abcd (Spec.Sm3.rounds H M (4 * n))
  v6 : s.v .v6 = efgh (Spec.Sm3.rounds H M (4 * n))
  msgs : ∀ k, n ≤ k → k < n + 4 → k ≤ 16 → s.v (msg k) = quad M k
  t : n ≠ 0 → n ≠ 4 → vword (s.v .v17) 3 = tRot (4 * n)
  save : ∀ r, (r = .v21 ∨ r = .v22) → s.v r = sB.v r
  gpr : ∀ r, r ≠ .x4 → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

/-- The four iterations of group `n`. -/
theorem rounds4_ok (H : HashValue) (M : Block) (n : Nat) (hn : n < 16) (s : State)
    (h5 : s.v .v5 = abcd (Spec.Sm3.rounds H M (4 * n)))
    (h6 : s.v .v6 = efgh (Spec.Sm3.rounds H M (4 * n)))
    (ht : vword (s.v .v17) 3 = tRot (4 * n))
    (hq : s.v (msg n) = quad M n) (hq' : s.v .v16 = quad M n ^^^ quad M (n + 1)) :
    WP isa (.block (round (4 * n) ++ (round (4 * n + 1) ++ (round (4 * n + 2) ++ round (4 * n + 3))))) s
      fun s' =>
        s'.v .v5 = abcd (Spec.Sm3.rounds H M (4 * (n + 1))) ∧
        s'.v .v6 = efgh (Spec.Sm3.rounds H M (4 * (n + 1))) ∧
        (n ≠ 3 → vword (s'.v .v17) 3 = tRot (4 * (n + 1))) ∧
        (∀ r, r ≠ .v5 → r ≠ .v6 → r ≠ .v7 → r ≠ .v17 → r ≠ .v18 → s'.v r = s.v r) ∧
        s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o := msg_other n
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at o
  obtain ⟨o5, o6, o7, -, o17, o18, -⟩ := o
  have t0 : vword (s.v (treg (4 * n + 0))) 3 = tRot (4 * n + 0) := by
    rw [Nat.add_zero, treg_even]; exact ht
  rw [WP.block_append_iff]
  refine WP.mono (round_ok' H M n 0 (by decide) s h5 h6 t0 hq hq')
    fun s₁ ⟨a5, a6, at₁, av, ag, am, ard, awr⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (round_ok' H M n 1 (by decide) s₁ a5 a6
    (at₁.trans (tnext (4 * n) (by omega_arith) (by omega_arith)))
    (by rw [av _ o5 o6 o7 o17 o18]; exact hq)
    (by rw [av _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hq'))
    fun s₂ ⟨b5, b6, bt, bv, bg, bm, brd, bwr⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (round_ok' H M n 2 (by decide) s₂ b5 b6
    (bt.trans (tnext (4 * n + 1) (by omega_arith) (by omega_arith)))
    (by rw [bv _ o5 o6 o7 o17 o18, av _ o5 o6 o7 o17 o18]; exact hq)
    (by rw [bv _ (by decide) (by decide) (by decide) (by decide) (by decide),
          av _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hq'))
    fun s₃ ⟨c5, c6, ct, cv, cg, cm, crd, cwr⟩ => ?_
  refine WP.mono (round_ok' H M n 3 (by decide) s₃ c5 c6
    (ct.trans (tnext (4 * n + 2) (by omega_arith) (by omega_arith)))
    (by rw [cv _ o5 o6 o7 o17 o18, bv _ o5 o6 o7 o17 o18, av _ o5 o6 o7 o17 o18]; exact hq)
    (by rw [cv _ (by decide) (by decide) (by decide) (by decide) (by decide),
          bv _ (by decide) (by decide) (by decide) (by decide) (by decide),
          av _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hq'))
    fun s₄ ⟨d5, d6, dt, dv, dg, dm, drd, dwr⟩ => ?_
  refine ⟨d5, d6, fun h3 => ?_, fun r r5 r6 r7 r17 r18 => ?_, by rw [dg, cg, bg, ag],
    by rw [dm, cm, bm, am], by rw [drd, crd, brd, ard], by rw [dwr, cwr, bwr, awr]⟩
  · have e := dt.trans (tnext (4 * n + 3) (by omega_arith) (by omega_arith))
    rw [show 4 * n + 3 + 1 = 4 * (n + 1) by omega_arith, treg_even] at e
    exact e
  · rw [dv r r5 r6 r7 r17 r18, cv r r5 r6 r7 r17 r18, bv r r5 r6 r7 r17 r18, av r r5 r6 r7 r17 r18]

theorem group_ok (H : HashValue) (M : Block) (sB : State) (n : Nat) (hn : n < 16) (s : State)
    (hs : RInv H M sB n s) : WP isa (.block (group n)) s (RInv H M sB (n + 1)) := by
  have o := msg_other
  rw [group, WP.block_append_iff]
  refine WP.mono (tinit_ok n s hs.t) fun s₁ ⟨ht₁, hv₁, hg₁, hm₁, hrd₁, hwr₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (expand_ok M n s₁
    (fun k h₁ h₂ h₃ => by rw [hv₁ _ (o k _ (by decide))]; exact hs.msgs k h₁ h₂ h₃) hn)
    fun s₂ ⟨hq₂, hv₂, hg₂, hm₂, hrd₂, hwr₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wprime_ok n s₂ _ _ (hq₂ n (Nat.le_refl _) (by omega_arith) (by omega_arith))
    (hq₂ (n + 1) (by omega_arith) (by omega_arith) (by omega_arith)))
    fun s₃ ⟨h16₃, hv₃, hg₃, hm₃, hrd₃, hwr₃⟩ => ?_
  -- A register with a fixed use, other than `v16`, `v17`, `v19` and `v20`, is as the group found it.
  have keep : ∀ r ∈ [VReg.v5, .v6, .v21, .v22], s₃.v r = s.v r := fun r hr => by
    have h : r ∈ [VReg.v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22] ∧ r ≠ .v16 ∧ r ≠ .v17 ∧
        r ≠ .v19 ∧ r ≠ .v20 := by
      revert r; decide
    rw [hv₃ _ h.2.1, hv₂ _ (fixed_ne h.1) h.2.2.2.1 h.2.2.2.2, hv₁ _ h.2.2.1]
  refine WP.mono (rounds4_ok H M n hn s₃ ((keep _ (by decide)).trans hs.v5) ((keep _ (by decide)).trans hs.v6)
    (by rw [hv₃ _ (by decide), hv₂ _ (fixed_ne (by decide)) (by decide) (by decide)]; exact ht₁)
    (by rw [hv₃ _ (o n _ (by decide))]; exact hq₂ n (Nat.le_refl _) (by omega_arith) (by omega_arith)) h16₃)
    fun s₄ ⟨e5, e6, et, ev, eg, em, erd, ewr⟩ => ?_
  refine ⟨e5, e6, fun k h₁ h₂ h₃ => ?_, fun _ h4 => et (by omega_arith), fun r hr => ?_, fun r h4 => ?_,
    by rw [em, hm₃, hm₂, hm₁, hs.mem], by rw [erd, hrd₃, hrd₂, hrd₁, hs.rd],
    by rw [ewr, hwr₃, hwr₂, hwr₁, hs.wr]⟩
  · rw [ev _ (o k _ (by decide)) (o k _ (by decide)) (o k _ (by decide)) (o k _ (by decide))
      (o k _ (by decide)), hv₃ _ (o k _ (by decide))]
    exact hq₂ k (by omega_arith) h₂ h₃
  · have h : r ∈ [VReg.v5, .v6, .v21, .v22] ∧ r ≠ .v5 ∧ r ≠ .v6 ∧ r ≠ .v7 ∧ r ≠ .v17 ∧ r ≠ .v18 := by
      rcases hr with rfl | rfl <;> decide
    rw [ev _ h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2, keep _ h.1]
    exact hs.save r hr
  · rw [eg, hg₃, hg₂, hg₁ r h4, hs.gpr r h4]

/-- The first `n` groups of a block. -/
theorem rounds_ok (H : HashValue) (M : Block) (sB : State)
    (h5 : sB.v .v5 = abcd H) (h6 : sB.v .v6 = efgh H) (hq : ∀ k < 4, sB.v (msg k) = quad M k) :
    ∀ n ≤ 16, WP isa (rounds n) sB (RInv H M sB n) := by
  intro n hn
  induction n with
  | zero =>
    exact WP.block_nil (M := isa) ⟨h5, h6, fun k _ h _ => hq k h, fun h => absurd rfl h, fun _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    exact WP.seq (WP.mono (ih (by omega_arith)) fun s hs => group_ok H M sB n (by omega_arith) s hs)

/-! ## The hash value and the block in memory -/

theorem load_abcd (m : Mem) (p : Addr) :
    extW 2 (VRevOp.rev64s.eval (m.read (p + BitVec.ofNat 64 0) 16))
      (VRevOp.rev64s.eval (m.read (p + BitVec.ofNat 64 0) 16)) = abcd (stateAt m p) := by
  rw [extW_self, read16, flip_eq]
  simp only [abcd, stateAt_get _ _ (by decide : 0 < 8), stateAt_get _ _ (by decide : 1 < 8),
    stateAt_get _ _ (by decide : 2 < 8), stateAt_get _ _ (by decide : 3 < 8), BitVec.add_zero]

theorem load_efgh (m : Mem) (p : Addr) :
    extW 2 (VRevOp.rev64s.eval (m.read (p + BitVec.ofNat 64 16) 16))
      (VRevOp.rev64s.eval (m.read (p + BitVec.ofNat 64 16) 16)) = efgh (stateAt m p) := by
  rw [extW_self, read16, flip_eq]
  simp only [efgh, stateAt_get _ _ (by decide : 4 < 8), stateAt_get _ _ (by decide : 5 < 8),
    stateAt_get _ _ (by decide : 6 < 8), stateAt_get _ _ (by decide : 7 < 8),
    Offset.add_add, Nat.reduceMul, Nat.reduceAdd]

theorem flip_abcd (v : HashValue) :
    extW 2 (VRevOp.rev64s.eval (abcd v)) (VRevOp.rev64s.eval (abcd v)) = ofVWords v[0] v[1] v[2] v[3] := by
  rw [extW_self, abcd, flip_eq]

theorem flip_efgh (v : HashValue) :
    extW 2 (VRevOp.rev64s.eval (efgh v)) (VRevOp.rev64s.eval (efgh v)) = ofVWords v[4] v[5] v[6] v[7] := by
  rw [extW_self, efgh, flip_eq]

theorem write_pair (m : Mem) (p : Addr) (v : HashValue) :
    (m.write (p + BitVec.ofNat 64 0) 16 (ofVWords v[0] v[1] v[2] v[3])).write (p + BitVec.ofNat 64 16) 16
      (ofVWords v[4] v[5] v[6] v[7]) = writeState m p v := by
  simp only [write16, writeState, Offset.add_add, Nat.reduceMul, Nat.reduceAdd, BitVec.add_zero]

theorem load_quad (M : Block) (m : Mem) (bp : Addr) {n : Nat} (hn : n < 4)
    (hblk : ∀ t : Nat, t < 16 → rev32 (m.readW (bp + BitVec.ofNat 64 (4 * t)) 32) = W M t) :
    VRevOp.rev32b.eval (m.read (bp + BitVec.ofNat 64 (16 * n)) 16) = quad M n := by
  apply vec_ext
  intro j hj
  rw [vword_rev32b _ hj, vword_read16 _ _ hj,
    Offset.add_add_eq _ (show 16 * n + 4 * j = 4 * (4 * n + j) by omega_arith), hblk _ (by omega_arith),
    vword_quad M n hj]

/-! ## The pieces of the function -/

theorem load_ok (s : State)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 0) 16)
    (h16 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 16) 16) :
    WP isa (.block (load ++ wordRev)) s fun s' =>
      s'.v .v5 = abcd (stateAt s.mem (s.gpr .x0)) ∧
      s'.v .v6 = efgh (stateAt s.mem (s.gpr .x0)) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, load, wordRev, List.cons_append,
    List.nil_append, runBlock_cons, runStep_some, runBlock_nil, reduceExec, addr, State.load,
    Option.bind_some, eval_rev, eval_ext2, and_self, isa, Option.map_some,
    RegUpd.gpr_setV, RegUpd.v_setV, RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV,
    h0, h16, load_abcd, load_efgh, Option.some.injEq, exists_eq_left']

theorem fetch_ok (M : Block) (s : State)
    (hin : ∀ n : Nat, n < 4 → InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (16 * n)) 16)
    (hblk : ∀ t : Nat, t < 16 → rev32 (s.mem.readW (s.gpr .x1 + BitVec.ofNat 64 (4 * t)) 32) = W M t) :
    WP isa (.block fetch) s fun s' =>
      (∀ k < 4, s'.v (msg k) = quad M k) ∧ s'.v .v21 = s.v .v5 ∧ s'.v .v22 = s.v .v6 ∧
      s'.v .v5 = s.v .v5 ∧ s'.v .v6 = s.v .v6 ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i0 := hin 0 (by decide); have i1 := hin 1 (by decide)
  have i2 := hin 2 (by decide); have i3 := hin 3 (by decide)
  have q0 := load_quad M s.mem (s.gpr .x1) (show 0 < 4 by decide) hblk
  have q1 := load_quad M s.mem (s.gpr .x1) (show 1 < 4 by decide) hblk
  have q2 := load_quad M s.mem (s.gpr .x1) (show 2 < 4 by decide) hblk
  have q3 := load_quad M s.mem (s.gpr .x1) (show 3 < 4 by decide) hblk
  simp only [Nat.reduceMul] at i0 i1 i2 i3 q0 q1 q2 q3
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, fetch,
    runBlock_cons, runStep_some, runBlock_nil, reduceExec, addr, State.load, Option.bind_some,
    eval_rev, eval_mov, and_self, isa, Option.map_some,
    RegUpd.gpr_setV, RegUpd.v_setV, RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV,
    i0, i1, i2, i3, q0, q1, q2, q3, Option.some.injEq, exists_eq_left']
  refine ⟨fun k hk => ?_, trivial⟩
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_arith) with rfl | rfl | rfl | rfl <;>
    simp only [msg, Nat.reduceMod, List.getD_cons_zero, List.getD_cons_succ, reduceCtorEq, ↓reduceIte]

theorem fold_ok (s : State) (v H : HashValue)
    (h5 : s.v .v5 = abcd v) (h6 : s.v .v6 = efgh v)
    (h21 : s.v .v21 = abcd H) (h22 : s.v .v22 = efgh H) :
    WP isa (.block fold) s fun s' =>
      s'.v .v5 = abcd (Vector.zipWith (· ^^^ ·) v H) ∧ s'.v .v6 = efgh (Vector.zipWith (· ^^^ ·) v H) ∧
      s'.gpr .x1 = s.gpr .x1 + 64 ∧ s'.gpr .x2 = s.gpr .x2 - 1 ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, fold, runBlock_cons, runStep_some, runBlock_nil,
    exec_vop, eval_eor, exec_addImm_x, exec_subImm_x, isa, State.read, Size.bits, Option.map_some,
    RegUpd.gpr_setV, RegUpd.v_setV,
    RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV, RegUpd.gpr_write_self,
    RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.v_write,
    h5, h6, h21, h22, xor_abcd, xor_efgh,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, rfl, rfl,
    fun r h1 h2 => by simp only [RegUpd.gpr_write_of_ne, h1, h2, not_false_eq_true]; rfl,
    trivial, trivial, trivial⟩

theorem store_ok (s : State) (v : HashValue)
    (h5 : s.v .v5 = abcd v) (h6 : s.v .v6 = efgh v)
    (h0 : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 0) 16)
    (h16 : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 16) 16) :
    WP isa (.block (wordRev ++ store)) s fun s' =>
      s'.mem = writeState s.mem (s.gpr .x0) v ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, store, wordRev,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, reduceExec, addr,
    State.store, Option.bind_some, eval_rev, eval_ext2, and_self, isa, Option.map_some,
    RegUpd.gpr_setV, RegUpd.v_setV, RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV,
    h0, h16, h5, h6, flip_abcd, flip_efgh, write_pair, Option.some.injEq, exists_eq_left']

/-! ## One block -/

theorem Pre.in_blk16 {s₀ : State} (hp : AArch64.Pre s₀) {i n : Nat} (hi : i < nb s₀) (hn : n < 4) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 (16 * n)) 16 := by
  have := hp.nb_lt
  refine ⟨blR s₀, by simp [hp.rd], ?_⟩
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (16 * n) =
    bp s₀ + BitVec.ofNat 64 (64 * i + 16 * n) from Offset.add_add _ _ _]
  exact contains_offset (by omega_arith) (by omega_arith)

/-- The loop invariant, at the start of block `i`: the hash value the blocks
carry in `v5` and `v6`, and the memory as the function found it. -/
structure VInv (s₀ : State) (i : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  x3 : s.gpr .x3 = scr s₀
  kept : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = s₀.mem
  x1 : s.gpr .x1 = blkAddr s₀ i
  x2 : s.gpr .x2 = BitVec.ofNat 64 (nb s₀ - i)
  v5 : s.v .v5 = abcd (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i)
  v6 : s.v .v6 = efgh (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i)

theorem body_ok {s₀ : State} (hp : AArch64.Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : VInv s₀ i s) : WP isa body s (VInv s₀ (i + 1)) := by
  have hlt := hp.nb_lt
  refine WP.seq (WP.mono (fetch_ok (blk s₀ i) s
    (fun n hn => by rw [hL.rd, hL.wr, hL.x1]; exact Pre.in_blk16 hp hi hn)
    (fun t ht => by rw [hL.mem, hL.x1]; exact blk_word i t ht))
    fun s₁ ⟨hq₁, h21, h22, h5₁, h6₁, hg₁, hm₁, hrd₁, hwr₁⟩ => ?_)
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) s₁ (h5₁.trans hL.v5) (h6₁.trans hL.v6) hq₁ 16
    (Nat.le_refl _)) fun s₂ hR => ?_)
  have hg₂ : ∀ r, r ≠ .x4 → s₂.gpr r = s.gpr r := fun r h4 => by rw [hR.gpr r h4, hg₁]
  refine WP.mono (fold_ok s₂ _ (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i) hR.v5 hR.v6
    (by rw [hR.save _ (.inl rfl), h21]; exact hL.v5) (by rw [hR.save _ (.inr rfl), h22]; exact hL.v6))
    fun s₃ ⟨hv5₃, hv6₃, hx1₃, hx2₃, hg₃, hm₃, hrd₃, hwr₃⟩ => ?_
  have hx2 : s₂.gpr .x2 - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [hg₂ .x2 (by decide), hL.x2]
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega_arith), Nat.sub_sub]
  refine ⟨?_, ?_, ?_, by rw [hrd₃, hR.rd, hrd₁, hL.rd], by rw [hwr₃, hR.wr, hwr₁, hL.wr],
    by rw [hm₃, hR.mem, hm₁, hL.mem], ?_, by rw [hx2₃, hx2], ?_, ?_⟩
  · rw [hg₃ .x0 (by decide) (by decide), hg₂ .x0 (by decide), hL.x0]
  · rw [hg₃ .x3 (by decide) (by decide), hg₂ .x3 (by decide), hL.x3]
  · intro r hr
    have key : ∀ r ∈ preserved, r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x4 := by decide
    have hn := key r hr
    rw [hg₃ r hn.1 hn.2.1, hg₂ r hn.2.2, hL.kept r hr]
  · rw [hx1₃, hg₂ .x1 (by decide), hL.x1]
    exact (Offset.add_add _ _ 64).trans
      (congrArg (bp s₀ + ·) (congrArg (BitVec.ofNat 64) (by omega_arith)))
  · rw [hv5₃, compressBlocks_succ]
    rfl
  · rw [hv6₃, compressBlocks_succ]
    rfl

/-- The hash value, stored after the last block. -/
theorem final_ok {s₀ : State} (hp : AArch64.Pre s₀) {s : State} (hV : VInv s₀ (nb s₀) s) :
    WP isa (.block (wordRev ++ store)) s (Common s₀ (nb s₀)) := by
  have hlt := hp.nb_lt
  have hout : ∀ d, d ≤ 16 → InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 d) 16 := by
    intro d hd
    refine ⟨stR s₀, by simp [hV.wr, hp.wr], ?_⟩
    rw [hV.x0]; exact contains_offset (by omega_arith) (by omega_arith)
  refine (store_ok s _ hV.v5 hV.v6 (hout 0 (by decide)) (hout 16 (by decide))).mono
    fun s' ⟨hm, hg, hrd, hwr⟩ => ?_
  refine ⟨by rw [hg, hV.x0], by rw [hg, hV.x3], fun r hr => by rw [hg, hV.kept r hr],
    by rw [hrd, hV.rd], by rw [hwr, hV.wr], ?_, ?_⟩
  · rw [hm, hV.x0, hV.mem]
    exact (frame_writeState (Frame.refl _ _) _).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [hm, hV.x0, stateAt_writeState]

theorem eval_x2 {s₀ : State} {i : Nat} {s : State} (h : s.gpr .x2 = BitVec.ofNat 64 (nb s₀ - i))
    (hn : nb s₀ < 2 ^ 64) :
    eval (.nonzero .x .x2) s = some (nb s₀ - i != 0) := by
  have e : (BitVec.ofNat 64 (nb s₀ - i) != 0) = (nb s₀ - i != 0) := by
    by_cases h0 : nb s₀ - i = 0
    · simp [h0]
    · have : BitVec.ofNat 64 (nb s₀ - i) ≠ 0 := by
        intro h'
        have h'' := congrArg BitVec.toNat h'
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at h''
        exact h0 h''
      rw [Bool.eq_iff_iff]
      simp only [bne_iff_ne, ne_eq]
      exact ⟨fun _ => h0, fun _ => this⟩
  simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, h, e]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : AArch64.Pre s₀) :
    WP isa Impl.Sm3.AArch64.Sm4.compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sm3.compressAArch64.post s₀ s' := by
  have hc₀ : Common s₀ 0 s₀ :=
    ⟨rfl, rfl, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, rfl⟩
  refine WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s' hc => ⟨hc.kept, hc.state⟩
  refine WP.ite (s₀.gpr .x2 == 0) (by simp [eval, State.read]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    have hlt := hp.nb_lt
    have hin : ∀ d, d ≤ 16 → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + BitVec.ofNat 64 d) 16 := by
      intro d hd
      refine ⟨stR s₀, by simp [hp.wr], ?_⟩
      exact contains_offset (by omega_arith) (by omega_arith)
    refine WP.seq ((load_ok s₀ (hin 0 (by decide)) (hin 16 (by decide))).mono
      fun s₁ ⟨hv5, hv6, hg₁, hm₁, hrd₁, hwr₁⟩ => ?_)
    have hL₀ : VInv s₀ 0 s₁ :=
      { x0 := (by rw [hg₁])
        x3 := (by rw [hg₁])
        kept := fun r _ => (by rw [hg₁])
        rd := hrd₁
        wr := hwr₁
        mem := hm₁
        x1 := (by rw [hg₁]; simp [blkAddr])
        x2 := (by rw [hg₁]; simp [nb])
        v5 := (by rw [hv5]; rfl)
        v6 := (by rw [hv6]; rfl) }
    refine WP.seq (WP.mono (Q := VInv s₀ (nb s₀)) ?_ fun s₃ hV₃ => final_ok hp hV₃)
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ VInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval (.nonzero .x .x2) s' = some false ∧ VInv s₀ (nb s₀) s') ∨
        (eval (.nonzero .x .x2) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' hV' => ?_
      have hev := eval_x2 hV'.x2 (by omega_arith)
      by_cases hlast : i + 1 = nb s₀
      · exact .inl ⟨by rw [hev, hlast]; simp, hlast ▸ hV'⟩
      · exact .inr ⟨by rw [hev]; simp; omega_arith, nb s₀ - (i + 1), by omega_arith, i + 1, rfl,
          by omega_arith, hV'⟩
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

theorem compress_verified :
    Verified AArch64.target Impl.Sm3.AArch64.Sm4.compress Proof.Sm3.compressAArch64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · exact AArch64.compress_verified.2.2

end VG.Proof.Sm3.AArch64.Sm4
