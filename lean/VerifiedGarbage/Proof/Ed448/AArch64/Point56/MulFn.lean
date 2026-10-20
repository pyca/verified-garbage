module

public import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Mul
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
public import VerifiedGarbage.Impl.X448.AArch64.Field56
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Tactic.SplitIfs

/-!
# Curve448's field product on AArch64, as a function

Untrusted: everything here is checked by Lean. `mulFn_ok`: from the arguments of
`vg_gf448_r56_mul` (`ws` in `x0`, the byte offsets `o`, `a`, `b` in `x1`–`x3`), the function
sets the operands' pointers (`ws + a` in `x10`, `ws + b` in `x30`, `ws + o` in `x1`), `ws` in
`x3` and the mask in `x12`, and runs `vg_x448`'s product with its operands addressed by the
pointers (`mulAt_ok`, `Proof/Curve448/AArch64/Fast/Mul.lean`): the result's limbs, and only the
result's 64 bytes and the operand sums' (`KA`) written. The callee-saved registers it changes
(and the return address, which holds the second operand's pointer while it runs) are kept in
lanes of `v21`–`v25` (`insOf_ok`, `umovOf_ok`), which the product does not write.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Point56

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.Curve448.AArch64.Fast (KA mulAt)
open VG.Impl.X448.AArch64 (ACC)
open VG.Proof.X448.AArch64 (Scr Keeps Outside2 limbs off)
open VG.Proof.Curve448.AArch64.Fast (Ib prodOut clob PtrOk mulAt_ok)
open VG.Proof.Ed25519.AArch64 (read_x)

/-- The registers `vg_gf448_r56_mul` may change and not restore: the product's (`clob`), the
result's pointer `x1`, and `x3` and `x12`, which it leaves as `ws` and the mask. -/
def mulClob : List Reg := .x1 :: .x3 :: .x12 :: clob

/-- What `vg_gf448_r56_mul` starts from: `ws` in `x0`, writable for its 8192 bytes, without
wrapping, the elements at the offsets in `x1`–`x3` below the products' coefficients, the result
not overlapping the second operand, and the operands' limbs below `Ib`. -/
structure MulPre (s : State) : Prop where
  wr : (⟨s.gpr .x0, 8192⟩ : Region) ∈ s.wr
  nowrap : (s.gpr .x0).toNat + 8192 ≤ 2 ^ 64
  o : (s.gpr .x1).toNat + 64 ≤ ACC
  a : (s.gpr .x2).toNat + 64 ≤ ACC
  b : (s.gpr .x3).toNat + 64 ≤ ACC
  ob : (s.gpr .x1).toNat + 64 ≤ (s.gpr .x3).toNat ∨ (s.gpr .x3).toNat + 64 ≤ (s.gpr .x1).toNat
  fa : ∀ i < 8, limbs s.mem (s.gpr .x0) (s.gpr .x2).toNat i < Ib
  fb : ∀ i < 8, limbs s.mem (s.gpr .x0) (s.gpr .x3).toNat i < Ib

/-- What `vg_gf448_r56_mul` ends in, from `s`: every register outside `mulClob`, or kept,
restored, `ws` in `x3` and the mask in `x12`; the product's limbs at `o`; and every byte but the
result's and the operand sums' kept. -/
abbrev MulPost (s u : State) : Prop :=
  (∀ r, (r ∉ mulClob ∨ r ∈ Point56.mulKept.map Prod.fst) → u.gpr r = s.gpr r) ∧
    u.gpr .x3 = s.gpr .x0 ∧ u.gpr .x12 = 0x0fffffff ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧
    (∀ i < 8, limbs u.mem (s.gpr .x0) (s.gpr .x1).toNat i =
      prodOut (limbs s.mem (s.gpr .x0) (s.gpr .x2).toNat)
        (limbs s.mem (s.gpr .x0) (s.gpr .x3).toNat) i) ∧
    Outside2 (s.gpr .x0) (s.gpr .x1).toNat 64 KA 64 s.mem u.mem

/-- The pointers, `ws` in `x3` and the mask in `x12`. -/
theorem mulSetup_ok (s : State) :
    WP isa (.block Point56.mulSetup) s fun t =>
      t.gpr .x10 = s.gpr .x0 + s.gpr .x2 ∧ t.gpr .x30 = s.gpr .x0 + s.gpr .x3 ∧
      t.gpr .x1 = s.gpr .x0 + s.gpr .x1 ∧ t.gpr .x3 = s.gpr .x0 ∧ t.gpr .x12 = 0x0fffffff ∧
      (∀ r, r ∉ [.x10, .x30, .x1, .x3, .x12] → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  apply WP.of_runBlock
  simp only [Point56.mulSetup, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (0 : Nat) < 4096 from by decide, Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, by decide, fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- A pointer `ws + x` to the element at offset `x` of the working space. -/
theorem ptrOk_of {s : State} {ws x : Addr} {r : Reg} (hr : s.gpr r = ws + x)
    (hx : x.toNat + 64 ≤ 8192) : PtrOk s ws r 0 x.toNat := by
  refine ⟨fun e => ?_, rfl, by decide, hx⟩
  rw [hr, Nat.zero_add]
  apply BitVec.eq_of_toNat_eq
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem mulKept_lanes : ∀ k ∈ Point56.mulKept, k.2.2 < 2 := by decide
theorem mulKept_nodup_lanes : (Point56.mulKept.map fun k => (k.2.1, k.2.2)).Nodup := by decide
theorem mulKept_nodup : (Point56.mulKept.map Prod.fst).Nodup := by decide

/-- The product writes no vector register. -/
theorem mulAt_noV' : (.block (mulAt .x10 0 .x30 0 .x1 0) : Prog isa).allInstrs
    (fun i => vdstOf i == none) = true := by decide +kernel

theorem mulAt_noV : ∀ i ∈ instrs (.block (mulAt .x10 0 .x30 0 .x1 0) : Prog isa),
    vdstOf i = none := fun i hi => by
  have h := mulAt_noV'
  rw [Code.allInstrs_eq] at h
  simpa using List.all_eq_true.mp h i hi

/-- **`vg_gf448_r56_mul`**, from its arguments. -/
theorem mulFn_ok {s : State} (h : MulPre s) : WP isa Point56.mulFn s fun u => MulPost s u := by
  unfold Point56.mulFn
  rw [WP.seq_iff, WP.block_append_iff]
  refine WP.mono (insOf_ok Point56.mulKept s mulKept_lanes mulKept_nodup_lanes)
    fun s₀ ⟨hg, hm, hr, hw, hsp, hls, _⟩ => ?_
  refine WP.mono (mulSetup_ok s₀) fun s₁ ⟨g10, g30, g1, g3, g12, gk, gm, gr, gw, gsp, gv⟩ => ?_
  rw [hg] at g10 g30 g1 g3 gk
  have hs : Scr s₁ (s.gpr .x0) := ⟨g3, g12, by rw [gw, hw]; exact h.wr, h.nowrap⟩
  have hA : ACC = 3584 := rfl
  have pa : PtrOk s₁ (s.gpr .x0) .x10 0 (s.gpr .x2).toNat := ptrOk_of g10 (by have := h.a; omega)
  have pb : PtrOk s₁ (s.gpr .x0) .x30 0 (s.gpr .x3).toNat := ptrOk_of g30 (by have := h.b; omega)
  have po : PtrOk s₁ (s.gpr .x0) .x1 0 (s.gpr .x1).toNat := ptrOk_of g1 (by have := h.o; omega)
  have fa : ∀ i < 8, limbs s₁.mem (s.gpr .x0) (s.gpr .x2).toNat i < Ib := by
    rw [gm, hm]; exact h.fa
  have fb : ∀ i < 8, limbs s₁.mem (s.gpr .x0) (s.gpr .x3).toNat i < Ib := by
    rw [gm, hm]; exact h.fb
  rw [WP.seq_iff]
  obtain ⟨tb, t, he, tv, tm, tk⟩ := mulAt_ok hs pa pb po (by decide) (by decide) (by decide) h.o h.b h.ob
    fa fb
  refine ⟨tb, t, he, ?_⟩
  have tl : ∀ k ∈ Point56.mulKept, laneOf t k.2.1 k.2.2 = s.gpr k.1 := fun k hk' => by
    have hv' : ∀ i ∈ instrs (.block (mulAt .x10 0 .x30 0 .x1 0) : Prog isa),
        vdstOf i ≠ some k.2.1 := fun i hi => by rw [mulAt_noV i hi]; exact fun e => nomatch e
    rw [laneOf, Exec.vec hv' he, gv, ← laneOf, hls k hk']
  refine WP.mono (umovOf_ok Point56.mulKept t mulKept_lanes mulKept_nodup)
    fun u ⟨um, ur, uw, usp, uls, uoth⟩ => ?_
  have kept3 : .x3 ∉ Point56.mulKept.map Prod.fst := by decide
  have kept12 : .x12 ∉ Point56.mulKept.map Prod.fst := by decide
  refine ⟨fun r hr' => ?_, by rw [uoth _ kept3, tk.1 _ (by decide), g3],
    by rw [uoth _ kept12, tk.1 _ (by decide), g12], by rw [ur, tk.2.1, gr, hr],
    by rw [uw, tk.2.2, gw, hw], by rw [usp, Exec.sp he, gsp, hsp], ?_, ?_⟩
  · by_cases hm' : r ∈ Point56.mulKept.map Prod.fst
    · obtain ⟨k, hk', rfl⟩ := List.mem_map.mp hm'
      rw [uls k hk', tl k hk']
    · have hr'' := hr'.resolve_right hm'
      simp only [mulClob, List.mem_cons, not_or] at hr''
      obtain ⟨h1, h3, h12, hc⟩ := hr''
      have h10 : r ≠ .x10 := fun e => hc (by rw [e]; decide)
      have h30 : r ≠ .x30 := fun e => hm' (by rw [e]; decide)
      rw [uoth r hm', tk.1 r hc, gk r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨h10, h30, h1, h3, h12⟩)]
  · intro i hi
    rw [um, tv i hi, gm, hm]
  · rw [um, ← hm, ← gm]; exact tm

end VG.Proof.Ed448.AArch64.Point56
