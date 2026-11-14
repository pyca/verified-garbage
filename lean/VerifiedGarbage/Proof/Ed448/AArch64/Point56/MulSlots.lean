module

public import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Mul
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
public import VerifiedGarbage.Impl.X448.AArch64.Field56
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.X448.AArch64.Fast.Chain
public import VerifiedGarbage.Proof.Framework.AArch64.StoreFrame
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/-! ### `Ed448.AArch64.Point56.MulCall`, which only this module used -/

section

/-! ### `Ed448.AArch64.Point56.MulFn`, which only this module used -/

section

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
  omega_using []

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
  have pa : PtrOk s₁ (s.gpr .x0) .x10 0 (s.gpr .x2).toNat := ptrOk_of g10 (by have := h.a; omega_using [hA, this])
  have pb : PtrOk s₁ (s.gpr .x0) .x30 0 (s.gpr .x3).toNat := ptrOk_of g30 (by have := h.b; omega_using [hA, this])
  have po : PtrOk s₁ (s.gpr .x0) .x1 0 (s.gpr .x1).toNat := ptrOk_of g1 (by have := h.o; omega_using [hA, this])
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

end

end


/-!
# Curve448's field product on AArch64: calls of `vg_gf448_r56_mul`

Untrusted: everything here is checked by Lean. `mulCall_ok`: a call (`mulCall o a b`, the
offsets as immediates and `ws` from `x3`, with `x1` kept in `x19`), from the register-resident
arithmetic's state (`Scr`), computes what the inlined product does (`mulAt_ok`): the product's
limbs at `o`, only the result's and the operand sums' bytes written, and every register but
`x19`, `x30` and the product's kept, with `ws` back in `x3`. The call runs on the working space alone (`WP.callV`,
with the function's own proof, `mulFn_ok`, as its contract, `mulK`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Point56

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.Curve448.AArch64.Fast (KA)
open VG.Impl.X448.AArch64 (ACC)
open VG.Proof.X448.AArch64 (Scr Keeps Outside2 limbs)
open VG.Proof.Curve448.AArch64.Fast (Ib prodOut clob)

/-- The contract of a call, from the function's own proof: the arguments `base`, `o`, `a`, `b`,
and `vg_gf448_r56_mul`'s precondition, on the working space alone. -/
def mulK (base : Addr) (o a b : Nat) : Contract isa where
  pre t := t.rd = [] ∧ t.wr = [⟨base, 8192⟩] ∧ t.gpr .x0 = base ∧ (t.gpr .x1).toNat = o ∧
    (t.gpr .x2).toNat = a ∧ (t.gpr .x3).toNat = b ∧ MulPre t
  post t t' := MulPost t t'
  pub _ _ := True

theorem mulFn_keepsV' : Point56.mulFn.allInstrs keepsV = true := by decide +kernel

theorem mulK_verified (base : Addr) (o a b : Nat) :
    ∀ t, (mulK base o a b).pre t → ∃ tr t', Exec isa Point56.mulFn t tr t' ∧ abiPreserved t t' ∧
      (mulK base o a b).post t t' := by
  intro t ⟨_, _, _, _, _, _, hp⟩
  obtain ⟨tr, t', he, hpost, hv⟩ := WP.preservedV (mulFn_ok hp) mulFn_keepsV'
  exact ⟨tr, t', he, ⟨fun r hr => hpost.1 r (by revert hr; revert r; decide), hpost.2.2.2.2.2.1, hv⟩,
    hpost⟩

/-- The arguments: `x1` kept in `x19`, `ws` from `x3`, and the offsets. -/
theorem mulArgs_ok (s : State) {o a b : Nat} (ho : o < 65536) (ha : a < 65536) (hb : b < 65536) :
    WP isa (.block [.addImm .x .x19 .x1 0, .addImm .x .x0 .x3 0, .movz .x .x1 (BitVec.ofNat 16 o) 0,
        .movz .x .x2 (BitVec.ofNat 16 a) 0, .movz .x .x3 (BitVec.ofNat 16 b) 0]) s fun t =>
      t.gpr .x19 = s.gpr .x1 ∧
      t.gpr .x0 = s.gpr .x3 ∧ (t.gpr .x1).toNat = o ∧ (t.gpr .x2).toNat = a ∧ (t.gpr .x3).toNat = b ∧
      (∀ r, r ∉ [.x0, .x1, .x2, .x3, .x19] → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show (0 : Nat) < 4096 from by decide, Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using [ho]
  · simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using [ha]
  · simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using [hb]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- **A call of `vg_gf448_r56_mul`**, as the inlined product. -/
theorem mulCall_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : o + 64 ≤ ACC) (ha : a + 64 ≤ ACC) (hb : b + 64 ≤ ACC) (hob : o + 64 ≤ b ∨ b + 64 ≤ o)
    (fa : ∀ i < 8, limbs s.mem base a i < Ib) (fb : ∀ i < 8, limbs s.mem base b i < Ib) :
    WP isa (Point56.mulCall o a b) s fun t =>
      (∀ i < 8, limbs t.mem base o i = prodOut (limbs s.mem base a) (limbs s.mem base b) i) ∧
      Outside2 base o 64 KA 64 s.mem t.mem ∧ Keeps (.x19 :: .x30 :: clob) s t ∧ t.sp = s.sp ∧
      (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) := by
  have hA : ACC = 3584 := rfl
  unfold Point56.mulCall
  rw [WP.seq_iff]
  refine WP.mono (mulArgs_ok s (o := o) (a := a) (b := b) (by omega_using [ho, hA]) (by omega_using [ha, hA]) (by omega_using [hb, hA]))
    fun s1 ⟨g19, g0, g1, g2, g3, gk, m1, r1, w1, sp1, v1⟩ => ?_
  rw [WP.seq_iff]
  have g0' : s1.gpr .x0 = base := by rw [g0, hs.x3]
  have hcov : Covers [⟨base, 8192⟩] s1.wr := Covers.of_mem fun r hr => by
    rw [List.mem_singleton.mp hr, w1]; exact hs.wr
  have e0 : (s1.callEntry.withRegions [] [⟨base, 8192⟩]).gpr .x0 = base := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), g0']
  have e1 : (s1.callEntry.withRegions [] [⟨base, 8192⟩]).gpr .x1 = s1.gpr .x1 := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide)]
  have e2 : (s1.callEntry.withRegions [] [⟨base, 8192⟩]).gpr .x2 = s1.gpr .x2 := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide)]
  have e3 : (s1.callEntry.withRegions [] [⟨base, 8192⟩]).gpr .x3 = s1.gpr .x3 := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide)]
  have em : (s1.callEntry.withRegions [] [⟨base, 8192⟩]).mem = s.mem := by
    rw [State.withRegions_mem, State.callEntry_mem, m1]
  refine WP.callV (k := mulK base o a b) (rd := []) (wr := [⟨base, 8192⟩]) (mulK_verified base o a b)
    ⟨rfl, rfl, e0, by rw [e1, g1], by rw [e2, g2], by rw [e3, g3],
      ⟨by rw [e0]; exact List.mem_singleton_self _, by rw [e0]; exact hs.nowrap,
        by rw [e1, g1]; exact ho, by rw [e2, g2]; exact ha, by rw [e3, g3]; exact hb,
        by rw [e1, e3, g1, g3]; exact hob, by rw [e0, e2, g2, em]; exact fa,
        by rw [e0, e3, g3, em]; exact fb⟩⟩
    (Covers.right hcov) hcov ?_
  intro t hrd hwr hsp _ _ _ hv ⟨hg, h3, h12, _, _, _, hl, hm⟩
  rw [e0, e1, g1, e2, g2, e3, g3, em] at hl
  rw [e0, e1, g1, em] at hm
  simp only [State.withRegions_gpr, State.withRegions_mem] at hg h3 h12 hl hm
  have t19 : t.gpr .x19 = s.gpr .x1 := by
    rw [hg .x19 (.inl (by decide)), State.callEntry_gpr _ (by decide), g19]
  refine WP.of_runBlock ⟨t.write .x .x1 (t.gpr .x19 + BitVec.ofNat 64 0), ?_, ?_⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
      show (0 : Nat) < 4096 from by decide, ite_true, BitVec.setWidth_eq]
  have u1 : (t.write .x .x1 (t.gpr .x19 + BitVec.ofNat 64 0)).gpr .x1 = s.gpr .x1 := by
    rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero, t19]
  have uk : ∀ r, r ≠ .x1 → (t.write .x .x1 (t.gpr .x19 + BitVec.ofNat 64 0)).gpr r = t.gpr r :=
    fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr
  refine ⟨hl, hm, ⟨fun r hr => ?_, by change t.rd = s.rd; rw [hrd, r1],
    by change t.wr = s.wr; rw [hwr, w1]⟩, by change t.sp = s.sp; rw [hsp, sp1],
    fun r hr => by change (t.v r).extractLsb' 0 64 = _; rw [hv r hr, v1]⟩
  by_cases e1' : r = .x1
  · subst e1'; exact u1
  rw [uk r e1']
  by_cases e3' : r = .x3
  · subst e3'; rw [h3, State.callEntry_gpr _ (by decide), g0', hs.x3]
  by_cases e12 : r = .x12
  · subst e12; rw [h12, hs.mask]
  simp only [List.mem_cons, not_or] at hr
  obtain ⟨h19, h30, hc⟩ := hr
  have hl' : r ∉ VG.AArch64.linkRegs := by
    simp only [VG.AArch64.linkRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨?_, ?_, h30⟩ <;> intro h <;> subst h <;> exact hc (by decide)
  have hnc : r ∉ mulClob := by
    simp only [mulClob, List.mem_cons, not_or]
    exact ⟨e1', e3', e12, hc⟩
  have h0 : r ≠ .x0 := fun h => by subst h; exact hc (by decide)
  have h2 : r ≠ .x2 := fun h => by subst h; exact hc (by decide)
  rw [hg r (.inl hnc), State.callEntry_gpr _ hl', gk r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h0, e1', h2, e3', h19⟩)]

end VG.Proof.Ed448.AArch64.Point56

end

end


/-!
# Curve448's field product on AArch64: calls on the slots

Untrusted: everything here is checked by Lean. `mulCallE`: a call of `vg_gf448_r56_mul` on
slots of the working space does what the inlined product does to them (`fmulE`): it updates
the result's slot with the product (`opMul`), keeps every slot's limbs below `Ib` and the
result's below `Mb`, and writes nothing but the result and the operand sums.

`PSpec`: what a chain of field operations whose products are calls (the square root's power,
`root`) computes, with the bytes it keeps (outside slots 14–21 and the products' coefficients),
from the inlined operations' `ISpec` and their stores (`PSpec.of_ispec`) and from the calls
(`mulCallP`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Point56

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Proof.X448.AArch64 (Scr Keeps Outside2 limbs FieldMem ofs)
open VG.Proof.X448.AArch64.Weak (Index Env opMul FieldOp applyOps)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd Same fclob ISpec IKeep FKeep fieldMem_same env_update slot_64
  slot_sep64)
open VG.Proof.Curve448.AArch64.Fast (prodOut clob)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- **A call of `vg_gf448_r56_mul`** on slots, as the inlined product (`fmulE`). -/
theorem mulCallE {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) (o a b : Index)
    (hob : o ≠ b) :
    WP isa (Point56.mulCall (slot o.val) (slot a.val) (slot b.val)) s fun t =>
      Keeps (.x19 :: .x30 :: fclob) s t ∧ t.sp = s.sp ∧
      (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) ∧
      Outside2 base (slot o.val) 64 ACC 64 s.mem t.mem ∧ BEnv t.mem base ∧
      Bnd Mb t.mem base (slot o.val) ∧ Same base [o] s.mem t.mem ∧
      EV t.mem base = opMul o a b (EV s.mem base) := by
  have hA : ACC = 3584 := rfl
  refine WP.mono (mulCall_ok hs (slot_64 o) (slot_64 a) (slot_64 b) (slot_sep64 hob) (hb a) (hb b))
    fun t ⟨tv, tm, tk, tsp, tV⟩ => ?_
  have fm : FieldMem base (slot o.val) s.mem t.mem := fun x h1 h2 =>
    tm x (by omega_using [h1]) (by have : VG.Impl.Curve448.AArch64.Fast.KA = 3584 := rfl; omega_using [hA, h2, this])
  have bo : Bnd Mb t.mem base (slot o.val) := fun i hi => by
    rw [tv i hi]; exact VG.Proof.Curve448.AArch64.Fast.prod_bound (hb a) (hb b) i hi
  refine ⟨tk, tsp, tV, tm, env_update hb fm (fun i hi =>
    Nat.lt_of_lt_of_le (bo i hi) VG.Proof.Curve448.AArch64.Fast.Mb_le_Ib), bo, fieldMem_same fm, ?_⟩
  rw [VG.Proof.X448.AArch64.Weak.E_update fm]
  simp only [opMul]
  refine congrArg (Function.update _ o) ?_
  change VG.Proof.X448.toFe _ = VG.Proof.X448.toFe _ * VG.Proof.X448.toFe _
  rw [VG.Proof.X448.Wide.valN_congr tv]
  exact VG.Proof.Curve448.AArch64.Fast.prod_val _ _

/-! ## Calls keeping `x19` and the return address -/

/-- No instruction of a call writes `v26`. -/
theorem mulCall_noV26' (o a b : Nat) : (Point56.mulCall o a b).allInstrs (fun i => vdstOf i != some .v26) = true := by
  simp only [Point56.mulCall, Code.allInstrs]
  rfl

theorem mulCall_noV26 (o a b : Nat) : ∀ i ∈ instrs (Point56.mulCall o a b), vdstOf i ≠ some .v26 :=
  fun i hi => by
    have h := mulCall_noV26' o a b
    rw [Code.allInstrs_eq] at h
    simpa using List.all_eq_true.mp h i hi

theorem mulCallK_keepsV (o a b : Nat) : (Point56.mulCallK o a b).allInstrs keepsV = true := by
  simp only [Point56.mulCallK, Point56.mulCall, Code.allInstrs]
  rfl

/-- **A call of `vg_gf448_r56_mul` keeping `x19` and `x30`**, as the inlined product: every
register but the product's kept. -/
theorem mulCallK_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : o + 64 ≤ ACC) (ha : a + 64 ≤ ACC) (hb : b + 64 ≤ ACC) (hob : o + 64 ≤ b ∨ b + 64 ≤ o)
    (fa : ∀ i < 8, limbs s.mem base a i < Ib) (fb : ∀ i < 8, limbs s.mem base b i < Ib) :
    WP isa (Point56.mulCallK o a b) s fun t =>
      (∀ i < 8, limbs t.mem base o i = prodOut (limbs s.mem base a) (limbs s.mem base b) i) ∧
      Outside2 base o 64 VG.Impl.Curve448.AArch64.Fast.KA 64 s.mem t.mem ∧ Keeps clob s t ∧
      t.sp = s.sp ∧ (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) := by
  have h : WP isa (Point56.mulCallK o a b) s fun t =>
      (∀ i < 8, limbs t.mem base o i = prodOut (limbs s.mem base a) (limbs s.mem base b) i) ∧
      Outside2 base o 64 VG.Impl.Curve448.AArch64.Fast.KA 64 s.mem t.mem ∧ Keeps clob s t ∧
      t.sp = s.sp := by
    unfold Point56.mulCallK
    rw [WP.seq_iff]
    refine WP.mono (insOf_ok [(.x19, .v26, 0), (.x30, .v26, 1)] s (by decide) (by decide))
      fun s₁ ⟨g₁, m₁, r₁, w₁, sp₁, l₁, _⟩ => ?_
    have hs₁ : Scr s₁ base := hs.of_keeps (rs := []) ⟨fun r _ => by rw [g₁], r₁, w₁⟩ (by decide)
    rw [WP.seq_iff]
    obtain ⟨tr, t, he, tl, tm, tk, tsp, _⟩ := mulCall_ok hs₁ ho ha hb hob (m₁ ▸ fa) (m₁ ▸ fb)
    refine ⟨tr, t, he, ?_⟩
    have hv : t.v .v26 = s₁.v .v26 := Exec.vec (mulCall_noV26 o a b) he
    have l19 : laneOf t .v26 0 = s.gpr .x19 := by
      rw [laneOf, hv, ← laneOf, l₁ (.x19, .v26, 0) List.mem_cons_self]
    have l30 : laneOf t .v26 1 = s.gpr .x30 := by
      rw [laneOf, hv, ← laneOf, l₁ (.x30, .v26, 1) (List.mem_cons_of_mem _ List.mem_cons_self)]
    refine WP.mono (umovOf_ok [(.x19, .v26, 0), (.x30, .v26, 1)] t (by decide) (by decide))
      fun u ⟨um, ur, uw, usp, ul, uo⟩ => ?_
    refine ⟨fun i hi => by rw [um, tl i hi, m₁], by rw [um, ← m₁]; exact tm,
      ⟨fun r hr => ?_, by rw [ur, tk.2.1, r₁], by rw [uw, tk.2.2, w₁]⟩, by rw [usp, tsp, sp₁]⟩
    by_cases h19 : r = .x19
    · subst h19; rw [ul (.x19, .v26, 0) List.mem_cons_self, l19]
    by_cases h30 : r = .x30
    · subst h30; rw [ul (.x30, .v26, 1) (List.mem_cons_of_mem _ List.mem_cons_self), l30]
    rw [uo r (by simp [h19, h30]), tk.1 r (by simp [h19, h30, hr]), g₁]
  exact WP.mono (WP.preservedV h (mulCallK_keepsV o a b)) fun t ⟨⟨h1, h2, h3, h4⟩, h5⟩ =>
    ⟨h1, h2, h3, h4, h5⟩

/-- **A call of `vg_gf448_r56_mul` keeping `x19` and `x30`** on slots, as the inlined product
(`fmulE`). -/
theorem mulCallKE {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) (o a b : Index)
    (hob : o ≠ b) :
    WP isa (Point56.mulCallK (slot o.val) (slot a.val) (slot b.val)) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Bnd Mb t.mem base (slot o.val) ∧
      Same base [o] s.mem t.mem ∧ EV t.mem base = VG.Proof.X448.AArch64.opMul o a b (EV s.mem base) := by
  have hA : ACC = 3584 := rfl
  refine WP.mono (mulCallK_ok hs (slot_64 o) (slot_64 a) (slot_64 b) (slot_sep64 hob) (hb a) (hb b))
    fun t ⟨tv, tm, tk, _, _⟩ => ?_
  have fm : FieldMem base (slot o.val) s.mem t.mem := fun x h1 h2 =>
    tm x (by omega_using [h1]) (by have : VG.Impl.Curve448.AArch64.Fast.KA = 3584 := rfl; omega_using [hA, h2, this])
  have bo : Bnd Mb t.mem base (slot o.val) := fun i hi => by
    rw [tv i hi]; exact VG.Proof.Curve448.AArch64.Fast.prod_bound (hb a) (hb b) i hi
  refine ⟨⟨tk, VG.Proof.X448.AArch64.Fast.fieldMem_outside2 fm⟩, env_update hb fm (fun i hi =>
    Nat.lt_of_lt_of_le (bo i hi) VG.Proof.Curve448.AArch64.Fast.Mb_le_Ib), bo, fieldMem_same fm, ?_⟩
  rw [VG.Proof.X448.AArch64.Weak.E_update fm]
  simp only [VG.Proof.X448.AArch64.opMul]
  refine congrArg (Function.update _ o) ?_
  change VG.Proof.X448.toFe _ = VG.Proof.X448.toFe _ * VG.Proof.X448.toFe _
  rw [VG.Proof.X448.Wide.valN_congr tv]
  exact VG.Proof.Curve448.AArch64.Fast.prod_val _ _

/-- The call in a chain of the register-resident arithmetic (`ISpec`), as the inlined product. -/
theorem mulCallKI (base : Addr) (o a b : Index) (hob : o ≠ b) :
    ISpec base (Point56.mulCallK (slot o.val) (slot a.val) (slot b.val)) (applyOps [.mul o a b]) :=
  fun _ hs hb => WP.mono (mulCallKE hs hb o a b hob) fun _ ⟨tk, tb, _, _, te⟩ =>
    ⟨tk.ikeep, tb, te⟩

/-! ## Operations with calls -/

open VG.Impl.X448.AArch64.Fast (opsK)

/-- A product in `opsK`: a square inlined, a product of distinct operands a call, either as the
inlined product (`mulOp`). -/
theorem mulOpK {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) (o a b : Index)
    (hob : a = b ∨ o ≠ b)
    {rest : List Impl.X448.AArch64.Fast.Op} {Q : State → Prop}
    (h : ∀ t, FKeep base s t → BEnv t.mem base → Bnd Mb t.mem base (slot o.val) →
      Same base [o] s.mem t.mem →
      EV t.mem base = Function.update (EV s.mem base) o (EV s.mem base a * EV s.mem base b) →
      WP isa (opsK rest) t Q) :
    WP isa (opsK (.mul (slot o.val) (slot a.val) (slot b.val) :: rest)) s Q := by
  simp only [opsK, Impl.X448.AArch64.Fast.Op.progK]
  split
  · refine WP.seq (WP.mono (VG.Proof.X448.AArch64.Fast.fmulE hs hb o a b hob)
      fun t ⟨tk, tb, tm, ts, te⟩ => h t tk tb tm ts ?_)
    rw [te]; rfl
  · rename_i hab
    have hob' : o ≠ b := hob.resolve_left fun e => hab (e ▸ rfl)
    exact WP.seq (WP.mono (mulCallKE hs hb o a b hob') fun t ⟨tk, tb, tm, ts, te⟩ => h t tk tb tm ts te)

/-- A difference in `opsK`, as in `ops` (`subOp`). -/
theorem subOpK {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) {o a b : Index}
    (ha : Bnd Mb s.mem base (slot a.val)) (hb' : Bnd Mb s.mem base (slot b.val)) (hoa : o ≠ a)
    (hob : o ≠ b) {rest : List Impl.X448.AArch64.Fast.Op} {Q : State → Prop}
    (h : ∀ t, FKeep base s t → BEnv t.mem base → Same base [o] s.mem t.mem →
      EV t.mem base = Function.update (EV s.mem base) o (EV s.mem base a - EV s.mem base b) →
      WP isa (opsK rest) t Q) :
    WP isa (opsK (.sub (slot o.val) (slot a.val) (slot b.val) :: rest)) s Q :=
  WP.seq (WP.mono (VG.Proof.X448.AArch64.Fast.subE hs hb ha hb' hoa hob) fun t ⟨tk, tb, ts, te⟩ =>
    h t tk tb ts te)

/-! ## Chains with calls -/

/-- The registers a chain with calls may change: the field operations', the counter `x19` (which
the calls change too), and the calls' `x30`. -/
abbrev pclob : List Reg := .x30 :: .x19 :: fclob

/-- What a chain with calls computes: `f` of the slots, every slot's limbs below `Ib`, and every
byte outside slots 14–21 and the products' coefficients kept. -/
def PSpec (base : Addr) (code : Prog isa) (f : Env → Env) : Prop :=
  ∀ s, Scr s base → BEnv s.mem base → WP isa code s fun t =>
    Keeps pclob s t ∧ BEnv t.mem base ∧ EV t.mem base = f (EV s.mem base) ∧
      Outside2 base 1856 1024 ACC 1152 s.mem t.mem

theorem PSpec.seq {base : Addr} {c₁ c₂ : Prog isa} {f g : Env → Env}
    (h₁ : PSpec base c₁ f) (h₂ : PSpec base c₂ g) :
    PSpec base (.seq c₁ c₂) (fun e => g (f e)) := fun s hs hb =>
  WP.seq (WP.mono (h₁ s hs hb) fun t ⟨tk, tb, te, tm⟩ =>
    WP.mono (h₂ t (hs.of_keeps tk (by decide)) tb) fun u ⟨uk, ub, ue, um⟩ =>
      ⟨tk.trans uk, ub, by rw [ue, te], tm.trans um⟩)

/-- Where the inlined operations of the power store: slots 14–21 and the products'
coefficients. -/
def rootOk (d : Nat) : Bool := (1856 ≤ d && d + 8 ≤ 2880) || (3584 ≤ d && d + 8 ≤ 4736)

/-- The bytes outside slots 14–21 and the products' coefficients, from the stores. -/
theorem outside2_of_rootOk {base : Addr} {m m' : Mem}
    (h : ∀ a, Unstored rootOk base a → m' a = m a) : Outside2 base 1856 1024 ACC 1152 m m' := by
  intro a h1 h2
  refine h a fun d hd => ?_
  simp only [rootOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hd
  simp only [ACC] at h2
  rw [show a - (base + BitVec.ofNat 64 d) = (a - base) - BitVec.ofNat 64 d by
    exact Offset.sub_add_eq a base _]
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  simp only [ofs] at h1 h2
  have : (a - base).toNat < 2 ^ 64 := (a - base).isLt
  omega_using [h1, h2, hd]

/-- An inlined chain that stores only where `rootOk` allows. -/
theorem PSpec.of_ispec {base : Addr} {c : Prog isa} {f : Env → Env} (h : ISpec base c f)
    (hst : ∀ i ∈ instrs c, storesAt rootOk i = true) : PSpec base c f := fun s hs hb =>
  WP.mono (WP.storeFrame hst (h s hs hb)) fun t ⟨⟨tk, tb, te⟩, _, tf⟩ =>
    ⟨tk.regs.mono fun r hr => List.mem_cons_of_mem _ hr, tb, te,
      outside2_of_rootOk (by rw [hs.x3] at tf; exact tf)⟩

/-- A call of `vg_gf448_r56_mul` writing one of slots 14–21. -/
theorem mulCallP (base : Addr) (o a b : Index) (hob : o ≠ b) (ho : 14 ≤ o.val) :
    PSpec base (Point56.mulCall (slot o.val) (slot a.val) (slot b.val)) (applyOps [.mul o a b]) :=
  fun s hs hb => WP.mono (mulCallE hs hb o a b hob) fun t ⟨tk, _, _, tm, tb, _, _, te⟩ =>
    ⟨tk.mono fun r hr => by
        simp only [List.mem_cons] at hr ⊢
        rcases hr with h | h | h
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h),
      tb, te, fun p h1 h2 => tm p (by have := o.isLt; simp only [slot]; omega_using [ho, h1])
        (by simp only [ACC] at h2 ⊢; omega_using [h2])⟩

end VG.Proof.Ed448.AArch64.Point56
