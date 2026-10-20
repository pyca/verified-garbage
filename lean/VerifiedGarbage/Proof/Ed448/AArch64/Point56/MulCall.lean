module

public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.MulFn
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

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
  · simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  · simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  · simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
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
  refine WP.mono (mulArgs_ok s (o := o) (a := a) (b := b) (by omega) (by omega) (by omega))
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
