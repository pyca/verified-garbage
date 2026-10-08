import VerifiedGarbage.Proof.X448.X86.Field

/-!
# X448 on x86 (32-bit): the field functions' context

What the field functions (`vg_gf448_r16_*`) know once `edi` holds the
working space (`FnCtx`): their arguments (`ArgArea`) and the offsets of the
result and the first operand, which fit below their own working space.
`argPtr_ok` points a register at an element from its offset.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

/-- What the field functions know on entry, after `edi = ws`: the working
space, the arguments, and the offsets `o`, `a` (and `b`) that fit below the
functions' own working space. -/
structure FnCtx (s : State) (base : Addr) (n : Nat) (o a : Nat) : Prop where
  scr : Scr s base
  args : ArgArea s base n
  n3 : 3 ≤ n
  argO : arg s 1 = BitVec.ofNat 32 o
  argA : arg s 2 = BitVec.ofNat 32 a
  slotO : Slot o
  slotA : Slot a

theorem FnCtx.keep {s t : State} {base : Addr} {n o a : Nat} (h : FnCtx s base n o a) {rs : List Reg}
    (hk : Keeps rs s t) (hr : .esp ∉ rs) (he : .edi ∉ rs) (hm : Outside base 0 8192 s.mem t.mem) :
    FnCtx t base n o a := by
  obtain ⟨ta, targ⟩ := h.args.keep (hk.1 _ hr) hk.2.1 hk.2.2 hm
  exact ⟨h.scr.of_keeps hk he, ta, h.n3, by rw [targ 1 (by have := h.n3; omega)]; exact h.argO,
    by rw [targ 2 (by have := h.n3; omega)]; exact h.argA, h.slotO, h.slotA⟩

/-- `r = ws + ` argument `i`. -/
theorem argPtr_ok {s : State} {base : Addr} {n : Nat} (ha : ArgArea s base n)
    {i : Nat} (hi : i < n) {r : Reg} (hr : r ≠ .edi) {d : Nat} (hd : arg s i = BitVec.ofNat 32 d) :
    WP isa (.block (argPtr r i)) s fun t =>
      t.gpr r = t.gpr .edi + BitVec.ofNat 32 d ∧ t.mem = s.mem ∧ Keeps [r] s t := by
  unfold argPtr
  refine ha.load hi fun u hu => wp_alu (Or.inl rfl) rfl fun v hv _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [hv.gpr, hv.other .edi hr.symm]
    change u.gpr r + u.gpr .edi = _
    rw [hu.gpr, hd, BitVec.add_comm]
  · rw [hv.mem, hu.mem]
  · exact (hu.rest (by simp)).trans (hv.rest (by simp))

end VG.Proof.X448.X86
