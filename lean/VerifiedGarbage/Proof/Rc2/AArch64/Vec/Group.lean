import VerifiedGarbage.Proof.Rc2.AArch64.Vec.Store

/-!
# One group of eight blocks

`group_ok`: the eight blocks at `x1` decrypted, each XORed with the
ciphertext block before it (the chaining value in `x11` before the first),
in place; the last ciphertext block into `x11`, and `x1` and `x10` advanced.
-/

namespace VG.Proof.Rc2.AArch64.Vec

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64 VG.Impl.Rc2.AArch64
  VG.Impl.Rc2.AArch64.Vec VG.Proof.Rc2

/-- The block before block `b` of the group at `q`: the chaining value `X` before the first. -/
def prevBlock (X : BitVec 64) (m : Mem) (q : Addr) (b : Nat) : Spec.Rc2.Block :=
  if b = 0 then wordBlock X else Spec.Rc2.blockAt m (q + BitVec.ofNat 64 (8 * (b - 1)))

structure GroupPost (m : Mem) (p : Addr) (t t' : State) : Prop where
  data : ∀ b < 8, Spec.Rc2.blockAt t'.mem (t.gpr .x1 + BitVec.ofNat 64 (8 * b)) =
    Spec.Rc2.xorBlock (Spec.Rc2.decryptBlock (Spec.Rc2.scheduleAt m p)
        (Spec.Rc2.blockAt t.mem (t.gpr .x1 + BitVec.ofNat 64 (8 * b))))
      (prevBlock (t.gpr .x11) t.mem (t.gpr .x1) b)
  frame : Frame [⟨t.gpr .x1, 64⟩] t.mem t'.mem
  chain : t'.gpr .x11 = t.mem.readW (t.gpr .x1 + BitVec.ofNat 64 56) 64
  ptr : t'.gpr .x1 = t.gpr .x1 + BitVec.ofNat 64 64
  count : t'.gpr .x10 = t.gpr .x10 - BitVec.ofNat 64 1
  reg : ∀ g, g ≠ .x1 → g ≠ .x6 → g ≠ .x7 → g ≠ .x9 → g ≠ .x10 → g ≠ .x11 → g ≠ .x12 →
    t'.gpr g = t.gpr g
  sched : SchedV t' m p
  mask : t'.v m16 = mask16
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  sp : t'.sp = t.sp

theorem exec_subImmx (s : State) (d n : Reg) {imm : Nat} (h : imm < 4096) :
    exec (.subImm .x d n imm) s = some (s.write .x d (s.gpr n - BitVec.ofNat 64 imm)) := by
  simp [exec, State.read, h]

/-- The output byte, as a block. -/
theorem out_block {m m' : Mem} {q : Addr} {X : BitVec 64} {R : Nat → Spec.Rc2.State}
    (h : ∀ o < 64, m' (q + BitVec.ofNat 64 o) = encByte (R (o / 8)) (o % 8) ^^^ prevByte X m q o)
    {b : Nat} (hb : b < 8) :
    Spec.Rc2.blockAt m' (q + BitVec.ofNat 64 (8 * b)) =
      Spec.Rc2.xorBlock (Spec.Rc2.encodeBlock (R b)) (prevBlock X m q b) := by
  apply Vector.ext
  intro j hj
  simp only [Spec.Rc2.blockAt, Spec.Rc2.xorBlock, Vector.getElem_ofFn, Offset.add_add, Fin.getElem_fin]
  rw [h _ (by omega), encodeBlock_getElem _ hj, show (8 * b + j) / 8 = b by omega,
    show (8 * b + j) % 8 = j by omega, prevByte, prevBlock]
  by_cases h0 : b = 0
  · subst h0
    simp only [ite_true, wordBlock, Vector.getElem_ofFn, show 8 * 0 + j = j by omega, hj]
  · simp only [show ¬ 8 * b + j < 8 by omega, h0, ite_false, Spec.Rc2.blockAt, Vector.getElem_ofFn,
      Offset.add_add, show 8 * (b - 1) + j = 8 * b + j - 8 by omega]

theorem group_ok {m : Mem} {p : Addr} (t : State) (hs : SchedV t m p) (hm : t.v m16 = mask16)
    (hrd : InRegions (t.rd ++ t.wr) (t.gpr .x1) 64) (hwr : InRegions t.wr (t.gpr .x1) 64) :
    WP isa (.block group) t (GroupPost m p t) := by
  rw [group, storeGroup_eq]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadGroup_ok t fun c hc => CallLay.inRegions_sub hrd (by omega) (by decide))
    fun a ⟨aS, av, ag, am, ard, awr, asp⟩ => ?_
  have aw : ∀ w, w ≠ .v0 → w ≠ .v1 → w ≠ .v2 → w ≠ .v3 → w ≠ .v4 → w ≠ .v5 →
      (∀ i < 4, ∀ h < 2, w ≠ wreg h i) → a.v w = t.v w := fun w a0 a1 a2 a3 a4 _ hw =>
    av w a0 a1 a2 a3 a4 hw
  have hsA : SchedV a m p := fun r hr => by
    obtain ⟨a0, a1, a2, a3, a4, a5, -, -⟩ := treg_ne8 r (by omega)
    rw [aw _ a0 a1 a2 a3 a4 a5 fun i hi h hh => ((regs_fixed h i hh hi).2.2.2.2.2.2.2.2 r hr).1]
    exact hs r hr
  have hmA : a.v m16 = mask16 := by
    rw [aw _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      fun i hi h hh => (regs_fixed h i hh hi).2.1]
    exact hm
  let R : Nat → Spec.Rc2.State := fun b => (List.range 16).foldl (revRound (Spec.Rc2.scheduleAt m p))
    (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt t.mem (t.gpr .x1 + BitVec.ofNat 64 (8 * b))))
  obtain ⟨b, runb, bS, bk⟩ := rounds_ok hsA hmA aS
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨b, runb, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (scatter_ok b (R := R) bS) fun c ⟨cS, cv, cg, cm, crd, cwr, csp⟩ => ?_
  have cx : ∀ g, g ≠ .x6 → g ≠ .x7 → g ≠ .x9 → c.gpr g = t.gpr g := fun g h6 h7 h9 => by
    rw [cg g h6 h7, bk.keep.reg g (by simp [h6, h9]), ag g h6 h7]
  have q₁ : c.gpr .x1 = t.gpr .x1 := cx _ (by decide) (by decide) (by decide)
  have mc : c.mem = t.mem := by rw [cm, bk.keep.mem, am]
  have rdc : c.rd = t.rd := by rw [crd, bk.keep.rd, ard]
  have wrc : c.wr = t.wr := by rw [cwr, bk.keep.wr, awr]
  obtain ⟨d, rund, dmem, dframe, d11, dg, dv, drd, dwr, dsp⟩ := xorStore_ok c (R := R) cS
    (by rw [rdc, wrc, q₁]; exact hrd) (by rw [wrc, q₁]; exact hwr)
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨d, rund, ?_⟩
  let e := d.write .x .x1 (d.gpr .x1 + BitVec.ofNat 64 64)
  let f := e.write .x .x10 (e.gpr .x10 - BitVec.ofNat 64 1)
  refine WP.of_runBlock ⟨f, by
    rw [runBlock_cons, exec_addImmx _ _ _ (by decide), runStep_some, runBlock_cons,
      exec_subImmx _ _ _ (by decide), runStep_some, runBlock_nil], ?_⟩
  have fg : ∀ g, g ≠ .x1 → g ≠ .x10 → f.gpr g = d.gpr g := fun g h1 h10 => by
    simp only [f, e, gpr_write_of_ne _ _ _ h10, gpr_write_of_ne _ _ _ h1]
  have x11 : c.gpr .x11 = t.gpr .x11 := cx _ (by decide) (by decide) (by decide)
  refine ⟨fun b hb => ?_, ?_, ?_, ?_, ?_, fun g h1 h6 h7 h9 h10 h11 h12 => ?_, fun r hr => ?_, ?_,
    by simp only [f, e, rd_write]; rw [drd, rdc], by simp only [f, e, wr_write]; rw [dwr, wrc],
    by simp only [f, e, sp_write]; rw [dsp, csp, bk.sp, asp]⟩
  · have := out_block (R := R) dmem hb
    rw [q₁, x11, mc] at this
    simp only [f, e, mem_write]
    rw [this, revRounds_eq]
  · simp only [f, e, mem_write]; rw [← mc, ← q₁]; exact dframe
  · rw [fg _ (by decide) (by decide), d11, mc, q₁]
  · simp only [f, e, gpr_write_of_ne _ _ _ (by decide : ¬Reg.x1 = .x10), gpr_write_self,
      BitVec.setWidth_eq]
    rw [dg _ (by decide) (by decide) (by decide), q₁]
  · simp only [f, gpr_write_self, BitVec.setWidth_eq, e, gpr_write_of_ne _ _ _ (by decide : ¬Reg.x10 = .x1)]
    rw [dg _ (by decide) (by decide) (by decide), cx _ (by decide) (by decide) (by decide)]
  · rw [fg g h1 h10, dg g h9 h11 h12, cx g h6 h7 h9]
  · simp only [f, e, v_write]
    obtain ⟨a0, a1, a2, a3, a4, a5, -, -⟩ := treg_ne8 r (by omega)
    rw [dv _ a0 a1 a2 a3 a4 a5, cv _ a0 a1 a2 a3 a4, bk.sched r hr]
    exact hsA r hr
  · simp only [f, e, v_write]
    rw [dv _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      cv _ (by decide) (by decide) (by decide) (by decide) (by decide), bk.mask]
    exact hmA

end VG.Proof.Rc2.AArch64.Vec
