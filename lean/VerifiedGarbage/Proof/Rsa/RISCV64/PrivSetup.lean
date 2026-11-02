module

public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivPre
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.Mem
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_private_checked` on RISC-V: the frame, up to the call of `vg_rsa_private_crt`

The frame (`Impl/Rsa/RISCV64/Priv.lean`) is all of the stack the function
uses, `kR`, from its base `fb`, and is writable. From the state after its
`alloc`: the saves of `s1`–`s6` and of the return address, the values kept in
`s1`–`s6`, the call's arguments, and its ten stack arguments copied from ours
(`setup_ok`, into `AtCrt`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Priv

open VG VG.RISCV64 VG.Impl.Rsa.RISCV64.Priv VG.RISCV64.RegUpd

/-! ## Addresses -/

theorem fb_toNat {s : State} (h : frameBytes ≤ s.sp.toNat) : (fb s).toNat + frameBytes = s.sp.toNat := by
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega

theorem fb_al {s : State} (h : PreP s) : (fb s).toNat % 16 = 0 := by
  have := fb_toNat h.sp1; have := h.sp16; unfold frameBytes at *; omega

/-- A word of the frame at an offset that is a multiple of 8 is aligned. -/
theorem fb_al8 {s : State} (h : PreP s) {d : Nat} (hd : d % 8 = 0) :
    (fb s + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  have := fb_toNat h.sp1; have := fb_al h
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold frameBytes at *; omega

/-- A region of the frame is in the stack the function uses. -/
theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    Region.Sub ⟨fb s + BitVec.ofNat 64 d, n⟩ (kR s) := Offset.sub_base _ h

theorem frame_contains (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    (kR s).Contains (fb s + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ h (by unfold frameBytes at h; omega)

/-- The frame is writable. -/
theorem in_fr (s : State) (rs : List Region) {d n : Nat} (h : d + n ≤ frameBytes) :
    InRegions (kR s :: rs) (fb s + BitVec.ofNat 64 d) n :=
  ⟨_, List.mem_cons_self .., frame_contains s h⟩

theorem stackArgAddr_eq (s : State) (j : Nat) :
    stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]

theorem in_aR {s : State} {j : Nat} (hj : j < 12) : (aR s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)

/-! ## The saves -/

/-- The slots of our caller's `s1`–`s6` and of the return address. -/
def saved : List (Reg × Nat) :=
  [(.s1, oSave), (.s2, oSave + 8), (.s3, oSave + 16), (.s4, oSave + 24), (.s5, oSave + 32),
    (.s6, oSave + 40), (.ra, oRa)]

/-- The restores, the return address first. -/
def restored : List (Reg × Nat) :=
  [(.ra, oRa), (.s1, oSave), (.s2, oSave + 8), (.s3, oSave + 16), (.s4, oSave + 24), (.s5, oSave + 32),
    (.s6, oSave + 40)]

/-- The callee-saved registers other than `s1`–`s6`. -/
def hiRegs : List Reg := [.s0, .s7, .s8, .s9, .s10, .s11]

/-- The moves to `s1`–`s6`. -/
abbrev movs : List Instr := [mov .s1 .a0, mov .s2 .a2, mov .s3 .a3, mov .s4 .a4, mov .s5 .a5, mov .s6 .a6]

theorem save_eq : save = ([.addSp .t0 0] : List Instr) ++ Spill.saveCode .t0 saved ++ movs := rfl

theorem restore_eq : restore = ([.addSp .t0 0] : List Instr) ++ Spill.restoreCode .t0 restored := rfl

theorem saved_offs : ∀ p ∈ saved, oSave ≤ p.2 ∧ p.2 + 8 ≤ oSave + 56 := by decide

theorem saved_fits : Spill.Fits saved := by decide

theorem restored_offs : ∀ p ∈ restored, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide

theorem restorable : Spill.Restorable .t0 restored := by decide

theorem restored_saved : ∀ p ∈ restored, p ∈ saved := by decide

theorem preserved_split {r : Reg} (h : r ∈ preserved) : r ∈ saved.map Prod.fst ∨ r ∈ hiRegs := by
  revert r; decide

/-- In the frame, from the entry state `s`: our caller's registers and
return address in their slots, the other callee-saved registers as on entry,
memory changed only in the stack the function uses. -/
structure Fr (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = kR s :: s.wr
  hi : ∀ r ∈ hiRegs, t.gpr r = s.gpr r
  mem : Frame [kR s] s.mem t.mem
  sv : Spill.Saved (fb s) s.gpr saved t.mem

/-- The saves, from the state after the frame's `alloc`: `t0` holds the
frame's base, `s1`–`s6` and the return address are in their slots, and memory
is changed only in the frame. -/
theorem save_ok {s : State} (h : PreP s) {rest : List Instr} {Q : State → Prop}
    (k : ∀ v, Fr s v → v.gpr .t0 = fb s → (∀ r, r ≠ .t0 → v.gpr r = s.gpr r) →
      WP isa (.block rest) v Q) :
    WP isa (.block (([.addSp .t0 0] : List Instr) ++ Spill.saveCode .t0 saved ++ rest))
      (allocd frameBytes s) Q := by
  simp only [List.cons_append, List.nil_append]
  refine WP.block_cons_iff.mpr ⟨_, exec_addSp (imm := 0) (by decide), ?_⟩
  generalize hu : (allocd frameBytes s).write .t0 ((allocd frameBytes s).sp + BitVec.ofNat 64 0) = u
  have u0 : u.gpr .t0 = fb s := by rw [← hu, gpr_write_self]; exact BitVec.add_zero _
  have ug : ∀ r, r ≠ .t0 → u.gpr r = s.gpr r := fun r hr => by
    rw [← hu, gpr_write_of_ne _ _ hr]; rfl
  have uwr : u.wr = kR s :: s.wr := by rw [← hu]; rfl
  refine Spill.save_ok (b := .t0) (l := saved) (by rw [u0]; have := fb_al h; omega)
    saved_fits.1 (fun p hp => ?_) ?_
  · have := saved_offs p hp
    rw [uwr, u0]; exact in_fr s _ (by unfold oSave frameBytes at *; omega)
  refine k _ ⟨?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩ ?_ fun r h0 => ?_
  · show u.sp = fb s; rw [← hu]; rfl
  · show u.rd = s.rd; rw [← hu]; rfl
  · exact uwr
  · exact ug r (by revert r; decide)
  · show Frame [kR s] s.mem (Spill.saveMem u.mem (u.gpr .t0) u.gpr saved)
    rw [u0, show u.mem = s.mem by rw [← hu]; rfl]
    exact Spill.saveMem_frame_base (fun p hp => by
      have := saved_offs p hp; unfold oSave frameBytes at *; omega) (by decide) _ _ _
  · show Spill.Saved (fb s) s.gpr saved (Spill.saveMem u.mem (u.gpr .t0) u.gpr saved)
    rw [u0]
    refine fun p hp => (Spill.saveMem_saved saved_fits _ _ _ p hp).trans (ug _ ?_)
    revert p; decide
  · exact u0
  · exact ug r h0

/-! ## The stack arguments -/

theorem stackArgAddr_al {s : State} (h : PreP s) (j : Nat) :
    (stackArgAddr s j).toNat % 8 = 0 := by
  have := h.sp16; have := h.sp2
  simp only [stackArgAddr, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- Our stack argument `j` is in the arguments' region, apart from the frame. -/
theorem arg_read {s : State} (h : PreP s) {m : Mem} (hm : Frame [kR s] s.mem m) {j : Nat} (hj : j < 12) :
    m.readW (stackArgAddr s j) 64 = stackArg s j :=
  hm.readW (in_aR hj) (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.ka.symm) (by decide)

/-- Our stack argument `j`, after the frame and the working space changed. -/
theorem arg_read2 {s : State} (h : PreP s) {m : Mem} (hm : Frame [kR s, sR s] s.mem m) {j : Nat}
    (hj : j < 12) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  refine hm.readW (in_aR hj) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.ka.symm
  · exact h.sa.symm

theorem arg_in {s t : State} (h : PreP s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 12) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 := by
  rw [hrd, h.hrd]
  exact ⟨_, List.mem_append_left _ (by simp), in_aR hj⟩

/-- `argBase`: `t6` holds the address of our first stack argument. -/
theorem argBase_ok {s v : State} (hsp : v.sp = fb s) {rest : List Instr} {Q : State → Prop}
    (k : ∀ w, w.gpr .t6 = s.sp → Keep [.t6] v w → w.mem = v.mem → w.sp = v.sp → WP isa (.block rest) w Q) :
    WP isa (.block (argBase ++ rest)) v Q := by
  simp only [argBase, List.cons_append, List.nil_append]
  have e1 := exec_addSp (s := v) (d := .t6) (imm := 2032) (by decide)
  have e2 := exec_addi_nat (s := v.write .t6 (v.sp + BitVec.ofNat 64 2032)) (d := .t6) (n := .t6)
    (m := frameBytes - 2032) (by unfold frameBytes; omega)
  refine WP.block_cons_iff.mpr ⟨_, e1, WP.block_cons_iff.mpr ⟨_, e2, k _ ?_ ⟨fun r hr => ?_, rfl, rfl⟩ rfl rfl⟩⟩
  · rw [gpr_write_self, gpr_write_self, hsp, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact BitVec.sub_add_cancel _ _
  · have : r ≠ .t6 := by simpa using hr
    rw [gpr_write_of_ne _ _ this, gpr_write_of_ne _ _ this]

/-! ## Up to the call -/

/-- The stack arguments of the calls, at the frame's base. -/
abbrev psaR (s : State) : Region := ⟨fb s, 80⟩

/-- At the call of `vg_rsa_private_crt`. -/
structure AtCrt (s t : State) : Prop extends Fr s t where
  a0 : t.gpr .a0 = fb s + BitVec.ofNat 64 oM
  a1 : t.gpr .a1 = s.gpr .a3
  a2 : t.gpr .a2 = s.gpr .a2
  a3 : t.gpr .a3 = s.gpr .a3
  a4 : t.gpr .a4 = s.gpr .a6
  a5 : t.gpr .a5 = s.gpr .a3
  a6 : t.gpr .a6 = stackArg s 0
  a7 : t.gpr .a7 = stackArg s 1
  s1 : t.gpr .s1 = s.gpr .a0
  s2 : t.gpr .s2 = s.gpr .a2
  s3 : t.gpr .s3 = s.gpr .a3
  s4 : t.gpr .s4 = s.gpr .a4
  s5 : t.gpr .s5 = s.gpr .a5
  s6 : t.gpr .s6 = s.gpr .a6
  psa : ∀ i < 10, t.mem.readW (fb s + BitVec.ofNat 64 (8 * i)) 64 = stackArg s (2 + i)

/-- After copying the first `n` stack arguments, from `w`. -/
structure CI (s w : State) (n : Nat) (t : State) : Prop where
  keep : Keep [.t1] w t
  mem : Frame [psaR s] w.mem t.mem
  psa : ∀ i < n, t.mem.readW (fb s + BitVec.ofNat 64 (8 * i)) 64 = stackArg s (2 + i)

theorem copy_step {s w : State} (h : PreP s) (hw0 : w.gpr .t0 = fb s) (hw6 : w.gpr .t6 = s.sp)
    (hrd : w.rd = s.rd) (hwr : w.wr = kR s :: s.wr) (hm : Frame [kR s] s.mem w.mem) {n : Nat} (hn : n < 10)
    {t : State} (hc : CI s w n t) : WP isa (.block (argCopy n)) t (CI s w (n + 1)) := by
  have t0 : t.gpr .t0 = fb s := (hc.keep.gpr (by decide)).trans hw0
  have t6 : t.gpr .t6 = s.sp := (hc.keep.gpr (by decide)).trans hw6
  have psa_sub : Region.Sub (psaR s) (kR s) := by
    have := frame_sub s (d := 0) (n := 80) (by decide); rwa [BitVec.add_zero] at this
  have hmt : Frame [kR s] s.mem t.mem := hm.trans (hc.mem.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, psa_sub⟩)
  have ea : t.gpr .t6 + BitVec.ofNat 64 (8 * (2 + n)) = stackArgAddr s (2 + n) := by rw [t6]; rfl
  have hin : InRegions (t.rd ++ t.wr) (t.gpr .t6 + BitVec.ofNat 64 (8 * (2 + n))) 8 := by
    rw [ea]; exact arg_in h (hc.keep.2.1.trans hrd) (by omega)
  have hv : t.mem.readW (t.gpr .t6 + BitVec.ofNat 64 (8 * (2 + n))) 64 = stackArg s (2 + n) := by
    rw [ea]; exact arg_read h hmt (by omega)
  have hal : (t.gpr .t6 + BitVec.ofNat 64 (8 * (2 + n))).toNat % 8 = 0 := by
    rw [ea]; exact stackArgAddr_al h _
  have ho : InRegions t.wr (t.gpr .t0 + BitVec.ofNat 64 (8 * n)) 8 := by
    rw [t0, hc.keep.2.2, hwr]; exact in_fr s _ (by unfold frameBytes; omega)
  apply WP.of_runBlock
  simp only [argCopy, runBlock_cons, runStep_some, exec_load_d (by omega) hal hin]
  rw [exec_store_d (by omega) (by rw [gpr_write_of_ne _ _ (by decide), t0]; exact fb_al8 h (by omega))
    (by rw [gpr_write_of_ne _ _ (show Reg.t0 ≠ .t1 by decide)]; exact ho)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  rw [gpr_write_of_ne _ _ (show Reg.t0 ≠ .t1 by decide), gpr_write_self, mem_write, hv, t0]
  refine ⟨⟨fun r hr => ?_, hc.keep.2.1, hc.keep.2.2⟩, ?_, fun i hi => ?_⟩
  · show (t.write .t1 _).gpr r = w.gpr r
    rw [gpr_write_of_ne _ _ (by simpa using hr)]; exact hc.keep.gpr hr
  · exact hc.mem.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide)]
      exact hc.psa i hi
    · rw [Mem.readW_writeW_self64]

theorem copies_ok {s w : State} (h : PreP s) (hw0 : w.gpr .t0 = fb s) (hw6 : w.gpr .t6 = s.sp)
    (hrd : w.rd = s.rd) (hwr : w.wr = kR s :: s.wr) (hm : Frame [kR s] s.mem w.mem) :
    WP isa (.block ((List.range 10).flatMap argCopy)) w (CI s w 10) :=
  wp_range_flatMap (M := isa) (CI s w) (fun _ _ hn hc => copy_step h hw0 hw6 hrd hwr hm hn hc) 10
    (Nat.le_refl _) w ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- `crtArgs` after `argBase`: the arguments in registers. -/
abbrev crtHead : List Instr :=
  [.addi .a0 .t0 oM, mov .a1 .s3, mov .a4 .s6, mov .a5 .s3, .load .d .a6 .t6 0, .load .d .a7 .t6 8]

theorem crtArgs_eq : crtArgs = argBase ++ (crtHead ++ (List.range 10).flatMap argCopy) := by
  simp only [crtArgs, List.append_assoc]

theorem movs_ok {s v : State} (hg : ∀ r, r ≠ .t0 → v.gpr r = s.gpr r) :
    WP isa (.block movs) v fun w =>
      (w.gpr .s1 = s.gpr .a0 ∧ w.gpr .s2 = s.gpr .a2 ∧ w.gpr .s3 = s.gpr .a3 ∧ w.gpr .s4 = s.gpr .a4 ∧
        w.gpr .s5 = s.gpr .a5 ∧ w.gpr .s6 = s.gpr .a6 ∧ w.mem = v.mem) ∧
      Keep [.s1, .s2, .s3, .s4, .s5, .s6] v w := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [mov, hg .a0 (by decide), hg .a2 (by decide), hg .a3 (by decide), hg .a4 (by decide),
    hg .a5 (by decide), hg .a6 (by decide), BitVec.add_zero]

theorem head_ok {s w : State} (h : PreP s) (hrd : w.rd = s.rd) (hm : Frame [kR s] s.mem w.mem)
    (h0 : w.gpr .t0 = fb s) (h6 : w.gpr .t6 = s.sp) (h3 : w.gpr .s3 = s.gpr .a3)
    (h6' : w.gpr .s6 = s.gpr .a6) :
    WP isa (.block crtHead) w fun u =>
      (u.gpr .a0 = fb s + BitVec.ofNat 64 oM ∧ u.gpr .a1 = s.gpr .a3 ∧ u.gpr .a4 = s.gpr .a6 ∧
        u.gpr .a5 = s.gpr .a3 ∧ u.gpr .a6 = stackArg s 0 ∧ u.gpr .a7 = stackArg s 1 ∧ u.mem = w.mem) ∧
      Keep [.a0, .a1, .a4, .a5, .a6, .a7] w u := by
  have i0 : InRegions (w.rd ++ w.wr) (s.sp + BitVec.ofNat 64 0) 8 := arg_in h hrd (j := 0) (by decide)
  have i1 : InRegions (w.rd ++ w.wr) (s.sp + BitVec.ofNat 64 8) 8 := arg_in h hrd (j := 1) (by decide)
  have l0 : (s.sp + BitVec.ofNat 64 0).toNat % 8 = 0 := stackArgAddr_al h 0
  have l1 : (s.sp + BitVec.ofNat 64 8).toNat % 8 = 0 := stackArgAddr_al h 1
  have r0 : w.mem.readW (s.sp + BitVec.ofNat 64 0) 64 = stackArg s 0 := arg_read h hm (j := 0) (by decide)
  have r1 : w.mem.readW (s.sp + BitVec.ofNat 64 8) 64 = stackArg s 1 := arg_read h hm (j := 1) (by decide)
  simp only [BitVec.add_zero] at i0 l0 r0
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [mov, h0, h6, h3, h6', i0, i1, l0, l1, r0, r1, BitVec.add_zero, oM]

theorem setup_core {s : State} (h : PreP s) :
    WP isa (.block (save ++ crtArgs)) (allocd frameBytes s) fun t => t.sp = fb s → AtCrt s t := by
  rw [save_eq, crtArgs_eq, List.append_assoc]
  refine save_ok h fun v F h0 hg => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.rdwr (movs_ok hg)) fun w ⟨⟨⟨w1, w2, w3, w4, w5, w6, wm⟩, kw⟩, wrd, wwr, wsp⟩ => ?_
  have w0 : w.gpr .t0 = fb s := (kw.gpr (by decide)).trans h0
  refine argBase_ok (s := s) (wsp.trans F.sp) fun x x6 kx xm _ => ?_
  have x0 : x.gpr .t0 = fb s := (kx.gpr (by decide)).trans w0
  have xrd : x.rd = s.rd := kx.2.1.trans (wrd.trans F.rd)
  have xwr : x.wr = kR s :: s.wr := kx.2.2.trans (wwr.trans F.wr)
  have xm' : Frame [kR s] s.mem x.mem := by rw [xm, wm]; exact F.mem
  rw [WP.block_append_iff]
  refine WP.mono (head_ok h xrd xm' x0 x6 ((kx.gpr (by decide)).trans w3) ((kx.gpr (by decide)).trans w6))
    fun y ⟨⟨y0, y1, y4, y5, y6, y7, ym⟩, ky⟩ => ?_
  refine WP.mono (copies_ok h ((ky.gpr (by decide)).trans x0) ((ky.gpr (by decide)).trans x6)
    (ky.2.1.trans xrd) (ky.2.2.trans xwr) (by rw [ym]; exact xm')) fun t hc tsp => ?_
  have k := hc.keep
  have psa_sub : Region.Sub (psaR s) (kR s) := by
    have := frame_sub s (d := 0) (n := 80) (by decide); rwa [BitVec.add_zero] at this
  have hsv : Spill.Saved (fb s) s.gpr saved y.mem := by rw [ym, xm, wm]; exact F.sv
  have g : ∀ r, r ∉ ([.t1, .a0, .a1, .a4, .a5, .a6, .a7] : List Reg) → t.gpr r = x.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k.gpr (by simp [hr.1]), ky.gpr (by simp [hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2])]
  refine ⟨⟨tsp, k.2.1.trans (ky.2.1.trans xrd), k.2.2.trans (ky.2.2.trans xwr), fun r hr => ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hc.psa⟩
  · rw [g r (by revert r; decide), kx.gpr (by revert r; decide), kw.gpr (by revert r; decide)]
    exact F.hi r hr
  · rw [← ym] at xm'
    exact xm'.trans (hc.mem.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, psa_sub⟩)
  · exact hsv.frame hc.mem fun p hp r hr => by
      rw [List.mem_singleton.mp hr]
      have := saved_offs p hp
      exact Offset.disjoint_base _ (by unfold oSave at this; omega) (by unfold oSave at this; omega)
  · rw [k.gpr (by decide)]; exact y0
  · rw [k.gpr (by decide)]; exact y1
  · rw [g _ (by decide), kx.gpr (by decide), kw.gpr (by decide)]; exact hg _ (by decide)
  · rw [g _ (by decide), kx.gpr (by decide), kw.gpr (by decide)]; exact hg _ (by decide)
  · rw [k.gpr (by decide)]; exact y4
  · rw [k.gpr (by decide)]; exact y5
  · rw [k.gpr (by decide)]; exact y6
  · rw [k.gpr (by decide)]; exact y7
  · rw [g _ (by decide), kx.gpr (by decide)]; exact w1
  · rw [g _ (by decide), kx.gpr (by decide)]; exact w2
  · rw [g _ (by decide), kx.gpr (by decide)]; exact w3
  · rw [g _ (by decide), kx.gpr (by decide)]; exact w4
  · rw [g _ (by decide), kx.gpr (by decide)]; exact w5
  · rw [g _ (by decide), kx.gpr (by decide)]; exact w6

theorem setup_ok {s : State} (h : PreP s) :
    WP isa (.block (save ++ crtArgs)) (allocd frameBytes s) (AtCrt s) :=
  WP.mono (WP.rdwr (setup_core h)) fun _ ⟨hc, _, _, hsp⟩ => hc hsp

/-- Between the calls, from the entry state `s`: the frame, the values kept
in `s1`–`s6`, the other callee-saved registers as on entry, our caller's
registers and return address in their slots, and memory changed only in the
frame and the working space. -/
structure Mid (s u : State) : Prop where
  sp : u.sp = fb s
  rd : u.rd = s.rd
  wr : u.wr = kR s :: s.wr
  s1 : u.gpr .s1 = s.gpr .a0
  s2 : u.gpr .s2 = s.gpr .a2
  s3 : u.gpr .s3 = s.gpr .a3
  s4 : u.gpr .s4 = s.gpr .a4
  s5 : u.gpr .s5 = s.gpr .a5
  s6 : u.gpr .s6 = s.gpr .a6
  hi : ∀ r ∈ hiRegs, u.gpr r = s.gpr r
  mem : Frame [kR s, sR s] s.mem u.mem
  sv : Spill.Saved (fb s) s.gpr saved u.mem

theorem AtCrt.mid {s t : State} (A : AtCrt s t) : Mid s t :=
  ⟨A.sp, A.rd, A.wr, A.s1, A.s2, A.s3, A.s4, A.s5, A.s6, A.hi,
    A.mem.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self .., A.sv⟩

/-- A buffer of the caller that the function does not write. -/
theorem bytes_of_frame {s : State} {rs : List Region} {m : Mem} (hf : Frame rs s.mem m) {p : Addr}
    {len : Nat} (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, len⟩ r) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) hd hl (List.mem_range.mp hi)

end VG.Proof.Rsa.RISCV64.Priv
