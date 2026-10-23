module

public import VerifiedGarbage.Proof.Scrypt.PPC64LE.Whole.Layout
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
public import VerifiedGarbage.Impl.Scrypt.PPC64LE.Scrypt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch

/-!
# scrypt on PPC64LE: the blocks between the calls

As on AArch64 (`Proof/Scrypt/AArch64/Whole/Steps.lean`): the facts about
the parameters the proof uses; reading and writing the frame in `Ctx`; and
each block between the calls (`setup` from the frame's push, the moves of
the calls' arguments, the next block, `restore`), keeping `Ctx` and giving
the calls' arguments (`PbkArgs`, `RomixArgs`) or the next block.
-/

@[expose] public section

namespace VG.Proof.Scrypt.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Scrypt.PPC64LE.Whole

/-! ## Arithmetic -/

theorem toNat_le_of_disjoint {R S : Region} (h : R.Disjoint S) (hS : 0 < S.len) : R.len < 2 ^ 64 := by
  refine Nat.lt_of_not_le fun hR => h S.base ?_ ?_
  · simp only [Region.Contains]; have := (S.base - R.base).isLt; omega
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem lsl7 (x : BitVec 64) : x <<< 7 = BitVec.ofNat 64 (x.toNat * 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]

namespace Lay.Ok

variable {L : Lay} (h : L.Ok)
include h

theorem blen_eq : L.blen.toNat = L.r.toNat * L.pp :=
  (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h.bmod)).symm
theorem pp_pos : 0 < L.pp := h.valid.2.2.2.1

/-- `b` is not the whole address space, since the stack is not in it. -/
theorem blen_lt : L.blen.toNat * 128 < 2 ^ 64 :=
  toNat_le_of_disjoint h.kb.symm (by show (0 : Nat) < 1120; omega)

theorem r_le : L.r.toNat ≤ L.blen.toNat := by
  rw [h.blen_eq]; exact Nat.le_mul_of_pos_right _ h.pp_pos

theorem r_lt : L.r.toNat * 128 < 2 ^ 64 := by have := h.blen_lt; have := h.r_le; omega

/-- `128 r p`, the length of `b`. -/
theorem len_b : 128 * L.r.toNat * L.pp = L.blen.toNat * 128 := by
  rw [h.blen_eq, Nat.mul_comm 128, Nat.mul_assoc, Nat.mul_comm 128, Nat.mul_assoc]

/-- The derived key of step 1 is not too long for PBKDF2. -/
theorem ol1 : L.blen.toNat * 128 ≤ (2 ^ 32 - 1) * 32 := by
  have h₁ := h.valid.2.2.2.2.1
  have h₂ := Nat.div_mul_le_self ((2 ^ 32 - 1) * 32) (128 * L.r.toNat)
  have h₃ : L.pp * (128 * L.r.toNat) ≤ (2 ^ 32 - 1) * 32 / (128 * L.r.toNat) * (128 * L.r.toNat) :=
    Nat.mul_le_mul_right _ h₁
  rw [← h.len_b, Nat.mul_comm (128 * L.r.toNat)]
  omega

theorem slen17 : 17 ≤ L.slen.toNat := by have := h.slen; have := h.rpos; omega

end Lay.Ok

/-! ## In the frame -/

/-- A register other than the callee-saved ones keeps them. -/
theorem gpr_write_pres {s : State} {r d : Reg} {v : BitVec 64} (hr : r ∈ preserved) (hd : d ∉ preserved) :
    (s.write d v).gpr r = s.gpr r :=
  RegUpd.gpr_write_of_ne _ _ fun e => hd (e ▸ hr)

/-- Reading a doubleword past a write of another. -/
theorem readW_writeW_off (B : Addr) (m : Mem) {x y : Nat} (v : BitVec 64) (h : x + 8 ≤ y ∨ y + 8 ≤ x)
    (hx : x + 8 ≤ 2 ^ 64) (hy : y + 8 ≤ 2 ^ 64) :
    (m.writeW (B + BitVec.ofNat 64 y) v).readW (B + BitVec.ofNat 64 x) 64 = m.readW (B + BitVec.ofNat 64 x) 64 :=
  Mem.readW_writeW_sep (Offset.sep B h hx hy) (by decide)

/-- A 64-bit `write` is a `writeW`. -/
theorem write8 (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

/-- The address of a doubleword of the frame (`r30 = B + 1008`). -/
theorem fr_addr (B : Addr) (d : Nat) :
    B + BitVec.ofNat 64 1008 + BitVec.ofNat 64 d = B + BitVec.ofNat 64 (1008 + d) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- The frame's cur slot. -/
abbrev curR (L : Lay) : Region := ⟨L.B + BitVec.ofNat 64 1104, 8⟩

namespace Ctx

variable {L : Lay} {g : Reg → BitVec 64} {lr : BitVec 64} {m₀ : Mem} {t t' : State}
  (hc : Ctx L g lr m₀ t)
include hc

theorem r30' : t.gpr .r30 = L.B + BitVec.ofNat 64 1008 := hc.r30

theorem inFr {d : Nat} (h₁ : 1040 ≤ d) (h₂ : d + 8 ≤ 1120) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inFrW {d : Nat} (h₁ : 1040 ≤ d) (h₂ : d + 8 ≤ 1120) : InRegions t.wr (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inArgs {d : Nat} (h₁ : 1216 ≤ d) (h₂ : d + 8 ≤ 1256) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.ARGS, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

/-- Code that writes only registers other than the callee-saved ones. -/
theorem regs (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp) (hm : t'.mem = t.mem)
    (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) : Ctx L g lr m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, (hg _ (by decide)).trans hc.r30,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hm]; exact hc.kept, by rw [hm]; exact hc.frame⟩

/-- Code that also writes the frame's cur slot. -/
theorem store (hL : L.Ok) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) (hf : Frame [curR L] t.mem t'.mem) : Ctx L g lr m₀ t' := by
  have hnB := hL.nB
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, (hg _ (by decide)).trans hc.r30,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), hc.kept.frame hf fun d hd R hR => ?_,
    hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  · simp only [List.mem_singleton] at hR; subst hR
    exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.STK, by simp, Offset.sub_base _ (by omega)⟩

end Ctx

/-- The callee-saved registers through the writes of a block that writes
none of them. -/
macro "pres_tac" : tactic => `(tactic| (
  intro r hr
  simp (disch := decide) only [gpr_write_pres hr]))

/-- The simp set running a block in the frame. -/
macro "frame_run" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  apply WP.of_runBlock
  set_option linter.unusedSimpArgs false in
  simp only [runBlock_cons, runStep_some, runBlock_nil, fld, argOff, locals, lrOff, r30Off, pwOff, pwlOff,
    rOff, bOff, blenOff, vOff, curOff, vlenArg, scratchArg, outArg, outLenArg,
    exec_ld, exec_std, exec_li, exec_lsl, exec_add, exec_sub, exec_addi', exec_mtlr,
    RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write,
    RegUpd.mem_write, RegUpd.lr_write, fr_addr, ne_eq, reduceCtorEq, not_false_eq_true,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, Nat.reducePow, and_self,
    Option.some.injEq, exists_eq_left', $ls,*]))

/-! ## The blocks -/

section
variable {L : Lay} {g : Reg → BitVec 64} {lr : BitVec 64} {m₀ : Mem}

/-- The arguments of a call of PBKDF2 with the salt `salt` (`sl` bytes) and
the output `out` (`ol` bytes): the password, `c = 1` and `scratch`. -/
structure PbkArgs (L : Lay) (salt : Addr) (sl : BitVec 64) (out : Addr) (ol : BitVec 64) (t : State) :
    Prop where
  r3 : t.gpr .r3 = L.pw
  r4 : t.gpr .r4 = L.pwl
  r5 : t.gpr .r5 = salt
  r6 : t.gpr .r6 = sl
  r7 : t.gpr .r7 = 1
  r8 : t.gpr .r8 = out
  r9 : t.gpr .r9 = ol
  r10 : t.gpr .r10 = L.scr

/-- The registers on entry to the frame's body, once our arguments are saved. -/
structure Entry (L : Lay) (t : State) : Prop where
  r3 : t.gpr .r3 = L.pw
  r4 : t.gpr .r4 = L.pwl
  r5 : t.gpr .r5 = L.salt
  r6 : t.gpr .r6 = L.sl
  r8 : t.gpr .r8 = L.b
  r9 : t.gpr .r9 = L.blen

theorem pbk1Args_ok {t : State} (hc : Ctx L g lr m₀ t) (he : Entry L t) :
    WP isa (.block pbk1Args) t fun t' => Ctx L g lr m₀ t' ∧ t'.mem = t.mem ∧
      PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t' := by
  have l1224 := hc.inArgs (d := 1224) (by omega) (by omega)
  frame_run [pbk1Args, hc.r30', l1224, hc.kept.scr]
  refine ⟨hc.regs rfl rfl rfl rfl (by pres_tac), trivial, ?_⟩
  exact ⟨he.r3, he.r4, he.r5, he.r6, rfl, he.r8, by rw [he.r9, lsl7]; rfl, rfl⟩

theorem cur0_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block cur0) t fun t' => Ctx L g lr m₀ t' ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 1104) 64 = L.b ∧ Frame [curR L] t.mem t'.mem := by
  have l1080 := hc.inFr (d := 1080) (by omega) (by omega)
  have w1104 := hc.inFrW (d := 1104) (by omega) (by omega)
  frame_run [cur0, hc.r30', l1080, w1104, hc.kept.b]
  have f : Frame [curR L] t.mem (t.mem.writeW (L.B + BitVec.ofNat 64 1104) L.b) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact ⟨hc.store hL rfl rfl rfl (by pres_tac) f, Mem.readW_writeW_self64 _ _ _, f⟩

/-- The arguments of a call of ROMix on the block at `cur`. -/
structure RomixArgs (L : Lay) (cur : Addr) (t : State) : Prop where
  r3 : t.gpr .r3 = cur
  r4 : t.gpr .r4 = L.r
  r5 : t.gpr .r5 = L.v
  r6 : t.gpr .r6 = L.vlen
  r7 : t.gpr .r7 = L.scr
  r8 : t.gpr .r8 = L.r + BitVec.ofNat 64 2

theorem romixArgs_ok {t : State} (hc : Ctx L g lr m₀ t) {cur : Addr}
    (hcur : t.mem.readW (L.B + BitVec.ofNat 64 1104) 64 = cur) :
    WP isa (.block romixArgs) t fun t' => Ctx L g lr m₀ t' ∧ t'.mem = t.mem ∧ RomixArgs L cur t' := by
  have l1104 := hc.inFr (d := 1104) (by omega) (by omega)
  have l1072 := hc.inFr (d := 1072) (by omega) (by omega)
  have l1096 := hc.inFr (d := 1096) (by omega) (by omega)
  have l1216 := hc.inArgs (d := 1216) (by omega) (by omega)
  have l1224 := hc.inArgs (d := 1224) (by omega) (by omega)
  frame_run [romixArgs, hc.r30', l1104, l1072, l1096, l1216, l1224, hcur, hc.kept.r, hc.kept.v,
    hc.kept.vlen, hc.kept.scr]
  exact ⟨hc.regs rfl rfl rfl rfl (by pres_tac), trivial, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem nextBlock_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {cur : Addr}
    (hcur : t.mem.readW (L.B + BitVec.ofNat 64 1104) 64 = cur) :
    WP isa (.block nextBlock) t fun t' => Ctx L g lr m₀ t' ∧ Frame [curR L] t.mem t'.mem ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 1104) 64 = cur + BitVec.ofNat 64 (L.r.toNat * 128) ∧
      t'.gpr .r5 = L.b + BitVec.ofNat 64 (L.blen.toNat * 128) - (cur + BitVec.ofNat 64 (L.r.toNat * 128)) := by
  have l1104 := hc.inFr (d := 1104) (by omega) (by omega)
  have w1104 := hc.inFrW (d := 1104) (by omega) (by omega)
  have l1072 := hc.inFr (d := 1072) (by omega) (by omega)
  have l1080 := hc.inFr (d := 1080) (by omega) (by omega)
  have l1088 := hc.inFr (d := 1088) (by omega) (by omega)
  frame_run [nextBlock, hc.r30', l1104, w1104, l1072, l1080, l1088, hcur, hc.kept.r, hc.kept.b,
    hc.kept.blen, lsl7]
  have f : Frame [curR L] t.mem
      (t.mem.writeW (L.B + BitVec.ofNat 64 1104) (cur + BitVec.ofNat 64 (L.r.toNat * 128))) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.store hL rfl rfl rfl (by pres_tac) f, f, Mem.readW_writeW_self64 _ _ _, ?_⟩
  show _ - _ = _
  rw [readW_writeW_off (x := 1080) (y := 1104) _ _ _ (by decide) (by decide) (by decide),
    readW_writeW_off (x := 1088) (y := 1104) _ _ _ (by decide) (by decide) (by decide), hc.kept.b, hc.kept.blen]

theorem pbk2Args_ok {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block pbk2Args) t fun t' => Ctx L g lr m₀ t' ∧ t'.mem = t.mem ∧
      PbkArgs L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol t' := by
  have l1056 := hc.inFr (d := 1056) (by omega) (by omega)
  have l1064 := hc.inFr (d := 1064) (by omega) (by omega)
  have l1080 := hc.inFr (d := 1080) (by omega) (by omega)
  have l1088 := hc.inFr (d := 1088) (by omega) (by omega)
  have l1224 := hc.inArgs (d := 1224) (by omega) (by omega)
  have l1240 := hc.inArgs (d := 1240) (by omega) (by omega)
  have l1248 := hc.inArgs (d := 1248) (by omega) (by omega)
  frame_run [pbk2Args, hc.r30', l1056, l1064, l1080, l1088, l1224, l1240, l1248, hc.kept.pw, hc.kept.pwl,
    hc.kept.b, hc.kept.blen, hc.kept.scr, hc.kept.out, hc.kept.ol, lsl7]
  exact ⟨hc.regs rfl rfl rfl rfl (by pres_tac), trivial, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The return address back in the link register and our caller's `r30` back. -/
theorem restore_ok {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block restore) t fun t' => t'.lr = lr ∧ t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧
      t'.wr = t.wr ∧ ∀ r ∈ preserved, t'.gpr r = g r := by
  have l1040 := hc.inFr (d := 1040) (by omega) (by omega)
  have l1048 := hc.inFr (d := 1048) (by omega) (by omega)
  frame_run [restore, hc.r30', l1040, l1048, hc.kept.lr, hc.kept.r30]
  refine ⟨by trivial, by trivial, by trivial, by trivial, by trivial, fun r hr => ?_⟩
  by_cases e : r = .r30
  · subst e; exact RegUpd.gpr_write_self _ _ _
  · rw [RegUpd.gpr_write_of_ne _ _ e]
    exact (gpr_write_pres hr (by decide)).trans (hc.cs r hr e)

/-! ## Entering the frame -/

theorem alloc_sp (s : State) : (allocated 112 s).sp = (lay s).B + BitVec.ofNat 64 1008 := by
  show s.sp - BitVec.ofNat 64 112 = s.sp - BitVec.ofNat 64 1120 + BitVec.ofNat 64 1008
  bv_omega

theorem alloc_wr (s : State) : (allocated 112 s).wr = (lay s).FR :: s.wr := by
  show (⟨s.sp - BitVec.ofNat 64 112 + 32, 112 - 32⟩ : Region) :: s.wr = _
  rw [show s.sp - BitVec.ofNat 64 112 + 32 = (lay s).B + BitVec.ofNat 64 1040 by
    show _ = s.sp - BitVec.ofNat 64 1120 + _; bv_omega]

theorem alloc_mem (s : State) : (allocated 112 s).mem = s.mem.writeW ((lay s).B + BitVec.ofNat 64 1008) s.sp := by
  show s.mem.write (s.sp - BitVec.ofNat 64 112) 8 s.sp = _
  rw [show s.sp - BitVec.ofNat 64 112 = (lay s).B + BitVec.ofNat 64 1008 from alloc_sp s, write8]

theorem alloc_gpr (s : State) : (allocated 112 s).gpr = s.gpr := rfl
theorem alloc_lr (s : State) : (allocated 112 s).lr = s.lr := rfl
theorem alloc_rd (s : State) : (allocated 112 s).rd = s.rd := rfl

theorem arg_slot (s : State) (i : Nat) (hi : i < 5) :
    stackArgAddr s i = (lay s).B + BitVec.ofNat 64 (1216 + 8 * i) := by
  simp only [stackArgAddr, lay]
  have : 8 * i < 2 ^ 64 := by omega
  bv_omega

theorem exec_addSp0 {s : State} {d : Reg} : exec (.addSp d 0) s = some (s.write d s.sp) := by
  simp [exec]

theorem add_ofNat_zero (x : BitVec 64) : x + BitVec.ofNat 64 0 = x := BitVec.add_zero x

theorem entry_ok {s : State} (h : scryptPPC.pre s) :
    WP isa (.block setup) (allocated locals s) fun t => Ctx (lay s) s.gpr s.lr s.mem t ∧ Entry (lay s) t := by
  have hL := lay_ok h
  have hnB := hL.nB
  have hw : ∀ d, 1040 ≤ d → d + 8 ≤ 1120 →
      InRegions (allocated 112 s).wr ((lay s).B + BitVec.ofNat 64 d) 8 :=
    fun d h₁ h₂ => ⟨(lay s).FR, by rw [alloc_wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩
  have w1040 := hw 1040 (by omega) (by omega)
  have w1048 := hw 1048 (by omega) (by omega)
  have w1056 := hw 1056 (by omega) (by omega)
  have w1064 := hw 1064 (by omega) (by omega)
  have w1072 := hw 1072 (by omega) (by omega)
  have w1080 := hw 1080 (by omega) (by omega)
  have w1088 := hw 1088 (by omega) (by omega)
  have w1096 := hw 1096 (by omega) (by omega)
  frame_run [setup, exec_addSp0, exec_mflr, alloc_sp, alloc_gpr, alloc_lr, add_ofNat_zero, w1040, w1048,
    w1056, w1064, w1072, w1080, w1088, w1096]
  have ka : ∀ i, i < 5 → s.mem.readW ((lay s).B + BitVec.ofNat 64 (1216 + 8 * i)) 64 = stackArg s i :=
    fun i hi => by rw [stackArg, arg_slot s i hi]
  have k0 : s.mem.readW ((lay s).B + BitVec.ofNat 64 1216) 64 = (lay s).vlen := ka 0 (by decide)
  have k1 : s.mem.readW ((lay s).B + BitVec.ofNat 64 1224) 64 = (lay s).scr := ka 1 (by decide)
  have k3 : s.mem.readW ((lay s).B + BitVec.ofNat 64 1240) 64 = (lay s).out := ka 3 (by decide)
  have k4 : s.mem.readW ((lay s).B + BitVec.ofNat 64 1248) 64 = (lay s).ol := ka 4 (by decide)
  refine ⟨⟨?_, ?_, rfl, RegUpd.gpr_write_self _ _ _, ?_, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · show s.rd = _
    rw [h.2.2.1, ← lay_args]; rfl
  · show (allocated 112 s).wr = _
    rw [alloc_wr, h.2.2.2.1]; rfl
  · intro r hr hr'
    rw [RegUpd.gpr_write_of_ne _ _ hr']
    dsimp only
    rw [gpr_write_pres hr (by decide), gpr_write_pres hr (by decide)]; rfl
  · constructor <;>
      simp (disch := decide) only [RegUpd.mem_write, alloc_mem, readW_writeW_off, Mem.readW_writeW_self64,
        k0, k1, k3, k4] <;> rfl
  · rw [RegUpd.mem_write]
    dsimp only
    rw [alloc_mem]
    refine Frame.sub (rs := [(lay s).STK]) ?_ fun r hr => ?_
    · repeat refine Frame.writeW ?_ (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
      exact Frame.refl _ _
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, fun _ h => h⟩

end

end VG.Proof.Scrypt.PPC64LE.Whole
