module

public import VerifiedGarbage.Proof.Scrypt.PPC64LE.Whole.Layout
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
public import VerifiedGarbage.Impl.Scrypt.PPC64LE.Scrypt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Whole.PPC64LE.Contract
public import VerifiedGarbage.Proof.Scrypt.PPC64LE.Common
import VerifiedGarbage.Proof.Scrypt.PPC64LE.RoMix
import VerifiedGarbage.Proof.Scrypt.PPC64LE.Lit
import VerifiedGarbage.Proof.Scrypt.Whole
import VerifiedGarbage.Proof.Scrypt.BlockMix
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Scrypt.PPC64LE.Whole.Steps`, which only this module used -/

section

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
  · simp only [Region.Contains]; have := (S.base - R.base).isLt; omega_using [hR]
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [hS]

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
  toNat_le_of_disjoint h.kb.symm (by show (0 : Nat) < 1120; omega_using [])

theorem r_le : L.r.toNat ≤ L.blen.toNat := by
  rw [h.blen_eq]; exact Nat.le_mul_of_pos_right _ h.pp_pos

theorem r_lt : L.r.toNat * 128 < 2 ^ 64 := by have := h.blen_lt; have := h.r_le; omega_arith

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
  omega_using [h₂, h₃]

theorem slen17 : 17 ≤ L.slen.toNat := by have := h.slen; have := h.rpos; omega_arith

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
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega_using [h₂]) (by omega_using [])⟩

theorem inFrW {d : Nat} (h₁ : 1040 ≤ d) (h₂ : d + 8 ≤ 1120) : InRegions t.wr (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega_using [h₂]) (by omega_using [])⟩

theorem inArgs {d : Nat} (h₁ : 1216 ≤ d) (h₂ : d + 8 ≤ 1256) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.ARGS, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega_using [h₂]) (by omega_using [])⟩

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
    exact Offset.disjoint _ (by omega) (by omega) (by omega_using [])
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.STK, by simp, Offset.sub_base _ (by omega_using [])⟩

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
  have l1224 := hc.inArgs (d := 1224) (by omega_using []) (by omega_using [])
  frame_run [pbk1Args, hc.r30', l1224, hc.kept.scr]
  refine ⟨hc.regs rfl rfl rfl rfl (by pres_tac), trivial, ?_⟩
  exact ⟨he.r3, he.r4, he.r5, he.r6, rfl, he.r8, by rw [he.r9, lsl7]; rfl, rfl⟩

theorem cur0_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block cur0) t fun t' => Ctx L g lr m₀ t' ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 1104) 64 = L.b ∧ Frame [curR L] t.mem t'.mem := by
  have l1080 := hc.inFr (d := 1080) (by omega_using []) (by omega_using [])
  have w1104 := hc.inFrW (d := 1104) (by omega_using []) (by omega_using [])
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
  have l1104 := hc.inFr (d := 1104) (by omega_using []) (by omega_using [])
  have l1072 := hc.inFr (d := 1072) (by omega_using []) (by omega_using [])
  have l1096 := hc.inFr (d := 1096) (by omega_using []) (by omega_using [])
  have l1216 := hc.inArgs (d := 1216) (by omega_using []) (by omega_using [])
  have l1224 := hc.inArgs (d := 1224) (by omega_using []) (by omega_using [])
  frame_run [romixArgs, hc.r30', l1104, l1072, l1096, l1216, l1224, hcur, hc.kept.r, hc.kept.v,
    hc.kept.vlen, hc.kept.scr]
  exact ⟨hc.regs rfl rfl rfl rfl (by pres_tac), trivial, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem nextBlock_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {cur : Addr}
    (hcur : t.mem.readW (L.B + BitVec.ofNat 64 1104) 64 = cur) :
    WP isa (.block nextBlock) t fun t' => Ctx L g lr m₀ t' ∧ Frame [curR L] t.mem t'.mem ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 1104) 64 = cur + BitVec.ofNat 64 (L.r.toNat * 128) ∧
      t'.gpr .r5 = L.b + BitVec.ofNat 64 (L.blen.toNat * 128) - (cur + BitVec.ofNat 64 (L.r.toNat * 128)) := by
  have l1104 := hc.inFr (d := 1104) (by omega_using []) (by omega_using [])
  have w1104 := hc.inFrW (d := 1104) (by omega_using []) (by omega_using [])
  have l1072 := hc.inFr (d := 1072) (by omega_using []) (by omega_using [])
  have l1080 := hc.inFr (d := 1080) (by omega_using []) (by omega_using [])
  have l1088 := hc.inFr (d := 1088) (by omega_using []) (by omega_using [])
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
  have l1056 := hc.inFr (d := 1056) (by omega_using []) (by omega_using [])
  have l1064 := hc.inFr (d := 1064) (by omega_using []) (by omega_using [])
  have l1080 := hc.inFr (d := 1080) (by omega_using []) (by omega_using [])
  have l1088 := hc.inFr (d := 1088) (by omega_using []) (by omega_using [])
  have l1224 := hc.inArgs (d := 1224) (by omega_using []) (by omega_using [])
  have l1240 := hc.inArgs (d := 1240) (by omega_using []) (by omega_using [])
  have l1248 := hc.inArgs (d := 1248) (by omega_using []) (by omega_using [])
  frame_run [pbk2Args, hc.r30', l1056, l1064, l1080, l1088, l1224, l1240, l1248, hc.kept.pw, hc.kept.pwl,
    hc.kept.b, hc.kept.blen, hc.kept.scr, hc.kept.out, hc.kept.ol, lsl7]
  exact ⟨hc.regs rfl rfl rfl rfl (by pres_tac), trivial, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The return address back in the link register and our caller's `r30` back. -/
theorem restore_ok {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block restore) t fun t' => t'.lr = lr ∧ t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧
      t'.wr = t.wr ∧ ∀ r ∈ preserved, t'.gpr r = g r := by
  have l1040 := hc.inFr (d := 1040) (by omega_using []) (by omega_using [])
  have l1048 := hc.inFr (d := 1048) (by omega_using []) (by omega_using [])
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
theorem arg_slot (s : State) (i : Nat) (hi : i < 5) :
    stackArgAddr s i = (lay s).B + BitVec.ofNat 64 (1216 + 8 * i) := by
  simp only [stackArgAddr, lay]
  have : 8 * i < 2 ^ 64 := by omega_using [hi]
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
    fun d h₁ h₂ => ⟨(lay s).FR, by rw [alloc_wr]; simp, Offset.contains _ h₁ (by omega_using [h₂]) (by omega_using [])⟩
  have w1040 := hw 1040 (by omega_using []) (by omega_using [])
  have w1048 := hw 1048 (by omega_using []) (by omega_using [])
  have w1056 := hw 1056 (by omega_using []) (by omega_using [])
  have w1064 := hw 1064 (by omega_using []) (by omega_using [])
  have w1072 := hw 1072 (by omega_using []) (by omega_using [])
  have w1080 := hw 1080 (by omega_using []) (by omega_using [])
  have w1088 := hw 1088 (by omega_using []) (by omega_using [])
  have w1096 := hw 1096 (by omega_using []) (by omega_using [])
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
    · repeat refine Frame.writeW ?_ (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega_using []))
      exact Frame.refl _ _
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, fun _ h => h⟩

end

end VG.Proof.Scrypt.PPC64LE.Whole

end

end


/-!
# scrypt on PPC64LE: correctness

As on AArch64 (`Proof/Scrypt/AArch64/Whole/Correct.lean`).
`vg_pbkdf2_hmac_sha256_scratch` (any implementation of it using at most
1008 bytes of stack) is verified against the shared contract
`(Proof.Pbkdf2.Instance.pbkdf2ScratchContract VG.Spec.Hmac.sha256I)`; we call it under that contract
spelt out (`pbkK`, the contract its proof is written against): `pbk_call`.
`romix_call` calls `vg_scrypt_romix`. Step 1 leaves the blocks `X k` of
`PBKDF2-HMAC-SHA256 (P, S, 1, 128 blen)` in `b` (`step1_ok`); the loop
replaces them by their scryptROMix one at a time (`Inv`, `loop_ok`); step 3
derives the key from them (`step3_ok`). `scrypt_ok` puts the frame around it.
-/

@[expose] public section

namespace VG.Proof.Scrypt.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Scrypt.PPC64LE.Whole
open VG.Proof.Pbkdf2.Whole.PPC64LE (pbkG)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt toNat_add_ofNat)
open VG.Spec.Scrypt (bytesAt)

/-! ## PBKDF2-HMAC-SHA256 as a callee -/

/-- `pbkdf2`'s contract, spelt out. -/
abbrev pbkK : Contract isa := pbkG Spec.Hmac.sha256S 1600 1008

theorem pbk_pre {s : State} (h : pbkK.pre s) :
    (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I PPC64LE.abi 1008).pre s := by
  simp only [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch]
  sig_pre [Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre,
    Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256I, Spec.Hmac.sha256S, PPC64LE.abi, PPC64LE.argRegs]
  simp only [pbkK, pbkG, Spec.Hmac.sha256S] at h
  sig_split h
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›
    | omega_arith

theorem pbk_post {s s' : State} (h : (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I PPC64LE.abi 1008).post s s') :
    pbkK.post s s' := by
  simp only [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch] at h
  sig_post [Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre,
    Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256I, Spec.Hmac.sha256S, PPC64LE.abi, PPC64LE.argRegs] at h
  exact h

theorem pbk_pub {s₁ s₂ : State} (h : pbkK.pub s₁ s₂) :
    (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I PPC64LE.abi 1008).pub s₁ s₂ := by
  simp only [Proof.Pbkdf2.Instance.pbkdf2ScratchContract, Spec.Hmac.Instance.pbkdf2Scratch]
  sig_pub [Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig, Spec.Pbkdf2.pbkdf2Pre,
    Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256I, Spec.Hmac.sha256S, PPC64LE.abi, PPC64LE.argRegs]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h9, h1, h2, h3, h4, h5, h6, h7, h8⟩

section
variable {pbk : Prog isa} (hv : Verified PPC64LE.target pbk (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I PPC64LE.abi 1008))
include hv

theorem pbk_correct (s : State) (h : pbkK.pre s) :
    ∃ t s', Exec isa pbk s t s' ∧ abiPreserved s s' ∧ pbkK.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := hv.1 s (pbk_pre h)
  exact ⟨t, s', he, ha, pbk_post hp⟩

theorem pbk_ct : ConstantTime isa pbkK.pre pbkK.pub pbk :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => hv.2.1 _ _ _ _ _ _ (pbk_pre h₁) (pbk_pre h₂) (pbk_pub hp) e₁ e₂

end

/-! ## The calls -/

theorem gpr_ce (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

section
variable {L : Lay} {g : Reg → BitVec 64} {lr : BitVec 64} {m₀ : Mem}

theorem Ctx.ce_sp {t : State} (hc : Ctx L g lr m₀ t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).sp = L.B + BitVec.ofNat 64 1008 := by
  rw [State.withRegions_sp, State.callEntry_sp, hc.sp]

theorem sub1008 (B : Addr) : B + BitVec.ofNat 64 1008 - BitVec.ofNat 64 1008 = B := BitVec.add_sub_cancel _ _

theorem sub48 (B : Addr) : B + BitVec.ofNat 64 1008 - 48 = B + BitVec.ofNat 64 960 := by
  rw [show (48 : BitVec 64) = BitVec.ofNat 64 48 from rfl, Offset.sub_ofNat_eq _ (by decide : 48 ≤ 1008), BitVec.add_sub_cancel]

namespace Lay.Ok

variable (hL : L.Ok)
include hL

/-- The password misses every writable buffer. -/
theorem pw_buf {r : Region} (h : InBuf L r) : L.PW.Disjoint r := by
  obtain ⟨R, hR, hs⟩ := h.sub
  rcases hR with rfl | rfl | rfl | rfl
  exacts [hL.pb.sub_right hs, hL.pv.sub_right hs, hL.pc.sub_right hs, hL.po.sub_right hs]

theorem stk_in {d n : Nat} (h₁ : d + n ≤ 1120) {r : Region} (h : InBuf L r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  obtain ⟨R, hR, hs⟩ := h.sub
  exact hL.stk_buf h₁ hR hs

/-- The 1008 bytes the calls use miss every writable buffer. -/
theorem low_in {r : Region} (h : InBuf L r) : Region.Disjoint ⟨L.B, 1008⟩ r := by
  have := hL.stk_in (d := 0) (n := 1008) (by omega_arith) h
  simpa using this

theorem scr_in : InBuf L ⟨L.scr, 1600⟩ :=
  .inr (.inr (.inl (within_base _ (by have := hL.slen17; omega_arith))))

end Lay.Ok

/-! ### PBKDF2 -/

section
variable {pbk : Prog isa}

/-- The regions a call of PBKDF2 reads and writes. -/
abbrev pbkRd (L : Lay) (salt : Addr) (sl : BitVec 64) : List Region := [L.PW, ⟨salt, sl.toNat⟩]
abbrev pbkWr (L : Lay) (out : Addr) (ol : BitVec 64) : List Region := [⟨out, ol.toNat⟩, ⟨L.scr, 1600⟩]

/-- What a call of PBKDF2 needs of its salt and its output, beyond being in our buffers. -/
structure PbkRegions (L : Lay) (salt : Addr) (sl : BitVec 64) (out : Addr) (ol : BitVec 64) : Prop where
  sw : ∃ R ∈ L.regions, Within ⟨salt, sl.toNat⟩ R
  ow : InBuf L ⟨out, ol.toNat⟩
  so : Region.Disjoint ⟨salt, sl.toNat⟩ ⟨out, ol.toNat⟩
  sc : Region.Disjoint ⟨salt, sl.toNat⟩ ⟨L.scr, 1600⟩
  oc : Region.Disjoint ⟨out, ol.toNat⟩ ⟨L.scr, 1600⟩
  ks : L.STK.Disjoint ⟨salt, sl.toNat⟩
  ns : salt.toNat + sl.toNat ≤ 2 ^ 64
  no : out.toNat + ol.toNat ≤ 2 ^ 64
  ol : ol.toNat ≤ (2 ^ 32 - 1) * 32

theorem pbk_pre' (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {salt : Addr} {sl : BitVec 64} {out : Addr}
    {ol : BitVec 64} (ha : PbkArgs L salt sl out ol t) (hr : PbkRegions L salt sl out ol) :
    pbkK.pre (t.callEntry.withRegions (pbkRd L salt sl) (pbkWr L out ol)) := by
  have hnB := hL.nB
  have t1008 : (L.B + BitVec.ofNat 64 1008).toNat = L.B.toNat + 1008 := toNat_add_ofNat _ (by omega_arith)
  have sw : InBuf L ⟨L.scr, 1600⟩ := hL.scr_in
  have lo : Region.Sub ⟨L.B, 1008⟩ L.STK := by simpa using Offset.sub_base L.B (d := 0) (n := 1008) (k := 1120) (by omega_arith)
  simp only [pbkK, pbkG, below, Spec.Hmac.sha256S, State.withRegions_rd, State.withRegions_wr,
    hc.ce_sp, sub1008, t1008, gpr_ce _ _ _ (by decide : Reg.r3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r6 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r7 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r8 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r9 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r10 ∉ linkRegs), ha.r3, ha.r4, ha.r5, ha.r6, ha.r7, ha.r8, ha.r9, ha.r10]
  exact ⟨trivial, trivial, hL.pw_buf hr.ow, hL.pw_buf sw, hr.so, hr.sc, hr.oc, by omega_arith,
    hL.kp.sub_left lo, hr.ks.sub_left lo, hL.low_in hr.ow, hL.low_in sw, hL.np, hr.ns, hr.no,
    by have := hL.nc; have := hL.slen17; omega_arith, by decide, hr.ol⟩

theorem pbk_sub (hL : L.Ok) {salt : Addr} {sl : BitVec 64} {out : Addr} {ol : BitVec 64}
    (hr : PbkRegions L salt sl out ol) :
    ∀ r ∈ pbkRd L salt sl ++ pbkWr L out ol, ∃ R ∈ L.regions, Within r R := by
  have hs := hr.sw
  simp only [pbkRd, pbkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact ⟨L.PW, by simp, within_base _ (Nat.le_refl _)⟩
  · obtain ⟨R, hR, hw⟩ := hs
    exact ⟨R, by simpa only [Lay.regions, List.mem_cons, List.not_mem_nil, or_false] using hR, hw⟩
  · rcases hr.ow with h | h | h | h
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
  · exact ⟨L.SC, by simp, within_base _ (by have := hL.slen17; omega_arith)⟩

theorem pbk_wsub (hL : L.Ok) {salt : Addr} {sl : BitVec 64} {out : Addr} {ol : BitVec 64}
    (hr : PbkRegions L salt sl out ol) : ∀ r ∈ pbkWr L out ol, InBuf L r := by
  simp only [pbkWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact hr.ow
  · exact hL.scr_in

theorem pbk_call (hv : Verified PPC64LE.target pbk (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I PPC64LE.abi 1008))
    (hd : sdepth pbk ≤ 1008) (name : String) (hL : L.Ok) {t : State}
    (hc : Ctx L g lr m₀ t) {salt : Addr} {sl : BitVec 64} {out : Addr} {ol : BitVec 64}
    (ha : PbkArgs L salt sl out ol t) (hr : PbkRegions L salt sl out ol) :
    WP isa (.call name pbk) t fun t' => Ctx L g lr m₀ t' ∧
      Frame [⟨out, ol.toNat⟩, ⟨L.scr, 1600⟩, ⟨L.B, 1008⟩] t.mem t'.mem ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt t.mem L.pw L.pwl.toNat) (bytesAt t.mem salt sl.toNat) 1
        ol.toNat = some (bytesAt t'.mem out ol.toNat) := by
  refine call_ok hL (pbk_correct hv) hd hc (pbk_pre' hL hc ha hr) (pbk_sub hL hr) (pbk_wsub hL hr)
    fun s' hc' hf _ hpost => ⟨hc', hf, ?_⟩
  have h := hpost
  simp only [pbkK, pbkG, State.withRegions_mem, State.callEntry_mem,
    gpr_ce _ _ _ (by decide : Reg.r3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r4 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r6 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r7 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r8 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r9 ∉ linkRegs), ha.r3, ha.r4, ha.r5, ha.r6, ha.r7, ha.r8,
    ha.r9] at h
  exact h

end

/-! ### ROMix -/

/-- Block `i` of `b`. -/
abbrev blkAt (L : Lay) (i : Nat) : Addr := L.b + BitVec.ofNat 64 (128 * L.r.toNat * i)

/-- The regions a call of ROMix on block `i` writes. -/
abbrev romixWr (L : Lay) (i : Nat) : List Region :=
  [⟨blkAt L i, L.r.toNat * 128⟩, ⟨L.v, L.vlen.toNat * 128⟩, ⟨L.scr, (L.r.toNat + 2) * 128⟩]

theorem blk_le (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + L.r.toNat * 128 ≤ L.blen.toNat * 128 := by
  rw [← hL.len_b, Nat.mul_comm L.r.toNat 128, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi

theorem blk_in (hL : L.Ok) {i : Nat} (hi : i < L.pp) : InBuf L ⟨blkAt L i, L.r.toNat * 128⟩ :=
  .inl (within_off _ (blk_le hL hi))

theorem r2 (hL : L.Ok) : (L.r + BitVec.ofNat 64 2).toNat = L.r.toNat + 2 := by
  have := hL.r_lt
  exact toNat_add_ofNat _ (by omega_arith)

theorem romix_pre (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat} (hi : i < L.pp)
    (ha : RomixArgs L (blkAt L i) t) :
    Proof.Scrypt.roMixPPC64LE.pre (t.callEntry.withRegions [] (romixWr L i)) := by
  have hnB := hL.nB
  have hb := blk_in hL hi
  have hv : InBuf L ⟨L.v, L.vlen.toNat * 128⟩ := .inr (.inl (within_base _ (Nat.le_refl _)))
  have hs : InBuf L ⟨L.scr, (L.r.toNat + 2) * 128⟩ :=
    .inr (.inr (.inl (within_base _ (by have := hL.slen; omega_arith))))
  have tb : (blkAt L i).toNat = L.b.toNat + 128 * L.r.toNat * i := by
    have := blk_le hL hi; have := hL.nb; have := hL.rpos
    exact toNat_add_ofNat _ (by omega_arith)
  have t1008 : (L.B + BitVec.ofNat 64 1008).toNat = L.B.toNat + 1008 := toNat_add_ofNat _ (by omega_arith)
  simp only [Proof.Scrypt.roMixPPC64LE, State.withRegions_rd, State.withRegions_wr, hc.ce_sp, sub48, t1008,
    gpr_ce _ _ _ (by decide : Reg.r3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r4 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r5 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r6 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r7 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r8 ∉ linkRegs),
    ha.r3, ha.r4, ha.r5, ha.r6, ha.r7, ha.r8, r2 hL]
  have kb := Within.sub (within_off L.b (blk_le hL hi))
  have ks := Within.sub (within_base L.scr (n := (L.r.toNat + 2) * 128) (k := L.slen.toNat * 128)
    (by have := hL.slen; omega_arith))
  exact ⟨trivial, trivial, hL.bv.sub_left kb, (hL.bc.sub_left kb).sub_right ks, hL.vc.sub_right ks,
    by omega_arith, hL.stk_in (by omega_arith) hb, hL.stk_in (by omega_arith) hv, hL.stk_in (by omega_arith) hs,
    by rw [tb]; have := blk_le hL hi; have := hL.nb; omega_arith, hL.nv,
    by have := hL.nc; have := hL.slen; omega_arith, hL.rpos, hL.vmod, Whole.valid_pow hL.valid, trivial⟩

theorem romix_sub (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    ∀ r ∈ ([] : List Region) ++ romixWr L i, ∃ R ∈ L.regions, Within r R := by
  simp only [romixWr, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ⟨L.BB, by simp, within_off _ (blk_le hL hi)⟩
  · exact ⟨L.VV, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.SC, by simp, within_base _ (by have := hL.slen; omega_arith)⟩

theorem romix_wsub (hL : L.Ok) {i : Nat} (hi : i < L.pp) : ∀ r ∈ romixWr L i, InBuf L r := by
  simp only [romixWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact blk_in hL hi
  · exact .inr (.inl (within_base _ (Nat.le_refl _)))
  · exact .inr (.inr (.inl (within_base _ (by have := hL.slen; omega_arith))))

theorem roMix_sdepth : sdepth Impl.Scrypt.PPC64LE.roMix ≤ 1008 := by lit_decide

theorem romix_call (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {i : Nat} (hi : i < L.pp)
    (ha : RomixArgs L (blkAt L i) t) :
    WP isa (.call "vg_scrypt_romix" Impl.Scrypt.PPC64LE.roMix) t fun t' => Ctx L g lr m₀ t' ∧
      Frame (romixWr L i ++ [⟨L.B, 1008⟩]) t.mem t'.mem ∧
      bytesAt t'.mem (blkAt L i) (128 * L.r.toNat) =
        Spec.Scrypt.roMix L.r.toNat L.NN (bytesAt t.mem (blkAt L i) (128 * L.r.toNat)) := by
  refine call_ok hL RoMix.roMix_correct roMix_sdepth hc (romix_pre hL hc hi ha)
    (romix_sub hL hi) (romix_wsub hL hi) fun s' hc' hf _ hpost => ⟨hc', hf, ?_⟩
  have h := hpost
  simp only [Proof.Scrypt.roMixPPC64LE, State.withRegions_mem, State.callEntry_mem,
    gpr_ce _ _ _ (by decide : Reg.r3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.r4 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.r6 ∉ linkRegs), ha.r3, ha.r4, ha.r6] at h
  exact h

end

/-! ## The password, the salt and the blocks -/

section
variable {L : Lay} {g : Reg → BitVec 64} {lr : BitVec 64} {m₀ : Mem}

namespace Ctx

variable {t : State} (hc : Ctx L g lr m₀ t) (hL : L.Ok)
include hc hL

theorem pw_bytes : bytesAt t.mem L.pw L.pwl.toNat = bytesAt m₀ L.pw L.pwl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.pb, hL.pv, hL.pc, hL.po, hL.kp.symm]) (by have := hL.np; omega_arith)

theorem salt_bytes : bytesAt t.mem L.salt L.sl.toNat = bytesAt m₀ L.salt L.sl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.sb, hL.sv, hL.sc, hL.so, hL.ks.symm]) (by have := hL.ns; omega_arith)

end Ctx

/-- Block `k` of step 1. -/
def X (L : Lay) (m₀ : Mem) (k : Nat) : List Byte :=
  (Spec.Scrypt.blocks (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) L.r.toNat L.pp).getD k []

/-- The derived key of step 1, from the password and the salt on entry. -/
abbrev Step1 (L : Lay) (m₀ : Mem) (B : List Byte) : Prop :=
  Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) 1
    (L.blen.toNat * 128) = some B

theorem X_of (hL : L.Ok) {m : Mem} (h : Step1 L m₀ (bytesAt m L.b (L.blen.toNat * 128))) {k : Nat}
    (hk : k < L.pp) : X L m₀ k = bytesAt m (blkAt L k) (128 * L.r.toNat) := by
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have h' : Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) 1
      (L.pp * 128 * L.r.toNat) = some (bytesAt m L.b (L.pp * 128 * L.r.toNat)) := by rw [e]; exact h
  have hl : k < (Spec.Scrypt.blocks (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat)
      L.r.toNat L.pp).length := by rw [Whole.blocks_length]; exact hk
  rw [X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some,
    Whole.blocks_getElem h' hl]

/-- Distinct blocks are disjoint. -/
theorem blk_disj (hL : L.Ok) {k i : Nat} (hk : k < L.pp) (hi : i < L.pp) (hne : k ≠ i) :
    Region.Disjoint ⟨blkAt L k, 128 * L.r.toNat⟩ ⟨blkAt L i, L.r.toNat * 128⟩ := by
  have h₁ := blk_le hL hk
  have h₂ := blk_le hL hi
  have := hL.nb
  have hr := hL.rpos
  refine Offset.disjoint _ ?_ (by omega_arith) (by omega_arith)
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · left
    have : 128 * L.r.toNat * k + 128 * L.r.toNat ≤ 128 * L.r.toNat * i := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    omega_arith
  · right
    have : 128 * L.r.toNat * i + 128 * L.r.toNat ≤ 128 * L.r.toNat * k := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    omega_arith

theorem blk_sub (hL : L.Ok) {k : Nat} (hk : k < L.pp) :
    Region.Sub ⟨blkAt L k, 128 * L.r.toNat⟩ L.BB := by
  have := blk_le hL hk
  exact Offset.sub_base _ (by omega_arith)

theorem scr_sub (hL : L.Ok) : Region.Sub ⟨L.scr, 1600⟩ L.SC :=
  Within.sub (within_base _ (by have := hL.slen17; omega_arith))

/-! ## Step 1 -/

section
variable {pbk : Prog isa} (hv : Verified PPC64LE.target pbk (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I PPC64LE.abi 1008))
  (hd : sdepth pbk ≤ 1008) (name : String)
include hv hd

omit hv hd in
theorem pbk1_regions (hL : L.Ok) :
    PbkRegions L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) := by
  have hb := hL.blen_lt
  refine ⟨⟨L.SALT, by simp, within_base _ (Nat.le_refl _)⟩, ?_, ?_, ?_, ?_, hL.ks, hL.ns, ?_, ?_⟩
  · rw [toNat_ofNat_lt hb]; exact .inl (within_base _ (Nat.le_refl _))
  · rw [toNat_ofNat_lt hb]; exact hL.sb
  · exact hL.sc.sub_right (scr_sub hL)
  · rw [toNat_ofNat_lt hb]
    exact hL.bc.sub_right (scr_sub hL)
  · rw [toNat_ofNat_lt hb]; exact hL.nb
  · rw [toNat_ofNat_lt hb]; exact hL.ol1

/-- The call of step 1. -/
theorem pbk1_call_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t)
    (ha : PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t) :
    WP isa (.call name pbk) t fun t' => Ctx L g lr m₀ t' ∧
      Step1 L m₀ (bytesAt t'.mem L.b (L.blen.toNat * 128)) ∧
      ∀ k < L.pp, bytesAt t'.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k := by
  have hb := hL.blen_lt
  refine WP.mono (pbk_call hv hd name hL hc ha (pbk1_regions hL)) fun t₂ ⟨hc₂, _, hp⟩ =>
    ⟨hc₂, ?_, fun k hk => ?_⟩
  · rw [toNat_ofNat_lt hb, hc.pw_bytes hL, hc.salt_bytes hL] at hp
    exact hp
  · rw [toNat_ofNat_lt hb, hc.pw_bytes hL, hc.salt_bytes hL] at hp
    exact (X_of hL hp hk).symm

theorem step1_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) (he : Entry L t) :
    WP isa (pbkCall name pbk pbk1Args) t fun t' => Ctx L g lr m₀ t' ∧
      Step1 L m₀ (bytesAt t'.mem L.b (L.blen.toNat * 128)) ∧
      ∀ k < L.pp, bytesAt t'.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k :=
  WP.seq (WP.mono (pbk1Args_ok hc he) fun _ ⟨hc₁, _, ha₁⟩ => pbk1_call_ok hv hd name hL hc₁ ha₁)

end

/-! ## The loop -/

/-- After `i` iterations of the loop: the next block is `i`, and blocks
`0, …, i - 1` are scryptROMix of those of step 1. -/
structure InvB (L : Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.mem.readW (L.B + BitVec.ofNat 64 1104) 64 = blkAt L i
  blks : ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) =
    if k < i then Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) else X L m₀ k

abbrev Inv (L : Lay) (g : Reg → BitVec 64) (lr : BitVec 64) (m₀ : Mem) (i : Nat) (t : State) : Prop :=
  Ctx L g lr m₀ t ∧ InvB L m₀ i t

/-- In iteration `i`, after the call of ROMix: blocks `0, …, i` are scryptROMix
of those of step 1. -/
structure Mid (L : Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.mem.readW (L.B + BitVec.ofNat 64 1104) 64 = blkAt L i
  blks : ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) =
    if k < i + 1 then Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) else X L m₀ k

theorem blk_le' (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + 128 * L.r.toNat ≤ L.blen.toNat * 128 := by
  have := blk_le hL hi; rw [Nat.mul_comm L.r.toNat 128] at this; exact this

theorem blk0 (L : Lay) : blkAt L 0 = L.b := by
  simp only [blkAt, Nat.mul_zero]; exact BitVec.add_zero _

/-- A block of `b` misses the frame's cur slot. -/
theorem blk_fr (hL : L.Ok) {k : Nat} (hk : k < L.pp) :
    Region.Disjoint ⟨blkAt L k, 128 * L.r.toNat⟩ (curR L) :=
  (hL.kb.symm.sub_left (blk_sub hL hk)).sub_right (Offset.sub_base _ (by omega_arith))

theorem start_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t)
    (hx : ∀ k < L.pp, bytesAt t.mem (blkAt L k) (128 * L.r.toNat) = X L m₀ k) :
    WP isa (.block cur0) t (Inv L g lr m₀ 0) :=
  WP.mono (cur0_ok hL hc) fun t' ⟨hc', hb, hf⟩ => ⟨hc', hb.trans (blk0 L).symm, fun k hk => by
    simp only [Nat.not_lt_zero, ite_false]
    rw [← hx k hk]
    exact Memory.frame_bytesAt hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact blk_fr hL hk)
      (by have := hL.blen_lt; have := blk_le hL hk; omega_arith)⟩

theorem next_eq (L : Lay) (i : Nat) :
    blkAt L i + BitVec.ofNat 64 (L.r.toNat * 128) = blkAt L (i + 1) := by
  simp only [blkAt]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_succ (128 * L.r.toNat) i, Nat.mul_comm L.r.toNat 128]

/-- The bytes of `b` left after block `i`, as the loop's condition reads them. -/
theorem left_eq (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    (L.b + BitVec.ofNat 64 (L.blen.toNat * 128) - blkAt L (i + 1) != 0) = decide (i + 1 ≠ L.pp) := by
  have h₁ := blk_le hL hi
  have hb := hL.blen_lt
  have hr := hL.rpos
  simp only [blkAt]
  rw [Offset.add_sub_add_left, ← hL.len_b]
  have e₁ : 128 * L.r.toNat * (i + 1) < 2 ^ 64 := by
    rw [Nat.mul_succ]; rw [← hL.len_b] at h₁ hb; omega_arith
  have e₂ : 128 * L.r.toNat * L.pp < 2 ^ 64 := by rw [hL.len_b]; exact hb
  rw [bne, Offset.ofNat_sub_ofNat_beq e₂ e₁, decide_not]
  refine congrArg (!·) (decide_eq_decide.mpr ⟨fun h => ?_, fun h => by rw [h]⟩)
  exact (Nat.eq_of_mul_eq_mul_left (by omega_arith) h).symm

theorem call_step (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (hc : Ctx L g lr m₀ t)
    (hb : InvB L m₀ i t) (ha : RomixArgs L (blkAt L i) t) :
    WP isa (.call "vg_scrypt_romix" Impl.Scrypt.PPC64LE.roMix) t fun t' =>
      Ctx L g lr m₀ t' ∧ Mid L m₀ i t' := by
  have hnB := hL.nB
  refine WP.mono (romix_call hL hc hi ha) fun t₂ ⟨hc₂, hf₂, hr₂⟩ => ⟨hc₂, ?_, fun k hk => ?_⟩
  · rw [← hb.cur]
    refine hf₂.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hL.stk_in (by omega_arith) (blk_in hL hi)
    · exact hL.stk_in (by omega_arith) (.inr (.inl (within_base _ (Nat.le_refl _))))
    · exact hL.stk_in (by omega_arith) (.inr (.inr (.inl (within_base _ (by have := hL.slen; omega_arith)))))
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  · by_cases hki : k = i
    · subst hki
      rw [hr₂, hb.blks k hk]
      simp only [Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
    · have e₂ : bytesAt t₂.mem (blkAt L k) (128 * L.r.toNat) = bytesAt t.mem (blkAt L k) (128 * L.r.toNat) :=
        Memory.frame_bytesAt hf₂ (fun r hr => by
          simp only [romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact blk_disj hL hk hi hki
          · exact hL.bv.sub_left (blk_sub hL hk)
          · exact (hL.bc.sub_left (blk_sub hL hk)).sub_right
              (Within.sub (within_base _ (by have := hL.slen; omega_arith)))
          · exact (hL.kb.symm.sub_left (blk_sub hL hk)).sub_right (Region.sub_prefix (by omega_arith)))
          (by have := hL.blen_lt; have := blk_le hL hk; omega_arith)
      rw [e₂, hb.blks k hk]
      by_cases hlt : k < i
      · have : k < i + 1 := by omega_arith
        simp only [hlt, this, ite_true]
      · have : ¬ k < i + 1 := by omega_arith
        simp only [hlt, this, ite_false]

theorem next_step (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (hc : Ctx L g lr m₀ t)
    (hm : Mid L m₀ i t) :
    WP isa (.block nextBlock) t fun t' => Ctx L g lr m₀ t' ∧ InvB L m₀ (i + 1) t' ∧
      (t'.gpr .r5 != 0) = decide (i + 1 ≠ L.pp) :=
  WP.mono (nextBlock_ok hL hc hm.cur) fun t₃ ⟨hc₃, hf₃, hb₃, hx₃⟩ =>
    ⟨hc₃, ⟨by rw [hb₃, next_eq], fun k hk => by
      rw [← hm.blks k hk]
      exact Memory.frame_bytesAt hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact blk_fr hL hk)
        (by have := hL.blen_lt; have := blk_le hL hk; omega_arith)⟩,
      by rw [hx₃, next_eq, left_eq hL hi]⟩

theorem body_ok (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (h : Inv L g lr m₀ i t) :
    WP isa (.seq (.block romixArgs) (.seq (.call "vg_scrypt_romix" Impl.Scrypt.PPC64LE.roMix)
      (.block nextBlock))) t fun t' =>
        Inv L g lr m₀ (i + 1) t' ∧ (t'.gpr .r5 != 0) = decide (i + 1 ≠ L.pp) :=
  WP.seq (WP.mono (romixArgs_ok h.1 h.2.cur) fun t₁ ⟨hc₁, hm₁, ha₁⟩ =>
    WP.seq (WP.mono (call_step hL hi hc₁ ⟨by rw [hm₁]; exact h.2.cur, by rw [hm₁]; exact h.2.blks⟩ ha₁)
      fun t₂ ⟨hc₂, hm₂⟩ => WP.mono (next_step hL hi hc₂ hm₂) fun _ ⟨hc₃, hb₃, hz₃⟩ => ⟨⟨hc₃, hb₃⟩, hz₃⟩))

theorem loop_ok (hL : L.Ok) {t : State} (h : Inv L g lr m₀ 0 t) :
    WP isa romixLoop t (Inv L g lr m₀ L.pp) :=
  RoMix.count_loop hL.pp_pos (Inv L g lr m₀) (fun _ hi _ h => body_ok hL hi h) h

/-! ## Step 3 -/

section
variable {pbk : Prog isa} (hv : Verified PPC64LE.target pbk (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I PPC64LE.abi 1008))
  (hd : sdepth pbk ≤ 1008) (name : String)
include hv hd

omit hv hd in
/-- The blocks after the loop, as one string. -/
theorem final_bytes' (hL : L.Ok) {t : State} (h : Inv L g lr m₀ L.pp t) :
    bytesAt t.mem L.b (L.blen.toNat * 128) =
      (List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) := by
  rw [← hL.len_b, Whole.bytesAt_chunks]
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [h.2.blks k hk]; simp only [hk, ite_true]

omit hv hd in
theorem pbk2_regions (hL : L.Ok) :
    PbkRegions L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol := by
  have hb := hL.blen_lt
  refine ⟨⟨L.BB, by simp, ?_⟩, .inr (.inr (.inr (within_base _ (Nat.le_refl _)))), ?_,
    ?_, hL.co.symm.sub_right (scr_sub hL), ?_, ?_, hL.no, hL.olb⟩
  · rw [toNat_ofNat_lt hb]; exact within_base _ (Nat.le_refl _)
  · rw [toNat_ofNat_lt hb]; exact hL.bo
  · rw [toNat_ofNat_lt hb]; exact hL.bc.sub_right (scr_sub hL)
  · rw [toNat_ofNat_lt hb]; exact hL.kb
  · rw [toNat_ofNat_lt hb]; exact hL.nb

theorem step3_ok (hL : L.Ok) {t : State} (h : Inv L g lr m₀ L.pp t) :
    WP isa (pbkCall name pbk pbk2Args) t fun t' => Ctx L g lr m₀ t' ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ L.pw L.pwl.toNat)
        ((List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k)) 1 L.ol.toNat =
        some (bytesAt t'.mem L.out L.ol.toNat) := by
  have hb := hL.blen_lt
  refine WP.seq (WP.mono (pbk2Args_ok h.1) fun t₁ ⟨hc₁, hm₁, ha₁⟩ => ?_)
  refine WP.mono (pbk_call hv hd name hL hc₁ ha₁ (pbk2_regions hL)) fun t₂ ⟨hc₂, _, hp⟩ => ⟨hc₂, ?_⟩
  rw [toNat_ofNat_lt hb, hc₁.pw_bytes hL, hm₁, final_bytes' hL h] at hp
  exact hp

/-- The frame's body after `setup` and before `restore`. -/
theorem rest_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) (he : Entry L t) {Q : State → Prop}
    (hQ : ∀ t', Ctx L g lr m₀ t' →
      Spec.Scrypt.scrypt (bytesAt m₀ L.pw L.pwl.toNat) (bytesAt m₀ L.salt L.sl.toNat) L.NN L.r.toNat L.pp
        L.ol.toNat = some (bytesAt t'.mem L.out L.ol.toNat) → WP isa (.block restore) t' Q) :
    WP isa (.seq (pbkCall name pbk pbk1Args) (.seq (.block cur0) (.seq romixLoop
      (.seq (pbkCall name pbk pbk2Args) (.block restore))))) t Q := by
  refine WP.seq (WP.mono (step1_ok hv hd name hL hc he) fun t₁ ⟨hc₁, h1, hx⟩ => ?_)
  refine WP.seq (WP.mono (start_ok hL hc₁ hx) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (loop_ok hL h₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (step3_ok hv hd name hL h₃) fun t₄ ⟨hc₄, hp⟩ => hQ t₄ hc₄ ?_)
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  refine Whole.scrypt_eq hL.valid (B := bytesAt t₁.mem L.b (L.blen.toNat * 128)) (by rw [e]; exact h1) ?_
  refine Eq.trans (congrArg (fun x => Spec.Pbkdf2.pbkdf2HmacSha256 _ x 1 _) ?_) hp
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [X_of hL h1 hk, Whole.chunk_bytesAt _ _ (blk_le' hL hk)]

end

end

/-! ## The whole function -/

section
variable {pbk : Prog isa} (hv : Verified PPC64LE.target pbk (Proof.Pbkdf2.Instance.pbkdf2ScratchContract Spec.Hmac.sha256I PPC64LE.abi 1008))
  (hd : sdepth pbk ≤ 1008) (name : String)
include hv hd

/-- `vg_scrypt` meets `scryptPPC` and the calling convention. -/
theorem scrypt_ok {s : State} (h : scryptPPC.pre s) :
    WP isa (scrypt name pbk) s fun s' => abiPreserved s s' ∧ scryptPPC.post s s' := by
  have hL := lay_ok h
  have h1120 : 1120 ≤ s.sp.toNat := h.1
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by simp only [locals]; omega_arith) ?_
  refine WP.seq (WP.mono (entry_ok h) fun t ⟨hc, he⟩ => ?_)
  refine rest_ok hv hd name hL hc he fun u hu ho => WP.mono (restore_ok hu) fun v ⟨vlr, vm, vsp, _, _, vg⟩ => ?_
  refine ⟨⟨fun r hr => vg r hr, ?_, vlr⟩, ?_⟩
  · show v.sp + BitVec.ofNat 64 112 = s.sp
    rw [vsp, hu.sp, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact lay_top s
  · show _ = some (bytesAt v.mem _ _)
    rw [vm]
    exact ho

end

end VG.Proof.Scrypt.PPC64LE.Whole
