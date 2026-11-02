module

public import VerifiedGarbage.Proof.Scrypt.RISCV64.Whole.Layout
public import VerifiedGarbage.Impl.Scrypt.RISCV64.Scrypt
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Scrypt.RISCV64.Whole.Layout
meta import VerifiedGarbage.Impl.Scrypt.RISCV64.Scrypt

/-!
# scrypt on RISC-V: the blocks between the calls

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/Scrypt/PPC64LE/Whole/Steps.lean`): the facts about the parameters the
proof uses; reading and writing the frame in `Ctx` (`fld_wp`, `fsd_wp`,
through `s3`); and each block between the calls (`setup` from the frame's
`alloc`, the moves of the calls' arguments, the next block, `restore`),
keeping `Ctx` and giving the calls' arguments (`PbkArgs`, `RomixArgs`) or
the next block.
-/

@[expose] public section

namespace VG.Proof.Scrypt.RISCV64.Whole

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Scrypt.RISCV64.Whole
open VG.Impl.Scrypt.RISCV64 (mov)

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
  toNat_le_of_disjoint h.kb.symm (by show (0 : Nat) < 1248; omega)

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

/-- The address of a doubleword of the frame (`s3 = B + 992`). -/
theorem fr_addr (B : Addr) (d : Nat) :
    B + BitVec.ofNat 64 992 + BitVec.ofNat 64 d = B + BitVec.ofNat 64 (992 + d) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- Reading a doubleword past a write of another. -/
theorem readW_writeW_off (B : Addr) (m : Mem) {x y : Nat} (v : BitVec 64) (h : x + 8 ≤ y ∨ y + 8 ≤ x)
    (hx : x + 8 ≤ 2 ^ 64) (hy : y + 8 ≤ 2 ^ 64) :
    (m.writeW (B + BitVec.ofNat 64 y) v).readW (B + BitVec.ofNat 64 x) 64 = m.readW (B + BitVec.ofNat 64 x) 64 :=
  Mem.readW_writeW_sep (Offset.sep B h hx hy) (by decide)

/-- The frame's cur slot. -/
abbrev curR (L : Lay) : Region := ⟨L.B + BitVec.ofNat 64 1056, 8⟩

namespace Ctx

variable {L : Lay} {g : Reg → BitVec 64} {m₀ : Mem} {t t' : State}
  (hc : Ctx L g m₀ t)
include hc

theorem s3' : t.gpr .s3 = L.B + BitVec.ofNat 64 992 := hc.s3

/-- Code that writes only registers other than the callee-saved ones. -/
theorem regs (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp) (hm : t'.mem = t.mem)
    (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) : Ctx L g m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, (hg _ (by decide)).trans hc.s3,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hm]; exact hc.kept, by rw [hm]; exact hc.frame⟩

/-- A write of a register other than the callee-saved ones. -/
theorem upd {d : Reg} {v : BitVec 64} (u : Upd t t' d v) (hd : d ∉ preserved) : Ctx L g m₀ t' :=
  hc.regs u.rd u.wr u.sp u.mem fun r hr => u.other r fun e => hd (e ▸ hr)

/-- Code that also writes the frame's cur slot. -/
theorem store (hL : L.Ok) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hg : ∀ r ∈ preserved, t'.gpr r = t.gpr r) (hf : Frame [curR L] t.mem t'.mem) : Ctx L g m₀ t' := by
  have hnB := hL.nB
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, (hg _ (by decide)).trans hc.s3,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), hc.kept.frame hf fun d hd R hR => ?_,
    hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  · simp only [List.mem_singleton] at hR; subst hR
    exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.STK, by simp, Offset.sub_base _ (by omega)⟩

end Ctx

section
variable {L : Lay} {g : Reg → BitVec 64} {m₀ : Mem}

/-- A doubleword of the frame or of our stack arguments is aligned. -/
theorem fr_al (hL : L.Ok) {d : Nat} (hd : d % 8 = 0) :
    (L.B + BitVec.ofNat 64 (992 + d)).toNat % 8 = 0 :=
  Spill.al8 (by have := hL.aB; omega) (by omega)

/-- `ld r, d(s3)`, of the frame or of our stack arguments. -/
theorem fld_wp (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {r : Reg} {d : Nat} (o : Nat)
    (hd : d + 8 ≤ 296) (h8 : d % 8 = 0) (ho : 992 + d = o) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd t s' r (t.mem.readW (L.B + BitVec.ofNat 64 o) 64) → WP isa (.block is) s' Q) :
    WP isa (.block (fld r d :: is)) t Q := by
  subst ho
  have hnB := hL.nB
  refine wp_ld (by omega) (by rw [hc.s3', fr_addr]) (fr_al hL h8) ?_ k
  rw [hc.rd, hc.wr]
  by_cases h256 : d + 8 ≤ 256
  · exact ⟨L.FR, by simp, Offset.contains _ (by omega) (by omega) (by omega)⟩
  · exact ⟨L.ARGS, by simp, Offset.contains _ (by omega) (by omega) (by omega)⟩

/-- `sd r, d(s3)`, of the frame. -/
theorem fsd_wp (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {r : Reg} {d : Nat} (o : Nat)
    (hd : d + 8 ≤ 256) (h8 : d % 8 = 0) (ho : 992 + d = o) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Mupd t s' (t.mem.writeW (L.B + BitVec.ofNat 64 o) (t.gpr r)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.store .d r .s3 d :: is)) t Q := by
  subst ho
  have hnB := hL.nB
  refine wp_sd (by omega) (by rw [hc.s3', fr_addr]) (fr_al hL h8) ?_ k
  rw [hc.wr]
  exact ⟨L.FR, by simp, Offset.contains _ (by omega) (by omega) (by omega)⟩

/-- The arguments of a call of PBKDF2 with the salt `salt` (`sl` bytes) and
the output `out` (`ol` bytes): the password and `c = 1`. -/
structure PbkArgs (L : Lay) (salt : Addr) (sl : BitVec 64) (out : Addr) (ol : BitVec 64) (t : State) :
    Prop where
  a0 : t.gpr .a0 = L.pw
  a1 : t.gpr .a1 = L.pwl
  a2 : t.gpr .a2 = salt
  a3 : t.gpr .a3 = sl
  a4 : t.gpr .a4 = 1
  a5 : t.gpr .a5 = out
  a6 : t.gpr .a6 = ol

/-- The registers on entry to the frame's body, once our arguments are saved. -/
structure Entry (L : Lay) (t : State) : Prop where
  a0 : t.gpr .a0 = L.pw
  a1 : t.gpr .a1 = L.pwl
  a2 : t.gpr .a2 = L.salt
  a3 : t.gpr .a3 = L.sl
  a5 : t.gpr .a5 = L.b
  a6 : t.gpr .a6 = L.blen

theorem pbk1Args_ok {t : State} (hc : Ctx L g m₀ t) (he : Entry L t) :
    WP isa (.block pbk1Args) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t' := by
  unfold pbk1Args
  refine wp_li (imm := 1) (by decide) fun a ua => wp_sll (by decide) fun b ub => WP.block_nil ?_
  refine ⟨(hc.upd ua (by decide)).upd ub (by decide), by rw [ub.mem, ua.mem], ?_⟩
  exact ⟨by rw [ub.other _ (by decide), ua.other _ (by decide), he.a0],
    by rw [ub.other _ (by decide), ua.other _ (by decide), he.a1],
    by rw [ub.other _ (by decide), ua.other _ (by decide), he.a2],
    by rw [ub.other _ (by decide), ua.other _ (by decide), he.a3],
    by rw [ub.other _ (by decide), ua.gpr]; rfl,
    by rw [ub.other _ (by decide), ua.other _ (by decide), he.a5],
    by rw [ub.gpr, ua.other _ (by decide), he.a6, lsl7]⟩

theorem cur0_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block cur0) t fun t' => Ctx L g m₀ t' ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 1056) 64 = L.b ∧ Frame [curR L] t.mem t'.mem := by
  have hnB := hL.nB
  unfold cur0
  refine fld_wp hL hc (d := bOff) 1032 (by decide) (by decide) (by decide) fun a ua => ?_
  have ha := hc.upd ua (by decide)
  refine fsd_wp hL ha (d := curOff) 1056 (by decide) (by decide) (by decide) fun b ub => WP.block_nil ?_
  have e : a.gpr .a0 = L.b := by rw [ua.gpr]; exact hc.kept.b
  have f : Frame [curR L] t.mem b.mem := by
    rw [ub.mem, ua.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.store hL (by rw [ub.rd, ua.rd]) (by rw [ub.wr, ua.wr]) (by rw [ub.sp, ua.sp])
    (fun r hr => by rw [ub.gpr, ua.other _ fun e => by subst e; revert hr; decide]) f, ?_, f⟩
  rw [ub.mem, e]
  exact Mem.readW_writeW_self64 _ _ _

/-- The low three bits of the pointers ROMix accesses by doublewords. -/
abbrev alBits (L : Lay) : BitVec 64 := (L.b ||| L.v ||| L.scr) &&& BitVec.ofInt 64 7

theorem alignBits_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block alignBits) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .t0 = alBits L := by
  unfold alignBits
  refine fld_wp hL hc (d := bOff) 1032 (by decide) (by decide) (by decide) fun a ua => ?_
  have ha := hc.upd ua (by decide)
  refine fld_wp hL ha (d := vOff) 1048 (by decide) (by decide) (by decide) fun b ub => ?_
  have hb := ha.upd ub (by decide)
  refine wp_or fun c uc => ?_
  have hc' := hb.upd uc (by decide)
  refine fld_wp hL hc' (d := argOff scratchArg) 1256 (by decide) (by decide) (by decide) fun d ud => ?_
  have hd := hc'.upd ud (by decide)
  refine wp_or fun e ue => ?_
  have he := hd.upd ue (by decide)
  refine wp_andi (by decide) fun f uf => WP.block_nil ?_
  refine ⟨he.upd uf (by decide), by rw [uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem], ?_⟩
  have e0 : a.gpr .t0 = L.b := by rw [ua.gpr]; exact hc.kept.b
  have e1 : b.gpr .t1 = L.v := by rw [ub.gpr, ua.mem]; exact hc.kept.v
  have e2 : b.gpr .t0 = L.b := by rw [ub.other _ (by decide), e0]
  have e3 : c.gpr .t0 = L.b ||| L.v := by rw [uc.gpr, e2, e1]
  have e4 : d.gpr .t1 = L.scr := by rw [ud.gpr, uc.mem, ub.mem, ua.mem]; exact hc.kept.scr
  have e5 : d.gpr .t0 = L.b ||| L.v := by rw [ud.other _ (by decide), e3]
  have e6 : e.gpr .t0 = L.b ||| L.v ||| L.scr := by rw [ue.gpr, e5, e4]
  rw [uf.gpr, e6]

/-- The arguments of a call of ROMix on the block at `cur`. -/
structure RomixArgs (L : Lay) (cur : Addr) (t : State) : Prop where
  a0 : t.gpr .a0 = cur
  a1 : t.gpr .a1 = L.r
  a2 : t.gpr .a2 = L.v
  a3 : t.gpr .a3 = L.vlen
  a4 : t.gpr .a4 = L.scr
  a5 : t.gpr .a5 = L.B + BitVec.ofNat 64 1072

theorem romixArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {cur : Addr}
    (hcur : t.mem.readW (L.B + BitVec.ofNat 64 1056) 64 = cur) :
    WP isa (.block romixArgs) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ RomixArgs L cur t' := by
  unfold romixArgs
  refine fld_wp hL hc (d := curOff) 1056 (by decide) (by decide) (by decide) fun a ua => ?_
  have ha := hc.upd ua (by decide)
  refine fld_wp hL ha (d := rOff) 1024 (by decide) (by decide) (by decide) fun b ub => ?_
  have hb := ha.upd ub (by decide)
  refine fld_wp hL hb (d := vOff) 1048 (by decide) (by decide) (by decide) fun c uc => ?_
  have hc' := hb.upd uc (by decide)
  refine fld_wp hL hc' (d := argOff vlenArg) 1248 (by decide) (by decide) (by decide) fun d ud => ?_
  have hd := hc'.upd ud (by decide)
  refine fld_wp hL hd (d := argOff scratchArg) 1256 (by decide) (by decide) (by decide) fun e ue => ?_
  have he := hd.upd ue (by decide)
  refine wp_addi (by decide) fun f uf => WP.block_nil ?_
  have me : e.mem = t.mem := by rw [ue.mem, ud.mem, uc.mem, ub.mem, ua.mem]
  refine ⟨he.upd uf (by decide), by rw [uf.mem, me], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.gpr, hcur]
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
      ub.gpr, ua.mem]; exact hc.kept.r
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), uc.gpr, ub.mem, ua.mem]
    exact hc.kept.v
  · rw [uf.other _ (by decide), ue.other _ (by decide), ud.gpr, uc.mem, ub.mem, ua.mem]
    exact hc.kept.vlen
  · rw [uf.other _ (by decide), ue.gpr, ud.mem, uc.mem, ub.mem, ua.mem]
    exact hc.kept.scr
  · rw [uf.gpr, he.s3', fr_addr]; rfl

theorem nextBlock_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {cur : Addr}
    (hcur : t.mem.readW (L.B + BitVec.ofNat 64 1056) 64 = cur) :
    WP isa (.block nextBlock) t fun t' => Ctx L g m₀ t' ∧ Frame [curR L] t.mem t'.mem ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 1056) 64 = cur + BitVec.ofNat 64 (L.r.toNat * 128) ∧
      t'.gpr .t0 = L.b + BitVec.ofNat 64 (L.blen.toNat * 128) -
        (cur + BitVec.ofNat 64 (L.r.toNat * 128)) := by
  have hnB := hL.nB
  unfold nextBlock
  refine fld_wp hL hc (d := curOff) 1056 (by decide) (by decide) (by decide) fun a ua => ?_
  have ha := hc.upd ua (by decide)
  refine fld_wp hL ha (d := rOff) 1024 (by decide) (by decide) (by decide) fun b ub => ?_
  have hb := ha.upd ub (by decide)
  refine wp_sll (by decide) fun c uc => ?_
  have hc' := hb.upd uc (by decide)
  refine wp_add fun d ud => ?_
  have hd := hc'.upd ud (by decide)
  have e0 : d.gpr .a0 = cur + BitVec.ofNat 64 (L.r.toNat * 128) := by
    rw [ud.gpr, uc.other _ (by decide), ub.other _ (by decide), ua.gpr, hcur, uc.gpr, ub.gpr, ua.mem,
      hc.kept.r, lsl7]
  have md : d.mem = t.mem := by rw [ud.mem, uc.mem, ub.mem, ua.mem]
  refine fsd_wp hL hd (d := curOff) 1056 (by decide) (by decide) (by decide) fun e ue => ?_
  have f : Frame [curR L] t.mem e.mem := by
    rw [ue.mem, md]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have he : Ctx L g m₀ e := hd.store hL ue.rd ue.wr ue.sp (fun r _ => by rw [ue.gpr]) (by rw [md]; exact f)
  refine fld_wp hL he (d := bOff) 1032 (by decide) (by decide) (by decide) fun h uh => ?_
  have hh := he.upd uh (by decide)
  refine fld_wp hL hh (d := blenOff) 1040 (by decide) (by decide) (by decide) fun i ui => ?_
  have hi := hh.upd ui (by decide)
  refine wp_sll (by decide) fun j uj => ?_
  have hj := hi.upd uj (by decide)
  refine wp_add fun k uk => ?_
  have hk := hj.upd uk (by decide)
  refine wp_sub fun l ul => WP.block_nil ?_
  have me : e.mem = t.mem.writeW (L.B + BitVec.ofNat 64 1056) (cur + BitVec.ofNat 64 (L.r.toNat * 128)) := by
    rw [ue.mem, md, e0]
  have ml : l.mem = e.mem := by rw [ul.mem, uk.mem, uj.mem, ui.mem, uh.mem]
  have eb : e.mem.readW (L.B + BitVec.ofNat 64 1032) 64 = L.b := by
    rw [me, readW_writeW_off (x := 1032) (y := 1056) _ _ _ (by decide) (by decide) (by decide)]
    exact hc.kept.b
  have ebl : e.mem.readW (L.B + BitVec.ofNat 64 1040) 64 = L.blen := by
    rw [me, readW_writeW_off (x := 1040) (y := 1056) _ _ _ (by decide) (by decide) (by decide)]
    exact hc.kept.blen
  refine ⟨hk.upd ul (by decide), by rw [ml]; exact f, by rw [ml, me]; exact Mem.readW_writeW_self64 _ _ _, ?_⟩
  have k0 : k.gpr .a0 = cur + BitVec.ofNat 64 (L.r.toNat * 128) := by
    rw [uk.other _ (by decide), uj.other _ (by decide), ui.other _ (by decide), uh.other _ (by decide),
      ue.gpr, e0]
  have i0 : i.gpr .t0 = L.b := by
    rw [ui.other _ (by decide), uh.gpr]; exact eb
  have j1 : j.gpr .t1 = BitVec.ofNat 64 (L.blen.toNat * 128) := by
    rw [uj.gpr, ui.gpr, uh.mem, ← lsl7]; exact congrArg (fun x : BitVec 64 => x <<< (7 : Nat)) ebl
  have k1 : k.gpr .t0 = L.b + BitVec.ofNat 64 (L.blen.toNat * 128) := by
    rw [uk.gpr, uj.other _ (by decide), i0, j1]
  rw [ul.gpr, k1, k0]

theorem pbk2Args_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block pbk2Args) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      PbkArgs L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol t' := by
  unfold pbk2Args
  refine fld_wp hL hc (d := pwOff) 1008 (by decide) (by decide) (by decide) fun a ua => ?_
  have ha := hc.upd ua (by decide)
  refine fld_wp hL ha (d := pwlOff) 1016 (by decide) (by decide) (by decide) fun b ub => ?_
  have hb := ha.upd ub (by decide)
  refine fld_wp hL hb (d := bOff) 1032 (by decide) (by decide) (by decide) fun c uc => ?_
  have hc' := hb.upd uc (by decide)
  refine fld_wp hL hc' (d := blenOff) 1040 (by decide) (by decide) (by decide) fun d ud => ?_
  have hd := hc'.upd ud (by decide)
  refine wp_sll (by decide) fun e ue => ?_
  have he := hd.upd ue (by decide)
  refine wp_li (imm := 1) (by decide) fun f uf => ?_
  have hf := he.upd uf (by decide)
  refine fld_wp hL hf (d := argOff outArg) 1272 (by decide) (by decide) (by decide) fun h uh => ?_
  have hh := hf.upd uh (by decide)
  refine fld_wp hL hh (d := argOff outLenArg) 1280 (by decide) (by decide) (by decide) fun i ui => WP.block_nil ?_
  have mh : h.mem = t.mem := by rw [uh.mem, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem]
  refine ⟨hh.upd ui (by decide), by rw [ui.mem, mh], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ui.other _ (by decide), uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide), ua.gpr]
    exact hc.kept.pw
  · rw [ui.other _ (by decide), uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.other _ (by decide), ub.gpr, ua.mem]
    exact hc.kept.pwl
  · rw [ui.other _ (by decide), uh.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.gpr, ub.mem, ua.mem]
    exact hc.kept.b
  · rw [ui.other _ (by decide), uh.other _ (by decide), uf.other _ (by decide), ue.gpr, ud.gpr, uc.mem,
      ub.mem, ua.mem, hc.kept.blen, lsl7]
  · rw [ui.other _ (by decide), uh.other _ (by decide), uf.gpr]; rfl
  · rw [ui.other _ (by decide), uh.gpr, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem]
    exact hc.kept.out
  · rw [ui.gpr, uh.mem, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem]
    exact hc.kept.ol

/-- The return address and our caller's `s3` back. -/
theorem restore_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block restore) t fun t' => t'.gpr .ra = g .ra ∧ t'.mem = t.mem ∧ t'.sp = t.sp ∧
      t'.rd = t.rd ∧ t'.wr = t.wr ∧ ∀ r ∈ preserved, t'.gpr r = g r := by
  unfold restore
  refine fld_wp hL hc (d := raOff) 992 (by decide) (by decide) (by decide) fun a ua => ?_
  have ha := hc.upd ua (by decide)
  refine fld_wp hL ha (d := s3Off) 1000 (by decide) (by decide) (by decide) fun b ub => WP.block_nil ?_
  refine ⟨by rw [ub.other _ (by decide), ua.gpr]; exact hc.kept.ra, by rw [ub.mem, ua.mem],
    by rw [ub.sp, ua.sp], by rw [ub.rd, ua.rd], by rw [ub.wr, ua.wr], fun r hr => ?_⟩
  by_cases e : r = .s3
  · subst e; rw [ub.gpr, ua.mem]; exact hc.kept.s3
  · rw [ub.other _ e, ua.other _ fun e' => by subst e'; revert hr; decide]
    exact hc.cs r hr e

end

/-! ## Entry -/

/-- `sd r, d(t0)` into the frame, before `s3` is set. -/
theorem esd {L : Lay} (hL : L.Ok) {t : State} {rest : List Region} (h0 : t.gpr .t0 = L.B + BitVec.ofNat 64 992)
    (hw : t.wr = L.FR :: rest) {r : Reg} {d : Nat} (o : Nat) (hd : d + 8 ≤ 256) (h8 : d % 8 = 0)
    (ho : 992 + d = o) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Mupd t s' (t.mem.writeW (L.B + BitVec.ofNat 64 o) (t.gpr r)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d r .t0 d :: is)) t Q := by
  subst ho
  have hnB := hL.nB
  refine wp_sd (by omega) (by rw [h0, fr_addr]) (fr_al hL h8) ?_ k
  rw [hw]
  exact ⟨L.FR, by simp, Offset.contains _ (by omega) (by omega) (by omega)⟩

theorem arg_addr (s : State) (i : Nat) :
    (lay s).B + BitVec.ofNat 64 (1248 + 8 * i) = stackArgAddr s i := by
  show _ = s.sp + _
  rw [← lay_top s, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem entry_ok {s : State} (h : scryptRV.pre s) :
    WP isa (.block setup) (allocd 256 s) fun t => Ctx (lay s) s.gpr s.mem t ∧ Entry (lay s) t := by
  have hL := lay_ok h
  have hnB := hL.nB
  have hsp : (allocd 256 s).sp = (lay s).B + BitVec.ofNat 64 992 :=
    Offset.sub_ofNat_eq s.sp (by decide : 256 ≤ 1248)
  have hw : (allocd 256 s).wr = (lay s).FR :: s.wr := by
    rw [show (allocd 256 s).wr = ⟨(allocd 256 s).sp, 256⟩ :: s.wr from rfl, hsp]
  unfold setup
  refine wp_addSp (by decide) fun a ua => ?_
  have a0 : a.gpr .t0 = (lay s).B + BitVec.ofNat 64 992 := by
    rw [ua.gpr, hsp]; exact BitVec.add_zero _
  have aw : a.wr = (lay s).FR :: s.wr := ua.wr.trans hw
  have ga : ∀ r, r ≠ .t0 → a.gpr r = s.gpr r := fun r hr => ua.other r hr
  refine esd hL a0 aw (d := raOff) 992 (by decide) (by decide) (by decide) fun b ub => ?_
  refine esd hL (by rw [ub.gpr]; exact a0) (ub.wr.trans aw) (d := s3Off) 1000 (by decide) (by decide)
    (by decide) fun c uc => ?_
  have cg : c.gpr = a.gpr := uc.gpr.trans ub.gpr
  have cw : c.wr = (lay s).FR :: s.wr := uc.wr.trans (ub.wr.trans aw)
  refine esd hL (by rw [cg]; exact a0) cw (d := pwOff) 1008 (by decide) (by decide) (by decide) fun d ud => ?_
  refine esd hL (by rw [ud.gpr, cg]; exact a0) (ud.wr.trans cw) (d := pwlOff) 1016 (by decide) (by decide)
    (by decide) fun e ue => ?_
  have eg : e.gpr = a.gpr := ue.gpr.trans (ud.gpr.trans cg)
  have ew : e.wr = (lay s).FR :: s.wr := ue.wr.trans (ud.wr.trans cw)
  refine esd hL (by rw [eg]; exact a0) ew (d := rOff) 1024 (by decide) (by decide) (by decide) fun f uf => ?_
  refine esd hL (by rw [uf.gpr, eg]; exact a0) (uf.wr.trans ew) (d := bOff) 1032 (by decide) (by decide)
    (by decide) fun i ui => ?_
  have ig : i.gpr = a.gpr := ui.gpr.trans (uf.gpr.trans eg)
  have iw : i.wr = (lay s).FR :: s.wr := ui.wr.trans (uf.wr.trans ew)
  refine esd hL (by rw [ig]; exact a0) iw (d := blenOff) 1040 (by decide) (by decide) (by decide) fun j uj => ?_
  refine esd hL (by rw [uj.gpr, ig]; exact a0) (uj.wr.trans iw) (d := vOff) 1048 (by decide) (by decide)
    (by decide) fun k uk => ?_
  have kg : k.gpr = a.gpr := uk.gpr.trans (uj.gpr.trans ig)
  refine wp_mv fun l ul => WP.block_nil ?_
  have hl : ∀ r, r ≠ .s3 → r ≠ .t0 → l.gpr r = s.gpr r := fun r h1 h2 => by
    rw [ul.other r h1, kg, ga r h2]
  have hm : l.mem = ((((((((s.mem.writeW ((lay s).B + BitVec.ofNat 64 992) (s.gpr .ra)).writeW
      ((lay s).B + BitVec.ofNat 64 1000) (s.gpr .s3)).writeW ((lay s).B + BitVec.ofNat 64 1008) (s.gpr .a0)).writeW
      ((lay s).B + BitVec.ofNat 64 1016) (s.gpr .a1)).writeW ((lay s).B + BitVec.ofNat 64 1024) (s.gpr .a4)).writeW
      ((lay s).B + BitVec.ofNat 64 1032) (s.gpr .a5)).writeW ((lay s).B + BitVec.ofNat 64 1040) (s.gpr .a6)).writeW
      ((lay s).B + BitVec.ofNat 64 1048) (s.gpr .a7)) := by
    rw [ul.mem, uk.mem, uj.mem, ui.mem, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem, uj.gpr, ig, uf.gpr, eg,
      ud.gpr, cg, ub.gpr, ga _ (by decide), ga _ (by decide), ga _ (by decide), ga _ (by decide),
      ga _ (by decide), ga _ (by decide), ga _ (by decide), ga _ (by decide)]
    rfl
  have k0 : s.mem.readW ((lay s).B + BitVec.ofNat 64 1248) 64 = (lay s).vlen := by
    rw [arg_addr s 0]; rfl
  have k1 : s.mem.readW ((lay s).B + BitVec.ofNat 64 1256) 64 = (lay s).scr := by
    rw [arg_addr s 1]; rfl
  have k3 : s.mem.readW ((lay s).B + BitVec.ofNat 64 1272) 64 = (lay s).out := by
    rw [arg_addr s 3]; rfl
  have k4 : s.mem.readW ((lay s).B + BitVec.ofNat 64 1280) 64 = (lay s).ol := by
    rw [arg_addr s 4]; rfl
  have lsp : l.sp = (lay s).B + BitVec.ofNat 64 992 := by
    rw [ul.sp, uk.sp, uj.sp, ui.sp, uf.sp, ue.sp, ud.sp, uc.sp, ub.sp, ua.sp, hsp]
  have lwr : l.wr = (lay s).FR :: s.wr := by rw [ul.wr, uk.wr, uj.wr, iw]
  have lrd : l.rd = s.rd := by
    rw [ul.rd, uk.rd, uj.rd, ui.rd, uf.rd, ue.rd, ud.rd, uc.rd, ub.rd, ua.rd]; rfl
  refine ⟨⟨?_, ?_, lsp, ?_, fun r hr hr' => hl r hr' fun e => by subst e; revert hr; decide, ?_, ?_⟩,
    hl _ (by decide) (by decide), hl _ (by decide) (by decide), hl _ (by decide) (by decide),
    hl _ (by decide) (by decide), hl _ (by decide) (by decide), hl _ (by decide) (by decide)⟩
  · rw [lrd, h.2.2.2.1, ← arg_addr s 0]; rfl
  · rw [lwr, h.2.2.2.2.1]; rfl
  · rw [ul.gpr, kg, a0]
  · rw [hm]
    constructor <;>
      simp (disch := decide) only [readW_writeW_off, Mem.readW_writeW_self64, k0, k1, k3, k4] <;> rfl
  · rw [hm]
    refine Frame.sub (rs := [(lay s).STK]) ?_ fun r hr => ?_
    · repeat refine Frame.writeW ?_ (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
      exact Frame.refl _ _
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, fun _ h => h⟩

end VG.Proof.Scrypt.RISCV64.Whole
