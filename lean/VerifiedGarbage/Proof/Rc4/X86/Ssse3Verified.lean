module

public import VerifiedGarbage.Impl.Rc4.X86.Ssse3
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.X86.Sse
import VerifiedGarbage.Proof.Rc4.X86.Ssse3Lit
public import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.Reduce
import VerifiedGarbage.Proof.Framework.X86.ByteMap
import VerifiedGarbage.Proof.Framework.X86.ByteLookup
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rc4.Memory
import VerifiedGarbage.Proof.Rc4.Scan32
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Rc4.Scratch
public import VerifiedGarbage.Proof.Rc4.X86.Contract
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Spec.Rc4.Contract
public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rc4.Identity
public import VerifiedGarbage.Proof.Rc4.Schedule
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Rc4.Table
import VerifiedGarbage.Proof.Rc4.Update
import VerifiedGarbage.Proof.Rc4.Stream
import VerifiedGarbage.Proof.Framework.X86.SymFrame
public import VerifiedGarbage.Proof.Rc4.X86.ConstantTime
public import VerifiedGarbage.Proof.Rc4.X86.Frame
import VerifiedGarbage.Proof.Modes.X86.Ops
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Rc4.X86.Ssse3
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.TCB.X86.Sse
meta import VerifiedGarbage.Proof.Rc4.X86.Ssse3Lit
meta import VerifiedGarbage.Proof.Framework.X86.Wp
meta import VerifiedGarbage.Proof.Framework.X86.Reduce
meta import VerifiedGarbage.Proof.Framework.X86.ByteMap
meta import VerifiedGarbage.Proof.Framework.X86.ByteLookup
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.X86.SseDword
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Rc4.Memory
meta import VerifiedGarbage.Proof.Rc4.Scan32
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86.StackScratch
meta import VerifiedGarbage.Proof.Rc4.Scratch
meta import VerifiedGarbage.Proof.Rc4.X86.Contract
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.TCB.X86.Target
meta import VerifiedGarbage.Impl.StackScratch.X86
meta import VerifiedGarbage.Spec.Rc4.Contract
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Rc4.Identity
meta import VerifiedGarbage.Proof.Rc4.Schedule
meta import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Rc4.Table
meta import VerifiedGarbage.Proof.Rc4.Update
meta import VerifiedGarbage.Proof.Rc4.Stream
meta import VerifiedGarbage.Proof.Framework.X86.SymFrame
meta import VerifiedGarbage.Proof.Rc4.X86.ConstantTime
meta import VerifiedGarbage.Proof.Rc4.X86.Frame
meta import VerifiedGarbage.Proof.Modes.X86.Ops
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# RC4 with the table's rows in XMM registers on x86 (32-bit): the proofs

`vg_rc4_init_ssse3` and `vg_rc4_apply_ssse3` (`Impl/Rc4/X86/Ssse3.lean`) meet
the baseline's contracts with four more bytes of stack, which the address of
their constants takes, in constant time and without secret residue.

* Values: the vectors by their bytes. `IsX` and `byte_mask` (the selector of
  a byte of the table, and the mask of a row), `byte_diff`, `byte_new` and
  `writeW_row` (a row's exchange and its store), `byte_align1` (the column
  that a pass over the rows collects) are about the rows only, whatever the
  code around them.
* The passes: `swapRows_wp` (the byte `j` takes a value, and a register what
  it held) and `readRows_wp` (a column of the table), each by induction on
  the pairs of rows; `exchange_wp` and `lookup_wp` around them.
* The loops: an iteration by its memory (`apply_step`, `sch_step`), then as
  the baseline's (`LoopI`, `SchI`), with the baseline's lemmas for the code
  that is the baseline's (`entry`, `save`, `start`, `finish`, `restore`, the
  end of a round of the key schedule).
* The contracts (`initC4`, `applyC4`), constant time by the taint analysis
  with the PRGA index `i` made public by hand as in the baseline
  (`entry_ct`), and the functions as emitted (`init_scrubbed`,
  `apply_scrubbed`).
-/

@[expose] public section

namespace VG.Proof.Rc4.X86.Ssse3

open VG VG.X86 VG.Impl.Rc4.X86.Ssse3
open VG.Impl.Rc4.X86 (at_ imm)
open VG.X86.Wp
open VG.X86.ByteMap (byte_pshufb byte_xor byte_and byte_ofBytes)
open VG.X86.ByteLookup (byte_or byte_low)
open VG.Proof.Rc4 (region_offset write_byte xor_byte32 writeW_byte8 low_byte32 byte_add32 byte_inc32 byte_add3_32
  low_xor32 sep_of_sub readW_write1 contains_prefix)
open VG.Proof.Rc4.X86 (idx_addr key_addr ApplyPre applyRegions upd upd_succ apply_entry apply_start apply_finish save_ok
  restore_ok savedMem savedMem_frame saved_savedMem Saved arg_contains')
open VG.Spec.Rc4 (Context contextAt bytesAt step update)
open VG.Proof.Rc4 (identityMem identityMem_zero identityMem_table identityMem_frame schedulePrefix scheduleRound
  schedule_zero schedule_succ keySchedule_eq key_next32 byte32 bytes_length bytes_get TableFrame)
open VG.Proof.Rc4.X86 (keyOf schedule_after InitPre InitFrame init_finish valid_length32)
open VG.Proof.Rc4 (frame_of_table frame_finish table_frame_readW)
open VG.Spec.Rc4 (keySchedule)
open VG.Proof.Rc4 (step_eq table_swap table_get context_ext bytes_snoc bytes_frame data_ne contextAt_frame context_finish
  bytes_write_sep)

/-! ## One instruction at a time, with the XMM registers -/

/-- `s'` is `s` but for the general register `d` and the flags. -/
structure GU (s s' : State) (d : Reg) (v : BitVec 32) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  xmm : s'.xmm = s.xmm
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  syms : s'.syms = s.syms

/-- `s'` is `s` but for the XMM register `d`. -/
structure XU (s s' : State) (d : XReg) (v : BitVec 128) : Prop where
  xmm : s'.xmm d = v
  other : ∀ r, r ≠ d → s'.xmm r = s.xmm r
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  syms : s'.syms = s.syms

/-- `s'` is `s` with memory `m`. -/
structure MU (s s' : State) (m : Mem) : Prop where
  mem : s'.mem = m
  gpr : s'.gpr = s.gpr
  xmm : s'.xmm = s.xmm
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  syms : s'.syms = s.syms

theorem GU.setReg (s : State) (d : Reg) (v : BitVec 32) : GU s (s.setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl, rfl, rfl⟩

theorem GU.flags (s : State) (d : Reg) (x : BitVec 32) (c o : Bool) (v : BitVec 32) :
    GU s ((arithFlags s x c o).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, arithFlags, State.setFlags, h], rfl, rfl, rfl, rfl, rfl⟩

theorem GU.setFlags (s : State) (d : Reg) (c o z n : Option Bool) (v : BitVec 32) :
    GU s ((s.setFlags c o z n).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, State.setFlags, h], rfl, rfl, rfl, rfl, rfl⟩

theorem XU.set (s : State) (d : XReg) (v : BitVec 128) : XU s (s.setXmm d v) d v :=
  ⟨by simp [State.setXmm], fun r h => by simp [State.setXmm, h], rfl, rfl, rfl, rfl, rfl⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem g_mov {d r : Reg} {V : BitVec 32} (hr : s.gpr r = V) (k : ∀ s', GU s s' d V → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  cons rfl (k _ (hr ▸ GU.setReg _ _ _))

theorem g_ld {d b : Reg} {B V : BitVec 32} {o : Nat} {a : Addr} (hb : s.gpr b = B) (ha : addr B o = a)
    (hin : InRegions (s.rd ++ s.wr) a 4) (hv : s.mem.readW a 32 = V)
    (k : ∀ s', GU s s' d V → WP isa (.block is) s' Q) : WP isa (.block (.mov d (.mem (at_ b o)) :: is)) s Q := by
  subst ha hv
  exact cons (s' := s.setReg d _) (by simp [reduceExec, at_, readSrc_mem hb hin]) (k _ (GU.setReg _ _ _))

theorem g_andi {d : Reg} {n : Nat} {V : BitVec 32} (hd : s.gpr d = V)
    (k : ∀ s', GU s s' d (V &&& BitVec.ofNat 32 n) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (imm n) :: is)) s Q :=
  cons rfl (k _ (hd ▸ GU.flags _ _ _ _ _ _))

theorem g_shr {d : Reg} {n : Nat} {V : BitVec 32} (hn : 1 ≤ n ∧ n ≤ 31) (hd : s.gpr d = V)
    (k : ∀ s', GU s s' d (V >>> n) → WP isa (.block is) s' Q) : WP isa (.block (.shift .shr d n :: is)) s Q := by
  subst hd
  exact cons (by simp only [reduceExec, execShift, hn, and_self, ite_true]; rfl) (k _ (GU.setFlags _ _ _ _ _ _ _))

theorem g_movzx {d b : Reg} {B : BitVec 32} {o : Nat} {a : Addr} {V : Byte} (hb : s.gpr b = B) (ha : addr B o = a)
    (hin : InRegions (s.rd ++ s.wr) a 1) (hv : s.mem a = V)
    (k : ∀ s', GU s s' d (V.setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d (at_ b o) :: is)) s Q := by
  subst ha hv
  exact cons (s' := s.setReg d _) (by simp [exec, at_, State.load8, ea_mk, hb, hin]) (k _ (GU.setReg _ _ _))

theorem x_bin {op : XBinOp} {d r : XReg} {A B : BitVec 128} (hd : s.xmm d = A) (hr : s.xmm r = B)
    (k : ∀ s', XU s s' d (XBinOp.eval op A B) → WP isa (.block is) s' Q) : WP isa (.block (x op d r :: is)) s Q :=
  cons rfl (k _ (hd ▸ hr ▸ XU.set _ _ _))

theorem x_movd {d : XReg} {r : Reg} {V : BitVec 32} (hr : s.gpr r = V)
    (k : ∀ s', XU s s' d ((0 : BitVec 96) ++ V) → WP isa (.block is) s' Q) :
    WP isa (.block (.xop (.movd d r) :: is)) s Q :=
  cons rfl (k _ (hr ▸ XU.set _ _ _))

theorem x_palignr {d r : XReg} {n : BitVec 8} {A B : BitVec 128} (hd : s.xmm d = A) (hr : s.xmm r = B)
    (k : ∀ s', XU s s' d (alignRight A B n) → WP isa (.block is) s' Q) :
    WP isa (.block (.xop (.palignr d r n) :: is)) s Q :=
  cons rfl (k _ (hd ▸ hr ▸ XU.set _ _ _))

/-- The constant at the byte offset `off` of the table. -/
def cst (off : Nat) : BitVec 128 := table.getD (off / 8 + 1) 0 ++ table.getD (off / 8) 0

theorem x_tb {d : XReg} {off : Nat} (hb : s.gpr tbr = s.syms tableName)
    (ho : off % 8 = 0 ∧ off / 8 + 2 ≤ table.length)
    (k : ∀ s', XU s s' d (cst off) → WP isa (.block is) s' Q) : WP isa (.block (tb d off :: is)) s Q :=
  cons (show (if s.gpr tbr = s.syms tableName ∧ off % 8 = 0 ∧ off / 8 + 2 ≤ table.length then some _ else none) = _ by
    rw [ite_eq_left (show _ ∧ _ ∧ _ from ⟨hb, ho.1, ho.2⟩)]; rfl) (k _ (XU.set _ _ _))

theorem x_ld {d : XReg} {P : BitVec 32} {o : Nat} {a : Addr} {V : BitVec 128} (hb : s.gpr .edi = P)
    (ha : addr P o = a) (hin : InRegions (s.rd ++ s.wr) a 16) (hv : s.mem.readW a 128 = V)
    (k : ∀ s', XU s s' d V → WP isa (.block is) s' Q) : WP isa (.block (ld d o :: is)) s Q := by
  subst ha hv
  exact cons (show (State.load128 s (s.ea (at_ .edi o))).map _ = _ by
    rw [show s.ea (at_ .edi o) = addr P o by rw [← hb]; rfl, State.load128, ite_eq_left hin]; rfl) (k _ (XU.set _ _ _))

theorem x_st {r : XReg} {P : BitVec 32} {o : Nat} {a : Addr} {V : BitVec 128} (hb : s.gpr .edi = P)
    (ha : addr P o = a) (hout : InRegions s.wr a 16) (hr : s.xmm r = V)
    (k : ∀ s', MU s s' (s.mem.writeW a V) → WP isa (.block is) s' Q) : WP isa (.block (stx o r :: is)) s Q := by
  subst ha hr
  exact cons (s' := { s with mem := s.mem.writeW (addr P o) (s.xmm r) })
    (show State.store128 s (s.ea (at_ .edi o)) (s.xmm r) = _ by
      rw [show s.ea (at_ .edi o) = addr P o by rw [← hb]; rfl, State.store128, ite_eq_left hout])
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem m_movq {r : XReg} {b : Reg} {B : BitVec 32} {o : Nat} {a : Addr} {V : BitVec 128} (hb : s.gpr b = B)
    (ha : addr B o = a) (hout : InRegions s.wr a 8) (hr : s.xmm r = V)
    (k : ∀ s', MU s s' (s.mem.writeW a (V.extractLsb' 0 64)) → WP isa (.block is) s' Q) :
    WP isa (.block (.movqStore (at_ b o) r :: is)) s Q := by
  subst ha hr
  exact cons (s' := { s with mem := s.mem.writeW (addr B o) ((s.xmm r).extractLsb' 0 64) })
    (show State.store64 s (s.ea (at_ b o)) ((s.xmm r).extractLsb' 0 64) = _ by
      rw [show s.ea (at_ b o) = addr B o by rw [← hb]; rfl, State.store64, ite_eq_left hout])
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

end

/-! ## The constants -/

theorem cst_C : ∀ r < 16, ∀ b < 16, byte (cst (oC r)) b = if b = r then 0xff#8 else 0#8 := by lit_decide

theorem cst_I : ∀ r < 16, ∀ b < 16, byte (cst (oI r)) b = BitVec.ofNat 8 (16 * r + b) := by lit_decide

theorem cst_T : ∀ b < 16, byte (cst oT) b = if b = 0 then 0#8 else 0x80#8 := by lit_decide

/-! ## Bytes of the vectors

The lemmas of this section are about values only, for the code that keeps the
table in rows of sixteen bytes: `IsX` and `byte_mask` (the mask of a row),
`byte_diff` and `byte_new` (a row's exchange), `writeW_row` (its store),
`byte_align1` (the column a pass over the rows collects). -/

theorem byte_zero (l : Nat) : byte (0 : BitVec 128) l = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [byte]

/-- `movd` of a byte. -/
theorem byte_movd (b : Byte) {k : Nat} (hk : k < 16) :
    byte ((0 : BitVec 96) ++ b.setWidth 32) k = if k = 0 then b else 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h0 : k = 0
  · subst h0
    have h32 : i < 32 := by omega
    rw [byte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    simp [hi, h32]
  · rw [ite_eq_right h0]
    simp only [byte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, BitVec.getLsbD_setWidth, BitVec.getLsbD_zero]
    have hb : b.getLsbD (8 * k + i) = false := BitVec.getLsbD_of_ge b _ (by omega)
    simp [hb]

theorem lo_reg (j : Byte) : j.setWidth 32 &&& 15#32 = (BitVec.ofNat 8 (j.toNat % 16)).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  have hj := j.isLt
  rw [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show 15 % 2 ^ 32 = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem hi_reg (j : Byte) : j.setWidth 32 >>> 4 = (BitVec.ofNat 8 (j.toNat / 16)).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  have hj := j.isLt
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  omega

theorem lane_facts : ∀ n < 16, ∀ l < 16, (BitVec.ofNat 8 l ^^^ BitVec.ofNat 8 n).msb = false ∧
    (((BitVec.ofNat 8 l ^^^ BitVec.ofNat 8 n).extractLsb' 0 4).toNat = 0 ↔ l = n) := by
  decide

theorem nib_facts : ∀ n < 16, (BitVec.ofNat 8 n).msb = false ∧ ((BitVec.ofNat 8 n).extractLsb' 0 4).toNat = n := by
  decide

/-- Lane `l` holds `l ^^^ (j % 16)`: zero in the lane of `j`'s column. -/
def lanesOf (j32 : BitVec 32) : BitVec 128 :=
  cst (oI 0) ^^^ XBinOp.eval .pshufb ((0 : BitVec 96) ++ (j32 &&& 15#32)) 0

theorem byte_lanes (j : Byte) {l : Nat} (hl : l < 16) :
    byte (lanesOf (j.setWidth 32)) l = BitVec.ofNat 8 l ^^^ BitVec.ofNat 8 (j.toNat % 16) := by
  rw [lanesOf, byte_xor, cst_I 0 (by decide) l hl, byte_pshufb _ _ hl, byte_zero, lo_reg,
    show (0#8).msb = false from rfl, ite_eq_right (by decide), show ((0#8).extractLsb' 0 4).toNat = 0 from rfl,
    byte_movd _ (by decide), ite_eq_left rfl, Nat.mul_zero, Nat.zero_add]

/-- A vector's byte 0, moved to the lane of `j`'s column; the other lanes take
`c`, which its other bytes hold. -/
theorem byte_pick {v : BitVec 128} {c : Byte} (hv : ∀ k < 16, k ≠ 0 → byte v k = c) (j : Byte) {l : Nat}
    (hl : l < 16) :
    byte (XBinOp.eval .pshufb v (lanesOf (j.setWidth 32))) l = if l = j.toNat % 16 then byte v 0 else c := by
  obtain ⟨hm, hz⟩ := lane_facts (j.toNat % 16) (Nat.mod_lt _ (by decide)) l hl
  rw [byte_pshufb _ _ hl, byte_lanes j hl, hm, ite_eq_right (by decide)]
  by_cases e : l = j.toNat % 16
  · rw [ite_eq_left e, hz.mpr e]
  · rw [ite_eq_right e]
    exact hv _ (BitVec.isLt _) fun h => e (hz.mp h)

/-- `X` selects the byte `j` of the table: its lane `j % 16` holds the row
`j / 16`, and the other lanes have their top bit set. -/
def IsX (X : BitVec 128) (j : Byte) : Prop :=
  ∀ l < 16, byte X l = if l = j.toNat % 16 then BitVec.ofNat 8 (j.toNat / 16) else 0x80#8

/-- `S` holds the byte `a` in the lane of `j`'s column, and zero elsewhere. -/
def IsSi (S : BitVec 128) (a j : Byte) : Prop := ∀ l < 16, byte S l = if l = j.toNat % 16 then a else 0#8

theorem isSi (a j : Byte) :
    IsSi (XBinOp.eval .pshufb ((0 : BitVec 96) ++ a.setWidth 32) (lanesOf (j.setWidth 32))) a j := by
  intro l hl
  rw [byte_pick (c := 0#8) (fun k hk h0 => by rw [byte_movd _ hk, ite_eq_right h0]) j hl, byte_movd _ (by decide),
    ite_eq_left rfl]

theorem isX (j : Byte) :
    IsX (XBinOp.eval .pshufb (XBinOp.eval .por (cst oT) ((0 : BitVec 96) ++ (j.setWidth 32 >>> 4)))
      (lanesOf (j.setWidth 32))) j := by
  intro l hl
  have hb (k : Nat) (hk : k < 16) : byte (XBinOp.eval .por (cst oT) ((0 : BitVec 96) ++ (j.setWidth 32 >>> 4))) k =
      if k = 0 then BitVec.ofNat 8 (j.toNat / 16) else 0x80#8 := by
    rw [show XBinOp.eval .por (cst oT) ((0 : BitVec 96) ++ (j.setWidth 32 >>> 4)) =
      cst oT ||| ((0 : BitVec 96) ++ (j.setWidth 32 >>> 4)) from rfl, byte_or, cst_T k hk, hi_reg,
      byte_movd _ hk]
    by_cases h0 : k = 0
    · rw [ite_eq_left h0, ite_eq_left h0, ite_eq_left h0, BitVec.zero_or]
    · rw [ite_eq_right h0, ite_eq_right h0, ite_eq_right h0, BitVec.or_zero]
  rw [byte_pick (c := 0x80#8) (fun k hk h0 => by rw [hb k hk, ite_eq_right h0]) j hl, hb 0 (by decide), ite_eq_left rfl]

/-- The mask of the row `r`: all ones in the lane of `j`'s column if `j` is in
the row, and zero elsewhere. -/
theorem byte_mask {X : BitVec 128} {j : Byte} (hX : IsX X j) {r l : Nat} (hr : r < 16) (hl : l < 16) :
    byte (XBinOp.eval .pshufb (cst (oC r)) X) l =
      if l = j.toNat % 16 ∧ j.toNat / 16 = r then 0xff#8 else 0#8 := by
  have hj := j.isLt
  rw [byte_pshufb _ _ hl, hX l hl]
  by_cases e : l = j.toNat % 16
  · obtain ⟨hm, hn⟩ := nib_facts (j.toNat / 16) (by omega)
    rw [ite_eq_left e, hm, ite_eq_right (by decide), hn, cst_C r hr _ (by omega)]
    by_cases h : j.toNat / 16 = r
    · rw [ite_eq_left h, ite_eq_left ⟨e, h⟩]
    · rw [ite_eq_right h, ite_eq_right fun h' => h h'.2]
  · rw [ite_eq_right e, show (0x80#8).msb = true from rfl, ite_eq_left rfl, ite_eq_right fun h' => e h'.1]

theorem and_ff (x : Byte) : x &&& 0xff#8 = x := by
  rw [show (0xff#8 : Byte) = BitVec.allOnes 8 by decide, BitVec.and_allOnes]

/-- What a row's exchange takes out of the row: where the mask is set, the
row's byte and the new byte's difference. -/
theorem byte_diff {M S row : BitVec 128} {a : Byte} {P : Prop} [Decidable P] {l : Nat}
    (hM : byte M l = if P then 0xff#8 else 0#8) (hS : P → byte S l = a) :
    byte (XBinOp.eval .pand (XBinOp.eval .pxor row S) M) l = if P then byte row l ^^^ a else 0#8 := by
  rw [show XBinOp.eval .pand (XBinOp.eval .pxor row S) M = (row ^^^ S) &&& M from rfl, byte_and, byte_xor, hM]
  by_cases h : P
  · rw [ite_eq_left h, ite_eq_left h, hS h, and_ff]
  · rw [ite_eq_right h, ite_eq_right h, BitVec.and_zero]

/-- The row after its exchange: the new byte where the mask is set. -/
theorem byte_new {M S row : BitVec 128} {a : Byte} {P : Prop} [Decidable P] {l : Nat}
    (hM : byte M l = if P then 0xff#8 else 0#8) (hS : P → byte S l = a) :
    byte (XBinOp.eval .pxor row (XBinOp.eval .pand (XBinOp.eval .pxor row S) M)) l =
      if P then a else byte row l := by
  rw [show XBinOp.eval .pxor row (XBinOp.eval .pand (XBinOp.eval .pxor row S) M) =
    row ^^^ XBinOp.eval .pand (XBinOp.eval .pxor row S) M from rfl, byte_xor, byte_diff hM hS]
  by_cases h : P
  · rw [ite_eq_left h, ite_eq_left h, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · rw [ite_eq_right h, ite_eq_right h, BitVec.xor_zero]

/-- A row read from memory. -/
theorem byte_row (m : Mem) (q : Addr) {l : Nat} (hl : l < 16) :
    byte (m.readW q 128) l = m (q + BitVec.ofNat 64 l) :=
  byte_readW m q (by omega)

/-- Storing a row that differs from memory in at most the lane `l₀`. -/
theorem writeW_row (m : Mem) (q : Addr) (v : BitVec 128) {c : Byte} {l₀ : Nat} {P : Prop} [Decidable P]
    (hl₀ : l₀ < 16) (h : ∀ l < 16, byte v l = if l = l₀ ∧ P then c else m (q + BitVec.ofNat 64 l)) :
    m.writeW q v = if P then m.write (q + BitVec.ofNat 64 l₀) 1 c else m := by
  funext x
  by_cases hx : (x - q).toNat < 16
  · obtain hxe : x = q + BitVec.ofNat 64 (x - q).toNat := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    rw [hxe, writeW_byte m q v (by omega) (by decide)]
    show byte v _ = _
    rw [h _ hx]
    by_cases hP : P
    · rw [ite_eq_left hP, write_byte]
      by_cases e : (x - q).toNat = l₀
      · rw [ite_eq_left ⟨e, hP⟩, e, ite_eq_left rfl]
      · rw [ite_eq_right fun h' => e h'.1, ite_eq_right (Offset.add_ofNat_ne q (by omega) (by omega) e)]
    · rw [ite_eq_right fun h' => hP h'.2, ite_eq_right hP]
  · rw [writeW_byte_off m q v x (by omega)]
    by_cases hP : P
    · rw [ite_eq_left hP, write_byte, ite_eq_right]
      intro e
      apply hx
      rw [e, Mem.sub_ofNat_toNat q (by omega)]
      exact hl₀
    · rw [ite_eq_right hP]

/-- `palignr a, b, 1`: `b` a byte down, and `a`'s byte 0 on top. -/
theorem byte_align1 (a b : BitVec 128) {l : Nat} (hl : l < 16) :
    byte (alignRight a b 1) l = if l = 15 then byte a 0 else byte b (l + 1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : l = 15
  · subst h
    rw [ite_eq_left rfl, byte, byte, alignRight, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
    simp [hi]
    rw [decide_eq_true (by omega), Bool.true_and, ite_eq_right (by omega), show 8 + (120 + i) - 128 = i by omega]
  · rw [ite_eq_right h, byte, byte, alignRight, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
    simp [hi]
    rw [decide_eq_true (by omega), Bool.true_and, ite_eq_left (by omega),
      show 8 + (8 * l + i) = 8 * (l + 1) + i by omega]

/-! ## The selectors of a byte of the table -/

/-- `head`: `xmm4` selects the byte `j` (`IsX`) and `xmm5` holds `a` in its
lane (`IsSi`). -/
theorem head_wp {s : State} {j a : Byte} {is : List Instr} {Q : State → Prop}
    (hbp : s.gpr .ebp = j.setWidth 32) (hcx : s.gpr .ecx = a.setWidth 32) (htb : s.gpr tbr = s.syms tableName)
    (k : ∀ s', IsX (s'.xmm .xmm4) j → IsSi (s'.xmm .xmm5) a j → (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (head ++ is)) s Q := by
  simp only [head, List.cons_append, List.nil_append]
  refine g_mov hbp fun s₁ u₁ => ?_
  refine g_andi u₁.gpr fun s₂ u₂ => ?_
  refine x_movd u₂.gpr fun s₃ u₃ => ?_
  refine x_bin rfl rfl fun s₄ u₄ => ?_
  refine x_bin ((u₄.other _ (by decide)).trans u₃.xmm) u₄.xmm fun s₅ u₅ => ?_
  obtain g₅ : ∀ r, r ≠ .eax → s₅.gpr r = s.gpr r := fun r h => by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.other r h, u₁.other r h]
  obtain sy₅ : s₅.syms = s.syms := by rw [u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]
  refine x_tb (by rw [g₅ _ (by decide), sy₅]; exact htb) (by decide) fun s₆ u₆ => ?_
  refine x_bin u₆.xmm ((u₆.other _ (by decide)).trans u₅.xmm) fun s₇ u₇ => ?_
  obtain L₇ : s₇.xmm .xmm1 = lanesOf (j.setWidth 32) := by
    rw [u₇.xmm, show XBinOp.eval .pxor (s₃.xmm .xmm1) (s₃.xmm .xmm1) = 0 from BitVec.xor_self]; rfl
  refine x_movd (show s₇.gpr .ecx = a.setWidth 32 by rw [u₇.gpr, u₆.gpr, g₅ _ (by decide)]; exact hcx)
    fun s₈ u₈ => ?_
  refine x_bin u₈.xmm ((u₈.other _ (by decide)).trans L₇) fun s₉ u₉ => ?_
  obtain g₉ : ∀ r, r ≠ .eax → s₉.gpr r = s.gpr r := fun r h => by
    rw [u₉.gpr, u₈.gpr, u₇.gpr, u₆.gpr]; exact g₅ r h
  obtain sy₉ : s₉.syms = s.syms := by rw [u₉.syms, u₈.syms, u₇.syms, u₆.syms]; exact sy₅
  refine x_tb (by rw [g₉ _ (by decide), sy₉]; exact htb) (by decide) fun s₁₀ u₁₀ => ?_
  refine g_mov (show s₁₀.gpr .ebp = j.setWidth 32 by rw [u₁₀.gpr, g₉ _ (by decide)]; exact hbp) fun s₁₁ u₁₁ => ?_
  refine g_shr (by decide) u₁₁.gpr fun s₁₂ u₁₂ => ?_
  refine x_movd u₁₂.gpr fun s₁₃ u₁₃ => ?_
  refine x_bin (show s₁₃.xmm .xmm4 = cst oT by rw [u₁₃.other _ (by decide), u₁₂.xmm, u₁₁.xmm]; exact u₁₀.xmm)
    u₁₃.xmm fun s₁₄ u₁₄ => ?_
  obtain L₁₄ : s₁₄.xmm .xmm1 = lanesOf (j.setWidth 32) := by
    rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.xmm, u₁₁.xmm, u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide)]
    exact L₇
  refine x_bin u₁₄.xmm L₁₄ fun s₁₅ u₁₅ => ?_
  refine k s₁₅ ?_ ?_ (fun r h => ?_) ?_ ?_ ?_ ?_
  · rw [u₁₅.xmm]; exact isX j
  · rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.xmm, u₁₁.xmm,
      u₁₀.other _ (by decide), u₉.xmm]
    exact isSi a j
  · rw [u₁₅.gpr, u₁₄.gpr, u₁₃.gpr, u₁₂.other r h, u₁₁.other r h, u₁₀.gpr]; exact g₉ r h
  · rw [u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem,
      u₃.mem, u₂.mem, u₁.mem]
  · rw [u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd,
      u₁.rd]
  · rw [u₁₅.wr, u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr,
      u₁.wr]
  · rw [u₁₅.syms, u₁₄.syms, u₁₃.syms, u₁₂.syms, u₁₁.syms, u₁₀.syms]; exact sy₉

/-! ## The first pass: the exchange -/

theorem tab_len : table.length = 66 := rfl

/-- The byte `j` of the table at `p`, by its row and its lane. -/
theorem row_addr (p : Addr) (j : Byte) :
    p + BitVec.ofNat 64 (16 * (j.toNat / 16)) + BitVec.ofNat 64 (j.toNat % 16) = p + BitVec.ofNat 64 j.toNat := by
  rw [Offset.add_add, show 16 * (j.toNat / 16) + j.toNat % 16 = j.toNat by omega]

/-- The exchange in the row `r`: the row takes `a` at the byte `j` if it is
the row's, and `ar` what the row held there, less `a`. -/
theorem swapRow_wp {s : State} {P : BitVec 32} {j a : Byte} {mr ar : XReg} {r : Nat} {is : List Instr}
    {Q : State → Prop} (hr : r < 16) (hma : mr ≠ ar) (hm4 : mr ≠ .xmm4) (hm5 : mr ≠ .xmm5)
    (ha5 : ar ≠ .xmm5) (hdi : s.gpr .edi = P) (fit : P.toNat + 256 ≤ 2 ^ 32)
    (hw : InRegions s.wr (P.setWidth 64) 256) (htb : s.gpr tbr = s.syms tableName) (hX : IsX (s.xmm .xmm4) j)
    (hS : IsSi (s.xmm .xmm5) a j)
    (k : ∀ s', (∀ l < 16, byte (s'.xmm ar) l = if l = j.toNat % 16 ∧ j.toNat / 16 = r then
          s.mem (P.setWidth 64 + BitVec.ofNat 64 j.toNat) ^^^ a else 0#8) →
        s'.mem = (if j.toNat / 16 = r then s.mem.write (P.setWidth 64 + BitVec.ofNat 64 j.toNat) 1 a else s.mem) →
        (∀ x, x ≠ mr → x ≠ ar → s'.xmm x = s.xmm x) → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
        s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (swapRow mr ar r ++ is)) s Q := by
  have hj := j.isLt
  simp only [swapRow, List.cons_append, List.nil_append]
  obtain ea : addr P (16 * r) = P.setWidth 64 + BitVec.ofNat 64 (16 * r) := addr_eq (by omega)
  obtain hrow : InRegions s.wr (P.setWidth 64 + BitVec.ofNat 64 (16 * r)) 16 :=
    region_offset _ _ _ _ _ (by omega) (by omega) hw
  obtain hrd : InRegions (s.rd ++ s.wr) (P.setWidth 64 + BitVec.ofNat 64 (16 * r)) 16 := by
    obtain ⟨R, hR, hc⟩ := hrow
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  refine x_tb htb ⟨by unfold oC; omega, by rw [tab_len]; unfold oC; omega⟩ fun s₁ u₁ => ?_
  refine x_bin u₁.xmm (u₁.other _ hm4.symm) fun s₂ u₂ => ?_
  refine x_ld (show s₂.gpr .edi = P by rw [u₂.gpr, u₁.gpr]; exact hdi) ea
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hrd)
    (show s₂.mem.readW _ 128 = s.mem.readW _ 128 by rw [u₂.mem, u₁.mem]) fun s₃ u₃ => ?_
  refine x_bin u₃.xmm (show s₃.xmm .xmm5 = s.xmm .xmm5 by
    rw [u₃.other _ ha5.symm, u₂.other _ hm5.symm, u₁.other _ hm5.symm]) fun s₄ u₄ => ?_
  refine x_bin u₄.xmm ((u₄.other _ hma).trans ((u₃.other _ hma).trans u₂.xmm)) fun s₅ u₅ => ?_
  refine x_ld (show s₅.gpr .edi = P by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]; exact hdi) ea
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hrd)
    (show s₅.mem.readW _ 128 = s.mem.readW _ 128 by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem])
    fun s₆ u₆ => ?_
  refine x_bin u₆.xmm ((u₆.other _ hma.symm).trans u₅.xmm) fun s₇ u₇ => ?_
  refine x_st (show s₇.gpr .edi = P by rw [u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]; exact hdi) ea
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hrow) u₇.xmm fun s₈ u₈ => ?_
  have hM (l : Nat) (hl : l < 16) := byte_mask hX hr hl
  have hSl (l : Nat) (hl : l < 16) : (l = j.toNat % 16 ∧ j.toNat / 16 = r) → byte (s.xmm .xmm5) l = a :=
    fun h => (hS l hl).trans (ite_eq_left h.1)
  refine k s₈ (fun l hl => ?_) ?_ (fun x hx1 hx2 => ?_) ?_ ?_ ?_ ?_
  · rw [u₈.xmm, u₇.other _ hma.symm, u₆.other _ hma.symm, u₅.xmm, byte_diff (hM l hl) (hSl l hl)]
    by_cases h : l = j.toNat % 16 ∧ j.toNat / 16 = r
    · rw [ite_eq_left h, ite_eq_left h, byte_row _ _ hl]
      obtain ⟨rfl, rfl⟩ := h
      rw [row_addr]
    · rw [ite_eq_right h, ite_eq_right h]
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem,
      writeW_row s.mem _ _ (c := a) (l₀ := j.toNat % 16) (P := j.toNat / 16 = r) (by omega) (fun l hl => by
        rw [byte_new (hM l hl) (hSl l hl), byte_row _ _ hl])]
    by_cases h : j.toNat / 16 = r
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl, row_addr]
    · rw [ite_eq_right h, ite_eq_right h]
  · rw [u₈.xmm, u₇.other _ hx1, u₆.other _ hx1, u₅.other _ hx2, u₄.other _ hx2, u₃.other _ hx2, u₂.other _ hx1,
      u₁.other _ hx1]
  · rw [u₈.gpr, u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₈.syms, u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]

/-- The exchange, after the rows before the row `n` (`n` even): `xmm3` holds
what the byte `j` held, less `a`, once its row is done (`n = 0`: nothing yet). -/
structure SwI (s₀ : State) (P : BitVec 32) (j a : Byte) (n : Nat) (t : State) : Prop where
  x : IsX (t.xmm .xmm4) j
  si : IsSi (t.xmm .xmm5) a j
  acc : 0 < n → ∀ l < 16, byte (t.xmm .xmm3) l = if l = j.toNat % 16 ∧ j.toNat / 16 < n then
    s₀.mem (P.setWidth 64 + BitVec.ofNat 64 j.toNat) ^^^ a else 0#8
  mem : t.mem = if j.toNat / 16 < n then s₀.mem.write (P.setWidth 64 + BitVec.ofNat 64 j.toNat) 1 a else s₀.mem
  gpr : t.gpr = s₀.gpr
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  syms : t.syms = s₀.syms

/-- A pair of rows. -/
theorem swapPair_wp {s₀ s : State} {P : BitVec 32} {j a : Byte} {p : Nat} {is : List Instr} {Q : State → Prop}
    (hp : p < 8) (hdi : s₀.gpr .edi = P) (fit : P.toNat + 256 ≤ 2 ^ 32)
    (hw : InRegions s₀.wr (P.setWidth 64) 256) (htb : s₀.gpr tbr = s₀.syms tableName) (h : SwI s₀ P j a (2 * p) s)
    (k : ∀ s', SwI s₀ P j a (2 * p + 2) s' → WP isa (.block is) s' Q) :
    WP isa (.block (swapPair p ++ is)) s Q := by
  rw [swapPair, List.append_assoc, List.append_assoc]
  refine swapRow_wp (r := 2 * p) (by omega) (by decide) (by decide) (by decide) (by decide)
    (by rw [h.gpr]; exact hdi) fit (by rw [h.wr]; exact hw) (by rw [h.gpr, h.syms]; exact htb) h.x h.si
    fun s₁ a₁ m₁ x₁ g₁ rd₁ wr₁ sy₁ => ?_
  refine swapRow_wp (r := 2 * p + 1) (by omega) (by decide) (by decide) (by decide) (by decide)
    (by rw [g₁, h.gpr]; exact hdi) fit (by rw [wr₁, h.wr]; exact hw) (by rw [g₁, sy₁, h.gpr, h.syms]; exact htb)
    (by rw [x₁ _ (by decide) (by decide)]; exact h.x) (by rw [x₁ _ (by decide) (by decide)]; exact h.si)
    fun s₂ a₂ m₂ x₂ g₂ rd₂ wr₂ sy₂ => ?_
  simp only [List.cons_append, List.nil_append]
  refine x_bin rfl (x₂ .xmm1 (by decide) (by decide)) fun s₃ u₃ => ?_
  -- where the byte `j`'s row is
  obtain hc : ((j.toNat / 16 < 2 * p) = True ∧ (j.toNat / 16 = 2 * p) = False ∧
        (j.toNat / 16 = 2 * p + 1) = False ∧ (j.toNat / 16 < 2 * p + 2) = True) ∨
      ((j.toNat / 16 < 2 * p) = False ∧ (j.toNat / 16 = 2 * p) = True ∧
        (j.toNat / 16 = 2 * p + 1) = False ∧ (j.toNat / 16 < 2 * p + 2) = True) ∨
      ((j.toNat / 16 < 2 * p) = False ∧ (j.toNat / 16 = 2 * p) = False ∧
        (j.toNat / 16 = 2 * p + 1) = True ∧ (j.toNat / 16 < 2 * p + 2) = True) ∨
      ((j.toNat / 16 < 2 * p) = False ∧ (j.toNat / 16 = 2 * p) = False ∧
        (j.toNat / 16 = 2 * p + 1) = False ∧ (j.toNat / 16 < 2 * p + 2) = False) := by
    simp only [eq_iff_iff, iff_true, iff_false]
    omega
  obtain hmem : s₂.mem = if j.toNat / 16 < 2 * p + 2 then
      s₀.mem.write (P.setWidth 64 + BitVec.ofNat 64 j.toNat) 1 a else s₀.mem := by
    rw [m₂, m₁, h.mem]
    rcases hc with ⟨c0, c1, c2, c3⟩ | ⟨c0, c1, c2, c3⟩ | ⟨c0, c1, c2, c3⟩ | ⟨c0, c1, c2, c3⟩ <;>
      simp only [c0, c1, c2, c3, ↓reduceIte]
  obtain hE : ∀ l < 16, byte (XBinOp.eval .por (s₂.xmm .xmm6) (s₁.xmm .xmm1)) l =
      if l = j.toNat % 16 ∧ ¬ j.toNat / 16 < 2 * p ∧ j.toNat / 16 < 2 * p + 2 then
        s₀.mem (P.setWidth 64 + BitVec.ofNat 64 j.toNat) ^^^ a else 0#8 := by
    intro l hl
    rw [show XBinOp.eval .por (s₂.xmm .xmm6) (s₁.xmm .xmm1) = s₂.xmm .xmm6 ||| s₁.xmm .xmm1 from rfl, byte_or,
      a₂ l hl, a₁ l hl, m₁, h.mem]
    rcases Classical.propComplete (l = j.toNat % 16) with e | e <;>
      rcases hc with ⟨c0, c1, c2, c3⟩ | ⟨c0, c1, c2, c3⟩ | ⟨c0, c1, c2, c3⟩ | ⟨c0, c1, c2, c3⟩ <;>
      simp only [e, c0, c1, c2, c3, ↓reduceIte, and_true, and_false, not_true_eq_false,
        not_false_eq_true, BitVec.or_zero, BitVec.zero_or]
  obtain x₃ : ∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm6 → s₃.xmm r = s.xmm r := fun r h0 h1 h2 h6 => by
    rw [u₃.other _ h6, x₂ _ h2 h6, x₁ _ h0 h1]
  have fin (s₄ : State) (u₄ : XU s₃ s₄ .xmm3 (if p = 0 then XBinOp.eval .por (s₂.xmm .xmm6) (s₁.xmm .xmm1) else
      XBinOp.eval .por (s.xmm .xmm3) (XBinOp.eval .por (s₂.xmm .xmm6) (s₁.xmm .xmm1)))) :
      SwI s₀ P j a (2 * p + 2) s₄ := by
    refine ⟨?_, ?_, fun _ l hl => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₄.other _ (by decide), x₃ _ (by decide) (by decide) (by decide) (by decide)]; exact h.x
    · rw [u₄.other _ (by decide), x₃ _ (by decide) (by decide) (by decide) (by decide)]; exact h.si
    · rw [u₄.xmm]
      by_cases hp0 : p = 0
      · subst hp0
        rw [ite_eq_left rfl, hE l hl]
        rcases Classical.propComplete (l = j.toNat % 16) with e | e <;>
          rcases Classical.propComplete (j.toNat / 16 < 2 * 0 + 2) with c | c <;>
          simp only [e, c, ↓reduceIte, and_true, and_false, Nat.mul_zero, Nat.not_lt_zero,
            not_false_eq_true]
      · rw [ite_eq_right hp0, show XBinOp.eval .por (s.xmm .xmm3) (XBinOp.eval .por (s₂.xmm .xmm6) (s₁.xmm .xmm1)) =
          s.xmm .xmm3 ||| XBinOp.eval .por (s₂.xmm .xmm6) (s₁.xmm .xmm1) from rfl, byte_or, hE l hl,
          h.acc (by omega) l hl]
        rcases Classical.propComplete (l = j.toNat % 16) with e | e <;>
          rcases hc with ⟨c0, c1, c2, c3⟩ | ⟨c0, c1, c2, c3⟩ | ⟨c0, c1, c2, c3⟩ | ⟨c0, c1, c2, c3⟩ <;>
          simp only [e, c0, c3, ↓reduceIte, and_true, and_false, not_true_eq_false,
            not_false_eq_true, BitVec.or_zero, BitVec.zero_or]
    · rw [u₄.mem, u₃.mem]; exact hmem
    · rw [u₄.gpr, u₃.gpr, g₂, g₁]; exact h.gpr
    · rw [u₄.rd, u₃.rd, rd₂, rd₁]; exact h.rd
    · rw [u₄.wr, u₃.wr, wr₂, wr₁]; exact h.wr
    · rw [u₄.syms, u₃.syms, sy₂, sy₁]; exact h.syms
  by_cases hp0 : p = 0
  · rw [ite_eq_left hp0]
    refine x_bin rfl u₃.xmm fun s₄ u₄ => k s₄ (fin s₄ ?_)
    rw [ite_eq_left hp0]; exact u₄
  · rw [ite_eq_right hp0]
    refine x_bin (x₃ _ (by decide) (by decide) (by decide) (by decide)) u₃.xmm fun s₄ u₄ => k s₄ (fin s₄ ?_)
    rw [ite_eq_right hp0]; exact u₄

/-- The pairs of rows from the pair `p` on. -/
theorem swapFrom_wp {s₀ : State} {P : BitVec 32} {j a : Byte} {is : List Instr} {Q : State → Prop}
    (hdi : s₀.gpr .edi = P) (fit : P.toNat + 256 ≤ 2 ^ 32) (hw : InRegions s₀.wr (P.setWidth 64) 256)
    (htb : s₀.gpr tbr = s₀.syms tableName) (k : ∀ s', SwI s₀ P j a 16 s' → WP isa (.block is) s' Q) :
    ∀ (n p : Nat) (s : State), p + n = 8 → SwI s₀ P j a (2 * p) s →
      WP isa (.block ((List.range' p n).flatMap swapPair ++ is)) s Q
  | 0, p, s, e, h => by
    obtain rfl : p = 8 := by omega
    exact k s h
  | n + 1, p, s, e, h => by
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    exact swapPair_wp (by omega) hdi fit hw htb h fun s' h' =>
      swapFrom_wp hdi fit hw htb k n (p + 1) s' (by omega) (by rw [Nat.mul_succ]; exact h')

/-- The first pass: the byte `j` of the table takes `a`, and `xmm3` holds in
its lane what it held, less `a`. -/
theorem swapRows_wp {s : State} {P : BitVec 32} {j a : Byte} {is : List Instr} {Q : State → Prop}
    (hdi : s.gpr .edi = P) (fit : P.toNat + 256 ≤ 2 ^ 32) (hw : InRegions s.wr (P.setWidth 64) 256)
    (htb : s.gpr tbr = s.syms tableName) (hX : IsX (s.xmm .xmm4) j) (hS : IsSi (s.xmm .xmm5) a j)
    (k : ∀ s', (∀ l < 16, byte (s'.xmm .xmm3) l = if l = j.toNat % 16 then
          s.mem (P.setWidth 64 + BitVec.ofNat 64 j.toNat) ^^^ a else 0#8) →
        s'.mem = s.mem.write (P.setWidth 64 + BitVec.ofNat 64 j.toNat) 1 a → s'.gpr = s.gpr → s'.rd = s.rd →
        s'.wr = s.wr → s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (swapRows ++ is)) s Q := by
  have hj := j.isLt
  rw [swapRows, List.range_eq_range']
  refine swapFrom_wp hdi fit hw htb (fun s' h' => ?_) 8 0 s rfl
    ⟨hX, hS, fun h => absurd h (by decide), (ite_eq_right (by omega)).symm, rfl, rfl, rfl, rfl⟩
  refine k s' (fun l hl => ?_) ?_ h'.gpr h'.rd h'.wr h'.syms
  · rw [h'.acc (by decide) l hl]
    by_cases e : l = j.toNat % 16
    · rw [ite_eq_left ⟨e, by omega⟩, ite_eq_left e]
    · rw [ite_eq_right (fun h => e h.1), ite_eq_right e]
  · rw [h'.mem, ite_eq_left (by omega)]

/-! ## Scalar instructions, with their operands' values -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem w_mov {d r : Reg} {V : BitVec 32} (hr : s.gpr r = V) (k : ∀ s', Upd s s' d V → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q := by
  subst hr; exact wp_mov k

theorem w_ld {d b : Reg} {o : Nat} {B V : BitVec 32} {a : Addr} (hb : s.gpr b = B) (ha : addr B o = a)
    (hin : InRegions (s.rd ++ s.wr) a 4) (hv : s.mem.readW a 32 = V)
    (k : ∀ s', Upd s s' d V → WP isa (.block is) s' Q) : WP isa (.block (.mov d (.mem (at_ b o)) :: is)) s Q := by
  subst ha hv; exact wp_ldm hb hin k

theorem w_st {b r : Reg} {o : Nat} {B V : BitVec 32} {a : Addr} (hb : s.gpr b = B) (ha : addr B o = a)
    (hout : InRegions s.wr a 4) (hr : s.gpr r = V)
    (k : ∀ s', Mupd s s' (s.mem.writeW a V) → WP isa (.block is) s' Q) :
    WP isa (.block (.store (at_ b o) r :: is)) s Q := by
  subst ha hr; exact wp_stm hb hout k

theorem w_xm {d b : Reg} {o : Nat} {B V W : BitVec 32} {a : Addr} (hd : s.gpr d = V) (hb : s.gpr b = B)
    (ha : addr B o = a) (hin : InRegions (s.rd ++ s.wr) a 4) (hv : s.mem.readW a 32 = W)
    (k : ∀ s', Upd s s' d (V ^^^ W) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.mem (at_ b o)) :: is)) s Q := by
  subst ha hv hd; exact wp_xorm hb hin k

theorem w_am {d b : Reg} {o : Nat} {B V W : BitVec 32} {a : Addr} (hd : s.gpr d = V) (hb : s.gpr b = B)
    (ha : addr B o = a) (hin : InRegions (s.rd ++ s.wr) a 4) (hv : s.mem.readW a 32 = W)
    (k : ∀ s', Upd s s' d (V + W) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.mem (at_ b o)) :: is)) s Q := by
  subst ha hv hd; exact wp_addm hb hin k

theorem w_lb {d b : Reg} {o : Nat} {B : BitVec 32} {a : Addr} {V : Byte} (hb : s.gpr b = B) (ha : addr B o = a)
    (hin : InRegions (s.rd ++ s.wr) a 1) (hv : s.mem a = V)
    (k : ∀ s', Upd s s' d (V.setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d (at_ b o) :: is)) s Q := by
  subst ha hv; exact VG.Proof.Modes.X86.wp_movzx hb hin k

theorem w_sb {b : Reg} {r : Reg8} {o : Nat} {B : BitVec 32} {a : Addr} {V : Byte} (hb : s.gpr b = B)
    (ha : addr B o = a) (hout : InRegions s.wr a 1) (hr : (s.gpr r.reg).setWidth 8 = V)
    (k : ∀ s', Mupd s s' (s.mem.write a 1 V) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 (at_ b o) r :: is)) s Q := by
  subst ha hr
  exact VG.Proof.Modes.X86.wp_st8 hb hout fun s' u => k s' (by rw [← writeW_byte8]; exact u)

theorem w_add {d r : Reg} {V W : BitVec 32} (hd : s.gpr d = V) (hr : s.gpr r = W)
    (k : ∀ s', Upd s s' d (V + W) → WP isa (.block is) s' Q) : WP isa (.block (.alu .add d (.reg r) :: is)) s Q := by
  subst hd hr; exact wp_add fun s' u _ => k s' u

theorem w_addi {d : Reg} {n : Nat} {V : BitVec 32} (hd : s.gpr d = V)
    (k : ∀ s', Upd s s' d (V + BitVec.ofNat 32 n) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (imm n) :: is)) s Q := by
  subst hd; exact wp_addi k

theorem w_andi {d : Reg} {n : Nat} {V : BitVec 32} (hd : s.gpr d = V)
    (k : ∀ s', Upd s s' d (V &&& BitVec.ofNat 32 n) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (imm n) :: is)) s Q := by
  subst hd; exact wp_andi k

theorem w_xor {d r : Reg} {V W : BitVec 32} (hd : s.gpr d = V) (hr : s.gpr r = W)
    (k : ∀ s', Upd s s' d (V ^^^ W) → WP isa (.block is) s' Q) : WP isa (.block (.alu .xor d (.reg r) :: is)) s Q := by
  subst hd hr; exact wp_xor k

end

/-! ## The byte the exchange took out, and the second pass -/

/-- The working space at an offset. -/
def sc (Sc : BitVec 32) (o : Nat) : Addr := Sc.setWidth 64 + BitVec.ofNat 64 o

theorem sc_addr {Sc : BitVec 32} {o : Nat} (sfit : Sc.toNat + 64 ≤ 2 ^ 32) (ho : o < 64) : addr Sc o = sc Sc o :=
  addr_eq (by omega)

/-- The byte `n` of a vector, brought to its byte 0. -/
theorem byte_sel (A : BitVec 128) {n : Nat} (hn : n < 16) :
    byte (XBinOp.eval .pshufb A ((0 : BitVec 96) ++ (BitVec.ofNat 8 n).setWidth 32)) 0 = byte A n := by
  obtain ⟨hm, he⟩ := nib_facts n hn
  rw [byte_pshufb _ _ (by decide), byte_movd _ (by decide), ite_eq_left rfl, hm, ite_eq_right (by decide), he]

/-- The first byte a `movq` stores. -/
theorem movq_byte (m : Mem) (q : Addr) (V : BitVec 128) : (m.writeW q (V.extractLsb' 0 64)) q = byte V 0 := by
  have h := writeW_byte m q (V.extractLsb' 0 64) (k := 0) (by decide) (by decide)
  rw [show q + BitVec.ofNat 64 0 = q from BitVec.add_zero q, extract_extract _ _ _ _ _ (by decide)] at h
  exact h

/-- The word at `scratch[24]` is apart from the eight bytes at `scratch[16]`. -/
theorem si_slot (m : Mem) (Sc : BitVec 32) (q : BitVec 64) :
    (m.writeW (sc Sc 16) q).readW (sc Sc 24) 32 = m.readW (sc Sc 24) 32 :=
  Mem.readW_writeW_sep (show Mem.Sep _ (32 / 8) _ (64 / 8) from
    Offset.sep (Sc.setWidth 64) (d := 24) (n := 4) (e := 16) (k := 8) (.inr (by decide)) (by decide) (by decide))
    (by decide)

/-- `sj`: `eax` is what the byte `j` held before the exchange. -/
theorem sj_wp {s : State} {Sc : BitVec 32} {j a b : Byte} {is : List Instr} {Q : State → Prop}
    (hbp : s.gpr .ebp = j.setWidth 32)
    (hacc : ∀ l < 16, byte (s.xmm .xmm3) l = if l = j.toNat % 16 then b ^^^ a else 0#8)
    (ha16 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4) (hv16 : s.mem.readW (addr (s.gpr .esp) 16) 32 = Sc)
    (sfit : Sc.toNat + 64 ≤ 2 ^ 32) (hw : InRegions s.wr (Sc.setWidth 64) 64)
    (hsi : s.mem.readW (sc Sc 24) 32 = a.setWidth 32)
    (k : ∀ s' (q : BitVec 64), s'.gpr .eax = b.setWidth 32 → s'.gpr .edx = Sc →
      (∀ r, r ≠ .eax → r ≠ .edx → s'.gpr r = s.gpr r) → s'.mem = s.mem.writeW (sc Sc 16) q → s'.rd = s.rd →
      s'.wr = s.wr → s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (sj ++ is)) s Q := by
  have hj := j.isLt
  obtain hrw : ∀ o k, o + k ≤ 64 → InRegions s.wr (sc Sc o) k := fun o k h =>
    region_offset _ _ _ _ _ (by omega) h hw
  obtain hrr : ∀ o k, o + k ≤ 64 → InRegions (s.rd ++ s.wr) (sc Sc o) k := fun o k h => by
    obtain ⟨R, hR, hc⟩ := hrw o k h
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  simp only [sj, List.cons_append, List.nil_append]
  refine g_mov hbp fun s₁ u₁ => ?_
  refine g_andi u₁.gpr fun s₂ u₂ => ?_
  refine x_movd u₂.gpr fun s₃ u₃ => ?_
  refine x_bin (show s₃.xmm .xmm3 = s.xmm .xmm3 by rw [u₃.other _ (by decide), u₂.xmm, u₁.xmm]) u₃.xmm
    fun s₄ u₄ => ?_
  refine g_ld (show s₄.gpr .esp = s.gpr .esp by rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)])
    rfl (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact ha16)
    (show s₄.mem.readW _ 32 = Sc by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact hv16) fun s₅ u₅ => ?_
  refine m_movq u₅.gpr (show addr Sc sSlot = sc Sc 16 from sc_addr sfit (by decide))
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hrw 16 8 (by decide))
    ((congrFun u₅.xmm _).trans u₄.xmm) fun s₆ u₆ => ?_
  obtain m₆ : s₆.mem = s.mem.writeW (sc Sc 16) ((XBinOp.eval .pshufb (s.xmm .xmm3)
      ((0 : BitVec 96) ++ (j.setWidth 32 &&& BitVec.ofNat 32 15))).extractLsb' 0 64) := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain rd₆ : s₆.rd = s.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain dx₆ : s₆.gpr .edx = Sc := (congrFun u₆.gpr _).trans u₅.gpr
  refine g_movzx dx₆ (show addr Sc sSlot = sc Sc 16 from sc_addr sfit (by decide))
    (by rw [rd₆, wr₆]; exact hrr 16 1 (by decide))
    (show s₆.mem (sc Sc 16) = b ^^^ a by
      rw [m₆, movq_byte, lo_reg, byte_sel _ (by omega), hacc _ (by omega), ite_eq_left rfl]) fun s₇ u₇ => ?_
  refine w_xm u₇.gpr ((u₇.other _ (by decide)).trans dx₆) (show addr Sc sSi = sc Sc 24 from sc_addr sfit (by decide))
    (by rw [u₇.rd, u₇.wr, rd₆, wr₆]; exact hrr 24 4 (by decide))
    (show s₇.mem.readW (sc Sc 24) 32 = a.setWidth 32 by rw [u₇.mem, m₆, si_slot]; exact hsi) fun s₈ u₈ => ?_
  refine k s₈ ((XBinOp.eval .pshufb (s.xmm .xmm3)
    ((0 : BitVec 96) ++ (j.setWidth 32 &&& BitVec.ofNat 32 15))).extractLsb' 0 64) ?_ ?_ (fun r h0 h1 => ?_) ?_ ?_ ?_ ?_
  · rw [u₈.gpr, xor_byte32, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide)]; exact dx₆
  · rw [u₈.other _ h0, u₇.other _ h0, u₆.gpr, u₅.other _ h1, u₄.gpr, u₃.gpr, u₂.other _ h0, u₁.other _ h0]
  · rw [u₈.mem, u₇.mem]; exact m₆
  · rw [u₈.rd, u₇.rd]; exact rd₆
  · rw [u₈.wr, u₇.wr]; exact wr₆
  · rw [u₈.syms, u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]

/-- A row of the second pass: `ar` is `br` a byte down, with the row's byte
`n` on top. -/
theorem readRow_wp {s : State} {P : BitVec 32} {n r : Nat} {ar br : XReg} {is : List Instr} {Q : State → Prop}
    (hr : r < 16) (hn : n < 16) (hab : ar ≠ br) (ha2 : ar ≠ .xmm2) (hdi : s.gpr .edi = P)
    (fit : P.toNat + 256 ≤ 2 ^ 32) (hrg : InRegions (s.rd ++ s.wr) (P.setWidth 64) 256)
    (h2 : s.xmm .xmm2 = (0 : BitVec 96) ++ (BitVec.ofNat 8 n).setWidth 32)
    (k : ∀ s', (∀ l < 16, byte (s'.xmm ar) l = if l = 15 then
          s.mem (P.setWidth 64 + BitVec.ofNat 64 (16 * r + n)) else byte (s.xmm br) (l + 1)) →
        (∀ x, x ≠ ar → s'.xmm x = s.xmm x) → s'.mem = s.mem → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
        s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (readRow ar br r ++ is)) s Q := by
  simp only [readRow, List.cons_append, List.nil_append]
  refine x_ld hdi (addr_eq (by omega)) (region_offset _ _ _ _ _ (by omega) (by omega) hrg) rfl fun s₁ u₁ => ?_
  refine x_bin u₁.xmm ((u₁.other _ ha2.symm).trans h2) fun s₂ u₂ => ?_
  refine x_palignr u₂.xmm ((u₂.other _ hab.symm).trans (u₁.other _ hab.symm)) fun s₃ u₃ => ?_
  refine k s₃ (fun l hl => ?_) (fun x hx => ?_) ?_ ?_ ?_ ?_ ?_
  · rw [u₃.xmm, byte_align1 _ _ hl, byte_sel _ hn, byte_row _ _ hn, Offset.add_add]
  · rw [u₃.other _ hx, u₂.other _ hx, u₁.other _ hx]
  · rw [u₃.mem, u₂.mem, u₁.mem]
  · rw [u₃.gpr, u₂.gpr, u₁.gpr]
  · rw [u₃.rd, u₂.rd, u₁.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr]
  · rw [u₃.syms, u₂.syms, u₁.syms]

/-- The second pass, after the rows before the row `r` (`r` even): the top
`r` bytes of `xmm3` are their bytes `n`. -/
structure RdI (s₀ : State) (P : BitVec 32) (n r : Nat) (t : State) : Prop where
  col : ∀ q < r, ∀ l, l + r = 16 + q →
    byte (t.xmm .xmm3) l = s₀.mem (P.setWidth 64 + BitVec.ofNat 64 (16 * q + n))
  x2 : t.xmm .xmm2 = s₀.xmm .xmm2
  mem : t.mem = s₀.mem
  gpr : t.gpr = s₀.gpr
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  syms : t.syms = s₀.syms

theorem readPair_wp {s₀ s : State} {P : BitVec 32} {n p : Nat} {is : List Instr} {Q : State → Prop} (hp : p < 8)
    (hn : n < 16) (hdi : s₀.gpr .edi = P) (fit : P.toNat + 256 ≤ 2 ^ 32)
    (hrg : InRegions (s₀.rd ++ s₀.wr) (P.setWidth 64) 256)
    (h2 : s₀.xmm .xmm2 = (0 : BitVec 96) ++ (BitVec.ofNat 8 n).setWidth 32) (h : RdI s₀ P n (2 * p) s)
    (k : ∀ s', RdI s₀ P n (2 * p + 2) s' → WP isa (.block is) s' Q) :
    WP isa (.block (readPair p ++ is)) s Q := by
  rw [readPair, List.append_assoc]
  refine readRow_wp (r := 2 * p) (by omega) hn (by decide) (by decide) (by rw [h.gpr]; exact hdi) fit
    (by rw [h.rd, h.wr]; exact hrg) (h.x2.trans h2) fun s₁ c₁ x₁ m₁ g₁ rd₁ wr₁ sy₁ => ?_
  refine readRow_wp (r := 2 * p + 1) (by omega) hn (by decide) (by decide) (by rw [g₁, h.gpr]; exact hdi) fit
    (by rw [rd₁, wr₁, h.rd, h.wr]; exact hrg) ((x₁ _ (by decide)).trans (h.x2.trans h2))
    fun s₂ c₂ x₂ m₂ g₂ rd₂ wr₂ sy₂ => ?_
  refine k s₂ ⟨fun q hq l hl => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c₂ l (by omega), m₁, h.mem]
    by_cases e : q = 2 * p + 1
    · subst e
      rw [ite_eq_left (by omega)]
    · rw [ite_eq_right (by omega), c₁ (l + 1) (by omega), h.mem]
      by_cases e' : q = 2 * p
      · subst e'
        rw [ite_eq_left (by omega)]
      · rw [ite_eq_right (by omega)]
        exact h.col q (by omega) _ (by omega)
  · rw [x₂ _ (by decide), x₁ _ (by decide)]; exact h.x2
  · rw [m₂, m₁]; exact h.mem
  · rw [g₂, g₁]; exact h.gpr
  · rw [rd₂, rd₁]; exact h.rd
  · rw [wr₂, wr₁]; exact h.wr
  · rw [sy₂, sy₁]; exact h.syms

theorem readFrom_wp {s₀ : State} {P : BitVec 32} {n : Nat} {is : List Instr} {Q : State → Prop} (hn : n < 16)
    (hdi : s₀.gpr .edi = P) (fit : P.toNat + 256 ≤ 2 ^ 32) (hrg : InRegions (s₀.rd ++ s₀.wr) (P.setWidth 64) 256)
    (h2 : s₀.xmm .xmm2 = (0 : BitVec 96) ++ (BitVec.ofNat 8 n).setWidth 32)
    (k : ∀ s', RdI s₀ P n 16 s' → WP isa (.block is) s' Q) :
    ∀ (c p : Nat) (s : State), p + c = 8 → RdI s₀ P n (2 * p) s →
      WP isa (.block ((List.range' p c).flatMap readPair ++ is)) s Q
  | 0, p, s, e, h => by
    obtain rfl : p = 8 := by omega
    exact k s h
  | c + 1, p, s, e, h => by
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    exact readPair_wp (by omega) hn hdi fit hrg h2 h fun s' h' =>
      readFrom_wp hn hdi fit hrg h2 k c (p + 1) s' (by omega) (by rw [Nat.mul_succ]; exact h')

/-- The second pass: byte `q` of `xmm3` is the byte `n` of the row `q`. -/
theorem readRows_wp {s : State} {P : BitVec 32} {n : Nat} {is : List Instr} {Q : State → Prop} (hn : n < 16)
    (hdi : s.gpr .edi = P) (fit : P.toNat + 256 ≤ 2 ^ 32) (hrg : InRegions (s.rd ++ s.wr) (P.setWidth 64) 256)
    (h2 : s.xmm .xmm2 = (0 : BitVec 96) ++ (BitVec.ofNat 8 n).setWidth 32)
    (k : ∀ s', (∀ q < 16, byte (s'.xmm .xmm3) q = s.mem (P.setWidth 64 + BitVec.ofNat 64 (16 * q + n))) →
      s'.mem = s.mem → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms →
      WP isa (.block is) s' Q) :
    WP isa (.block (readRows ++ is)) s Q := by
  rw [readRows, List.range_eq_range']
  exact readFrom_wp hn hdi fit hrg h2 (fun s' h' => k s' (fun q hq => h'.col q hq q (Nat.add_comm q 16)) h'.mem h'.gpr h'.rd h'.wr
    h'.syms) 8 0 s rfl ⟨fun q hq => absurd hq (by omega), rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The exchange and the lookup -/

/-- The exchange: the byte `j` of the table takes `a`, and `eax` what it held. -/
theorem exchange_wp {s : State} {P Sc : BitVec 32} {j a : Byte} {is : List Instr} {Q : State → Prop}
    (hbp : s.gpr .ebp = j.setWidth 32) (hcx : s.gpr .ecx = a.setWidth 32) (htb : s.gpr tbr = s.syms tableName)
    (hdi : s.gpr .edi = P) (fit : P.toNat + 256 ≤ 2 ^ 32) (hw : InRegions s.wr (P.setWidth 64) 256)
    (ha16 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4)
    (hv16 : (s.mem.write (P.setWidth 64 + BitVec.ofNat 64 j.toNat) 1 a).readW (addr (s.gpr .esp) 16) 32 = Sc)
    (sfit : Sc.toNat + 64 ≤ 2 ^ 32) (hws : InRegions s.wr (Sc.setWidth 64) 64)
    (hsi : (s.mem.write (P.setWidth 64 + BitVec.ofNat 64 j.toNat) 1 a).readW (sc Sc 24) 32 = a.setWidth 32)
    (k : ∀ s' (q : BitVec 64), s'.gpr .eax = (s.mem (P.setWidth 64 + BitVec.ofNat 64 j.toNat)).setWidth 32 →
      s'.gpr .edx = Sc → (∀ r, r ≠ .eax → r ≠ .edx → s'.gpr r = s.gpr r) →
      s'.mem = (s.mem.write (P.setWidth 64 + BitVec.ofNat 64 j.toNat) 1 a).writeW (sc Sc 16) q → s'.rd = s.rd →
      s'.wr = s.wr → s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (head ++ (swapRows ++ (sj ++ is)))) s Q := by
  refine head_wp hbp hcx htb fun s₁ X₁ S₁ g₁ m₁ rd₁ wr₁ sy₁ => ?_
  refine swapRows_wp (by rw [g₁ _ (by decide)]; exact hdi) fit (by rw [wr₁]; exact hw)
    (by rw [g₁ _ (by decide), sy₁]; exact htb) X₁ S₁ fun s₂ acc₂ m₂ g₂ rd₂ wr₂ sy₂ => ?_
  refine sj_wp (b := s.mem (P.setWidth 64 + BitVec.ofNat 64 j.toNat)) (by rw [g₂, g₁ _ (by decide)]; exact hbp)
    (by rw [← m₁]; exact acc₂) (by rw [rd₂, wr₂, rd₁, wr₁, g₂, g₁ _ (by decide)]; exact ha16)
    (by rw [m₂, g₂, g₁ _ (by decide), m₁]; exact hv16) sfit (by rw [wr₂, wr₁]; exact hws)
    (by rw [m₂, m₁]; exact hsi) fun s₃ q ax dx g₃ m₃ rd₃ wr₃ sy₃ => ?_
  exact k s₃ q ax dx (fun r h0 h1 => by rw [g₃ r h0 h1, g₂]; exact g₁ r h0) (by rw [m₃, m₂, m₁])
    (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁]) (by rw [sy₃, sy₂, sy₁])

/-- The lookup: `eax` is the byte `t` of the table. -/
theorem lookup_wp {s : State} {P Sc : BitVec 32} {t : Byte} {is : List Instr} {Q : State → Prop}
    (hax : s.gpr .eax = t.setWidth 32) (hcx : s.gpr .ecx = t.setWidth 32 &&& BitVec.ofNat 32 15)
    (hdx : s.gpr .edx = Sc) (hdi : s.gpr .edi = P) (fit : P.toNat + 256 ≤ 2 ^ 32)
    (hrg : InRegions (s.rd ++ s.wr) (P.setWidth 64) 256) (sfit : Sc.toNat + 64 ≤ 2 ^ 32)
    (hws : InRegions s.wr (Sc.setWidth 64) 64)
    (k : ∀ s' (q : BitVec 64), s'.gpr .eax = (s.mem (P.setWidth 64 + BitVec.ofNat 64 t.toNat)).setWidth 32 →
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.mem = s.mem.writeW (sc Sc 16) q → s'.rd = s.rd → s'.wr = s.wr →
      s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (.xop (.movd .xmm2 .ecx) :: .shift .shr .eax 4 :: (readRows ++
      (.xop (.movd .xmm7 .eax) :: x .pshufb .xmm3 .xmm7 :: .movqStore (at_ .edx sSlot) .xmm3 ::
        .movzx8 .eax (at_ .edx sSlot) :: is)))) s Q := by
  have ht := t.isLt
  refine x_movd hcx fun s₁ u₁ => ?_
  refine g_shr (by decide) (show s₁.gpr .eax = t.setWidth 32 by rw [u₁.gpr]; exact hax) fun s₂ u₂ => ?_
  refine readRows_wp (n := t.toNat % 16) (by omega)
    (show s₂.gpr .edi = P by rw [u₂.other _ (by decide), u₁.gpr]; exact hdi) fit
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hrg)
    (show s₂.xmm .xmm2 = (0 : BitVec 96) ++ (BitVec.ofNat 8 (t.toNat % 16)).setWidth 32 by
      rw [u₂.xmm, u₁.xmm, lo_reg]) fun s₃ col m₃ g₃ rd₃ wr₃ sy₃ => ?_
  refine x_movd (show s₃.gpr .eax = (BitVec.ofNat 8 (t.toNat / 16)).setWidth 32 by rw [g₃, u₂.gpr, hi_reg])
    fun s₄ u₄ => ?_
  refine x_bin (A := s₃.xmm .xmm3) (u₄.other _ (by decide)) u₄.xmm fun s₅ u₅ => ?_
  obtain rd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd]
  obtain wr₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr]
  obtain dx₅ : s₅.gpr .edx = Sc := by rw [u₅.gpr, u₄.gpr, g₃, u₂.other _ (by decide), u₁.gpr]; exact hdx
  refine m_movq dx₅ (show addr Sc sSlot = sc Sc 16 from sc_addr sfit (by decide))
    (by rw [wr₅]; exact region_offset _ _ _ 16 8 (by decide) (by decide) hws) u₅.xmm fun s₆ u₆ => ?_
  obtain m₆ : s₆.mem = s.mem.writeW (sc Sc 16) ((XBinOp.eval .pshufb (s₃.xmm .xmm3)
      ((0 : BitVec 96) ++ (BitVec.ofNat 8 (t.toNat / 16)).setWidth 32)).extractLsb' 0 64) := by
    rw [u₆.mem, u₅.mem, u₄.mem, m₃, u₂.mem, u₁.mem]
  refine g_movzx ((congrFun u₆.gpr _).trans dx₅) (show addr Sc sSlot = sc Sc 16 from sc_addr sfit (by decide))
    (by
      rw [u₆.rd, u₆.wr, rd₅, wr₅]
      obtain ⟨R, hR, hc⟩ := region_offset _ _ _ 16 1 (by decide) (by decide) hws
      exact ⟨R, List.mem_append_right _ hR, hc⟩)
    (show s₆.mem (sc Sc 16) = s.mem (P.setWidth 64 + BitVec.ofNat 64 t.toNat) by
      rw [m₆, movq_byte, byte_sel _ (by omega), col _ (by omega), u₂.mem, u₁.mem,
        show 16 * (t.toNat / 16) + t.toNat % 16 = t.toNat by omega]) fun s₇ u₇ => ?_
  refine k s₇ ((XBinOp.eval .pshufb (s₃.xmm .xmm3)
    ((0 : BitVec 96) ++ (BitVec.ofNat 8 (t.toNat / 16)).setWidth 32)).extractLsb' 0 64) u₇.gpr (fun r h => ?_) ?_ ?_
    ?_ ?_
  · rw [u₇.other _ h, u₆.gpr, u₅.gpr, u₄.gpr, g₃, u₂.other _ h, u₁.gpr]
  · rw [u₇.mem]; exact m₆
  · rw [u₇.rd, u₆.rd]; exact rd₅
  · rw [u₇.wr, u₆.wr]; exact wr₅
  · rw [u₇.syms, u₆.syms, u₅.syms, u₄.syms, sy₃, u₂.syms, u₁.syms]

/-! ## The pieces of an iteration -/

/-- The constants' address, at `scratch[28]`, is apart from the word at `scratch[24]`. -/
theorem tab_slot (m : Mem) (Sc : BitVec 32) (v : BitVec 32) :
    (m.writeW (sc Sc 24) v).readW (sc Sc 28) 32 = m.readW (sc Sc 28) 32 :=
  Mem.readW_writeW_sep (show Mem.Sep _ (32 / 8) _ (32 / 8) from
    Offset.sep (Sc.setWidth 64) (d := 28) (n := 4) (e := 24) (k := 4) (.inr (by decide)) (by decide) (by decide))
    (by decide)

theorem inr_wr {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨R, hR, hc⟩ := h
  exact ⟨R, List.mem_append_right _ hR, hc⟩

/-- The table after an iteration's writes: its exchange, whatever the working
space holds. -/
theorem swapped_bytes (m : Mem) (p w16 w24 : Addr) (ii jj a b : Byte) (v : BitVec 32) (q : BitVec 64)
    (h16 : Mem.Sep p 256 w16 8) (h24 : Mem.Sep p 256 w24 4) {y : Nat} (hy : y < 256) :
    ((((m.writeW w24 v).write (p + BitVec.ofNat 64 jj.toNat) 1 a).writeW w16 q).write
        (p + BitVec.ofNat 64 ii.toNat) 1 b) (p + BitVec.ofNat 64 y) =
      ((m.write (p + BitVec.ofNat 64 jj.toNat) 1 a).write (p + BitVec.ofNat 64 ii.toNat) 1 b)
        (p + BitVec.ofNat 64 y) := by
  have hy' : (p + BitVec.ofNat 64 y - p).toNat < 256 := by rw [Mem.sub_ofNat_toNat p (by omega)]; exact hy
  have e16 := h16 _ hy'
  have e24 := h24 _ hy'
  simp only [write_byte]
  rw [writeW_byte_off _ _ _ _ (show 64 / 8 ≤ _ by omega), write_byte,
    writeW_byte_off _ _ _ _ (show 32 / 8 ≤ _ by omega)]

/-- `S[i]` to `ecx` and to its slot, and the constants' address to `edx`. -/
theorem loadSi_wp {s : State} {P Sc T : BitVec 32} {i : Byte} {is : List Instr} {Q : State → Prop}
    (hsi : s.gpr .esi = i.setWidth 32) (hdi : s.gpr .edi = P) (fit : P.toNat + 256 ≤ 2 ^ 32)
    (hrg : InRegions (s.rd ++ s.wr) (P.setWidth 64) 256)
    (ha16 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4) (hv16 : s.mem.readW (addr (s.gpr .esp) 16) 32 = Sc)
    (sfit : Sc.toNat + 64 ≤ 2 ^ 32) (hws : InRegions s.wr (Sc.setWidth 64) 64)
    (htab : s.mem.readW (sc Sc 28) 32 = T)
    (k : ∀ s', s'.gpr .ecx = (s.mem (P.setWidth 64 + BitVec.ofNat 64 i.toNat)).setWidth 32 → s'.gpr .edx = T →
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) →
      s'.mem = s.mem.writeW (sc Sc 24) ((s.mem (P.setWidth 64 + BitVec.ofNat 64 i.toNat)).setWidth 32) →
      s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (loadSi ++ is)) s Q := by
  have hi := i.isLt
  simp only [loadSi, List.cons_append, List.nil_append]
  refine w_mov hdi fun s₁ u₁ => ?_
  refine w_add u₁.gpr ((u₁.other _ (by decide)).trans hsi) fun s₂ u₂ => ?_
  refine w_lb u₂.gpr (idx_addr fit i)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact region_offset _ _ _ _ _ (by omega) (by omega) hrg)
    (by rw [u₂.mem, u₁.mem]) fun s₃ u₃ => ?_
  refine w_ld (show s₃.gpr .esp = s.gpr .esp by
      rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]) rfl
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact ha16)
    (show s₃.mem.readW _ 32 = Sc by rw [u₃.mem, u₂.mem, u₁.mem]; exact hv16) fun s₄ u₄ => ?_
  refine w_st u₄.gpr (show addr Sc sSi = sc Sc 24 from sc_addr sfit (by decide))
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact region_offset _ _ _ 24 4 (by decide) (by decide) hws)
    ((u₄.other _ (by decide)).trans u₃.gpr) fun s₅ u₅ => ?_
  refine w_ld (show s₅.gpr .eax = Sc by rw [u₅.gpr]; exact u₄.gpr)
    (show addr Sc sTab = sc Sc 28 from sc_addr sfit (by decide))
    (by
      rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
      exact inr_wr (region_offset _ _ _ 28 4 (by decide) (by decide) hws))
    (show s₅.mem.readW (sc Sc 28) 32 = T by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, tab_slot]; exact htab)
    fun s₆ u₆ => ?_
  refine k s₆ ?_ u₆.gpr (fun r h0 h1 h2 => ?_) ?_ ?_ ?_ ?_
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide)]; exact u₃.gpr
  · rw [u₆.other _ h2, u₅.gpr, u₄.other _ h0, u₃.other _ h1, u₂.other _ h0, u₁.other _ h0]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]

/-- A stream iteration before the exchange: `i` and `j` advance. -/
theorem apply_pre_wp {s : State} {P Sc T : BitVec 32} {i j : Byte} {is : List Instr} {Q : State → Prop}
    (hsi : s.gpr .esi = i.setWidth 32) (hbp : s.gpr .ebp = j.setWidth 32) (hdi : s.gpr .edi = P)
    (fit : P.toNat + 256 ≤ 2 ^ 32) (hrg : InRegions (s.rd ++ s.wr) (P.setWidth 64) 256)
    (ha16 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4) (hv16 : s.mem.readW (addr (s.gpr .esp) 16) 32 = Sc)
    (sfit : Sc.toNat + 64 ≤ 2 ^ 32) (hws : InRegions s.wr (Sc.setWidth 64) 64)
    (htab : s.mem.readW (sc Sc 28) 32 = T)
    (k : ∀ s', s'.gpr .esi = (i + 1#8).setWidth 32 →
      s'.gpr .ecx = (s.mem (P.setWidth 64 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 32 →
      s'.gpr .ebp = (j + s.mem (P.setWidth 64 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 32 → s'.gpr .edx = T →
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .ebp → s'.gpr r = s.gpr r) →
      s'.mem = s.mem.writeW (sc Sc 24) ((s.mem (P.setWidth 64 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 32) →
      s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add .esi (imm 1) :: .alu .and .esi (imm 255) ::
      (loadSi ++ (.alu .add .ebp (.reg .ecx) :: .alu .and .ebp (imm 255) :: is)))) s Q := by
  refine w_addi hsi fun s₁ u₁ => ?_
  refine w_andi u₁.gpr fun s₂ u₂ => ?_
  refine loadSi_wp (i := i + 1#8) (by rw [u₂.gpr, byte_inc32])
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact hdi) fit
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hrg)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, u₂.other _ (by decide), u₁.other _ (by decide)]; exact ha16)
    (by rw [u₂.mem, u₁.mem, u₂.other _ (by decide), u₁.other _ (by decide)]; exact hv16) sfit
    (by rw [u₂.wr, u₁.wr]; exact hws) (show s₂.mem.readW (sc Sc 28) 32 = T by rw [u₂.mem, u₁.mem]; exact htab)
    fun s₃ cx₃ dx₃ g₃ m₃ rd₃ wr₃ sy₃ => ?_
  rw [u₂.mem, u₁.mem] at cx₃ m₃
  refine w_add (show s₃.gpr .ebp = j.setWidth 32 by
      rw [g₃ _ (by decide) (by decide) (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact hbp)
    cx₃ fun s₄ u₄ => ?_
  refine w_andi u₄.gpr fun s₅ u₅ => ?_
  refine k s₅ ?_ ?_ ?_ ?_ (fun r h0 h1 h2 h3 h4 => ?_) ?_ ?_ ?_ ?_
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide) (by decide) (by decide), u₂.gpr,
      byte_inc32]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide)]; exact cx₃
  · rw [u₅.gpr, byte_add32]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide)]; exact dx₃
  · rw [u₅.other _ h4, u₄.other _ h4, g₃ _ h0 h1 h2, u₂.other _ h3, u₁.other _ h3]
  · rw [u₅.mem, u₄.mem]; exact m₃
  · rw [u₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr]
  · rw [u₅.syms, u₄.syms, sy₃, u₂.syms, u₁.syms]

/-- A stream iteration between the exchange and the lookup: the byte `i` of
the table takes what the byte `j` held, and `eax` the index of the keystream
byte. -/
theorem apply_mid_wp {s : State} {P Sc : BitVec 32} {i a b : Byte} {is : List Instr} {Q : State → Prop}
    (hax : s.gpr .eax = b.setWidth 32) (hdx : s.gpr .edx = Sc) (hdi : s.gpr .edi = P)
    (hsi : s.gpr .esi = i.setWidth 32) (fit : P.toNat + 256 ≤ 2 ^ 32) (hw : InRegions s.wr (P.setWidth 64) 256)
    (sfit : Sc.toNat + 64 ≤ 2 ^ 32) (hws : InRegions s.wr (Sc.setWidth 64) 64)
    (hv : (s.mem.write (P.setWidth 64 + BitVec.ofNat 64 i.toNat) 1 b).readW (sc Sc 24) 32 = a.setWidth 32)
    (k : ∀ s', s'.gpr .eax = (b + a).setWidth 32 → s'.gpr .ecx = (b + a).setWidth 32 &&& BitVec.ofNat 32 15 →
      (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) →
      s'.mem = s.mem.write (P.setWidth 64 + BitVec.ofNat 64 i.toNat) 1 b → s'.rd = s.rd → s'.wr = s.wr →
      s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (.mov .ecx (.reg .edi) :: .alu .add .ecx (.reg .esi) :: .store8 (at_ .ecx 0) .al ::
      .alu .add .eax (.mem (at_ .edx sSi)) :: .alu .and .eax (imm 255) :: .mov .ecx (.reg .eax) ::
      .alu .and .ecx (imm 15) :: is)) s Q := by
  have hi := i.isLt
  refine w_mov hdi fun s₁ u₁ => ?_
  refine w_add u₁.gpr ((u₁.other _ (by decide)).trans hsi) fun s₂ u₂ => ?_
  refine w_sb (r := .al) u₂.gpr (idx_addr fit i)
    (by rw [u₂.wr, u₁.wr]; exact region_offset _ _ _ _ _ (by omega) (by omega) hw)
    (show (s₂.gpr .eax).setWidth 8 = b by
      rw [u₂.other _ (by decide), u₁.other _ (by decide), hax, low_byte32]) fun s₃ u₃ => ?_
  refine w_am (show s₃.gpr .eax = b.setWidth 32 by
      rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]; exact hax)
    (show s₃.gpr .edx = Sc by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]; exact hdx)
    (show addr Sc sSi = sc Sc 24 from sc_addr sfit (by decide))
    (by
      rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
      exact inr_wr (region_offset _ _ _ 24 4 (by decide) (by decide) hws))
    (show s₃.mem.readW (sc Sc 24) 32 = a.setWidth 32 by rw [u₃.mem, u₂.mem, u₁.mem]; exact hv) fun s₄ u₄ => ?_
  refine w_andi u₄.gpr fun s₅ u₅ => ?_
  refine w_mov u₅.gpr fun s₆ u₆ => ?_
  refine w_andi u₆.gpr fun s₇ u₇ => ?_
  refine k s₇ ?_ ?_ (fun r h0 h1 => ?_) ?_ ?_ ?_ ?_
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, byte_add32]
  · rw [u₇.gpr, byte_add32]
  · rw [u₇.other _ h1, u₆.other _ h1, u₅.other _ h0, u₄.other _ h0, u₃.gpr, u₂.other _ h1, u₁.other _ h1]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]

/-- A stream iteration after the lookup: the data byte takes the keystream
byte, and the count advances. -/
theorem apply_tail_wp {s : State} {D L : BitVec 32} {kb : Byte} {n : Nat} {Q : State → Prop}
    (hax : s.gpr .eax = kb.setWidth 32) (hbx : s.gpr .ebx = BitVec.ofNat 32 n) (hn : n < L.toNat)
    (dfit : D.toNat + L.toNat ≤ 2 ^ 32) (ha8 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4)
    (hv8 : s.mem.readW (addr (s.gpr .esp) 8) 32 = D)
    (hd : InRegions s.wr (D.setWidth 64 + BitVec.ofNat 64 n) 1)
    (ha12 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 12) 4)
    (hv12 : ∀ v, (s.mem.write (D.setWidth 64 + BitVec.ofNat 64 n) 1 v).readW (addr (s.gpr .esp) 12) 32 = L)
    (k : ∀ s', s'.mem = s.mem.write (D.setWidth 64 + BitVec.ofNat 64 n) 1
        (s.mem (D.setWidth 64 + BitVec.ofNat 64 n) ^^^ kb) → s'.gpr .ebx = BitVec.ofNat 32 (n + 1) →
      s'.zf = some (BitVec.ofNat 32 (n + 1) - L == 0#32) → (∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .ebx → s'.gpr r = s.gpr r) →
      s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms → Q s') :
    WP isa (.block [.mov .ecx (.mem (at_ .esp 8)), .alu .add .ecx (.reg .ebx), .movzx8 .edx (at_ .ecx 0),
      .alu .xor .edx (.reg .eax), .store8 (at_ .ecx 0) .dl, .alu .add .ebx (imm 1),
      .mov .edx (.mem (at_ .esp 12)), .alu .cmp .ebx (.reg .edx)]) s Q := by
  refine w_ld rfl rfl ha8 hv8 fun s₁ u₁ => ?_
  refine w_add u₁.gpr ((u₁.other _ (by decide)).trans hbx) fun s₂ u₂ => ?_
  refine w_lb u₂.gpr (key_addr dfit hn) (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact inr_wr hd)
    (by rw [u₂.mem, u₁.mem]) fun s₃ u₃ => ?_
  refine w_xor u₃.gpr (show s₃.gpr .eax = kb.setWidth 32 by
      rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact hax) fun s₄ u₄ => ?_
  refine w_sb (r := .dl) (show s₄.gpr .ecx = D + BitVec.ofNat 32 n by
      rw [u₄.other _ (by decide), u₃.other _ (by decide)]; exact u₂.gpr) (key_addr dfit hn)
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hd)
    (show (s₄.gpr .edx).setWidth 8 = s.mem (D.setWidth 64 + BitVec.ofNat 64 n) ^^^ kb by rw [u₄.gpr, low_xor32])
    fun s₅ u₅ => ?_
  refine w_addi (show s₅.gpr .ebx = BitVec.ofNat 32 n by
      rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
      exact hbx) fun s₆ u₆ => ?_
  obtain sp₆ : s₆.gpr .esp = s.gpr .esp := by
    rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]
  refine w_ld sp₆ rfl
    (by
      rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
      exact ha12)
    (show s₆.mem.readW _ 32 = L by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact hv12 _)
    fun s₇ u₇ => ?_
  refine wp_cmp fun s₈ u₈ _ z₈ => WP.block_nil ?_
  refine k s₈ ?_ ?_ ?_ (fun r h0 h1 h2 => ?_) ?_ ?_ ?_
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.gpr, ← BitVec.ofNat_add]
  · rw [z₈, u₇.gpr, u₇.other _ (by decide), u₆.gpr, ← BitVec.ofNat_add]
    rfl
  · rw [u₈.gpr, u₇.other _ h1, u₆.other _ h2, u₅.gpr, u₄.other _ h1, u₃.other _ h1, u₂.other _ h0, u₁.other _ h0]
  · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₈.syms, u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]

/-! ## A stream iteration -/

/-- What an iteration writes but data: the table, and twelve bytes of the
working space. -/
def workRegions (P Sc : BitVec 32) : List Region := [⟨P.setWidth 64, 256⟩, ⟨sc Sc 16, 12⟩]

/-- What the stream loop writes: the table, twelve bytes of the working space
and the data. -/
def stepRegions (P D L Sc : BitVec 32) : List Region :=
  [⟨P.setWidth 64, 256⟩, ⟨sc Sc 16, 12⟩, ⟨D.setWidth 64, L.toNat⟩]

theorem step_sub_apply (P D L Sc : BitVec 32) :
    ∀ r ∈ stepRegions P D L Sc, ∃ r' ∈ applyRegions P D L Sc, Region.Sub r r' := by
  intro r hr
  simp only [stepRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), Offset.sub_base _ (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (Nat.le_refl _)⟩

theorem work_mem_step (P D L Sc : BitVec 32) : ∀ r ∈ workRegions P Sc, r ∈ stepRegions P D L Sc := by
  intro r hr
  simp only [workRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

/-- One iteration of the stream loop, by its memory: the table's exchange,
the data byte, and nothing else but twelve bytes of the working space. -/
theorem apply_step {s₀ t : State} {P D L Sc : BitVec 32} (hp : ApplyPre s₀ P D L Sc) (i j : Byte) {n : Nat}
    (hf : Frame (applyRegions P D L Sc) s₀.mem t.mem) (hsp : t.gpr .esp = s₀.gpr .esp) (hrd : t.rd = s₀.rd)
    (hwr : t.wr = s₀.wr) (hdi : t.gpr .edi = P) (hsi : t.gpr .esi = i.setWidth 32)
    (hbp : t.gpr .ebp = j.setWidth 32) (hbx : t.gpr .ebx = BitVec.ofNat 32 n) (hn : n < L.toNat)
    (htab : t.mem.readW (sc Sc 28) 32 = t.syms tableName) :
    let p := P.setWidth 64
    let ii := i + 1#8
    let a := t.mem (p + BitVec.ofNat 64 ii.toNat)
    let jj := j + a
    let b := t.mem (p + BitVec.ofNat 64 jj.toNat)
    let swapped := (t.mem.write (p + BitVec.ofNat 64 jj.toNat) 1 a).write (p + BitVec.ofNat 64 ii.toNat) 1 b
    WP isa (.block applyStep) t fun u =>
      (∀ y < 256, u.mem (p + BitVec.ofNat 64 y) = swapped (p + BitVec.ofNat 64 y)) ∧
      u.mem (D.setWidth 64 + BitVec.ofNat 64 n) =
        t.mem (D.setWidth 64 + BitVec.ofNat 64 n) ^^^ swapped (p + BitVec.ofNat 64 (a + b).toNat) ∧
      (∀ x, ¬ (x - p).toNat < 256 → ¬ (x - sc Sc 16).toNat < 12 → x ≠ D.setWidth 64 + BitVec.ofNat 64 n →
        u.mem x = t.mem x) ∧
      Frame (stepRegions P D L Sc) t.mem u.mem ∧
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.syms = t.syms ∧ u.gpr .edi = P ∧ u.gpr .esp = t.gpr .esp ∧
      u.gpr .esi = ii.setWidth 32 ∧ u.gpr .ebp = jj.setWidth 32 ∧ u.gpr .ebx = BitVec.ofNat 32 (n + 1) ∧
      u.zf = some (BitVec.ofNat 32 (n + 1) - L == 0#32) := by
  intro p ii a jj b swapped
  have hLlt := L.isLt
  obtain fit : P.toNat + 256 ≤ 2 ^ 32 := by have := hp.ctxFit; omega
  obtain hT : InRegions t.wr (P.setWidth 64) 256 := by
    rw [hwr]
    obtain ⟨R, hR, hc⟩ := hp.ctx
    exact ⟨R, hR, by simp only [Region.Contains] at hc ⊢; omega⟩
  obtain hS : InRegions t.wr (Sc.setWidth 64) 64 := by rw [hwr]; exact hp.scratch
  obtain hDn : InRegions t.wr (D.setWidth 64 + BitVec.ofNat 64 n) 1 := by
    rw [hwr]; exact region_offset _ _ _ n 1 (by omega) (by omega) hp.data
  have argin (k : Nat) (hk : k < 4) : InRegions (t.rd ++ t.wr) (argAddr s₀ k) 4 := by
    rw [hrd, hwr]; exact hp.arg_in hk
  have hW1 : (⟨p, 256⟩ : Region) ∈ workRegions P Sc := List.mem_cons_self
  have hW2 : (⟨sc Sc 16, 12⟩ : Region) ∈ workRegions P Sc := List.mem_cons_of_mem _ List.mem_cons_self
  have wsub : ∀ r ∈ workRegions P Sc, ∃ r' ∈ applyRegions P D L Sc, Region.Sub r r' := fun r hr =>
    step_sub_apply P D L Sc r (work_mem_step P D L Sc r hr)
  have cT (y : Byte) : (⟨p, 256⟩ : Region).Contains (p + BitVec.ofNat 64 y.toNat) 1 :=
    Offset.contains_base _ (by have := y.isLt; omega) (by have := y.isLt; omega)
  have c24 : (⟨sc Sc 16, 12⟩ : Region).Contains (sc Sc 24) (32 / 8) :=
    Offset.contains _ (by decide) (by decide) (by decide)
  have c16 : (⟨sc Sc 16, 12⟩ : Region).Contains (sc Sc 16) (64 / 8) :=
    Offset.contains _ (by decide) (by decide) (by decide)
  obtain sT16 : Mem.Sep p 256 (sc Sc 16) 8 :=
    sep_of_sub hp.ctxScratch (contains_prefix p (n := 256) (k := 258) (by decide))
      (Offset.contains_base (Sc.setWidth 64) (d := 16) (n := 8) (k := 64) (by decide) (by decide))
  obtain sT24 : Mem.Sep p 256 (sc Sc 24) 4 :=
    sep_of_sub hp.ctxScratch (contains_prefix p (n := 256) (k := 258) (by decide))
      (Offset.contains_base (Sc.setWidth 64) (d := 24) (n := 4) (k := 64) (by decide) (by decide))
  have s24T (y : Byte) : Mem.Sep (sc Sc 24) 4 (p + BitVec.ofNat 64 y.toNat) 1 :=
    sep_of_sub hp.ctxScratch.symm (Offset.contains_base _ (by decide) (by decide))
      (Offset.contains_base _ (by have := y.isLt; omega) (by have := y.isLt; omega))
  have inT (y : Nat) (hy : y < 256) : (p + BitVec.ofNat 64 y - p).toNat < 256 := by
    rw [Mem.sub_ofNat_toNat p (by omega)]; exact hy
  obtain hdw : ∀ r ∈ workRegions P Sc, Region.Disjoint ⟨D.setWidth 64, L.toNat⟩ r := by
    intro r hr
    simp only [workRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.ctxData.sub_left (Region.sub_prefix (by decide))).symm
    · exact (hp.dataScratch.symm.sub_left (Offset.sub_base _ (by decide))).symm
  simp only [applyStep, List.append_assoc, List.cons_append, List.nil_append]
  refine apply_pre_wp hsi hbp hdi fit (inr_wr hT) (by rw [hsp]; exact argin 3 (by decide))
    (by rw [hsp]; exact (hp.arg_eq hf (i := 3) (by decide)).trans hp.aS) hp.scratchFit hS htab
    fun s₁ si₁ cx₁ bp₁ dx₁ g₁ m₁ rd₁ wr₁ sy₁ => ?_
  obtain di₁ : s₁.gpr .edi = P := (g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hdi
  obtain sp₁ : s₁.gpr .esp = s₀.gpr .esp :=
    (g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsp
  obtain bx₁ : s₁.gpr .ebx = BitVec.ofNat 32 n :=
    (g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbx
  obtain f₁ : Frame (workRegions P Sc) t.mem s₁.mem := by
    rw [m₁]; exact (Frame.refl _ _).writeW hW2 _ c24
  obtain f₂ : Frame (workRegions P Sc) t.mem (s₁.mem.write (p + BitVec.ofNat 64 jj.toNat) 1 a) :=
    f₁.write hW1 _ (cT jj)
  obtain hb : s₁.mem (p + BitVec.ofNat 64 jj.toNat) = b := by
    have := sT24 _ (inT _ jj.isLt)
    rw [m₁, writeW_byte_off _ _ _ _ (show 32 / 8 ≤ _ by omega)]
  refine exchange_wp (j := jj) (a := a) bp₁ cx₁ (by rw [sy₁]; exact dx₁) di₁ fit (by rw [wr₁]; exact hT)
    (by rw [rd₁, wr₁, sp₁]; exact argin 3 (by decide))
    (by rw [sp₁]; exact (hp.arg_eq (hf.trans (f₂.sub wsub)) (i := 3) (by decide)).trans hp.aS) hp.scratchFit
    (by rw [wr₁]; exact hS) (by rw [readW_write1 (s24T jj), m₁, Mem.readW_writeW_self32])
    fun s₂ q ax₂ dx₂ g₂ m₂ rd₂ wr₂ sy₂ => ?_
  rw [hb] at ax₂
  obtain di₂ : s₂.gpr .edi = P := (g₂ _ (by decide) (by decide)).trans di₁
  obtain sp₂ : s₂.gpr .esp = s₀.gpr .esp := (g₂ _ (by decide) (by decide)).trans sp₁
  obtain bx₂ : s₂.gpr .ebx = BitVec.ofNat 32 n := (g₂ _ (by decide) (by decide)).trans bx₁
  obtain si₂ : s₂.gpr .esi = ii.setWidth 32 := (g₂ _ (by decide) (by decide)).trans si₁
  obtain bp₂ : s₂.gpr .ebp = jj.setWidth 32 := (g₂ _ (by decide) (by decide)).trans bp₁
  obtain f₃ : Frame (workRegions P Sc) t.mem s₂.mem := by rw [m₂]; exact f₂.writeW hW2 _ c16
  refine apply_mid_wp (i := ii) (a := a) (b := b) ax₂ dx₂ di₂ si₂ fit (by rw [wr₂, wr₁]; exact hT) hp.scratchFit
    (by rw [wr₂, wr₁]; exact hS)
    (by rw [readW_write1 (s24T ii), m₂, si_slot, readW_write1 (s24T jj), m₁, Mem.readW_writeW_self32])
    fun s₃ ax₃ cx₃ g₃ m₃ rd₃ wr₃ sy₃ => ?_
  obtain di₃ : s₃.gpr .edi = P := (g₃ _ (by decide) (by decide)).trans di₂
  obtain sp₃ : s₃.gpr .esp = s₀.gpr .esp := (g₃ _ (by decide) (by decide)).trans sp₂
  obtain bx₃ : s₃.gpr .ebx = BitVec.ofNat 32 n := (g₃ _ (by decide) (by decide)).trans bx₂
  obtain si₃ : s₃.gpr .esi = ii.setWidth 32 := (g₃ _ (by decide) (by decide)).trans si₂
  obtain bp₃ : s₃.gpr .ebp = jj.setWidth 32 := (g₃ _ (by decide) (by decide)).trans bp₂
  obtain dx₃ : s₃.gpr .edx = Sc := (g₃ _ (by decide) (by decide)).trans dx₂
  obtain f₄ : Frame (workRegions P Sc) t.mem s₃.mem := by rw [m₃]; exact f₃.write hW1 _ (cT ii)
  obtain hk : s₃.mem (p + BitVec.ofNat 64 (a + b).toNat) = swapped (p + BitVec.ofNat 64 (a + b).toNat) := by
    rw [m₃, m₂, m₁]
    exact swapped_bytes t.mem p (sc Sc 16) (sc Sc 24) ii jj a b _ q sT16 sT24 (a + b).isLt
  refine lookup_wp (t := a + b) (by rw [BitVec.add_comm]; exact ax₃) (by rw [BitVec.add_comm]; exact cx₃) dx₃ di₃
    fit (by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact inr_wr hT) hp.scratchFit
    (by rw [wr₃, wr₂, wr₁]; exact hS) fun s₄ q' ax₄ g₄ m₄ rd₄ wr₄ sy₄ => ?_
  rw [hk] at ax₄
  obtain sp₄ : s₄.gpr .esp = s₀.gpr .esp := (g₄ _ (by decide)).trans sp₃
  obtain f₅ : Frame (workRegions P Sc) t.mem s₄.mem := by rw [m₄]; exact f₄.writeW hW2 _ c16
  obtain rd₄' : s₄.rd = t.rd := by rw [rd₄, rd₃, rd₂, rd₁]
  obtain wr₄' : s₄.wr = t.wr := by rw [wr₄, wr₃, wr₂, wr₁]
  have hmD : (⟨D.setWidth 64, L.toNat⟩ : Region) ∈ applyRegions P D L Sc :=
    List.mem_cons_of_mem _ List.mem_cons_self
  have cD : (⟨D.setWidth 64, L.toNat⟩ : Region).Contains (D.setWidth 64 + BitVec.ofNat 64 n) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  refine apply_tail_wp (D := D) (L := L) ax₄ ((g₄ _ (by decide)).trans bx₃) hn hp.dataFit
    (by rw [rd₄', wr₄', sp₄]; exact argin 1 (by decide))
    (by rw [sp₄]; exact (hp.arg_eq (hf.trans (f₅.sub wsub)) (i := 1) (by decide)).trans hp.aD)
    (by rw [wr₄']; exact hDn) (by rw [rd₄', wr₄', sp₄]; exact argin 2 (by decide))
    (fun v => by
      rw [sp₄]
      exact (hp.arg_eq (hf.trans ((f₅.sub wsub).write hmD _ cD)) (i := 2) (by decide)).trans hp.aL)
    fun s₅ m₅ bx₅ z₅ g₅ rd₅ wr₅ sy₅ => ?_
  obtain hd : s₄.mem (D.setWidth 64 + BitVec.ofNat 64 n) = t.mem (D.setWidth 64 + BitVec.ofNat 64 n) :=
    f₅.bytes (R := ⟨D.setWidth 64, L.toNat⟩) hdw (show L.toNat ≤ 2 ^ 64 by omega) hn
  obtain sTD : Mem.Sep p 256 (D.setWidth 64 + BitVec.ofNat 64 n) 1 :=
    sep_of_sub (hp.ctxData.sub_left (Region.sub_prefix (by decide))) (Region.contains_self _ _) cD
  refine ⟨fun y hy => ?_, ?_, fun x hx1 hx2 hx3 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, bx₅, z₅⟩
  · have h16 := sT16 _ (inT y hy)
    rw [m₅, write_byte, ite_eq_right (fun e => sTD _ (inT y hy) (by rw [e, BitVec.sub_self]; decide)), m₄,
      writeW_byte_off _ _ _ _ (show 64 / 8 ≤ _ by omega), m₃, m₂, m₁]
    exact swapped_bytes t.mem p (sc Sc 16) (sc Sc 24) ii jj a b _ q sT16 sT24 hy
  · rw [m₅, write_byte, ite_eq_left rfl, hd]
  · rw [m₅, write_byte, ite_eq_right hx3]
    have hx1' : ¬ (x - P.setWidth 64).toNat < 256 := hx1
    refine f₅ x fun r hr hc => ?_
    simp only [workRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [Region.Contains] at hc <;> omega
  · rw [m₅]
    exact (f₅.mono (work_mem_step P D L Sc)).write
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) _ cD
  · rw [rd₅]; exact rd₄'
  · rw [wr₅]; exact wr₄'
  · rw [sy₅, sy₄, sy₃, sy₂, sy₁]
  · rw [g₅ _ (by decide) (by decide) (by decide), g₄ _ (by decide)]; exact di₃
  · rw [g₅ _ (by decide) (by decide) (by decide), sp₄, hsp]
  · rw [g₅ _ (by decide) (by decide) (by decide), g₄ _ (by decide)]; exact si₃
  · rw [g₅ _ (by decide) (by decide) (by decide), g₄ _ (by decide)]; exact bp₃

/-! ## The stream loop -/

theorem table_congr {m m' : Mem} {p : Addr}
    (h : ∀ y < 256, m' (p + BitVec.ofNat 64 y) = m (p + BitVec.ofNat 64 y)) :
    (contextAt m' p).table = (contextAt m p).table := by
  apply Vector.ext
  intro k hk
  simp only [contextAt, Vector.getElem_ofFn]
  exact h k hk

/-- The iteration realizes the abstract PRGA transition. -/
theorem apply_step_table {s₀ t : State} {P D L Sc : BitVec 32} (hp : ApplyPre s₀ P D L Sc) (i j : Byte) {k : Nat}
    (hf : Frame (applyRegions P D L Sc) s₀.mem t.mem) (hsp : t.gpr .esp = s₀.gpr .esp) (hrd : t.rd = s₀.rd)
    (hwr : t.wr = s₀.wr) (hdi : t.gpr .edi = P) (hsi : t.gpr .esi = i.setWidth 32)
    (hbp : t.gpr .ebp = j.setWidth 32) (hbx : t.gpr .ebx = BitVec.ofNat 32 k) (hk : k < L.toNat)
    (htab : t.mem.readW (sc Sc 28) 32 = t.syms tableName) :
    let next := step { table := (contextAt t.mem (P.setWidth 64)).table, i, j }
    WP isa (.block applyStep) t fun u =>
      (contextAt u.mem (P.setWidth 64)).table = next.1.table ∧
      u.gpr .esi = next.1.i.setWidth 32 ∧ u.gpr .ebp = next.1.j.setWidth 32 ∧
      u.mem (D.setWidth 64 + BitVec.ofNat 64 k) = t.mem (D.setWidth 64 + BitVec.ofNat 64 k) ^^^ next.2 ∧
      (∀ x, ¬ (x - P.setWidth 64).toNat < 256 → ¬ (x - sc Sc 16).toNat < 12 →
        x ≠ D.setWidth 64 + BitVec.ofNat 64 k → u.mem x = t.mem x) ∧
      Frame (stepRegions P D L Sc) t.mem u.mem ∧
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.syms = t.syms ∧ u.gpr .edi = P ∧ u.gpr .esp = t.gpr .esp ∧
      u.gpr .ebx = BitVec.ofNat 32 (k + 1) ∧ u.zf = some (BitVec.ofNat 32 (k + 1) - L == 0#32) := by
  dsimp only
  rw [step_eq]
  dsimp only
  simp only [table_get]
  have hone : (1 : Byte) = 1#8 := rfl
  simp only [hone]
  refine WP.mono (apply_step hp i j hf hsp hrd hwr hdi hsi hbp hbx hk htab)
    fun u ⟨hT, hDb, hO, hF, hrd', hwr', hsy, hdi', hsp', hsi', hbp', hbx', hz⟩ => ?_
  refine ⟨?_, hsi', hbp', ?_, hO, hF, hrd', hwr', hsy, hdi', hsp', hbx', hz⟩
  · rw [← table_swap]
    exact table_congr hT
  · rw [hDb]
    obtain ht := table_swap t.mem (P.setWidth 64) (i + 1#8)
      (j + t.mem (P.setWidth 64 + BitVec.ofNat 64 (i + 1#8).toNat))
    rw [← ht, table_get]

/-- The stream loop after `k` bytes, `m₁` being the memory it started from. -/
structure LoopI (s : State) (P D L Sc : BitVec 32) (m₁ : Mem) (k : Nat) (t : State) : Prop where
  le : k ≤ L.toNat
  table : (contextAt t.mem (P.setWidth 64)).table = (upd s P D k).1.table
  i : t.gpr .esi = (upd s P D k).1.i.setWidth 32
  j : t.gpr .ebp = (upd s P D k).1.j.setWidth 32
  data : bytesAt t.mem (D.setWidth 64) k = (upd s P D k).2
  tail : ∀ x, k ≤ x → x < L.toNat →
    t.mem (D.setWidth 64 + BitVec.ofNat 64 x) = s.mem (D.setWidth 64 + BitVec.ofNat 64 x)
  frame : Frame (stepRegions P D L Sc) m₁ t.mem
  bx : t.gpr .ebx = BitVec.ofNat 32 k
  p : t.gpr .edi = P
  sp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms
  tab : t.mem.readW (sc Sc 28) 32 = s.syms tableName

theorem loop_step {s : State} {P D L Sc : BitVec 32} {m₁ : Mem} (hp : ApplyPre s P D L Sc)
    (hb : Frame (applyRegions P D L Sc) s.mem m₁) {k : Nat} (hk : k < L.toNat) {t : State}
    (ht : LoopI s P D L Sc m₁ k t) :
    WP isa (.block applyStep) t fun u => LoopI s P D L Sc m₁ (k + 1) u ∧
      u.zf = some (BitVec.ofNat 32 (k + 1) - L == 0#32) := by
  have hLlt := L.isLt
  obtain hft : Frame (applyRegions P D L Sc) s.mem t.mem := hb.trans (ht.frame.sub (step_sub_apply P D L Sc))
  obtain sTD : Mem.Sep (P.setWidth 64) 256 (D.setWidth 64) L.toNat :=
    sep_of_sub hp.ctxData (contains_prefix _ (n := 256) (k := 258) (by decide)) (contains_prefix _ (Nat.le_refl _))
  obtain sSD : Mem.Sep (sc Sc 16) 12 (D.setWidth 64) L.toNat :=
    sep_of_sub hp.dataScratch.symm
      (Offset.contains_base (Sc.setWidth 64) (d := 16) (n := 12) (k := 64) (by decide) (by decide))
      (contains_prefix _ (Nat.le_refl _))
  obtain hsD : ∀ x, x < L.toNat → ¬ (D.setWidth 64 + BitVec.ofNat 64 x - P.setWidth 64).toNat < 256 ∧
      ¬ (D.setWidth 64 + BitVec.ofNat 64 x - sc Sc 16).toNat < 12 := by
    intro x hx
    obtain hin : (D.setWidth 64 + BitVec.ofNat 64 x - D.setWidth 64).toNat < L.toNat := by
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hx
    exact ⟨fun h => sTD _ h hin, fun h => sSD _ h hin⟩
  obtain hctx : (⟨(contextAt t.mem (P.setWidth 64)).table, (upd s P D k).1.i, (upd s P D k).1.j⟩ :
      Context) = (upd s P D k).1 := context_ext ht.table rfl rfl
  obtain hst := apply_step_table hp (upd s P D k).1.i (upd s P D k).1.j hft ht.sp ht.rd ht.wr ht.p ht.i ht.j ht.bx
    hk (by rw [ht.syms]; exact ht.tab)
  rw [hctx] at hst
  refine WP.mono hst fun u ⟨htab, hui, huj, hbyte, hother, hfr, hurd, huwr, husy, hudi, husp, hubx, huz⟩ =>
    ⟨?_, huz⟩
  obtain hkeep : ∀ x, x < L.toNat → x ≠ k →
      u.mem (D.setWidth 64 + BitVec.ofNat 64 x) = t.mem (D.setWidth 64 + BitVec.ofNat 64 x) :=
    fun x hx hne => hother _ (hsD x hx).1 (hsD x hx).2 (data_ne hx hk hne)
  refine
    { le := hk
      table := by rw [upd_succ]; exact htab
      i := by rw [upd_succ]; exact hui
      j := by rw [upd_succ]; exact huj
      data := ?_
      tail := fun x hx hxL => by
        rw [hkeep x hxL (by omega)]
        exact ht.tail x (by omega) hxL
      frame := ht.frame.trans hfr
      bx := hubx
      p := hudi
      sp := husp.trans ht.sp
      rd := hurd.trans ht.rd
      wr := huwr.trans ht.wr
      syms := husy.trans ht.syms
      tab := ?_ }
  · rw [bytes_snoc, upd_succ, hbyte, ht.tail k (Nat.le_refl _) hk, ← ht.data]
    refine congrArg (· ++ _) ?_
    exact bytes_frame _ _ _ _ fun x hx => hkeep x (by omega) (by omega)
  · refine (hfr.readW (r := ⟨sc Sc 28, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)).trans ht.tab
    simp only [stepRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ((hp.ctxScratch.sub_left (Region.sub_prefix (by decide))).symm).sub_left (Offset.sub_base _ (by decide))
    · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
    · exact hp.dataScratch.symm.sub_left (Offset.sub_base _ (by decide))

theorem apply_loop {s : State} {P D L Sc : BitVec 32} {m₁ : Mem} (hp : ApplyPre s P D L Sc)
    (hb : Frame (applyRegions P D L Sc) s.mem m₁) {k : Nat} (hk : k < L.toNat) {t : State}
    (ht : LoopI s P D L Sc m₁ k t) :
    WP isa (.loop (.block applyStep) .ne) t (LoopI s P D L Sc m₁ L.toNat) := by
  refine WP.loop (M := isa)
    (fun rem u => ∃ j, j < L.toNat ∧ rem = L.toNat - j ∧ LoopI s P D L Sc m₁ j u)
    ?_ (L.toNat - k) t ⟨k, hk, rfl, ht⟩
  intro rem u ⟨j, hj, hrem, hu⟩
  refine WP.mono (loop_step hp hb hj hu) fun v ⟨hv, hz⟩ => ?_
  by_cases hend : j + 1 = L.toNat
  · left
    refine ⟨?_, hend ▸ hv⟩
    rw [hend, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.sub_self] at hz
    simp only [eval, hz, Option.map_some]
    rfl
  · right
    have hL := L.isLt
    obtain hnz : BitVec.ofNat 32 (j + 1) - L ≠ 0#32 := by
      intro h
      obtain h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h'
      omega
    refine ⟨?_, L.toNat - (j + 1), by omega, j + 1, by omega, rfl, hv⟩
    simp only [eval, hz, Option.map_some, beq_eq_false_iff_ne.mpr hnz, Bool.not_false]

/-! ## The stream function -/

theorem applyPre_transport {s t : State} {P D L Sc : BitVec 32} (hp : ApplyPre s P D L Sc)
    (ha : ∀ i < 4, arg t i = arg s i) (hsp : t.gpr .esp = s.gpr .esp) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) :
    ApplyPre t P D L Sc := by
  obtain hA : argAddr t 0 = argAddr s 0 := by unfold argAddr; rw [hsp]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := hp
  exact ⟨(ha 0 (by decide)).trans h1, (ha 1 (by decide)).trans h2, (ha 2 (by decide)).trans h3,
    (ha 3 (by decide)).trans h4, by rw [hrd, hA]; exact h5, by rw [hwr]; exact h6, by rw [hwr]; exact h7,
    by rw [hwr]; exact h8, h9, h10, h11, by rw [hsp]; exact h12, h13, h14, h15, by rw [hA]; exact h16,
    by rw [hA]; exact h17, by rw [hA]; exact h18⟩

/-- The constants' address to its slot and to `edx`. -/
theorem keepTable_wp {s : State} {Sc T : BitVec 32} {is : List Instr} {Q : State → Prop} (hax : s.gpr .eax = T)
    (ha16 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4) (hv16 : s.mem.readW (addr (s.gpr .esp) 16) 32 = Sc)
    (sfit : Sc.toNat + 64 ≤ 2 ^ 32) (hws : InRegions s.wr (Sc.setWidth 64) 64)
    (k : ∀ s', s'.gpr .edx = T → (∀ r, r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) →
      s'.mem = s.mem.writeW (sc Sc 28) T → s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms →
      WP isa (.block is) s' Q) :
    WP isa (.block (keepTable ++ is)) s Q := by
  simp only [keepTable, List.cons_append, List.nil_append]
  refine w_ld rfl rfl ha16 hv16 fun s₁ u₁ => ?_
  refine w_st u₁.gpr (show addr Sc sTab = sc Sc 28 from sc_addr sfit (by decide))
    (by rw [u₁.wr]; exact region_offset _ _ _ 28 4 (by decide) (by decide) hws)
    ((u₁.other _ (by decide)).trans hax) fun s₂ u₂ => ?_
  refine w_mov (show s₂.gpr .eax = T by rw [u₂.gpr, u₁.other _ (by decide)]; exact hax) fun s₃ u₃ => ?_
  exact k s₃ u₃.gpr (fun r h0 h1 => by rw [u₃.other _ h1, u₂.gpr, u₁.other _ h0])
    (by rw [u₃.mem, u₂.mem, u₁.mem]) (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₃.syms, u₂.syms, u₁.syms])

/-- The stream function, including empty input. It writes its buffers and
the four bytes below `esp`. -/
theorem apply_ok (s : State) {P D L Sc : BitVec 32} (hp : ApplyPre s P D L Sc) (hsp4 : 4 ≤ (s.gpr .esp).toNat)
    (hstk : ∀ r ∈ applyRegions P D L Sc, Region.Disjoint (below (s.gpr .esp) 4) r) :
    WP isa Impl.Rc4.X86.Ssse3.apply s fun t =>
      (contextAt t.mem (P.setWidth 64) = (upd s P D L.toNat).1 ∧
        bytesAt t.mem (D.setWidth 64) L.toNat = (upd s P D L.toNat).2) ∧
      Frame (below (s.gpr .esp) 4 :: applyRegions P D L Sc) s.mem t.mem ∧ t.gpr .ebx = s.gpr .ebx ∧
      t.gpr .esi = s.gpr .esi ∧ t.gpr .edi = s.gpr .edi ∧ t.gpr .ebp = s.gpr .ebp ∧
      t.gpr .esp = s.gpr .esp := by
  have hLlt := L.isLt
  have mP : (⟨P.setWidth 64, 258⟩ : Region) ∈ applyRegions P D L Sc := List.mem_cons_self
  have mD : (⟨D.setWidth 64, L.toNat⟩ : Region) ∈ applyRegions P D L Sc :=
    List.mem_cons_of_mem _ List.mem_cons_self
  have mS : (⟨Sc.setWidth 64, 64⟩ : Region) ∈ applyRegions P D L Sc :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  unfold Impl.Rc4.X86.Ssse3.apply
  refine WP.seq (WP.mono (apply_entry s hp) fun a ⟨ham, hak, hax, haz⟩ => ?_)
  obtain hasp : a.gpr .esp = s.gpr .esp := hak.gpr (by decide)
  refine WP.ite (L == 0#32) (by simp only [eval, haz, BitVec.and_self]) (fun hz => ?_) (fun hnz => ?_)
  · have hL : L.toNat = 0 := by rw [beq_iff_eq.mp hz]; rfl
    refine WP.block_nil ?_
    rw [hL, ham]
    exact ⟨⟨rfl, rfl⟩, Frame.refl _ _, hak.gpr (by decide), hak.gpr (by decide), hak.gpr (by decide),
      hak.gpr (by decide), hasp⟩
  obtain hL0 : L.toNat ≠ 0 := fun h => by
    have : L = 0#32 := BitVec.eq_of_toNat_eq h
    rw [this] at hnz
    exact absurd hnz (by decide)
  unfold applyRest
  refine WP.seq ?_
  rw [WP.block_append_iff]
  obtain hsc : InRegions a.wr (Sc.setWidth 64) 64 := by rw [hak.2.2]; exact hp.scratch
  refine WP.mono (save_ok a Sc hp.scratchFit
    (by rw [hak.2.1, hak.2.2, hasp]; exact hp.arg_in (i := 3) (by decide))
    (by rw [ham, hasp]; exact hp.aS) hsc) fun b ⟨hbm, hbk⟩ => ?_
  obtain hsave : Frame [⟨Sc.setWidth 64, 64⟩] s.mem b.mem := by
    rw [hbm, ham]; exact savedMem_frame _ _ _ _ _ _
  obtain hbf : Frame (applyRegions P D L Sc) s.mem b.mem :=
    hsave.mono fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact mS
  obtain hbsp : b.gpr .esp = s.gpr .esp := (hbk.gpr (by decide)).trans hasp
  obtain hbrd : b.rd = s.rd := hbk.2.1.trans hak.2.1
  obtain hbwr : b.wr = s.wr := hbk.2.2.trans hak.2.2
  obtain r257 : InRegions (b.rd ++ b.wr) (P.setWidth 64 + 257#64) 1 := by
    obtain ⟨r, hr, hc⟩ := region_offset _ _ _ 257 1 (by decide) (by decide) hp.ctx
    exact ⟨r, by rw [hbrd, hbwr]; exact List.mem_append_right _ hr, hc⟩
  refine WP.mono (apply_start b P hp.ctxFit
    (by rw [hbrd, hbwr, hbsp]; exact hp.arg_in (i := 0) (by decide))
    (by rw [hbsp]; exact (hp.arg_eq hbf (i := 0) (by decide)).trans hp.aP) r257)
    fun c ⟨hcm, hck, hcsi, hcdi, hcbp, hcbx⟩ => ?_
  obtain hcsp : c.gpr .esp = s.gpr .esp := (hck.gpr (by decide)).trans hbsp
  obtain hcrd : c.rd = s.rd := hck.2.1.trans hbrd
  obtain hcwr : c.wr = s.wr := hck.2.2.trans hbwr
  -- the constants' address
  refine WP.seq (WP.mono (symFrame_ok tableName c (by rw [hcsp]; exact hsp4)) fun d hd => ?_)
  obtain hdsp : d.gpr .esp = s.gpr .esp := (hd.gpr _ (by decide)).trans hcsp
  obtain hdrd : d.rd = s.rd := hd.rd.trans hcrd
  obtain hdwr : d.wr = s.wr := hd.wr.trans hcwr
  obtain hfd : Frame [below (s.gpr .esp) 4] c.mem d.mem := by rw [← hcsp]; exact hd.frame
  obtain argd : ∀ i < 4, arg d i = arg s i := fun i hi => by
    rw [hd.arg (by rw [hcsp]; exact hsp4) (by have := hp.spFit; rw [hcsp]; omega)]
    unfold arg argAddr
    rw [hcsp, hcm]
    exact hp.arg_eq hbf hi
  refine WP.seq ?_
  rw [← List.append_nil keepTable]
  refine keepTable_wp (Sc := Sc) hd.addr (by rw [hdrd, hdwr, hdsp]; exact hp.arg_in (i := 3) (by decide))
    ((argd 3 (by decide)).trans hp.aS) hp.scratchFit (by rw [hdwr]; exact hp.scratch)
    fun e edx eg em erd ewr esy => WP.block_nil ?_
  obtain hesp : e.gpr .esp = s.gpr .esp := (eg _ (by decide) (by decide)).trans hdsp
  obtain herd : e.rd = s.rd := erd.trans hdrd
  obtain hewr : e.wr = s.wr := ewr.trans hdwr
  have c28 : (⟨Sc.setWidth 64, 64⟩ : Region).Contains (sc Sc 28) (32 / 8) :=
    Offset.contains_base _ (by decide) (by decide)
  obtain hde : Frame [⟨Sc.setWidth 64, 64⟩] d.mem e.mem := by
    rw [em]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c28
  -- from the entry to the loop: the working space and the word below `esp`
  obtain hse : Frame [below (s.gpr .esp) 4, ⟨Sc.setWidth 64, 64⟩] s.mem e.mem := by
    refine ((hsave.mono fun r hr => List.mem_cons_of_mem _ hr).trans ?_).trans
      (hde.mono fun r hr => List.mem_cons_of_mem _ hr)
    rw [← hcm]
    exact hfd.mono fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact List.mem_cons_self
  obtain arge : ∀ i < 4, arg e i = arg s i := fun i hi => by
    rw [← argd i hi]
    unfold arg argAddr
    rw [hesp, hdsp]
    exact hde.readW (arg_contains' hp.spFit hi) (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact hp.argsScratch) (by decide)
  obtain hpe : ApplyPre e P D L Sc := applyPre_transport hp arge hesp herd hewr
  obtain hctxE : contextAt e.mem (P.setWidth 64) = contextAt s.mem (P.setWidth 64) :=
    contextAt_frame hse fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hstk _ mP).symm
      · exact hp.ctxScratch
  obtain hdataE : ∀ x, x < L.toNat →
      e.mem (D.setWidth 64 + BitVec.ofNat 64 x) = s.mem (D.setWidth 64 + BitVec.ofNat 64 x) := fun x hx =>
    hse.bytes (R := ⟨D.setWidth 64, L.toNat⟩) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hstk _ mD).symm
      · exact hp.dataScratch) (show L.toNat ≤ 2 ^ 64 by omega) hx
  obtain hupd : upd e P D L.toNat = upd s P D L.toNat := by
    unfold upd
    rw [hctxE, bytes_frame _ _ _ _ fun x hx => hdataE x hx]
  obtain hinv : LoopI e P D L Sc e.mem 0 e := by
    have hu0 : upd e P D 0 = (contextAt e.mem (P.setWidth 64), []) := rfl
    refine
      { le := Nat.zero_le _
        table := by rw [hu0]
        i := by
          rw [hu0, hctxE, eg _ (by decide) (by decide), hd.gpr _ (by decide), hcsi,
            (hbk.gpr (by decide) : b.gpr .eax = a.gpr .eax), hax]
        j := by
          rw [hu0, hctxE, eg _ (by decide) (by decide), hd.gpr _ (by decide), hcbp,
            ← contextAt_frame hsave (fun r hr => by
              simp only [List.mem_singleton] at hr
              subst hr
              exact hp.ctxScratch)]
          rfl
        data := by rw [hu0]; rfl
        tail := fun x _ _ => rfl
        frame := Frame.refl _ _
        bx := by rw [eg _ (by decide) (by decide), hd.gpr _ (by decide)]; exact hcbx
        p := by rw [eg _ (by decide) (by decide), hd.gpr _ (by decide)]; exact hcdi
        sp := rfl
        rd := rfl
        wr := rfl
        syms := rfl
        tab := by rw [em, Mem.readW_writeW_self32, esy, hd.syms] }
  refine WP.seq (WP.mono (apply_loop hpe (Frame.refl _ _) (Nat.pos_of_ne_zero hL0) hinv) fun g hg => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (apply_finish g (upd e P D L.toNat).1.i (upd e P D L.toNat).1.j P hp.ctxFit
    hg.i hg.j hg.p (by rw [hg.wr, hewr]; exact hp.ctx)) fun f ⟨hfm, hfk⟩ => ?_
  obtain hgf : Frame [⟨P.setWidth 64, 258⟩] g.mem f.mem := by
    rw [hfm]
    refine Frame.write ?_ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  obtain hef : Frame (applyRegions P D L Sc) e.mem f.mem :=
    (hg.frame.sub (step_sub_apply P D L Sc)).trans (hgf.mono fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact mP)
  obtain hsf : Frame (below (s.gpr .esp) 4 :: applyRegions P D L Sc) s.mem f.mem := by
    refine (hse.mono fun r hr => ?_).trans (hef.mono fun r hr => List.mem_cons_of_mem _ hr)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ mS
  obtain hsaved : Saved f.mem Sc a := by
    obtain h0 := saved_savedMem a.mem Sc a
    rw [← hbm, ← hcm] at h0
    obtain h1 := h0.frame hfd fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact (hstk _ mS).symm.sub_left (Region.sub_prefix (by decide))
    obtain h2 := h1.frame (show Frame [⟨sc Sc 28, 4⟩] d.mem e.mem by
      rw [em]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)) fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact Offset.base_disjoint _ (by decide) (by decide)
    obtain h3 := h2.frame hg.frame fun r hr => by
      simp only [stepRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ((hp.ctxScratch.sub_left (Region.sub_prefix (by decide))).symm).sub_left
          (Region.sub_prefix (by decide))
      · exact Offset.base_disjoint _ (by decide) (by decide)
      · exact (hp.dataScratch.symm).sub_left (Region.sub_prefix (by decide))
    exact h3.frame hgf fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact (hp.ctxScratch.symm).sub_left (Region.sub_prefix (by decide))
  obtain hfsp : f.gpr .esp = s.gpr .esp := (hfk.gpr (by decide)).trans (hg.sp.trans hesp)
  obtain hfrd : f.rd = s.rd := hfk.2.1.trans (hg.rd.trans herd)
  obtain hfwr : f.wr = s.wr := hfk.2.2.trans (hg.wr.trans hewr)
  refine WP.mono (restore_ok a f Sc hp.scratchFit
    (by rw [hfrd, hfwr, hfsp]; exact hp.arg_in (i := 3) (by decide))
    (by
      rw [show f.gpr .esp = e.gpr .esp from (hfk.gpr (by decide)).trans hg.sp]
      exact (hpe.arg_eq hef (i := 3) (by decide)).trans hpe.aS)
    (by rw [hfrd, hfwr]; exact (by obtain ⟨r, hr, hc⟩ := hp.scratch; exact ⟨r, List.mem_append_right _ hr, hc⟩ : InRegions (s.rd ++ s.wr) (Sc.setWidth 64) 64)) hsaved) fun h ⟨gbx, gsi, gdi, gbp, gm, gk⟩ => ?_
  have hDP (o : Nat) (ho : o < 258) :
      Mem.Sep (D.setWidth 64) L.toNat (P.setWidth 64 + BitVec.ofNat 64 o) 1 :=
    sep_of_sub hp.ctxData.symm (contains_prefix _ (Nat.le_refl _))
      (Offset.contains_base _ (by omega) (by omega))
  refine ⟨⟨?_, ?_⟩, by rw [gm]; exact hsf, gbx.trans (hak.gpr (by decide)), gsi.trans (hak.gpr (by decide)),
    gdi.trans (hak.gpr (by decide)), gbp.trans (hak.gpr (by decide)), (gk.gpr (by decide)).trans hfsp⟩
  · rw [gm, hfm, context_finish, ← hupd]
    exact context_ext hg.table rfl rfl
  · rw [gm, hfm, bytes_write_sep _ _ _ _ _ (by omega) (hDP 257 (by decide)),
      bytes_write_sep _ _ _ _ _ (by omega) (hDP 256 (by decide)), ← hupd]
    exact hg.data

/-! ## Initialization: the identity permutation -/

/-- A row of the identity permutation, stored. -/
theorem identity_row (m : Mem) (p : Addr) {r : Nat} (hr : r < 16) :
    (identityMem m p (16 * r)).writeW (p + BitVec.ofNat 64 (16 * r)) (cst (oI r)) =
      identityMem m p (16 * (r + 1)) := by
  funext x
  have hlt := Offset.lt_iff x p (d := 16 * r) (n := 16) (by omega)
  have e := Offset.toNat_sub_add x p (d := 16 * r) (by omega)
  have hxp := (x - p).isLt
  by_cases hx : (x - (p + BitVec.ofNat 64 (16 * r))).toNat < 16
  · obtain hxe : x = p + BitVec.ofNat 64 (16 * r) + BitVec.ofNat 64 (x - (p + BitVec.ofNat 64 (16 * r))).toNat := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    have h1 := hlt.mp hx
    rw [show identityMem m p (16 * (r + 1)) x = BitVec.ofNat 8 (x - p).toNat by
      simp only [identityMem]; rw [ite_eq_left (by omega)]]
    rw [hxe, writeW_byte _ _ _ (by omega) (by decide)]
    show byte (cst (oI r)) _ = _
    rw [cst_I r hr _ hx, ← hxe]
    congr 1
    omega
  · rw [writeW_byte_off _ _ _ _ (by omega)]
    have h1 : ¬ (16 * r ≤ (x - p).toNat ∧ (x - p).toNat < 16 * r + 16) := fun h => hx (hlt.mpr h)
    simp only [identityMem]
    by_cases h2 : (x - p).toNat < 16 * r
    · rw [ite_eq_left h2, ite_eq_left (by omega)]
    · rw [ite_eq_right h2, ite_eq_right (by omega)]

/-- The rows of the identity permutation from the row `r` on. -/
theorem identityFrom_wp {s₀ : State} {P : BitVec 32} {is : List Instr} {Q : State → Prop}
    (hdi : s₀.gpr .edi = P) (fit : P.toNat + 256 ≤ 2 ^ 32) (hw : InRegions s₀.wr (P.setWidth 64) 256)
    (htb : s₀.gpr tbr = s₀.syms tableName)
    (k : ∀ s', s'.mem = identityMem s₀.mem (P.setWidth 64) 256 → s'.gpr = s₀.gpr → s'.rd = s₀.rd → s'.wr = s₀.wr →
      s'.syms = s₀.syms → WP isa (.block is) s' Q) :
    ∀ (n r : Nat) (s : State), r + n = 16 → s.mem = identityMem s₀.mem (P.setWidth 64) (16 * r) → s.gpr = s₀.gpr →
      s.rd = s₀.rd → s.wr = s₀.wr → s.syms = s₀.syms →
      WP isa (.block ((List.range' r n).flatMap identityRow ++ is)) s Q
  | 0, r, s, e, hm, hg, hrd, hwr, hsy => by
    obtain rfl : r = 16 := by omega
    exact k s hm hg hrd hwr hsy
  | n + 1, r, s, e, hm, hg, hrd, hwr, hsy => by
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    simp only [identityRow, List.cons_append, List.nil_append]
    refine x_tb (by rw [hg, hsy]; exact htb) ⟨by unfold oI; omega, by rw [tab_len]; unfold oI; omega⟩
      fun s₁ u₁ => ?_
    refine x_st (show s₁.gpr .edi = P by rw [u₁.gpr, hg]; exact hdi) (addr_eq (by omega))
      (by rw [u₁.wr, hwr]; exact region_offset _ _ _ (16 * r) 16 (by omega) (by omega) hw) u₁.xmm fun s₂ u₂ => ?_
    exact identityFrom_wp hdi fit hw htb k n (r + 1) s₂ (by omega)
      (by rw [u₂.mem, u₁.mem, hm, identity_row _ _ (by omega)]) (by rw [u₂.gpr, u₁.gpr, hg])
      (by rw [u₂.rd, u₁.rd, hrd]) (by rw [u₂.wr, u₁.wr, hwr]) (by rw [u₂.syms, u₁.syms, hsy])

/-! ## Initialization: a round of the key schedule -/

/-- What the key schedule needs of the state `s₀` it starts from: the key at
`K`, the table at `P`, the working space at `Sc`, and the arguments, which
it reads whatever it has written. -/
structure SchPre (s₀ : State) (K Lk P Sc : BitVec 32) : Prop where
  len : 1 ≤ Lk.toNat ∧ Lk.toNat ≤ 256
  pfit : P.toNat + 258 ≤ 2 ^ 32
  sfit : Sc.toNat + 64 ≤ 2 ^ 32
  keyFit : K.toNat + Lk.toNat ≤ 2 ^ 32
  table : InRegions s₀.wr (P.setWidth 64) 256
  scratch : InRegions s₀.wr (Sc.setWidth 64) 64
  key : InRegions (s₀.rd ++ s₀.wr) (K.setWidth 64) Lk.toNat
  a4 : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) 4) 4
  a8 : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) 8) 4
  a16 : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) 16) 4
  v4 : ∀ m, Frame (workRegions P Sc) s₀.mem m → m.readW (addr (s₀.gpr .esp) 4) 32 = K
  v8 : ∀ m, Frame (workRegions P Sc) s₀.mem m → m.readW (addr (s₀.gpr .esp) 8) 32 = Lk
  v16 : ∀ m, Frame (workRegions P Sc) s₀.mem m → m.readW (addr (s₀.gpr .esp) 16) 32 = Sc
  keyD : ∀ r ∈ workRegions P Sc, Region.Disjoint ⟨K.setWidth 64, Lk.toNat⟩ r
  tS : Region.Disjoint ⟨P.setWidth 64, 258⟩ ⟨Sc.setWidth 64, 64⟩

/-- The key schedule after `r` rounds. -/
structure SchI (s₀ : State) (K Lk P Sc : BitVec 32) (r : Nat) (s : State) : Prop where
  frame : Frame (workRegions P Sc) s₀.mem s.mem
  table : (contextAt s.mem (P.setWidth 64)).table = (schedulePrefix (keyOf s₀.mem K Lk) r).1
  j : s.gpr .ebp = (schedulePrefix (keyOf s₀.mem K Lk) r).2.setWidth 32
  i : s.gpr .esi = BitVec.ofNat 32 r
  off : s.gpr .ebx = BitVec.ofNat 32 (r % Lk.toNat)
  p : s.gpr .edi = P
  sp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  syms : s.syms = s₀.syms
  tab : s.mem.readW (sc Sc 28) 32 = s₀.syms tableName

theorem sch_step {s₀ s : State} {K Lk P Sc : BitVec 32} {r : Nat} (hr : r < 256) (hpre : SchPre s₀ K Lk P Sc)
    (h : SchI s₀ K Lk P Sc r s) :
    WP isa (.block scheduleStep) s fun t => SchI s₀ K Lk P Sc (r + 1) t ∧
      t.zf = some (BitVec.ofNat 32 (r + 1) - BitVec.ofNat 32 256 == 0#32) := by
  have hlen := hpre.len
  have hrt : (BitVec.ofNat 8 r).toNat = r := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  obtain hi : s.gpr .esi = (BitVec.ofNat 8 r).setWidth 32 := by rw [h.i, byte32, hrt]
  obtain fit : P.toNat + 256 ≤ 2 ^ 32 := by have := hpre.pfit; omega
  have hmod := Nat.mod_lt r (show 0 < Lk.toNat by omega)
  obtain hT : InRegions s.wr (P.setWidth 64) 256 := by rw [h.wr]; exact hpre.table
  obtain hS : InRegions s.wr (Sc.setWidth 64) 64 := by rw [h.wr]; exact hpre.scratch
  have hW1 : (⟨P.setWidth 64, 256⟩ : Region) ∈ workRegions P Sc := List.mem_cons_self
  have hW2 : (⟨sc Sc 16, 12⟩ : Region) ∈ workRegions P Sc := List.mem_cons_of_mem _ List.mem_cons_self
  have cT (y : Byte) : (⟨P.setWidth 64, 256⟩ : Region).Contains (P.setWidth 64 + BitVec.ofNat 64 y.toNat) 1 :=
    Offset.contains_base _ (by have := y.isLt; omega) (by have := y.isLt; omega)
  have c24 : (⟨sc Sc 16, 12⟩ : Region).Contains (sc Sc 24) (32 / 8) :=
    Offset.contains _ (by decide) (by decide) (by decide)
  have c16 : (⟨sc Sc 16, 12⟩ : Region).Contains (sc Sc 16) (64 / 8) :=
    Offset.contains _ (by decide) (by decide) (by decide)
  obtain sT16 : Mem.Sep (P.setWidth 64) 256 (sc Sc 16) 8 :=
    sep_of_sub hpre.tS (contains_prefix (P.setWidth 64) (n := 256) (k := 258) (by decide))
      (Offset.contains_base (Sc.setWidth 64) (d := 16) (n := 8) (k := 64) (by decide) (by decide))
  obtain sT24 : Mem.Sep (P.setWidth 64) 256 (sc Sc 24) 4 :=
    sep_of_sub hpre.tS (contains_prefix (P.setWidth 64) (n := 256) (k := 258) (by decide))
      (Offset.contains_base (Sc.setWidth 64) (d := 24) (n := 4) (k := 64) (by decide) (by decide))
  have s24T (y : Byte) : Mem.Sep (sc Sc 24) 4 (P.setWidth 64 + BitVec.ofNat 64 y.toNat) 1 :=
    sep_of_sub hpre.tS.symm (Offset.contains_base _ (by decide) (by decide))
      (Offset.contains_base _ (by have := y.isLt; omega) (by have := y.isLt; omega))
  have inT (y : Nat) (hy : y < 256) : (P.setWidth 64 + BitVec.ofNat 64 y - P.setWidth 64).toNat < 256 := by
    rw [Mem.sub_ofNat_toNat _ (by omega)]; exact hy
  simp only [scheduleStep, List.append_assoc, List.cons_append, List.nil_append]
  refine loadSi_wp (i := BitVec.ofNat 8 r) hi h.p fit (by rw [h.rd, h.wr]; exact inr_wr hpre.table)
    (by rw [h.rd, h.wr, h.sp]; exact hpre.a16) (by rw [h.sp]; exact hpre.v16 _ h.frame) hpre.sfit hS h.tab
    fun s₁ cx₁ dx₁ g₁ m₁ rd₁ wr₁ sy₁ => ?_
  rw [hrt] at cx₁ m₁
  obtain f₁ : Frame (workRegions P Sc) s.mem s₁.mem := by rw [m₁]; exact (Frame.refl _ _).writeW hW2 _ c24
  obtain sp₁ : s₁.gpr .esp = s₀.gpr .esp := (g₁ _ (by decide) (by decide) (by decide)).trans h.sp
  refine w_add ((g₁ _ (by decide) (by decide) (by decide)).trans h.j) cx₁ fun s₂ u₂ => ?_
  refine w_ld (show s₂.gpr .esp = s₀.gpr .esp by rw [u₂.other _ (by decide)]; exact sp₁) rfl
    (by rw [u₂.rd, u₂.wr, rd₁, wr₁, h.rd, h.wr]; exact hpre.a4)
    (show s₂.mem.readW _ 32 = K by rw [u₂.mem]; exact hpre.v4 _ (h.frame.trans f₁)) fun s₃ u₃ => ?_
  refine w_add u₃.gpr (show s₃.gpr .ebx = BitVec.ofNat 32 (r % Lk.toNat) by
      rw [u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide) (by decide) (by decide)]; exact h.off)
    fun s₄ u₄ => ?_
  obtain hkb : s₁.mem (K.setWidth 64 + BitVec.ofNat 64 (r % Lk.toNat)) =
      (keyOf s₀.mem K Lk).getD (r % (keyOf s₀.mem K Lk).length) 0 := by
    rw [(h.frame.trans f₁).bytes (R := ⟨K.setWidth 64, Lk.toNat⟩) hpre.keyD (show Lk.toNat ≤ 2 ^ 64 by omega) hmod]
    dsimp only [keyOf]
    rw [bytes_length, bytes_get _ _ _ _ hmod]
  refine w_lb u₄.gpr (key_addr hpre.keyFit hmod)
    (by
      rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, rd₁, wr₁, h.rd, h.wr]
      exact region_offset _ _ _ _ _ (by omega) (by omega) hpre.key)
    (show s₄.mem (K.setWidth 64 + BitVec.ofNat 64 (r % Lk.toNat)) =
        (keyOf s₀.mem K Lk).getD (r % (keyOf s₀.mem K Lk).length) 0 by
      rw [u₄.mem, u₃.mem, u₂.mem]; exact hkb) fun s₅ u₅ => ?_
  refine w_add ((u₅.other _ (by decide)).trans ((u₄.other _ (by decide)).trans
      ((u₃.other _ (by decide)).trans u₂.gpr))) u₅.gpr fun s₆ u₆ => ?_
  refine w_andi u₆.gpr fun s₇ u₇ => ?_
  -- the state before the exchange
  obtain m₇ : s₇.mem = s₁.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  obtain rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁, h.rd]
  obtain wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁, h.wr]
  obtain sy₇ : s₇.syms = s₀.syms := by rw [u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, sy₁, h.syms]
  have g₇ (x : Reg) (h0 : x ≠ .eax) (h1 : x ≠ .ecx) (h2 : x ≠ .edx) (h3 : x ≠ .ebp) : s₇.gpr x = s.gpr x := by
    rw [u₇.other _ h3, u₆.other _ h3, u₅.other _ h0, u₄.other _ h0, u₃.other _ h0, u₂.other _ h3, g₁ _ h0 h1 h2]
  let a := s.mem (P.setWidth 64 + BitVec.ofNat 64 r)
  let jj := (schedulePrefix (keyOf s₀.mem K Lk) r).2 + a +
    (keyOf s₀.mem K Lk).getD (r % (keyOf s₀.mem K Lk).length) 0
  obtain bp₇ : s₇.gpr .ebp = jj.setWidth 32 := by rw [u₇.gpr, byte_add3_32]
  obtain cx₇ : s₇.gpr .ecx = a.setWidth 32 := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide)]
    exact cx₁
  obtain f₂ : Frame (workRegions P Sc) s.mem (s₇.mem.write (P.setWidth 64 + BitVec.ofNat 64 jj.toNat) 1 a) := by
    rw [m₇]; exact f₁.write hW1 _ (cT jj)
  obtain hb : s₇.mem (P.setWidth 64 + BitVec.ofNat 64 jj.toNat) = s.mem (P.setWidth 64 + BitVec.ofNat 64 jj.toNat) := by
    have := sT24 _ (inT _ jj.isLt)
    rw [m₇, m₁, writeW_byte_off _ _ _ _ (show 32 / 8 ≤ _ by omega)]
  refine exchange_wp (j := jj) (a := a) bp₇ cx₇
    (by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), sy₇]
      exact dx₁)
    ((g₇ _ (by decide) (by decide) (by decide) (by decide)).trans h.p) fit (by rw [wr₇]; exact hpre.table)
    (by rw [rd₇, wr₇, g₇ _ (by decide) (by decide) (by decide) (by decide), h.sp]; exact hpre.a16)
    (by
      rw [g₇ _ (by decide) (by decide) (by decide) (by decide), h.sp]
      exact hpre.v16 _ (h.frame.trans f₂)) hpre.sfit (by rw [wr₇]; exact hpre.scratch)
    (by rw [readW_write1 (s24T jj), m₇, m₁, Mem.readW_writeW_self32]) fun s₈ q ax₈ dx₈ g₈ m₈ rd₈ wr₈ sy₈ => ?_
  rw [hb] at ax₈
  obtain di₈ : s₈.gpr .edi = P := (g₈ _ (by decide) (by decide)).trans
    ((g₇ _ (by decide) (by decide) (by decide) (by decide)).trans h.p)
  obtain sp₈ : s₈.gpr .esp = s₀.gpr .esp := (g₈ _ (by decide) (by decide)).trans
    ((g₇ _ (by decide) (by decide) (by decide) (by decide)).trans h.sp)
  obtain f₃ : Frame (workRegions P Sc) s.mem s₈.mem := by rw [m₈]; exact f₂.writeW hW2 _ c16
  refine WP.mono_syms (schedule_after s₈ (BitVec.ofNat 8 r) (s.mem (P.setWidth 64 + BitVec.ofNat 64 jj.toNat)) Lk
    ((g₈ _ (by decide) (by decide)).trans ((g₇ _ (by decide) (by decide) (by decide) (by decide)).trans hi)) ax₈
    (by rw [di₈]; exact fit)
    (by rw [wr₈, wr₇, di₈, hrt]; exact region_offset _ _ _ _ _ (by omega) (by omega) hpre.table)
    (by rw [rd₈, wr₈, rd₇, wr₇, sp₈]; exact hpre.a8)
    (by rw [sp₈]; exact hpre.v8 _ (h.frame.trans f₃))) fun t ⟨tm, tbx, tsi, tz, tk⟩ tsy => ?_
  rw [di₈, hrt] at tm
  obtain f₄ : Frame (workRegions P Sc) s.mem t.mem := by
    rw [tm]
    exact f₃.write hW1 _ (Offset.contains_base _ (by omega) (by omega))
  have hnext := schedule_succ (keyOf s₀.mem K Lk) r
  dsimp only [scheduleRound] at hnext
  obtain htab : (contextAt s.mem (P.setWidth 64)).table.getD r 0 = a := by
    have hg := table_get s.mem (P.setWidth 64) (BitVec.ofNat 8 r)
    rwa [hrt] at hg
  rw [h.table] at htab
  have hcast : (BitVec.ofNat 8 r).setWidth 32 + 1#32 = BitVec.ofNat 32 (r + 1) := by
    rw [byte32, hrt, ← BitVec.ofNat_add]
  refine ⟨⟨h.frame.trans f₄, ?_, ?_, ?_, ?_, (tk.gpr (by decide)).trans di₈, (tk.gpr (by decide)).trans sp₈,
    tk.2.1.trans (rd₈.trans rd₇), tk.2.2.trans (wr₈.trans wr₇), ?_, ?_⟩, ?_⟩
  · rw [hnext, htab]
    have hsw := table_swap s.mem (P.setWidth 64) (BitVec.ofNat 8 r) jj
    rw [hrt, h.table] at hsw
    rw [← hsw]
    refine table_congr fun y hy => ?_
    rw [tm, m₈, m₇, m₁]
    have := swapped_bytes s.mem (P.setWidth 64) (sc Sc 16) (sc Sc 24) (BitVec.ofNat 8 r) jj a
      (s.mem (P.setWidth 64 + BitVec.ofNat 64 jj.toNat)) (a.setWidth 32) q sT16 sT24 hy
    rwa [hrt] at this
  · rw [tk.gpr (by decide), g₈ _ (by decide) (by decide), bp₇, hnext, htab]
  · rw [tsi, hcast]
  · rw [tbx, g₈ _ (by decide) (by decide), g₇ _ (by decide) (by decide) (by decide) (by decide), h.off]
    exact key_next32 r _ (by omega) hlen.2
  · rw [tsy, sy₈, sy₇]
  · refine (f₄.readW (r := ⟨sc Sc 28, 4⟩) (Region.contains_self _ _) (fun r' hr' => ?_) (by decide)).trans h.tab
    simp only [workRegions, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact ((hpre.tS.sub_left (Region.sub_prefix (by decide))).symm).sub_left (Offset.sub_base _ (by decide))
    · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
  · rw [tz, hcast]

theorem sch_loop {s₀ s : State} {K Lk P Sc : BitVec 32} {r : Nat} (hr : r < 256) (hpre : SchPre s₀ K Lk P Sc)
    (h : SchI s₀ K Lk P Sc r s) : WP isa (.loop (.block scheduleStep) .ne) s (SchI s₀ K Lk P Sc 256) := by
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < 256 ∧ rem = 256 - j ∧ SchI s₀ K Lk P Sc j t)
    ?_ (256 - r) s ⟨r, hr, rfl, h⟩
  intro rem t ⟨j, hj, hrem, ht⟩
  refine WP.mono (sch_step hj hpre ht) fun u ⟨hu, hz⟩ => ?_
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    simp only [eval, hz, hend, Option.map_some]
    rfl
  · right
    have hnz : BitVec.ofNat 32 (j + 1) - BitVec.ofNat 32 256 ≠ 0#32 := by
      intro h'
      obtain h'' := congrArg BitVec.toNat h'
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h''
      omega
    refine ⟨?_, 256 - (j + 1), by omega, j + 1, by omega, rfl, hu⟩
    simp only [eval, hz, Option.map_some, beq_eq_false_iff_ne.mpr hnz, Bool.not_false]

/-! ## Initialization -/

theorem initPre_transport {s t : State} (hp : InitPre s) (ha : ∀ i < 4, arg t i = arg s i)
    (hsp : t.gpr .esp = s.gpr .esp) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : InitPre t := by
  obtain hA : argAddr t 0 = argAddr s 0 := by unfold argAddr; rw [hsp]
  have a0 := ha 0 (by decide)
  have a1 := ha 1 (by decide)
  have a2 := ha 2 (by decide)
  have a3 := ha 3 (by decide)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrd, hA]; exact h1
  · rw [hrd, a0, a1]; exact h2
  · rw [hwr, a2]; exact h3
  · rw [hwr, a3]; exact h4
  · rw [a0, a1]; exact h5
  · rw [a2]; exact h6
  · rw [a3]; exact h7
  · rw [hsp]; exact h8
  · rw [a0, a1, a2]; exact h9
  · rw [a0, a1, a3]; exact h10
  · rw [a2, a3]; exact h11
  · rw [hA, a2]; exact h12
  · rw [hA, a3]; exact h13

/-- Key scheduling, for a key of a valid length. It writes the context, the
working space and the four bytes below `esp`. -/
theorem init_valid (s : State) (hp : InitPre s) (hlen : 1 ≤ (arg s 1).toNat ∧ (arg s 1).toNat ≤ 256)
    (hsp4 : 4 ≤ (s.gpr .esp).toNat)
    (hkS : Region.Disjoint (below (s.gpr .esp) 4) ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩)
    (hsS : Region.Disjoint (below (s.gpr .esp) 4) ⟨(arg s 3).setWidth 64, 64⟩) :
    WP isa initValid s fun t => t.gpr .eax = 0#32 ∧
      contextAt t.mem ((arg s 2).setWidth 64) =
        { table := keySchedule (bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat), i := 0, j := 0 } ∧
      Frame [below (s.gpr .esp) 4, ⟨(arg s 2).setWidth 64, 258⟩, ⟨(arg s 3).setWidth 64, 64⟩] s.mem t.mem ∧
      t.gpr .ebx = s.gpr .ebx ∧ t.gpr .esi = s.gpr .esi ∧ t.gpr .edi = s.gpr .edi ∧ t.gpr .ebp = s.gpr .ebp ∧
      t.gpr .esp = s.gpr .esp := by
  obtain fit : (arg s 2).toNat + 256 ≤ 2 ^ 32 := by have := hp.ctxFit; omega
  obtain hT : InRegions s.wr ((arg s 2).setWidth 64) 256 := by
    obtain ⟨R, hR, hc⟩ := hp.ctx
    exact ⟨R, hR, by simp only [Region.Contains] at hc ⊢; omega⟩
  have mC : (⟨(arg s 2).setWidth 64, 258⟩ : Region) ∈
      [(⟨(arg s 2).setWidth 64, 258⟩ : Region), ⟨(arg s 3).setWidth 64, 64⟩] := List.mem_cons_self
  have mS : (⟨(arg s 3).setWidth 64, 64⟩ : Region) ∈
      [(⟨(arg s 2).setWidth 64, 258⟩ : Region), ⟨(arg s 3).setWidth 64, 64⟩] :=
    List.mem_cons_of_mem _ List.mem_cons_self
  unfold initValid
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (save_ok s (arg s 3) hp.scratchFit (hp.arg_in (i := 3) (by decide)) rfl hp.scratch)
    fun a ⟨ham, hak⟩ => ?_
  obtain haf : InitFrame s a.mem := by
    rw [ham]
    exact (savedMem_frame _ _ _ _ _ _).mono fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact mS
  obtain hasp : a.gpr .esp = s.gpr .esp := hak.gpr (by decide)
  refine w_ld hasp rfl (by rw [hak.2.1, hak.2.2]; exact hp.arg_in (i := 2) (by decide))
    (hp.arg_eq haf (i := 2) (by decide)) fun b ub => WP.block_nil ?_
  obtain bsp : b.gpr .esp = s.gpr .esp := (ub.other _ (by decide)).trans hasp
  obtain brd : b.rd = s.rd := ub.rd.trans hak.2.1
  obtain bwr : b.wr = s.wr := ub.wr.trans hak.2.2
  -- the constants' address
  refine WP.seq (WP.mono (symFrame_ok tableName b (by rw [bsp]; exact hsp4)) fun d hd => ?_)
  obtain dsp : d.gpr .esp = s.gpr .esp := (hd.gpr _ (by decide)).trans bsp
  obtain drd : d.rd = s.rd := hd.rd.trans brd
  obtain dwr : d.wr = s.wr := hd.wr.trans bwr
  obtain hfd : Frame [below (s.gpr .esp) 4] a.mem d.mem := by rw [← bsp, ← ub.mem]; exact hd.frame
  obtain argd : ∀ i < 4, arg d i = arg s i := fun i hi => by
    rw [hd.arg (by rw [bsp]; exact hsp4) (by have := hp.spFit; rw [bsp]; omega)]
    unfold arg argAddr
    rw [bsp, ub.mem]
    exact hp.arg_eq haf hi
  -- a word of the arguments, in memory changed since then only within the context and `scratch`
  have argm (m : Mem) (hm : Frame [⟨(arg s 2).setWidth 64, 258⟩, ⟨(arg s 3).setWidth 64, 64⟩] d.mem m) (i : Nat)
      (hi : i < 4) : m.readW (argAddr s i) 32 = arg s i := by
    rw [← argd i hi]
    unfold arg argAddr
    rw [dsp]
    exact hm.readW (hp.arg_contains hi) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.argsCtx
      · exact hp.argsScratch) (by decide)
  refine WP.seq ?_
  rw [List.append_assoc]
  refine keepTable_wp (Sc := arg s 3) hd.addr (by rw [drd, dwr, dsp]; exact hp.arg_in (i := 3) (by decide))
    (argd 3 (by decide)) hp.scratchFit (by rw [dwr]; exact hp.scratch) fun e edx eg em erd ewr esy => ?_
  rw [List.range_eq_range']
  refine identityFrom_wp (s₀ := e) (P := arg s 2)
    (by rw [eg _ (by decide) (by decide), hd.gpr _ (by decide)]; exact ub.gpr) fit
    (by rw [ewr, dwr]; exact hT) (by rw [esy, hd.syms]; exact edx) (fun f fm fg frd fwr fsy => ?_) 16 0 e rfl
    (by rw [identityMem_zero]) rfl rfl rfl rfl
  refine wp_movi fun g₁ v₁ => ?_
  refine wp_movi fun g₂ v₂ => ?_
  refine wp_movi fun g v₃ => WP.block_nil ?_
  obtain gm : g.mem = identityMem e.mem ((arg s 2).setWidth 64) 256 := by rw [v₃.mem, v₂.mem, v₁.mem]; exact fm
  obtain gsp : g.gpr .esp = s.gpr .esp := by
    rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), fg, eg _ (by decide) (by decide)]
    exact dsp
  obtain gdi : g.gpr .edi = arg s 2 := by
    rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), fg, eg _ (by decide) (by decide),
      hd.gpr _ (by decide)]
    exact ub.gpr
  obtain grd : g.rd = s.rd := by rw [v₃.rd, v₂.rd, v₁.rd, frd, erd]; exact drd
  obtain gwr : g.wr = s.wr := by rw [v₃.wr, v₂.wr, v₁.wr, fwr, ewr]; exact dwr
  obtain gsy : g.syms = b.syms := by rw [v₃.syms, v₂.syms, v₁.syms, fsy, esy]; exact hd.syms
  have c28 : (⟨(arg s 3).setWidth 64, 64⟩ : Region).Contains (sc (arg s 3) 28) (32 / 8) :=
    Offset.contains_base _ (by decide) (by decide)
  obtain hde : Frame [⟨(arg s 2).setWidth 64, 258⟩, ⟨(arg s 3).setWidth 64, 64⟩] d.mem e.mem := by
    rw [em]; exact (Frame.refl _ _).writeW mS _ c28
  obtain heg : Frame [⟨(arg s 2).setWidth 64, 258⟩] e.mem g.mem := by
    rw [gm]; exact frame_of_table (identityMem_frame _ _ _ (by decide))
  obtain hdg : Frame [⟨(arg s 2).setWidth 64, 258⟩, ⟨(arg s 3).setWidth 64, 64⟩] d.mem g.mem :=
    hde.trans (heg.mono fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact mC)
  have wsub : ∀ r ∈ workRegions (arg s 2) (arg s 3),
      ∃ r' ∈ [(⟨(arg s 2).setWidth 64, 258⟩ : Region), ⟨(arg s 3).setWidth 64, 64⟩], Region.Sub r r' := by
    intro r hr
    simp only [workRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, mC, Region.sub_prefix (by decide)⟩
    · exact ⟨_, mS, Offset.sub_base _ (by decide)⟩
  -- from the entry to the loop: the context, the working space and the word below `esp`
  obtain hsg : Frame [below (s.gpr .esp) 4, ⟨(arg s 2).setWidth 64, 258⟩, ⟨(arg s 3).setWidth 64, 64⟩]
      s.mem g.mem := by
    refine ((haf.mono fun r hr => List.mem_cons_of_mem _ hr).trans (hfd.mono fun r hr => ?_)).trans
      (hdg.mono fun r hr => List.mem_cons_of_mem _ hr)
    simp only [List.mem_singleton] at hr
    subst hr
    exact List.mem_cons_self
  obtain hkey : keyOf g.mem (arg s 0) (arg s 1) = bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat := by
    unfold keyOf
    refine bytes_frame _ _ _ _ fun k hk => ?_
    exact hsg.bytes (R := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hkS.symm
      · exact hp.keyCtx
      · exact hp.keyScratch) (show (arg s 1).toNat ≤ 2 ^ 64 by omega) hk
  obtain hpre : SchPre g (arg s 0) (arg s 1) (arg s 2) (arg s 3) := by
    refine
      { len := hlen
        pfit := hp.ctxFit
        sfit := hp.scratchFit
        keyFit := hp.keyFit
        table := by rw [gwr]; exact hT
        scratch := by rw [gwr]; exact hp.scratch
        key := by
          rw [grd, gwr]
          obtain ⟨r, hr, hc⟩ := hp.key
          exact ⟨r, List.mem_append_left _ hr, hc⟩
        a4 := by rw [grd, gwr, gsp]; exact hp.arg_in (i := 0) (by decide)
        a8 := by rw [grd, gwr, gsp]; exact hp.arg_in (i := 1) (by decide)
        a16 := by rw [grd, gwr, gsp]; exact hp.arg_in (i := 3) (by decide)
        v4 := fun m hm => by rw [gsp]; exact argm m (hdg.trans (hm.sub wsub)) 0 (by decide)
        v8 := fun m hm => by rw [gsp]; exact argm m (hdg.trans (hm.sub wsub)) 1 (by decide)
        v16 := fun m hm => by rw [gsp]; exact argm m (hdg.trans (hm.sub wsub)) 3 (by decide)
        keyD := fun r hr => by
          simp only [workRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact (hp.keyCtx.symm.sub_left (Region.sub_prefix (by decide))).symm
          · exact (hp.keyScratch.symm.sub_left (Offset.sub_base _ (by decide))).symm
        tS := hp.ctxScratch }
  obtain s28T : Mem.Sep (sc (arg s 3) 28) 4 ((arg s 2).setWidth 64) 256 :=
    sep_of_sub hp.ctxScratch.symm
      (Offset.contains_base ((arg s 3).setWidth 64) (d := 28) (n := 4) (k := 64) (by decide) (by decide))
      (contains_prefix ((arg s 2).setWidth 64) (n := 256) (k := 258) (by decide))
  obtain hinv : SchI g (arg s 0) (arg s 1) (arg s 2) (arg s 3) 0 g := by
    refine ⟨Frame.refl _ _, ?_, ?_, ?_, ?_, gdi, rfl, rfl, rfl, rfl, ?_⟩
    · rw [gm, identityMem_table, schedule_zero]
    · rw [v₃.gpr]; rfl
    · rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr]
    · rw [v₃.other _ (by decide), v₂.gpr, Nat.zero_mod]
    · rw [gm, table_frame_readW (identityMem_frame _ _ _ (by decide)) s28T, em, Mem.readW_writeW_self32, gsy]
  refine WP.seq (WP.mono (sch_loop (by decide) hpre hinv) fun h hh => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (init_finish h (by rw [hh.p]; exact hp.ctxFit) (by rw [hh.wr, gwr, hh.p]; exact hp.ctx))
    fun f' ⟨fax, fm', fk⟩ => ?_
  rw [hh.p] at fm'
  obtain hhf : Frame [⟨(arg s 2).setWidth 64, 258⟩] h.mem f'.mem := by
    rw [fm']; exact frame_finish (Frame.refl _ _) _ _
  obtain hdf : Frame [⟨(arg s 2).setWidth 64, 258⟩, ⟨(arg s 3).setWidth 64, 64⟩] d.mem f'.mem :=
    (hdg.trans (hh.frame.sub wsub)).trans (hhf.mono fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact mC)
  obtain hsaved : Saved f'.mem (arg s 3) s := by
    obtain h0 := saved_savedMem s.mem (arg s 3) s
    rw [← ham] at h0
    obtain h1 := h0.frame hfd fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact hsS.symm.sub_left (Region.sub_prefix (by decide))
    obtain h2 := h1.frame (show Frame [⟨sc (arg s 3) 28, 4⟩] d.mem e.mem by
      rw [em]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)) fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact Offset.base_disjoint _ (by decide) (by decide)
    obtain h3 := h2.frame heg fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact (hp.ctxScratch.symm).sub_left (Region.sub_prefix (by decide))
    obtain h4 := h3.frame hh.frame fun r hr => by
      simp only [workRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ((hp.ctxScratch.sub_left (Region.sub_prefix (by decide))).symm).sub_left
          (Region.sub_prefix (by decide))
      · exact Offset.base_disjoint _ (by decide) (by decide)
    exact h4.frame hhf fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact (hp.ctxScratch.symm).sub_left (Region.sub_prefix (by decide))
  obtain hfS : f'.gpr .esp = s.gpr .esp := (fk.gpr (by decide)).trans (hh.sp.trans gsp)
  obtain hfrd : f'.rd = s.rd := fk.2.1.trans (hh.rd.trans grd)
  obtain hfwr : f'.wr = s.wr := fk.2.2.trans (hh.wr.trans gwr)
  refine WP.mono (restore_ok s f' (arg s 3) hp.scratchFit
    (by rw [hfrd, hfwr, hfS]; exact hp.arg_in (i := 3) (by decide))
    (by rw [hfS]; exact argm f'.mem hdf 3 (by decide))
    (by rw [hfrd, hfwr]; exact inr_wr hp.scratch) hsaved) fun z ⟨zbx, zsi, zdi, zbp, zm, zk⟩ => ?_
  refine ⟨(zk.gpr (by decide)).trans fax, ?_, ?_, zbx, zsi, zdi, zbp, (zk.gpr (by decide)).trans hfS⟩
  · rw [zm, fm', context_finish, hh.table, ← keySchedule_eq, hkey]
    rfl
  · rw [zm]
    refine hsg.trans ((hh.frame.sub wsub).trans (hhf.mono fun r hr => ?_) |>.mono fun r hr =>
      List.mem_cons_of_mem _ hr)
    simp only [List.mem_singleton] at hr
    subst hr
    exact mC

/-- The checked initializer. -/
theorem init_ok (s : State) (hp : InitPre s) (hsp4 : 4 ≤ (s.gpr .esp).toNat)
    (hkS : Region.Disjoint (below (s.gpr .esp) 4) ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩)
    (hsS : Region.Disjoint (below (s.gpr .esp) 4) ⟨(arg s 3).setWidth 64, 64⟩) :
    WP isa Impl.Rc4.X86.Ssse3.init s fun t =>
      (match VG.Spec.Rc4.init (bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) with
      | .ok ctx => t.gpr .eax = 0#32 ∧ contextAt t.mem ((arg s 2).setWidth 64) = ctx
      | .error .invalidKeyLength => t.gpr .eax = 1#32) ∧
      Frame [below (s.gpr .esp) 4, ⟨(arg s 2).setWidth 64, 258⟩, ⟨(arg s 3).setWidth 64, 64⟩] s.mem t.mem ∧
      t.gpr .ebx = s.gpr .ebx ∧ t.gpr .esi = s.gpr .esi ∧ t.gpr .edi = s.gpr .edi ∧ t.gpr .ebp = s.gpr .ebp ∧
      t.gpr .esp = s.gpr .esp := by
  unfold Impl.Rc4.X86.Ssse3.init
  refine WP.seq ?_
  refine w_ld rfl rfl (hp.arg_in (i := 1) (by decide)) rfl fun s₁ u₁ => ?_
  refine wp_subi fun s₂ u₂ _ _ => ?_
  refine wp_cmpi fun t u₃ cf₃ _ => WP.block_nil ?_
  obtain htm : t.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain hg : ∀ r, r ≠ .eax → t.gpr r = s.gpr r := fun r h => by rw [u₃.gpr, u₂.other _ h, u₁.other _ h]
  obtain htr : t.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  obtain htw : t.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  obtain htcf : t.cf = some (decide ((arg s 1 - 1#32).toNat < 256)) := by
    rw [cf₃, u₂.gpr, u₁.gpr]; rfl
  obtain ha : ∀ i, arg t i = arg s i := fun i => by
    unfold arg argAddr; rw [htm, hg .esp (by decide)]
  obtain htp : InitPre t := initPre_transport hp (fun i _ => ha i) (hg _ (by decide)) htr htw
  let good := 1 ≤ (arg s 1).toNat ∧ (arg s 1).toNat ≤ 256
  obtain hcond : isa.eval .ae t = some (decide (¬ good)) := by
    simp only [eval, htcf, Option.map_some]
    congr 1
    by_cases hg' : good
    · rw [decide_eq_true ((valid_length32 _).mpr hg'), decide_eq_false (not_not_intro hg')]
      rfl
    · rw [decide_eq_false (fun h => hg' ((valid_length32 _).mp h)), decide_eq_true hg']
      rfl
  refine WP.ite (decide (¬ good)) hcond (fun hn => ?_) (fun hy => ?_)
  · have hn' : ¬ good := of_decide_eq_true hn
    change ¬ (1 ≤ (arg s 1).toNat ∧ (arg s 1).toNat ≤ 256) at hn'
    simp only [VG.Spec.Rc4.init, bytes_length, hn', ite_false]
    refine wp_movi fun u v => WP.block_nil ?_
    refine ⟨v.gpr, by rw [v.mem, htm]; exact Frame.refl _ _, ?_, ?_, ?_, ?_, ?_⟩ <;>
      exact (v.other _ (by decide)).trans (hg _ (by decide))
  · have hg' : good := Classical.not_not.mp (of_decide_eq_false hy)
    change 1 ≤ (arg s 1).toNat ∧ (arg s 1).toNat ≤ 256 at hg'
    simp only [VG.Spec.Rc4.init, bytes_length, hg', and_self, ite_true]
    refine WP.mono (init_valid t htp (by rw [ha]; exact hg') (by rw [hg _ (by decide)]; exact hsp4)
      (by rw [hg _ (by decide), ha, ha]; exact hkS)
      (by rw [hg _ (by decide), ha]; exact hsS)) fun u ⟨hu0, huc, huf, hbx, hsi, hdi, hbp, hsp⟩ => ?_
    simp only [ha, htm, hg .esp (by decide)] at huc huf
    exact ⟨⟨hu0, huc⟩, huf, hbx.trans (hg _ (by decide)), hsi.trans (hg _ (by decide)),
      hdi.trans (hg _ (by decide)), hbp.trans (hg _ (by decide)), hsp.trans (hg _ (by decide))⟩

/-! ## The contracts

The baseline's (`Proof/Rc4/X86/Contract.lean`), with four bytes of stack,
which the constants' address takes. -/

open VG.Proof.Rc4 (initScratchContract applyScratchContract initScratchSig applyScratchSig ret_low)
open VG.Spec.Rc4 (initPost applyPost applyLeak)
open VG.Proof.Rc4.X86 (wideInit wideApply initSat applySat initRd initWr applyRd applyWr wideInit_pre wideApply_pre
  callee_saved applyPre_of)

/-- `Proof.Rc4.X86.initC`, with four bytes of stack apart from the buffers. -/
def initC4 : Contract isa :=
  { VG.Proof.Rc4.X86.initC with
    pre := fun s => VG.Proof.Rc4.X86.initC.pre s ∧
      (below (s.gpr .esp) 4).Disjoint ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ ∧
      (below (s.gpr .esp) 4).Disjoint ⟨(arg s 2).setWidth 64, 258⟩ ∧
      (below (s.gpr .esp) 4).Disjoint ⟨(arg s 3).setWidth 64, 64⟩ ∧ 4 ≤ (s.gpr .esp).toNat }

/-- `Proof.Rc4.X86.applyC`, with four bytes of stack apart from the buffers. -/
def applyC4 : Contract isa :=
  { VG.Proof.Rc4.X86.applyC with
    pre := fun s => VG.Proof.Rc4.X86.applyC.pre s ∧
      (below (s.gpr .esp) 4).Disjoint ⟨(arg s 0).setWidth 64, 258⟩ ∧
      (below (s.gpr .esp) 4).Disjoint ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩ ∧
      (below (s.gpr .esp) 4).Disjoint ⟨(arg s 3).setWidth 64, 64⟩ ∧ 4 ≤ (s.gpr .esp).toNat }

/-- `initC4`, with the arguments writable. -/
def wideInit4 : Contract isa :=
  { wideInit with
    pre := fun s => wideInit.pre s ∧
      (below (s.gpr .esp) 4).Disjoint ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ ∧
      (below (s.gpr .esp) 4).Disjoint ⟨(arg s 2).setWidth 64, 258⟩ ∧
      (below (s.gpr .esp) 4).Disjoint ⟨(arg s 3).setWidth 64, 64⟩ ∧ 4 ≤ (s.gpr .esp).toNat }

/-- `applyC4`, with the arguments writable. -/
def wideApply4 : Contract isa :=
  { wideApply with
    pre := fun s => wideApply.pre s ∧
      (below (s.gpr .esp) 4).Disjoint ⟨(arg s 0).setWidth 64, 258⟩ ∧
      (below (s.gpr .esp) 4).Disjoint ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩ ∧
      (below (s.gpr .esp) 4).Disjoint ⟨(arg s 3).setWidth 64, 64⟩ ∧ 4 ≤ (s.gpr .esp).toNat }

local syntax "wide_pre4 " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
local macro_rules
  | `(tactic| wide_pre4 [$ls,*]) => `(tactic| (
    intro s h
    sig_pre [$ls,*] at h
    sig_split h
    sig_reduce [$ls,*]
    sig_simp [$ls,*] []
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (rw [Taint.sub_setWidth (by omega)]
         first
           | with_reducible assumption
           | with_reducible exact Region.Disjoint.symm ‹_›)))

theorem init_implies : wideInit4.Implies (initScratchContract abi 4) where
  pre := by
    wide_pre4 [initScratchContract, initScratchSig, initPost, abi, argSlots, argVal, argBytes, wideInit4,
      wideInit, VG.Proof.Rc4.X86.initC, below]
  post := by
    sig_implies_post [initScratchContract, initScratchSig, initPost, abi, argSlots, argVal, argBytes, wideInit4,
      wideInit, VG.Proof.Rc4.X86.initC, below]
  pub := by
    sig_implies_pub [initScratchContract, initScratchSig, initPost, abi, argSlots, argVal, argBytes, wideInit4,
      wideInit, VG.Proof.Rc4.X86.initC, below]
  sat := by
    sig_implies_sat [initScratchContract, initScratchSig, initPost, abi, argSlots, argVal, argBytes, wideInit4,
      wideInit, VG.Proof.Rc4.X86.initC, below] [initSat, arg, argAddr, Mem.readW, Mem.read] using initSat

theorem apply_implies : wideApply4.Implies (applyScratchContract abi 4) where
  pre := by
    wide_pre4 [applyScratchContract, applyScratchSig, applyPost, applyLeak, abi, argSlots, argVal, argBytes,
      wideApply4, wideApply, VG.Proof.Rc4.X86.applyC, below]
  post := by
    sig_implies_post [applyScratchContract, applyScratchSig, applyPost, applyLeak, abi, argSlots, argVal, argBytes,
      wideApply4, wideApply, VG.Proof.Rc4.X86.applyC, below]
  pub := by
    sig_implies_pub [applyScratchContract, applyScratchSig, applyPost, applyLeak, abi, argSlots, argVal, argBytes,
      wideApply4, wideApply, VG.Proof.Rc4.X86.applyC, below]
  sat := by
    sig_implies_sat [applyScratchContract, applyScratchSig, applyPost, applyLeak, abi, argSlots, argVal, argBytes,
      wideApply4, wideApply, VG.Proof.Rc4.X86.applyC, below] [applySat, arg, argAddr, Mem.readW, Mem.read]
      using applySat

/-! ## The functions meet their contracts -/

/-- The return address's slot is apart from the four bytes below it. -/
theorem ret_below {sp : BitVec 32} (low : 4 ≤ sp.toNat) : Region.Disjoint ⟨sp.setWidth 64, 4⟩ (below sp 4) := by
  have hsp := sp.isLt
  obtain e : sp.setWidth 64 = (sp - BitVec.ofNat 32 4).setWidth 64 + BitVec.ofNat 64 4 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [e]
  exact (Offset.base_disjoint _ (by decide) (by decide)).symm

theorem init_correct (s : State) (hs : initC4.pre s) :
    WP isa Impl.Rc4.X86.Ssse3.init s fun s' => abiPreserved s s' ∧ initC4.post s s' := by
  obtain ⟨⟨hrd, hwr, kc, ks, cs, ac, as, rc, rs, kfit, cfit, sfit, spfit⟩, hkS, hcS, hsS, sp4⟩ := hs
  obtain hp : InitPre s :=
    { args := ⟨_, by rw [hrd]; exact List.mem_cons_of_mem _ List.mem_cons_self, Region.contains_self _ _⟩
      key := ⟨_, by rw [hrd]; exact List.mem_cons_self, Region.contains_self _ _⟩
      ctx := ⟨_, by rw [hwr]; exact List.mem_cons_self, Region.contains_self _ _⟩
      scratch := ⟨_, by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self, Region.contains_self _ _⟩
      keyFit := kfit, ctxFit := cfit, scratchFit := sfit, spFit := spfit
      keyCtx := kc, keyScratch := ks, ctxScratch := cs, argsCtx := ac, argsScratch := as }
  refine WP.mono (init_ok s hp sp4 hkS hsS) fun t ⟨hpost, hf, hbx, hsi, hdi, hbp, hsp⟩ =>
    ⟨⟨callee_saved hsp hbx hsi hdi hbp, ?_⟩, ?_⟩
  · refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [ret_below sp4, rc, rs]
  · show VG.Proof.Rc4.X86.initC.post s t
    unfold VG.Proof.Rc4.X86.initC
    dsimp only
    revert hpost
    cases Spec.Rc4.init (bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) with
    | ok c => intro hpost; exact ⟨by rw [ret_low, hpost.1]; rfl, hpost.2⟩
    | error e => cases e; intro hpost; rw [ret_low, hpost]; rfl

theorem apply_correct (s : State) (hs : applyC4.pre s) :
    WP isa Impl.Rc4.X86.Ssse3.apply s fun s' => abiPreserved s s' ∧ applyC4.post s s' := by
  obtain ⟨hb, kc, kd, ks, sp4⟩ := hs
  obtain hp := applyPre_of hb
  obtain ⟨_, _, _, _, _, _, _, _, rc, rd, rs, _⟩ := hb
  refine WP.mono (apply_ok s hp sp4 fun r hr => by
      simp only [applyRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [kc, kd, ks]) fun t ⟨hpost, hf, hbx, hsi, hdi, hbp, hsp⟩ =>
    ⟨⟨callee_saved hsp hbx hsi hdi hbp, ?_⟩, hpost⟩
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [applyRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [ret_below sp4, rc, rd, rs]

/-! ## Constant time

As the baseline's: initialization by the taint analysis alone, and the
stream function with the PRGA index `i`, which its contract lets leak, made
public by hand after `entry` (the baseline's block). The room is the four
bytes below `esp`. -/

def τI : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [258, 64], argLen := 20, argBases := [(12, 0), (16, 1)],
    room := 4 }

def τA : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [258, 0, 64], argLen := 20,
    argBases := [(4, 0), (8, 1), (16, 2)], room := 4 }

/-- After `entry`, with `i` in `eax`. -/
def τL : VG.X86.Taint.T := { τA with regs := .ofList [.esp, .eax] }

theorem τI_wf {s : State} (hs : initC4.pre s) : VG.X86.Taint.Wf τI s := by
  obtain ⟨⟨_, hwr, _, _, cs, ac, as, rc, rs, _, cfit, sfit, spfit⟩, _, hcS, hsS, sp4⟩ := hs
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨spfit, ?_⟩, ?_⟩ ?_
  · rw [hwr]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨cs, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) rc ac
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) rs as
  · intro p hp
    simp only [τI, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]
  · intro _
    refine ⟨sp4, fun r hr => ?_⟩
    have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4 = (s.gpr .esp - BitVec.ofNat 32 4).setWidth 64 :=
      (VG.X86.Taint.sub_setWidth sp4).symm
    change (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ : Region).Disjoint r
    rw [e]
    simp only [hwr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hcS, hsS]

theorem τI_agree {s t : State} (hs : initC4.pre s) (ht : initC4.pre t) (hp : initC4.pub s t) :
    VG.X86.Taint.Agree τI s t := by
  obtain ⟨sp, args⟩ := hp
  have fit : ∀ s, initC4.pre s → (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 := by
    intro s hs; obtain ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, h⟩, _⟩ := hs; exact h
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, τI_wf hs, τI_wf ht, VG.X86.Taint.slotsOk_empty,
    VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [τI, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · rw [hs.1.2.1, ht.1.2.1, args 2 (by decide), args 3 (by decide)]
  · simp only [τI] at hk
    rw [show VG.X86.Taint.depth τI.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (fit _ hs) h4 hk, VG.X86.Taint.argByte_eq (fit _ ht) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))

theorem init_ct : ConstantTime isa initC4.pre initC4.pub Impl.Rc4.X86.Ssse3.init :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) τI (fun _ _ h₁ h₂ hp => τI_agree h₁ h₂ hp) (by taint_decide)

theorem τA_wf {s : State} (hs : applyC4.pre s) : VG.X86.Taint.Wf τA s := by
  obtain ⟨⟨_, hwr, cd, cs, ds, ac, ad, as, rc, rd, rs, cfit, dfit, sfit, spfit⟩, hcS, hdS, hsS, sp4⟩ := hs
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨spfit, ?_⟩, ?_⟩ ?_
  · rw [hwr]
    exact .cons (Nat.le_refl _) (.cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil))
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨cd, cs⟩, ds, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) rc ac
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) rd ad
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) rs as
  · intro p hp
    simp only [τA, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]
  · intro _
    refine ⟨sp4, fun r hr => ?_⟩
    have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4 = (s.gpr .esp - BitVec.ofNat 32 4).setWidth 64 :=
      (VG.X86.Taint.sub_setWidth sp4).symm
    change (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ : Region).Disjoint r
    rw [e]
    simp only [hwr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hcS, hdS, hsS]

theorem τA_agree {s t : State} (hs : applyC4.pre s) (ht : applyC4.pre t) (sp : s.gpr .esp = t.gpr .esp)
    (args : ∀ i < 4, arg s i = arg t i) : VG.X86.Taint.Agree τA s t := by
  have fit : ∀ s, applyC4.pre s → (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 := by
    intro s hs; obtain ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩, _⟩ := hs; exact h
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, τA_wf hs, τA_wf ht, VG.X86.Taint.slotsOk_empty,
    VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [τA, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · rw [hs.1.2.1, ht.1.2.1, args 0 (by decide), args 1 (by decide), args 2 (by decide), args 3 (by decide)]
  · simp only [τA] at hk
    rw [show VG.X86.Taint.depth τA.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (fit _ hs) h4 hk, VG.X86.Taint.argByte_eq (fit _ ht) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))

/-- The PRGA index `i` is loaded from the context, where the taint analysis
takes it for secret: it may leak, so it is public. -/
theorem entry_ct : RelCT isa (fun a b => applyC4.pre a ∧ applyC4.pre b ∧ applyC4.pub a b)
    (.block VG.Impl.Rc4.X86.entry) fun a b => VG.X86.Taint.Agree τL a b ∧ a.zf = b.zf := by
  intro a b tr tr' a' b' ⟨hpa, hpb, hsp, hargs, hi⟩ ea eb
  have hag := τA_agree hpa hpb hsp hargs
  obtain ⟨htrace, -⟩ := RelCT.taint (A := VG.X86.sseTaint) (P := fun a b => VG.X86.Taint.Agree τA a b)
    τA (fun _ _ h => h) (by taint_decide) a b tr tr' a' b' hag ea eb
  obtain ⟨_, u, eu, ham, hak, hax, haz⟩ := apply_entry a (applyPre_of hpa.1)
  obtain ⟨_, rfl⟩ := Exec.det eu ea
  obtain ⟨_, v, ev, hbm, hbk, hbx, hbz⟩ := apply_entry b (applyPre_of hpb.1)
  obtain ⟨_, rfl⟩ := Exec.det ev eb
  have hi' : (contextAt a.mem ((arg a 0).setWidth 64)).i = (contextAt b.mem ((arg b 0).setWidth 64)).i :=
    BitVec.eq_of_toNat_eq (List.cons.inj hi).1
  have hsp₁ : u.gpr .esp = a.gpr .esp := hak.gpr (by decide)
  have hsp₂ : v.gpr .esp = b.gpr .esp := hbk.gpr (by decide)
  refine ⟨htrace, VG.X86.Taint.Agree.keep hag ⟨fun r hr => ?_, fun h => nomatch h⟩ rfl rfl rfl rfl
    rfl hak.2.2 hbk.2.2 ham hbm hsp₁ hsp₂ (fun _ h => (List.not_mem_nil h).elim)
    (fun _ h => (List.not_mem_nil h).elim), ?_⟩
  · simp only [τL, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hsp₁, hsp₂, hsp]
    · rw [hax, hbx, hi']
  · rw [haz, hbz, hargs 2 (by decide)]

theorem apply_ct : ConstantTime isa applyC4.pre applyC4.pub Impl.Rc4.X86.Ssse3.apply := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  unfold Impl.Rc4.X86.Ssse3.apply
  refine RelCT.seq entry_ct (RelCT.ite ?_ VG.Proof.Rc4.X86.nil_ct ?_)
  · intro a b ⟨_, hz⟩
    simp only [eval, hz]
  · exact RelCT.taint (A := VG.X86.sseTaint) τL (fun _ _ h => h.1.1) (by taint_decide)

/-! ## `Verified` -/

local macro "narrow4" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| plain_simp_names simp only [VG.Proof.Rc4.X86.Ssse3.initC4, VG.Proof.Rc4.X86.Ssse3.wideInit4,
                     VG.Proof.Rc4.X86.Ssse3.applyC4, VG.Proof.Rc4.X86.Ssse3.wideApply4,
                     VG.Proof.Rc4.X86.initC, VG.Proof.Rc4.X86.wideInit,
                     VG.Proof.Rc4.X86.applyC, VG.Proof.Rc4.X86.wideApply,
                     VG.Proof.Rc4.X86.initRd, VG.Proof.Rc4.X86.initWr,
                     VG.Proof.Rc4.X86.applyRd, VG.Proof.Rc4.X86.applyWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $(loc)?)

theorem wideInit4_pre (s : State) (h : wideInit4.pre s) : initC4.pre (s.withRegions (initRd s) (initWr s)) := by
  refine ⟨wideInit_pre s h.1, ?_⟩
  simp only [VG.X86.arg_withRegions, VG.X86.State.withRegions_gpr]
  exact h.2

theorem wideApply4_pre (s : State) (h : wideApply4.pre s) :
    applyC4.pre (s.withRegions (applyRd s) (applyWr s)) := by
  refine ⟨wideApply_pre s h.1, ?_⟩
  simp only [VG.X86.arg_withRegions, VG.X86.State.withRegions_gpr]
  exact h.2

theorem init_verified : Verified target Impl.Rc4.X86.Ssse3.init (initScratchContract abi 4) := by
  have hsat := init_implies.sat_left
  obtain narrowSat : ∃ s, initC4.pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wideInit4_pre s hs⟩
  apply Verified.of_implies _ init_implies
  refine Verified.narrowTo (Verified.of_correct init_correct init_ct (.refl narrowSat))
    initRd initWr wideInit4_pre ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨⟨rd, wr, _⟩, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [initRd, initWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp only [h, true_or, or_true]
  · intro s h
    obtain ⟨⟨_, wr, _⟩, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [initWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp only [h, true_or, or_true]
  · intro s s' _ h
    narrow4 at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    narrow4
    exact h

theorem apply_verified : Verified target Impl.Rc4.X86.Ssse3.apply (applyScratchContract abi 4) := by
  have hsat := apply_implies.sat_left
  obtain narrowSat : ∃ s, applyC4.pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wideApply4_pre s hs⟩
  apply Verified.of_implies _ apply_implies
  refine Verified.narrowTo (Verified.of_correct apply_correct apply_ct (.refl narrowSat))
    applyRd applyWr wideApply4_pre ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨⟨rd, wr, _⟩, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [applyRd, applyWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp only [h, true_or, or_true]
  · intro s h
    obtain ⟨⟨_, wr, _⟩, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [applyWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp only [h, true_or, or_true]
  · intro s s' _ h
    narrow4 at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    narrow4
    exact h

/-! ## The working space on the stack, and the functions as emitted

The functions run their code in a frame of 88 bytes, which allocates the 64
bytes of working space and copies the three argument slots
(`Verified.stackScratch`); with the four bytes the code uses below it, 92
bytes of stack, which the emitted functions zero before returning. -/

theorem initFrameSat_pre : ∃ s, (Spec.Rc4.initContract X86.abi 92).pre s := by
  implies_sat [Spec.Rc4.initContract, Spec.Rc4.initSig, Spec.Rc4.initPost, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes] [VG.Proof.Rc4.X86.initFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using VG.Proof.Rc4.X86.initFrameSat

theorem applyFrameSat_pre : ∃ s, (Spec.Rc4.applyContract X86.abi 92).pre s := by
  implies_sat [Spec.Rc4.applyContract, Spec.Rc4.applySig, Spec.Rc4.applyPost, Spec.Rc4.applyLeak,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [VG.Proof.Rc4.X86.applyFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using VG.Proof.Rc4.X86.applyFrameSat

theorem init_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 88 3 Impl.Rc4.X86.Ssse3.init)
      (Spec.Rc4.initContract X86.abi 92) :=
  X86.Verified.stackScratch (sig := Spec.Rc4.initSig) (nm := "scratch") (e := .u64) (n := 8)
    (post := Spec.Rc4.initPost X86.abi.ptrBits) (wa := true) (stack := 4) (bytes := 88)
    init_verified (by decide) (by lit_decide) (by lit_decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Rc4.initPost_local _)
    (fun vs m m₁ m₂ r hl _ hb h => Proof.Rc4.initPostOut_local _ vs m m₁ m₂ r hl hb h) initFrameSat_pre

theorem apply_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 88 3 Impl.Rc4.X86.Ssse3.apply)
      (Spec.Rc4.applyContract X86.abi 92) :=
  X86.Verified.stackScratch (sig := Spec.Rc4.applySig) (nm := "scratch") (e := .u64) (n := 8)
    (post := Spec.Rc4.applyPost X86.abi.ptrBits) (wa := true) (stack := 4) (bytes := 88)
    (leak := some (Spec.Rc4.applyLeak X86.abi.ptrBits))
    apply_verified (by decide) (by lit_decide) (by lit_decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Rc4.applyPost_local _)
    (fun vs m m₁ m₂ r hl _ hb h => Proof.Rc4.applyPostOut_local _ vs m m₁ m₂ r hl hb h) applyFrameSat_pre
    (hleak := Proof.Rc4.applyLeak_local _)

open VG.X86.Scrub (verifiedScrubbedAll PostOut postOut_of_local ScrubAbi)

theorem initOut : PostOut (Spec.Rc4.initContract X86.abi 92) (Spec.Rc4.initSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Rc4.initPostOut_local _)

theorem applyOut : PostOut (Spec.Rc4.applyContract X86.abi 92) (Spec.Rc4.applySig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Rc4.applyPostOut_local _)

/-- `Spec.Rc4.initApi` as emitted for SSSE3 (`Impl.Rc4.X86.Ssse3.Fn.init`) meets
its contract in constant time and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed X86.target Impl.Rc4.X86.Ssse3.Fn.init (Spec.Rc4.initContract X86.abi 92) 32 :=
  verifiedScrubbedAll (api := Spec.Rc4.initApi)
    { suffix := "_ssse3"
      code := Impl.StackScratch.X86.withStackScratch 88 3 Impl.Rc4.X86.Ssse3.init
      verified := init_framed }
    initOut

/-- `Spec.Rc4.applyApi` as emitted for SSSE3 (`Impl.Rc4.X86.Ssse3.Fn.apply`)
meets its contract in constant time and returns without secret residue. -/
theorem apply_scrubbed :
    VerifiedScrubbed X86.target Impl.Rc4.X86.Ssse3.Fn.apply (Spec.Rc4.applyContract X86.abi 92) 0 :=
  verifiedScrubbedAll (api := Spec.Rc4.applyApi)
    { suffix := "_ssse3"
      code := Impl.StackScratch.X86.withStackScratch 88 3 Impl.Rc4.X86.Ssse3.apply
      verified := apply_framed }
    applyOut

end VG.Proof.Rc4.X86.Ssse3

