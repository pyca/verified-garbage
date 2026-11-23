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

theorem g_add {d r : Reg} {V W : BitVec 32} (hd : s.gpr d = V) (hr : s.gpr r = W)
    (k : ∀ s', GU s s' d (V + W) → WP isa (.block is) s' Q) : WP isa (.block (.alu .add d (.reg r) :: is)) s Q := by
  subst hd hr
  exact cons rfl (k _ (GU.flags _ _ _ _ _ _))

theorem g_or {d r : Reg} {V W : BitVec 32} (hd : s.gpr d = V) (hr : s.gpr r = W)
    (k : ∀ s', GU s s' d (V ||| W) → WP isa (.block is) s' Q) : WP isa (.block (.alu .or d (.reg r) :: is)) s Q := by
  subst hd hr
  exact cons rfl (k _ (GU.flags _ _ _ _ _ _))

theorem g_ori {d : Reg} {n : Nat} {V : BitVec 32} (hd : s.gpr d = V)
    (k : ∀ s', GU s s' d (V ||| BitVec.ofNat 32 n) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d (imm n) :: is)) s Q := by
  subst hd
  exact cons rfl (k _ (GU.flags _ _ _ _ _ _))

theorem g_orm {d b : Reg} {B V W : BitVec 32} {o : Nat} {a : Addr} (hd : s.gpr d = V) (hb : s.gpr b = B)
    (ha : addr B o = a) (hin : InRegions (s.rd ++ s.wr) a 4) (hv : s.mem.readW a 32 = W)
    (k : ∀ s', GU s s' d (V ||| W) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d (.mem (at_ b o)) :: is)) s Q := by
  subst ha hv hd
  exact cons (by simp [reduceExec, at_, execAlu, readSrc_mem hb hin]; rfl) (k _ (GU.flags _ _ _ _ _ _))

theorem g_ror {d : Reg} {n : Nat} {V : BitVec 32} (hn : 1 ≤ n ∧ n ≤ 31) (hd : s.gpr d = V)
    (k : ∀ s', GU s s' d (V.rotateRight n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .ror d n :: is)) s Q := by
  subst hd
  exact cons (by simp only [reduceExec, execShift, hn, and_self, ite_true]; rfl) (k _ (GU.setFlags _ _ _ _ _ _ _))

theorem m_st {b r : Reg} {B V : BitVec 32} {o : Nat} {a : Addr} (hb : s.gpr b = B) (ha : addr B o = a)
    (hout : InRegions s.wr a 4) (hr : s.gpr r = V)
    (k : ∀ s', MU s s' (s.mem.writeW a V) → WP isa (.block is) s' Q) :
    WP isa (.block (.store (at_ b o) r :: is)) s Q := by
  subst ha hr
  refine cons (s' := { s with mem := s.mem.writeW (addr B o) (s.gpr r) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp [reduceExec, at_, State.store32, ea_mk, hb, hout]

theorem x_ldm {d : XReg} {b : Reg} {B : BitVec 32} {o : Nat} {a : Addr} {V : BitVec 128} (hb : s.gpr b = B)
    (ha : addr B o = a) (hin : InRegions (s.rd ++ s.wr) a 16) (hv : s.mem.readW a 128 = V)
    (k : ∀ s', XU s s' d V → WP isa (.block is) s' Q) : WP isa (.block (.movdquLoad d (at_ b o) :: is)) s Q := by
  subst ha hv
  exact cons (show (State.load128 s (s.ea (at_ b o))).map _ = _ by
    rw [show s.ea (at_ b o) = addr B o by rw [← hb]; rfl, State.load128, ite_eq_left hin]; rfl) (k _ (XU.set _ _ _))

theorem x_stm {r : XReg} {b : Reg} {B : BitVec 32} {o : Nat} {a : Addr} {V : BitVec 128} (hb : s.gpr b = B)
    (ha : addr B o = a) (hout : InRegions s.wr a 16) (hr : s.xmm r = V)
    (k : ∀ s', MU s s' (s.mem.writeW a V) → WP isa (.block is) s' Q) :
    WP isa (.block (.movdquStore (at_ b o) r :: is)) s Q := by
  subst ha hr
  exact cons (s' := { s with mem := s.mem.writeW (addr B o) (s.xmm r) })
    (show State.store128 s (s.ea (at_ b o)) (s.xmm r) = _ by
      rw [show s.ea (at_ b o) = addr B o by rw [← hb]; rfl, State.store128, ite_eq_left hout])
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

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

theorem cst_H : ∀ b < 16, byte (cst oH) b = 0x80#8 := by lit_decide

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

theorem tab_len : table.length = 68 := rfl

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

/-! ## The byte the exchange took out -/

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

/-! ## The exchange -/

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

/-! ### Two columns at a time -/

/-- `movd` of a doubleword. -/
theorem byte_movd32 (v : BitVec 32) {k : Nat} (hk : k < 4) :
    byte ((0 : BitVec 96) ++ v) k = v.extractLsb' (8 * k) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h32 : 8 * k + i < 32 := by omega
  rw [byte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi, h32]

/-- Two bytes in a register: the first. -/
theorem pack_lo (a b : Byte) : (a.setWidth 32 ||| (b.setWidth 32).rotateRight 24).extractLsb' 0 8 = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb : b.getLsbD (24 + i) = false := BitVec.getLsbD_of_ge b _ (by omega)
  simp [hi, hb, show i < 32 by omega]

/-- Two bytes in a register: the second. -/
theorem pack_hi (a b : Byte) : (a.setWidth 32 ||| (b.setWidth 32).rotateRight 24).extractLsb' 8 8 = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi, show 8 + i < 32 by omega]
  intro h
  omega

/-- `palignr a, b, 2`: `b` two bytes down, and `a`'s bytes 0 and 1 on top. -/
theorem byte_align2 (a b : BitVec 128) {l : Nat} (hl : l < 16) :
    byte (alignRight a b 2) l = if l < 14 then byte b (l + 2) else byte a (l - 14) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [byte, alignRight, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_append, show (2 : BitVec 8).toNat * 8 = 16 from rfl]
  by_cases h : l < 14
  · rw [ite_eq_left h, byte, BitVec.getLsbD_extractLsb']
    simp [hi]
    rw [decide_eq_true (by omega), Bool.true_and, ite_eq_left (by omega),
      show 16 + (8 * l + i) = 8 * (l + 2) + i by omega]
  · rw [ite_eq_right h, byte, BitVec.getLsbD_extractLsb']
    simp [hi]
    rw [decide_eq_true (by omega), Bool.true_and, ite_eq_right (by omega),
      show 16 + (8 * l + i) - 128 = 8 * (l - 14) + i by omega]

/-- The selector of a row's byte in a half's column: twice the row's number
in its half, with the top bit for the second half. -/
theorem sel_facts : ∀ h < 16,
    (BitVec.ofNat 8 (2 * (h % 8) + 128 * (h / 8))).msb = decide (8 ≤ h) ∧
    ((BitVec.ofNat 8 (2 * (h % 8) + 128 * (h / 8))).extractLsb' 0 4).toNat = 2 * (h % 8) ∧
    (BitVec.ofNat 8 (2 * (h % 8) + 128 * (h / 8)) ^^^ 0x80#8).msb = !decide (8 ≤ h) ∧
    ((BitVec.ofNat 8 (2 * (h % 8) + 128 * (h / 8)) ^^^ 0x80#8).extractLsb' 0 4).toNat = 2 * (h % 8) ∧
    (BitVec.ofNat 8 (2 * (h % 8) + 128 * (h / 8) + 1)).msb = decide (8 ≤ h) ∧
    ((BitVec.ofNat 8 (2 * (h % 8) + 128 * (h / 8) + 1)).extractLsb' 0 4).toNat = 2 * (h % 8) + 1 ∧
    (BitVec.ofNat 8 (2 * (h % 8) + 128 * (h / 8) + 1) ^^^ 0x80#8).msb = !decide (8 ≤ h) ∧
    ((BitVec.ofNat 8 (2 * (h % 8) + 128 * (h / 8) + 1) ^^^ 0x80#8).extractLsb' 0 4).toNat = 2 * (h % 8) + 1 ∧
    (BitVec.ofNat 8 (2 * (h % 8) + 128 * (h / 8))).setWidth 32 ||| 1#32 =
      (BitVec.ofNat 8 (2 * (h % 8) + 128 * (h / 8) + 1)).setWidth 32 := by
  decide

theorem sel32 : ∀ h < 16, ∀ l < 16,
    (BitVec.ofNat 8 (16 * h + l)).setWidth 32 &&& 128#32 |||
        ((BitVec.ofNat 8 (16 * h + l)).setWidth 32 >>> 3 &&& 14#32) =
      (BitVec.ofNat 8 (2 * (h % 8) + 128 * (h / 8))).setWidth 32 := by
  decide

theorem sel_reg (t : Byte) : t.setWidth 32 &&& 128#32 ||| (t.setWidth 32 >>> 3 &&& 14#32) =
    (BitVec.ofNat 8 (2 * (t.toNat / 16 % 8) + 128 * (t.toNat / 16 / 8))).setWidth 32 := by
  have ht := t.isLt
  have h := sel32 (t.toNat / 16) (by omega) (t.toNat % 16) (by omega)
  rwa [show 16 * (t.toNat / 16) + t.toNat % 16 = t.toNat by omega, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h

/-! ### The first pass, with the difference known -/

theorem regs_ne (r : Nat) : maskReg r ≠ rowReg r ∧ maskReg r ≠ .xmm4 ∧ maskReg r ≠ .xmm5 ∧ rowReg r ≠ .xmm4 ∧
    rowReg r ≠ .xmm5 := by
  rcases (by omega : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2) with h | h | h <;> simp [maskReg, rowReg, h]

/-- A row of the pass: the byte `j` is exclusive-ored with `d` if it is the
row's. -/
theorem xorRow_wp {s : State} {P : BitVec 32} {j d : Byte} {r : Nat} {is : List Instr} {Q : State → Prop}
    (hr : r < 16) (hdi : s.gpr .edi = P) (fit : P.toNat + 256 ≤ 2 ^ 32)
    (hw : InRegions s.wr (P.setWidth 64) 256) (htb : s.gpr tbr = s.syms tableName) (hX : IsX (s.xmm .xmm4) j)
    (hS : IsSi (s.xmm .xmm5) d j)
    (k : ∀ s', s'.mem = (if j.toNat / 16 = r then s.mem.write (P.setWidth 64 + BitVec.ofNat 64 j.toNat) 1
          (s.mem (P.setWidth 64 + BitVec.ofNat 64 j.toNat) ^^^ d) else s.mem) →
        s'.xmm .xmm4 = s.xmm .xmm4 → s'.xmm .xmm5 = s.xmm .xmm5 → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
        s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (xorRow r ++ is)) s Q := by
  have hj := j.isLt
  obtain ⟨n1, n2, n3, n4, n5⟩ := regs_ne r
  simp only [xorRow, List.cons_append, List.nil_append]
  obtain ea : addr P (16 * r) = P.setWidth 64 + BitVec.ofNat 64 (16 * r) := addr_eq (by omega)
  obtain hrow : InRegions s.wr (P.setWidth 64 + BitVec.ofNat 64 (16 * r)) 16 :=
    region_offset _ _ _ _ _ (by omega) (by omega) hw
  refine x_tb htb ⟨by unfold oC; omega, by rw [tab_len]; unfold oC; omega⟩ fun s₁ u₁ => ?_
  refine x_bin u₁.xmm (u₁.other _ n2.symm) fun s₂ u₂ => ?_
  refine x_bin u₂.xmm ((u₂.other _ n3.symm).trans (u₁.other _ n3.symm)) fun s₃ u₃ => ?_
  refine x_ld (show s₃.gpr .edi = P by rw [u₃.gpr, u₂.gpr, u₁.gpr]; exact hdi) ea
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact (by obtain ⟨R, hR, hc⟩ := hrow; exact ⟨R, List.mem_append_right _ hR, hc⟩ : InRegions (s.rd ++ s.wr) (P.setWidth 64 + BitVec.ofNat 64 (16 * r)) 16))
    (show s₃.mem.readW _ 128 = s.mem.readW _ 128 by rw [u₃.mem, u₂.mem, u₁.mem]) fun s₄ u₄ => ?_
  refine x_bin u₄.xmm ((u₄.other _ n1).trans u₃.xmm) fun s₅ u₅ => ?_
  refine x_st (show s₅.gpr .edi = P by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]; exact hdi) ea
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hrow) u₅.xmm fun s₆ u₆ => ?_
  refine k s₆ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem,
      writeW_row s.mem _ _ (c := s.mem (P.setWidth 64 + BitVec.ofNat 64 (16 * r) + BitVec.ofNat 64 (j.toNat % 16)) ^^^ d)
        (l₀ := j.toNat % 16) (P := j.toNat / 16 = r) (by omega) (fun l hl => by
        rw [show XBinOp.eval .pxor (s.mem.readW (P.setWidth 64 + BitVec.ofNat 64 (16 * r)) 128)
            (XBinOp.eval .pand (XBinOp.eval .pshufb (cst (oC r)) (s.xmm .xmm4)) (s.xmm .xmm5)) =
            s.mem.readW (P.setWidth 64 + BitVec.ofNat 64 (16 * r)) 128 ^^^
              (XBinOp.eval .pshufb (cst (oC r)) (s.xmm .xmm4) &&& s.xmm .xmm5) from rfl,
          byte_xor, byte_and, byte_mask hX hr hl, hS l hl, byte_row _ _ hl]
        by_cases h : l = j.toNat % 16 ∧ j.toNat / 16 = r
        · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h.1, BitVec.and_comm, and_ff, h.1]
        · rw [ite_eq_right h, ite_eq_right h, BitVec.zero_and, BitVec.xor_zero])]
    by_cases h : j.toNat / 16 = r
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl, row_addr]
    · rw [ite_eq_right h, ite_eq_right h]
  · rw [u₆.xmm, u₅.other _ n4.symm, u₄.other _ n4.symm, u₃.other _ n2.symm, u₂.other _ n2.symm, u₁.other _ n2.symm]
  · rw [u₆.xmm, u₅.other _ n5.symm, u₄.other _ n5.symm, u₃.other _ n3.symm, u₂.other _ n3.symm, u₁.other _ n3.symm]
  · rw [u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]

/-- The rows from the row `r` on. -/
theorem xorFrom_wp {s₀ : State} {P : BitVec 32} {j d : Byte} {is : List Instr} {Q : State → Prop}
    (hdi : s₀.gpr .edi = P) (fit : P.toNat + 256 ≤ 2 ^ 32) (hw : InRegions s₀.wr (P.setWidth 64) 256)
    (htb : s₀.gpr tbr = s₀.syms tableName) (hX : IsX (s₀.xmm .xmm4) j) (hS : IsSi (s₀.xmm .xmm5) d j)
    (k : ∀ s', s'.mem = s₀.mem.write (P.setWidth 64 + BitVec.ofNat 64 j.toNat) 1
          (s₀.mem (P.setWidth 64 + BitVec.ofNat 64 j.toNat) ^^^ d) → s'.gpr = s₀.gpr → s'.rd = s₀.rd →
        s'.wr = s₀.wr → s'.syms = s₀.syms → WP isa (.block is) s' Q) :
    ∀ (n r : Nat) (s : State), r + n = 16 →
      s.mem = (if j.toNat / 16 < r then s₀.mem.write (P.setWidth 64 + BitVec.ofNat 64 j.toNat) 1
        (s₀.mem (P.setWidth 64 + BitVec.ofNat 64 j.toNat) ^^^ d) else s₀.mem) →
      s.xmm .xmm4 = s₀.xmm .xmm4 → s.xmm .xmm5 = s₀.xmm .xmm5 → s.gpr = s₀.gpr → s.rd = s₀.rd → s.wr = s₀.wr →
      s.syms = s₀.syms → WP isa (.block ((List.range' r n).flatMap xorRow ++ is)) s Q
  | 0, r, s, e, hm, _, _, hg, hrd, hwr, hsy => by
    have hj := j.isLt
    obtain rfl : r = 16 := by omega
    exact k s (by rw [hm, ite_eq_left (by omega)]) hg hrd hwr hsy
  | n + 1, r, s, e, hm, h4, h5, hg, hrd, hwr, hsy => by
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    refine xorRow_wp (by omega) (by rw [hg]; exact hdi) fit (by rw [hwr]; exact hw) (by rw [hg, hsy]; exact htb)
      (by rw [h4]; exact hX) (by rw [h5]; exact hS) fun s' m' x4 x5 g' rd' wr' sy' =>
      xorFrom_wp hdi fit hw htb hX hS k n (r + 1) s' (by omega) ?_ (x4.trans h4) (x5.trans h5) (g'.trans hg)
        (rd'.trans hrd) (wr'.trans hwr) (sy'.trans hsy)
    rw [m', hm]
    rcases Classical.propComplete (j.toNat / 16 = r) with c1 | c1
    · have c0 : (j.toNat / 16 < r) = False := by simp only [eq_iff_iff, iff_true, iff_false] at c1 ⊢; omega
      have c2 : (j.toNat / 16 < r + 1) = True := by simp only [eq_iff_iff, iff_true] at c1 ⊢; omega
      simp only [c0, c1, c2, ↓reduceIte]
    · rcases Classical.propComplete (j.toNat / 16 < r) with c0 | c0
      · have c2 : (j.toNat / 16 < r + 1) = True := by simp only [eq_iff_iff, iff_true] at c0 ⊢; omega
        simp only [c0, c1, c2, ↓reduceIte]
      · have c2 : (j.toNat / 16 < r + 1) = False := by
          simp only [eq_iff_iff, iff_false] at c0 c1 ⊢; omega
        simp only [c0, c1, c2, ↓reduceIte]

/-- The first pass: the byte `j` of the table is exclusive-ored with `d`. -/
theorem xorRows_wp {s : State} {P : BitVec 32} {j d : Byte} {is : List Instr} {Q : State → Prop}
    (hdi : s.gpr .edi = P) (fit : P.toNat + 256 ≤ 2 ^ 32) (hw : InRegions s.wr (P.setWidth 64) 256)
    (htb : s.gpr tbr = s.syms tableName) (hX : IsX (s.xmm .xmm4) j) (hS : IsSi (s.xmm .xmm5) d j)
    (k : ∀ s', s'.mem = s.mem.write (P.setWidth 64 + BitVec.ofNat 64 j.toNat) 1
          (s.mem (P.setWidth 64 + BitVec.ofNat 64 j.toNat) ^^^ d) → s'.gpr = s.gpr → s'.rd = s.rd →
        s'.wr = s.wr → s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (xorRows ++ is)) s Q := by
  rw [xorRows, List.range_eq_range']
  exact xorFrom_wp hdi fit hw htb hX hS k 16 0 s rfl (ite_eq_right (by omega)).symm rfl rfl rfl rfl rfl rfl

/-! ### The pieces of the stream function's iteration -/

/-- A word of the working space is apart from another's write. -/
theorem sc_rw (m : Mem) (Sc : BitVec 32) {a b : Nat} (v : BitVec 32) (h : a + 4 ≤ b ∨ b + 4 ≤ a)
    (ha : a + 4 ≤ 64) (hb : b + 4 ≤ 64) : (m.writeW (sc Sc a) v).readW (sc Sc b) 32 = m.readW (sc Sc b) 32 :=
  Mem.readW_writeW_sep (show Mem.Sep _ (32 / 8) _ (32 / 8) from
    Offset.sep (Sc.setWidth 64) (d := b) (n := 4) (e := a) (k := 4) (by omega) (by omega) (by omega)) (by decide)

theorem hi16 : ∀ h < 16, ∀ l < 16,
    (BitVec.ofNat 8 (16 * h + l)).setWidth 32 &&& 240#32 = BitVec.ofNat 32 (16 * h) := by
  decide

/-- The row of the byte `i`, from its index in a register. -/
theorem irow_addr {P : BitVec 32} (fit : P.toNat + 256 ≤ 2 ^ 32) (i : Byte) :
    addr ((i.setWidth 32 &&& BitVec.ofNat 32 240) + P) 0 =
      P.setWidth 64 + BitVec.ofNat 64 (16 * (i.toNat / 16)) := by
  have hi := i.isLt
  have h := hi16 (i.toNat / 16) (by omega) (i.toNat % 16) (by omega)
  rw [show 16 * (i.toNat / 16) + i.toNat % 16 = i.toNat by omega, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  rw [h, BitVec.add_comm]
  exact key_addr (K := P) (Lk := 256#32) (by have : (256#32).toNat = 256 := rfl; omega)
    (by have : (256#32).toNat = 256 := rfl; omega)

/-- The borrow of `(x ^^^ y) - 1`: whether the bytes are equal. -/
theorem mask_eq (x y : Byte) :
    decide ((x.setWidth 32 ^^^ y.setWidth 32).toNat < (BitVec.ofNat 32 1).toNat) = decide (y = x) := by
  have e : ((x ^^^ y).setWidth 32).toNat = (x ^^^ y).toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := (x ^^^ y).isLt; omega)
  rw [xor_byte32, e, show (BitVec.ofNat 32 1).toNat = 1 from rfl]
  by_cases h : y = x
  · subst h
    rw [BitVec.xor_self]
    simp
  · rw [decide_eq_false h, decide_eq_false]
    intro h1
    exact h (BitVec.xor_eq_zero_iff.mp (BitVec.eq_of_toNat_eq (by simpa using Nat.lt_one_iff.mp h1))).symm

/-- A byte or another, by a mask of all ones or zero. -/
theorem next_val (s1 si : Byte) (c : Bool) :
    ((s1.setWidth 32 ^^^ si.setWidth 32) &&& (if c then BitVec.allOnes 32 else 0)) ^^^ s1.setWidth 32 =
      (if c then si else s1).setWidth 32 := by
  cases c
  · simp
  · simp only [ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm (s1.setWidth 32), BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- The next `S[i]` to its slot: the table's byte at `i + 1`, or `S[i]` where
`j = i + 1`. -/
theorem nextSi_wp {s : State} {P Sc : BitVec 32} {i j si : Byte} {is : List Instr} {Q : State → Prop}
    (hsi : s.gpr .esi = i.setWidth 32) (hbp : s.gpr .ebp = j.setWidth 32) (hdi : s.gpr .edi = P)
    (fit : P.toNat + 256 ≤ 2 ^ 32) (hrg : InRegions (s.rd ++ s.wr) (P.setWidth 64) 256)
    (ha16 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4) (hv16 : s.mem.readW (addr (s.gpr .esp) 16) 32 = Sc)
    (sfit : Sc.toNat + 64 ≤ 2 ^ 32) (hws : InRegions s.wr (Sc.setWidth 64) 64)
    (v24 : s.mem.readW (sc Sc 24) 32 = si.setWidth 32)
    (k : ∀ s', s'.gpr .edx = Sc → (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) →
      s'.mem = (s.mem.writeW (sc Sc 36) ((s.mem (P.setWidth 64 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 32)).writeW
        (sc Sc 36) ((if j = i + 1#8 then si else
          s.mem (P.setWidth 64 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 32) →
      s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (nextSi ++ is)) s Q := by
  have hi1 := (i + 1#8).isLt
  obtain w36 : InRegions s.wr (sc Sc 36) 4 := region_offset _ _ _ 36 4 (by decide) (by decide) hws
  obtain r24 : InRegions (s.rd ++ s.wr) (sc Sc 24) 4 := inr_wr (region_offset _ _ _ 24 4 (by decide) (by decide) hws)
  simp only [nextSi, List.cons_append, List.nil_append]
  refine w_mov hsi fun s₁ u₁ => ?_
  refine w_addi u₁.gpr fun s₂ u₂ => ?_
  refine w_andi u₂.gpr fun s₃ u₃ => ?_
  obtain cx₃ : s₃.gpr .ecx = (i + 1#8).setWidth 32 := by rw [u₃.gpr, byte_inc32]
  refine w_mov (show s₃.gpr .edi = P by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact hdi) fun s₄ u₄ => ?_
  refine w_add u₄.gpr ((u₄.other _ (by decide)).trans cx₃) fun s₅ u₅ => ?_
  refine w_lb u₅.gpr (idx_addr fit (i + 1#8))
    (by
      rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
      exact region_offset _ _ _ _ _ (by omega) (by omega) hrg)
    (by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]) fun s₆ u₆ => ?_
  refine w_xor (show s₆.gpr .ecx = (i + 1#8).setWidth 32 by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide)]; exact cx₃)
    (show s₆.gpr .ebp = j.setWidth 32 by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide)]; exact hbp) fun s₇ u₇ => ?_
  refine wp_subi fun s₈ u₈ cf₈ _ => ?_
  refine wp_sbb_self (c := decide (j = i + 1#8)) (by rw [cf₈, u₇.gpr, mask_eq]) fun s₉ u₉ => ?_
  obtain ax₉ : s₉.gpr .eax = (s.mem (P.setWidth 64 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 32 := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide)]; exact u₆.gpr
  obtain m₉ : s₉.mem = s.mem := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain rd₉ : s₉.rd = s.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr₉ : s₉.wr = s.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have g₉ (r : Reg) (h0 : r ≠ .eax) (h1 : r ≠ .ecx) : s₉.gpr r = s.gpr r := by
    rw [u₉.other _ h1, u₈.other _ h1, u₇.other _ h1, u₆.other _ h0, u₅.other _ h0, u₄.other _ h0, u₃.other _ h1,
      u₂.other _ h1, u₁.other _ h1]
  refine w_ld (g₉ .esp (by decide) (by decide)) rfl (by rw [rd₉, wr₉]; exact ha16)
    (show s₉.mem.readW _ 32 = Sc by rw [m₉]; exact hv16) fun s₁₀ u₁₀ => ?_
  refine w_st u₁₀.gpr (show addr Sc sNext = sc Sc 36 from sc_addr sfit (by decide))
    (by rw [u₁₀.wr, wr₉]; exact w36) ((u₁₀.other _ (by decide)).trans ax₉) fun s₁₁ u₁₁ => ?_
  refine w_xm (show s₁₁.gpr .eax = _ from (congrFun u₁₁.gpr _).trans ((u₁₀.other _ (by decide)).trans ax₉))
    ((congrFun u₁₁.gpr _).trans u₁₀.gpr) (show addr Sc sSi = sc Sc 24 from sc_addr sfit (by decide))
    (by rw [u₁₁.rd, u₁₁.wr, u₁₀.rd, u₁₀.wr, rd₉, wr₉]; exact r24)
    (show s₁₁.mem.readW (sc Sc 24) 32 = si.setWidth 32 by
      rw [u₁₁.mem, u₁₀.mem, m₉, sc_rw _ _ _ (by decide) (by decide) (by decide)]; exact v24) fun s₁₂ u₁₂ => ?_
  refine wp_and fun s₁₃ u₁₃ => ?_
  refine w_xm (show s₁₃.gpr .eax = _ by
      rw [u₁₃.gpr, u₁₂.gpr, u₁₂.other _ (by decide), congrFun u₁₁.gpr _, u₁₀.other _ (by decide), u₉.gpr])
    (show s₁₃.gpr .edx = Sc by
      rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), congrFun u₁₁.gpr _]; exact u₁₀.gpr)
    (show addr Sc sNext = sc Sc 36 from sc_addr sfit (by decide))
    (by rw [u₁₃.rd, u₁₃.wr, u₁₂.rd, u₁₂.wr, u₁₁.rd, u₁₁.wr, u₁₀.rd, u₁₀.wr, rd₉, wr₉]; exact inr_wr w36)
    (show s₁₃.mem.readW (sc Sc 36) 32 = _ by
      rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, Mem.readW_writeW_self32]) fun s₁₄ u₁₄ => ?_
  refine w_st (show s₁₄.gpr .edx = Sc by
      rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), congrFun u₁₁.gpr _]
      exact u₁₀.gpr) (show addr Sc sNext = sc Sc 36 from sc_addr sfit (by decide))
    (by rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, wr₉]; exact w36) u₁₄.gpr fun s₁₅ u₁₅ => ?_
  refine k s₁₅ ?_ (fun r h0 h1 h2 => ?_) ?_ ?_ ?_ ?_
  · rw [congrFun u₁₅.gpr _, u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide),
      congrFun u₁₁.gpr _]
    exact u₁₀.gpr
  · rw [congrFun u₁₅.gpr _, u₁₄.other _ h0, u₁₃.other _ h0, u₁₂.other _ h0, congrFun u₁₁.gpr _, u₁₀.other _ h2]
    exact g₉ r h0 h1
  · rw [u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, m₉, next_val]
    simp only [decide_eq_true_eq]
  · rw [u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd]; exact rd₉
  · rw [u₁₅.wr, u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr]; exact wr₉
  · rw [u₁₅.syms, u₁₄.syms, u₁₃.syms, u₁₂.syms, u₁₁.syms, u₁₀.syms, u₉.syms, u₈.syms, u₇.syms, u₆.syms, u₅.syms,
      u₄.syms, u₃.syms, u₂.syms, u₁.syms]

/-- The index of the keystream byte, and the next `i`, `S[i]` and `j`. -/
theorem advance_wp {s : State} {Sc : BitVec 32} {i j si sj nx : Byte} {is : List Instr} {Q : State → Prop}
    (hsi : s.gpr .esi = i.setWidth 32) (hbp : s.gpr .ebp = j.setWidth 32)
    (ha16 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4) (hv16 : s.mem.readW (addr (s.gpr .esp) 16) 32 = Sc)
    (sfit : Sc.toNat + 64 ≤ 2 ^ 32) (hws : InRegions s.wr (Sc.setWidth 64) 64)
    (v24 : s.mem.readW (sc Sc 24) 32 = si.setWidth 32) (v32 : s.mem.readW (sc Sc 32) 32 = sj.setWidth 32)
    (v36 : s.mem.readW (sc Sc 36) 32 = nx.setWidth 32)
    (k : ∀ s', s'.gpr .eax = (sj + si).setWidth 32 → s'.gpr .esi = (i + 1#8).setWidth 32 →
      s'.gpr .ebp = (j + nx).setWidth 32 → s'.gpr .edx = Sc →
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .ebp → s'.gpr r = s.gpr r) →
      s'.mem = s.mem.writeW (sc Sc 24) (nx.setWidth 32) → s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms →
      WP isa (.block is) s' Q) :
    WP isa (.block (advance ++ is)) s Q := by
  have rr (o : Nat) (ho : o + 4 ≤ 64) : InRegions (s.rd ++ s.wr) (sc Sc o) 4 :=
    inr_wr (region_offset _ _ _ o 4 (by omega) ho hws)
  simp only [advance, List.cons_append, List.nil_append]
  refine w_ld rfl rfl ha16 hv16 fun s₁ u₁ => ?_
  refine w_ld u₁.gpr (show addr Sc sSj = sc Sc 32 from sc_addr sfit (by decide))
    (by rw [u₁.rd, u₁.wr]; exact rr 32 (by decide)) (show s₁.mem.readW (sc Sc 32) 32 = sj.setWidth 32 by rw [u₁.mem]; exact v32)
    fun s₂ u₂ => ?_
  refine w_am u₂.gpr ((u₂.other _ (by decide)).trans u₁.gpr)
    (show addr Sc sSi = sc Sc 24 from sc_addr sfit (by decide))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rr 24 (by decide))
    (show s₂.mem.readW (sc Sc 24) 32 = si.setWidth 32 by rw [u₂.mem, u₁.mem]; exact v24) fun s₃ u₃ => ?_
  refine w_andi u₃.gpr fun s₄ u₄ => ?_
  refine w_addi (show s₄.gpr .esi = i.setWidth 32 by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
      exact hsi) fun s₅ u₅ => ?_
  refine w_andi u₅.gpr fun s₆ u₆ => ?_
  obtain dx₆ : s₆.gpr .edx = Sc := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide)]
    exact u₁.gpr
  obtain m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain rd₆ : s₆.rd = s.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine w_ld dx₆ (show addr Sc sNext = sc Sc 36 from sc_addr sfit (by decide))
    (by rw [rd₆, wr₆]; exact rr 36 (by decide)) (show s₆.mem.readW (sc Sc 36) 32 = nx.setWidth 32 by rw [m₆]; exact v36)
    fun s₇ u₇ => ?_
  refine w_st ((u₇.other _ (by decide)).trans dx₆) (show addr Sc sSi = sc Sc 24 from sc_addr sfit (by decide))
    (by rw [u₇.wr, wr₆]; exact region_offset _ _ _ 24 4 (by decide) (by decide) hws) u₇.gpr fun s₈ u₈ => ?_
  refine w_add (show s₈.gpr .ebp = j.setWidth 32 by
      rw [congrFun u₈.gpr _, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
      exact hbp) ((congrFun u₈.gpr _).trans u₇.gpr) fun s₉ u₉ => ?_
  refine w_andi u₉.gpr fun s₁₀ u₁₀ => ?_
  refine k s₁₀ ?_ ?_ ?_ ?_ (fun r h0 h1 h2 h3 h4 => ?_) ?_ ?_ ?_ ?_
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), congrFun u₈.gpr _, u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, byte_add32]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), congrFun u₈.gpr _, u₇.other _ (by decide), u₆.gpr,
      byte_inc32]
  · rw [u₁₀.gpr, byte_add32]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), congrFun u₈.gpr _, u₇.other _ (by decide)]; exact dx₆
  · rw [u₁₀.other _ h4, u₉.other _ h4, congrFun u₈.gpr _, u₇.other _ h1, u₆.other _ h3, u₅.other _ h3,
      u₄.other _ h0, u₃.other _ h0, u₂.other _ h0, u₁.other _ h2]
  · rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, m₆]
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd]; exact rd₆
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr]; exact wr₆
  · rw [u₁₀.syms, u₉.syms, u₈.syms, u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]

/-- The row of the public `i`: the byte `i` is exclusive-ored with the
difference of the two bytes of the exchange, which `ecx` keeps. -/
theorem iRow_wp {s : State} {P Sc : BitVec 32} {i si sj : Byte} {is : List Instr} {Q : State → Prop}
    (hdx : s.gpr .edx = Sc) (hsi : s.gpr .esi = i.setWidth 32) (hdi : s.gpr .edi = P)
    (fit : P.toNat + 256 ≤ 2 ^ 32) (hw : InRegions s.wr (P.setWidth 64) 256) (sfit : Sc.toNat + 64 ≤ 2 ^ 32)
    (hws : InRegions s.wr (Sc.setWidth 64) 64) (v24 : s.mem.readW (sc Sc 24) 32 = si.setWidth 32)
    (v32 : s.mem.readW (sc Sc 32) 32 = sj.setWidth 32) (v28 : s.mem.readW (sc Sc 28) 32 = s.syms tableName)
    (k : ∀ s', s'.gpr .ecx = (sj ^^^ si).setWidth 32 → s'.gpr tbr = s'.syms tableName →
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) →
      s'.mem = s.mem.write (P.setWidth 64 + BitVec.ofNat 64 i.toNat) 1
        (s.mem (P.setWidth 64 + BitVec.ofNat 64 i.toNat) ^^^ (sj ^^^ si)) →
      s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (iRow ++ is)) s Q := by
  have hi := i.isLt
  have rr (o : Nat) (ho : o + 4 ≤ 64) : InRegions (s.rd ++ s.wr) (sc Sc o) 4 :=
    inr_wr (region_offset _ _ _ o 4 (by omega) ho hws)
  obtain hrow : InRegions s.wr (P.setWidth 64 + BitVec.ofNat 64 (16 * (i.toNat / 16))) 16 :=
    region_offset _ _ _ _ _ (by omega) (by omega) hw
  simp only [iRow, List.cons_append, List.nil_append]
  refine w_ld hdx (show addr Sc sSj = sc Sc 32 from sc_addr sfit (by decide)) (rr 32 (by decide)) v32
    fun s₁ u₁ => ?_
  refine w_xm u₁.gpr ((u₁.other _ (by decide)).trans hdx) (show addr Sc sSi = sc Sc 24 from sc_addr sfit (by decide))
    (by rw [u₁.rd, u₁.wr]; exact rr 24 (by decide))
    (show s₁.mem.readW (sc Sc 24) 32 = si.setWidth 32 by rw [u₁.mem]; exact v24) fun s₂ u₂ => ?_
  refine w_ld ((u₂.other _ (by decide)).trans ((u₁.other _ (by decide)).trans hdx))
    (show addr Sc sTab = sc Sc 28 from sc_addr sfit (by decide))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rr 28 (by decide))
    (show s₂.mem.readW (sc Sc 28) 32 = s.syms tableName by rw [u₂.mem, u₁.mem]; exact v28) fun s₃ u₃ => ?_
  obtain cx₃ : s₃.gpr .ecx = (sj ^^^ si).setWidth 32 := by rw [u₃.other _ (by decide), u₂.gpr, xor_byte32]
  obtain g₃ : ∀ r, r ≠ .ecx → r ≠ .edx → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.other _ h2, u₂.other _ h1, u₁.other _ h1]
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  obtain wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  obtain sy₃ : s₃.syms = s.syms := by rw [u₃.syms, u₂.syms, u₁.syms]
  refine x_movd cx₃ fun s₄ u₄ => ?_
  refine g_mov (show s₄.gpr .esi = i.setWidth 32 by rw [u₄.gpr, g₃ _ (by decide) (by decide)]; exact hsi)
    fun s₅ u₅ => ?_
  refine g_andi u₅.gpr fun s₆ u₆ => ?_
  refine x_movd u₆.gpr fun s₇ u₇ => ?_
  refine x_bin rfl rfl fun s₈ u₈ => ?_
  refine x_bin ((u₈.other _ (by decide)).trans u₇.xmm) u₈.xmm fun s₉ u₉ => ?_
  have g₉ (r : Reg) (h0 : r ≠ .eax) : s₉.gpr r = s₃.gpr r := by
    rw [u₉.gpr, u₈.gpr, u₇.gpr, u₆.other _ h0, u₅.other _ h0, u₄.gpr]
  obtain sy₉ : s₉.syms = s.syms := by rw [u₉.syms, u₈.syms, u₇.syms, u₆.syms, u₅.syms, u₄.syms]; exact sy₃
  refine x_tb (by rw [g₉ _ (by decide), sy₉]; exact u₃.gpr) (by decide) fun s₁₀ u₁₀ => ?_
  refine x_bin u₁₀.xmm ((u₁₀.other _ (by decide)).trans u₉.xmm) fun s₁₁ u₁₁ => ?_
  obtain L : s₁₁.xmm .xmm1 = lanesOf (i.setWidth 32) := by
    rw [u₁₁.xmm, show XBinOp.eval .pxor (s₇.xmm .xmm1) (s₇.xmm .xmm1) = 0 from BitVec.xor_self]; rfl
  refine x_bin (show s₁₁.xmm .xmm7 = (0 : BitVec 96) ++ (sj ^^^ si).setWidth 32 by
      rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.xmm, u₅.xmm]
      exact u₄.xmm) L fun s₁₂ u₁₂ => ?_
  have g₁₂ (r : Reg) (h0 : r ≠ .eax) : s₁₂.gpr r = s₃.gpr r := by
    rw [u₁₂.gpr, u₁₁.gpr, u₁₀.gpr]; exact g₉ r h0
  refine g_mov (show s₁₂.gpr .esi = i.setWidth 32 by
    rw [g₁₂ _ (by decide), g₃ _ (by decide) (by decide)]; exact hsi) fun s₁₃ u₁₃ => ?_
  refine g_andi u₁₃.gpr fun s₁₄ u₁₄ => ?_
  refine g_add u₁₄.gpr (show s₁₄.gpr .edi = P by
    rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), g₁₂ _ (by decide), g₃ _ (by decide) (by decide)]
    exact hdi) fun s₁₅ u₁₅ => ?_
  obtain m₁₅ : s₁₅.mem = s.mem := by
    rw [u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
    exact m₃
  obtain rd₁₅ : s₁₅.rd = s.rd := by
    rw [u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd]; exact rd₃
  obtain wr₁₅ : s₁₅.wr = s.wr := by
    rw [u₁₅.wr, u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr]; exact wr₃
  refine x_ldm u₁₅.gpr (irow_addr fit i) (by rw [rd₁₅, wr₁₅]; exact inr_wr hrow)
    (show s₁₅.mem.readW _ 128 = s.mem.readW _ 128 by rw [m₁₅]) fun s₁₆ u₁₆ => ?_
  refine x_bin u₁₆.xmm (show s₁₆.xmm .xmm7 = _ from
    (u₁₆.other _ (by decide)).trans ((congrFun u₁₅.xmm _).trans ((congrFun u₁₄.xmm _).trans
      ((congrFun u₁₃.xmm _).trans u₁₂.xmm)))) fun s₁₇ u₁₇ => ?_
  refine x_stm (show s₁₇.gpr .eax = _ from (congrFun u₁₇.gpr _).trans ((congrFun u₁₆.gpr _).trans u₁₅.gpr))
    (irow_addr fit i) (by rw [u₁₇.wr, u₁₆.wr, wr₁₅]; exact hrow) u₁₇.xmm fun s₁₈ u₁₈ => ?_
  have g₁₈ (r : Reg) (h0 : r ≠ .eax) : s₁₈.gpr r = s₃.gpr r := by
    rw [u₁₈.gpr, u₁₇.gpr, u₁₆.gpr, u₁₅.other _ h0, u₁₄.other _ h0, u₁₃.other _ h0]; exact g₁₂ r h0
  obtain sy₁₈ : s₁₈.syms = s.syms := by
    rw [u₁₈.syms, u₁₇.syms, u₁₆.syms, u₁₅.syms, u₁₄.syms, u₁₃.syms, u₁₂.syms, u₁₁.syms, u₁₀.syms]; exact sy₉
  refine k s₁₈ ((g₁₈ _ (by decide)).trans cx₃) (by rw [g₁₈ _ (by decide), sy₁₈]; exact u₃.gpr)
    (fun r h0 h1 h2 => (g₁₈ r h0).trans (g₃ r h1 h2)) ?_ (by rw [u₁₈.rd, u₁₇.rd, u₁₆.rd]; exact rd₁₅)
    (by rw [u₁₈.wr, u₁₇.wr, u₁₆.wr]; exact wr₁₅) sy₁₈
  rw [u₁₈.mem, u₁₇.mem, u₁₆.mem, m₁₅,
    writeW_row s.mem _ _ (c := s.mem (P.setWidth 64 + BitVec.ofNat 64 (16 * (i.toNat / 16)) +
        BitVec.ofNat 64 (i.toNat % 16)) ^^^ (sj ^^^ si)) (l₀ := i.toNat % 16) (P := True) (by omega) (fun l hl => by
      rw [show XBinOp.eval .pxor (s.mem.readW (P.setWidth 64 + BitVec.ofNat 64 (16 * (i.toNat / 16))) 128)
          (XBinOp.eval .pshufb ((0 : BitVec 96) ++ (sj ^^^ si).setWidth 32) (lanesOf (i.setWidth 32))) =
          s.mem.readW (P.setWidth 64 + BitVec.ofNat 64 (16 * (i.toNat / 16))) 128 ^^^
            XBinOp.eval .pshufb ((0 : BitVec 96) ++ (sj ^^^ si).setWidth 32) (lanesOf (i.setWidth 32)) from rfl,
        byte_xor, isSi (sj ^^^ si) i l hl, byte_row _ _ hl]
      by_cases h : l = i.toNat % 16
      · rw [ite_eq_left h, ite_eq_left ⟨h, trivial⟩, h]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.1), BitVec.xor_zero]),
    ite_eq_left trivial, row_addr]

/-! ### The second pass: two columns -/

theorem colReg_add3 (h k : Nat) : colReg h (k + 3) = colReg h k := by
  simp only [colReg, Nat.add_mod_right]

theorem colReg_ne (h k : Nat) : colReg h k ≠ colReg h (k + 2) ∧ colReg h k ≠ .xmm7 := by
  have e2 : (k + 2) % 3 = (k % 3 + 2) % 3 := by omega
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with e | e | e <;> by_cases hh : h = 0 <;>
    simp [colReg, e, e2, hh]

theorem colReg1_ne (k : Nat) : XReg.xmm1 ≠ colReg 1 k := by
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with e | e | e <;> simp [colReg, e]

/-- A row of the second pass: the column two bytes down, with the row's two
bytes on top. -/
theorem readRow2_wp {s : State} {P : BitVec 32} {n₀ n₁ h k : Nat} {is : List Instr} {Q : State → Prop}
    (hh : h < 2) (hk : k < 8) (h0 : n₀ < 16) (h1 : n₁ < 16) (hdi : s.gpr .edi = P)
    (fit : P.toNat + 256 ≤ 2 ^ 32) (hrg : InRegions (s.rd ++ s.wr) (P.setWidth 64) 256)
    (h7 : byte (s.xmm .xmm7) 0 = BitVec.ofNat 8 n₀ ∧ byte (s.xmm .xmm7) 1 = BitVec.ofNat 8 n₁)
    (k' : ∀ s', (∀ l < 16, byte (s'.xmm (colReg h k)) l = if l < 14 then byte (s.xmm (colReg h (k + 2))) (l + 2)
          else s.mem (P.setWidth 64 + BitVec.ofNat 64 (16 * (8 * h + k) + (if l = 14 then n₀ else n₁)))) →
        (∀ x, x ≠ colReg h k → s'.xmm x = s.xmm x) → s'.mem = s.mem → s'.gpr = s.gpr → s'.rd = s.rd →
        s'.wr = s.wr → s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (readRow2 h k ++ is)) s Q := by
  obtain ⟨c1, c7⟩ := colReg_ne h k
  simp only [readRow2, List.cons_append, List.nil_append]
  refine x_ld hdi (addr_eq (by omega)) (region_offset _ _ _ _ _ (by omega) (by omega) hrg) rfl fun s₁ u₁ => ?_
  refine x_bin u₁.xmm (u₁.other _ c7.symm) fun s₂ u₂ => ?_
  refine x_palignr u₂.xmm ((u₂.other _ c1.symm).trans (u₁.other _ c1.symm)) fun s₃ u₃ => ?_
  have sh (b n : Nat) (hb : b < 16) (hn : n < 16) (e : byte (s.xmm .xmm7) b = BitVec.ofNat 8 n) :
      byte (XBinOp.eval .pshufb (s.mem.readW (P.setWidth 64 + BitVec.ofNat 64 (16 * (8 * h + k))) 128)
        (s.xmm .xmm7)) b = s.mem (P.setWidth 64 + BitVec.ofNat 64 (16 * (8 * h + k) + n)) := by
    obtain ⟨hm, he⟩ := nib_facts n hn
    rw [byte_pshufb _ _ hb, e, hm, ite_eq_right (by decide), he, byte_row _ _ hn, Offset.add_add]
  refine k' s₃ (fun l hl => ?_) (fun x hx => ?_) ?_ ?_ ?_ ?_ ?_
  · rw [u₃.xmm, byte_align2 _ _ hl]
    by_cases h14 : l < 14
    · rw [ite_eq_left h14, ite_eq_left h14]
    · rw [ite_eq_right h14, ite_eq_right h14]
      rcases (by omega : l = 14 ∨ l = 15) with rfl | rfl
      · rw [ite_eq_left rfl]; exact sh 0 n₀ (by decide) h0 h7.1
      · rw [ite_eq_right (by decide)]; exact sh 1 n₁ (by decide) h1 h7.2
  · rw [u₃.other _ hx, u₂.other _ hx, u₁.other _ hx]
  · rw [u₃.mem, u₂.mem, u₁.mem]
  · rw [u₃.gpr, u₂.gpr, u₁.gpr]
  · rw [u₃.rd, u₂.rd, u₁.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr]
  · rw [u₃.syms, u₂.syms, u₁.syms]

/-- A half of the second pass after `k` rows: the top `2 k` bytes of the
column's register are their bytes at the two nibbles. -/
structure RdH (s₀ : State) (P : BitVec 32) (n₀ n₁ h k : Nat) (t : State) : Prop where
  col : ∀ q < k, ∀ l, l + 2 * k = 16 + 2 * q →
    byte (t.xmm (colReg h (k + 2))) l = s₀.mem (P.setWidth 64 + BitVec.ofNat 64 (16 * (8 * h + q) + n₀)) ∧
    byte (t.xmm (colReg h (k + 2))) (l + 1) = s₀.mem (P.setWidth 64 + BitVec.ofNat 64 (16 * (8 * h + q) + n₁))
  keep : ∀ x, (∀ k', x ≠ colReg h k') → t.xmm x = s₀.xmm x
  mem : t.mem = s₀.mem
  gpr : t.gpr = s₀.gpr
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  syms : t.syms = s₀.syms

theorem readHalfFrom_wp {s₀ : State} {P : BitVec 32} {n₀ n₁ h : Nat} {is : List Instr} {Q : State → Prop}
    (hh : h < 2) (h0 : n₀ < 16) (h1 : n₁ < 16) (hdi : s₀.gpr .edi = P) (fit : P.toNat + 256 ≤ 2 ^ 32)
    (hrg : InRegions (s₀.rd ++ s₀.wr) (P.setWidth 64) 256)
    (h7 : byte (s₀.xmm .xmm7) 0 = BitVec.ofNat 8 n₀ ∧ byte (s₀.xmm .xmm7) 1 = BitVec.ofNat 8 n₁)
    (k' : ∀ s', RdH s₀ P n₀ n₁ h 8 s' → WP isa (.block is) s' Q) :
    ∀ (c k : Nat) (s : State), k + c = 8 → RdH s₀ P n₀ n₁ h k s →
      WP isa (.block ((List.range' k c).flatMap (readRow2 h) ++ is)) s Q
  | 0, k, s, e, hs => by
    obtain rfl : k = 8 := by omega
    exact k' s hs
  | c + 1, k, s, e, hs => by
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    have x7 : s.xmm .xmm7 = s₀.xmm .xmm7 := hs.keep _ fun k' => (colReg_ne h k').2.symm
    refine readRow2_wp hh (by omega) h0 h1 (by rw [hs.gpr]; exact hdi) fit (by rw [hs.rd, hs.wr]; exact hrg)
      (by rw [x7]; exact h7) fun s' col x' m' g' rd' wr' sy' =>
      readHalfFrom_wp hh h0 h1 hdi fit hrg h7 k' c (k + 1) s' (by omega) ?_
    refine ⟨fun q hq l hl => ?_, fun x hx => (x' x (hx k)).trans (hs.keep x hx), m'.trans hs.mem, g'.trans hs.gpr,
      rd'.trans hs.rd, wr'.trans hs.wr, sy'.trans hs.syms⟩
    rw [show k + 1 + 2 = k + 3 from rfl, colReg_add3, col l (by omega), col (l + 1) (by omega), hs.mem]
    by_cases e' : q = k
    · subst e'
      obtain rfl : l = 14 := by omega
      exact ⟨by rw [ite_eq_right (by decide), ite_eq_left rfl], by
        rw [ite_eq_right (by decide), ite_eq_right (by decide)]⟩
    · obtain ⟨a, b⟩ := hs.col q (by omega) (l + 2) (by omega)
      exact ⟨by rw [ite_eq_left (by omega)]; exact a, by rw [ite_eq_left (by omega)]; exact b⟩

/-- A half of the second pass: byte `2 q` of its column is the byte `n₀` of
its row `q`, and byte `2 q + 1` the byte `n₁`. -/
theorem readHalf_wp {s : State} {P : BitVec 32} {n₀ n₁ h : Nat} {is : List Instr} {Q : State → Prop}
    (hh : h < 2) (h0 : n₀ < 16) (h1 : n₁ < 16) (hdi : s.gpr .edi = P) (fit : P.toNat + 256 ≤ 2 ^ 32)
    (hrg : InRegions (s.rd ++ s.wr) (P.setWidth 64) 256)
    (h7 : byte (s.xmm .xmm7) 0 = BitVec.ofNat 8 n₀ ∧ byte (s.xmm .xmm7) 1 = BitVec.ofNat 8 n₁)
    (k' : ∀ s', (∀ q < 8,
          byte (s'.xmm (colReg h 7)) (2 * q) = s.mem (P.setWidth 64 + BitVec.ofNat 64 (16 * (8 * h + q) + n₀)) ∧
          byte (s'.xmm (colReg h 7)) (2 * q + 1) = s.mem (P.setWidth 64 + BitVec.ofNat 64 (16 * (8 * h + q) + n₁))) →
        (∀ x, (∀ k, x ≠ colReg h k) → s'.xmm x = s.xmm x) → s'.mem = s.mem → s'.gpr = s.gpr → s'.rd = s.rd →
        s'.wr = s.wr → s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (readHalf h ++ is)) s Q := by
  rw [readHalf, List.range_eq_range']
  refine readHalfFrom_wp hh h0 h1 hdi fit hrg h7 (fun s' hs => ?_) 8 0 s rfl
    ⟨fun q hq => absurd hq (by omega), fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine k' s' (fun q hq => ?_) hs.keep hs.mem hs.gpr hs.rd hs.wr hs.syms
  have := hs.col q hq (2 * q) (by omega)
  rwa [show (8 : Nat) + 2 = 7 + 3 from rfl, colReg_add3] at this

theorem movq_byte1 (m : Mem) (q : Addr) (V : BitVec 128) :
    (m.writeW q (V.extractLsb' 0 64)) (q + BitVec.ofNat 64 1) = byte V 1 := by
  have h := writeW_byte m q (V.extractLsb' 0 64) (k := 1) (by decide) (by decide)
  rw [extract_extract _ _ _ _ _ (by decide)] at h
  exact h

/-- A word of the working space from its byte 24 on is apart from the eight bytes at 16. -/
theorem q16_rw (m : Mem) (Sc : BitVec 32) (q : BitVec 64) {b : Nat} (hb : 24 ≤ b) (hb' : b + 4 ≤ 64) :
    (m.writeW (sc Sc 16) q).readW (sc Sc b) 32 = m.readW (sc Sc b) 32 :=
  Mem.readW_writeW_sep (show Mem.Sep _ (32 / 8) _ (64 / 8) from
    Offset.sep (Sc.setWidth 64) (d := b) (n := 4) (e := 16) (k := 8) (.inr hb) (by omega) (by decide)) (by decide)

/-- A byte of the table is apart from a write in the working space. -/
theorem tbl_sc {P Sc : BitVec 32} (tS : Region.Disjoint ⟨P.setWidth 64, 258⟩ ⟨Sc.setWidth 64, 64⟩) (m : Mem)
    {w : Nat} (v : BitVec w) {o : Nat} (ho : o + w / 8 ≤ 64) {y : Nat} (hy : y < 256) :
    (m.writeW (sc Sc o) v) (P.setWidth 64 + BitVec.ofNat 64 y) = m (P.setWidth 64 + BitVec.ofNat 64 y) := by
  have hs : Mem.Sep (P.setWidth 64) 256 (sc Sc o) (w / 8) :=
    sep_of_sub tS (contains_prefix _ (n := 256) (k := 258) (by decide))
      (Offset.contains_base (Sc.setWidth 64) (d := o) (n := w / 8) (k := 64) ho (by omega))
  have := hs _ (show (P.setWidth 64 + BitVec.ofNat 64 y - P.setWidth 64).toNat < 256 by
    rw [Mem.sub_ofNat_toNat _ (by omega)]; exact hy)
  exact writeW_byte_off _ _ _ _ (by omega)

/-- The byte of the two halves' columns that a selector takes: the row `hx`'s,
of the column `e`. -/
theorem byte_pick2 {C0 C1 I : BitVec 128} {b hx e : Nat} (hb : b < 16) (hhx : hx < 16) (he : e < 2)
    (hI : byte I b = BitVec.ofNat 8 (2 * (hx % 8) + 128 * (hx / 8) + e)) :
    byte (XBinOp.eval .por (XBinOp.eval .pshufb C0 I) (XBinOp.eval .pshufb C1 (XBinOp.eval .pxor I (cst oH)))) b =
      if hx < 8 then byte C0 (2 * (hx % 8) + e) else byte C1 (2 * (hx % 8) + e) := by
  obtain ⟨f1, f2, f3, f4, g1, g2, g3, g4, _⟩ := sel_facts hx hhx
  rw [show XBinOp.eval .por (XBinOp.eval .pshufb C0 I) (XBinOp.eval .pshufb C1 (XBinOp.eval .pxor I (cst oH))) =
      XBinOp.eval .pshufb C0 I ||| XBinOp.eval .pshufb C1 (I ^^^ cst oH) from rfl, byte_or, byte_pshufb _ _ hb,
    byte_pshufb _ _ hb, byte_xor, cst_H b hb, hI]
  rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
  · simp only [Nat.add_zero]
    rw [f1, f2, f3, f4]
    by_cases h8 : 8 ≤ hx
    · simp only [h8, decide_true, Bool.not_true, ↓reduceIte, Bool.false_eq_true, BitVec.zero_or,
        show ¬ hx < 8 by omega]
    · simp only [h8, decide_false, Bool.not_false, ↓reduceIte, Bool.false_eq_true, BitVec.or_zero,
        show hx < 8 by omega]
  · rw [g1, g2, g3, g4]
    by_cases h8 : 8 ≤ hx
    · simp only [h8, decide_true, Bool.not_true, ↓reduceIte, Bool.false_eq_true, BitVec.zero_or,
        show ¬ hx < 8 by omega]
    · simp only [h8, decide_false, Bool.not_false, ↓reduceIte, Bool.false_eq_true, BitVec.or_zero,
        show hx < 8 by omega]

/-- The second pass's index: the two low nibbles in `xmm7`'s bytes 0 and 1,
and the first index kept in its slot. -/
theorem read2_ix_wp {s : State} {Sc : BitVec 32} {t j : Byte} {is : List Instr} {Q : State → Prop}
    (hax : s.gpr .eax = t.setWidth 32) (hbp : s.gpr .ebp = j.setWidth 32) (hdx : s.gpr .edx = Sc)
    (sfit : Sc.toNat + 64 ≤ 2 ^ 32) (hws : InRegions s.wr (Sc.setWidth 64) 64)
    (k : ∀ s', (byte (s'.xmm .xmm7) 0 = BitVec.ofNat 8 (t.toNat % 16) ∧
        byte (s'.xmm .xmm7) 1 = BitVec.ofNat 8 (j.toNat % 16)) →
      (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) → s'.mem = s.mem.writeW (sc Sc 40) (t.setWidth 32) →
      s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (.store (at_ .edx sT) .eax :: .mov .ecx (.reg .ebp) :: .alu .and .ecx (imm 15) ::
      .shift .ror .ecx 24 :: .alu .and .eax (imm 15) :: .alu .or .eax (.reg .ecx) :: .xop (.movd .xmm7 .eax) ::
      is)) s Q := by
  refine w_st hdx (show addr Sc sT = sc Sc 40 from sc_addr sfit (by decide))
    (region_offset _ _ _ 40 4 (by decide) (by decide) hws) hax fun s₁ u₁ => ?_
  refine w_mov ((congrFun u₁.gpr _).trans hbp) fun s₂ u₂ => ?_
  refine w_andi u₂.gpr fun s₃ u₃ => ?_
  refine wp_ror (by decide) fun s₄ u₄ => ?_
  refine w_andi (show s₄.gpr .eax = t.setWidth 32 by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), congrFun u₁.gpr _]; exact hax)
    fun s₅ u₅ => ?_
  refine wp_or fun s₆ u₆ => ?_
  obtain ax₆ : s₆.gpr .eax = (BitVec.ofNat 8 (t.toNat % 16)).setWidth 32 |||
      ((BitVec.ofNat 8 (j.toNat % 16)).setWidth 32).rotateRight 24 := by
    rw [u₆.gpr, u₅.gpr, u₅.other _ (by decide), u₄.gpr, u₃.gpr, lo_reg t, lo_reg j]
  refine x_movd ax₆ fun s₇ u₇ => ?_
  refine k s₇ ?_ (fun r h0 h1 => ?_) ?_ ?_ ?_ ?_
  · rw [u₇.xmm]
    exact ⟨(byte_movd32 _ (by decide)).trans (pack_lo _ _), (byte_movd32 _ (by decide)).trans (pack_hi _ _)⟩
  · rw [u₇.gpr, u₆.other _ h0, u₅.other _ h0, u₄.other _ h1, u₃.other _ h1, u₂.other _ h1, congrFun u₁.gpr _]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]

/-- A selector in `eax`, from an index: `ecx` is clobbered. -/
theorem sel_wp {s : State} {x : Byte} {is : List Instr} {Q : State → Prop} (hax : s.gpr .eax = x.setWidth 32)
    (k : ∀ s', s'.gpr .eax = (BitVec.ofNat 8 (2 * (x.toNat / 16 % 8) + 128 * (x.toNat / 16 / 8))).setWidth 32 →
      (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) → s'.xmm = s.xmm → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (.mov .ecx (.reg .eax) :: .shift .shr .ecx 3 :: .alu .and .ecx (imm 14) ::
      .alu .and .eax (imm 128) :: .alu .or .eax (.reg .ecx) :: is)) s Q := by
  refine g_mov hax fun s₁ u₁ => ?_
  refine g_shr (by decide) u₁.gpr fun s₂ u₂ => ?_
  refine g_andi u₂.gpr fun s₃ u₃ => ?_
  refine g_andi (show s₃.gpr .eax = x.setWidth 32 by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact hax) fun s₄ u₄ => ?_
  refine g_or u₄.gpr ((u₄.other _ (by decide)).trans u₃.gpr) fun s₅ u₅ => ?_
  refine k s₅ (by rw [u₅.gpr]; exact sel_reg x) (fun r h0 h1 => ?_) ?_ ?_ ?_ ?_ ?_
  · rw [u₅.other _ h0, u₄.other _ h0, u₃.other _ h1, u₂.other _ h1, u₁.other _ h1]
  · rw [u₅.xmm, u₄.xmm, u₃.xmm, u₂.xmm, u₁.xmm]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]

/-- The end of the second pass: the two selected bytes of the halves'
columns, the first to `eax` and the second to `S[j]`'s slot. -/
theorem read2_out_wp {s : State} {Sc : BitVec 32} {is : List Instr} {Q : State → Prop} (hdx : s.gpr .edx = Sc)
    (sfit : Sc.toNat + 64 ≤ 2 ^ 32) (hws : InRegions s.wr (Sc.setWidth 64) 64)
    (v28 : s.mem.readW (sc Sc 28) 32 = s.syms tableName)
    (k : ∀ s' (q : BitVec 64),
      s'.gpr .eax = (byte (XBinOp.eval .por (XBinOp.eval .pshufb (s.xmm .xmm1) (s.xmm .xmm7))
        (XBinOp.eval .pshufb (s.xmm .xmm6) (XBinOp.eval .pxor (s.xmm .xmm7) (cst oH)))) 0).setWidth 32 →
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) →
      s'.mem = (s.mem.writeW (sc Sc 16) q).writeW (sc Sc 32)
        ((byte (XBinOp.eval .por (XBinOp.eval .pshufb (s.xmm .xmm1) (s.xmm .xmm7))
          (XBinOp.eval .pshufb (s.xmm .xmm6) (XBinOp.eval .pxor (s.xmm .xmm7) (cst oH)))) 1).setWidth 32) →
      s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (x .pshufb .xmm1 .xmm7 :: .mov .eax (.reg .edx) :: .mov .edx (.mem (at_ .eax sTab)) ::
      tb .xmm5 oH :: x .pxor .xmm7 .xmm5 :: x .pshufb .xmm6 .xmm7 :: x .por .xmm1 .xmm6 ::
      .movqStore (at_ .eax sSlot) .xmm1 :: .movzx8 .ecx (at_ .eax (sSlot + 1)) :: .store (at_ .eax sSj) .ecx ::
      .movzx8 .eax (at_ .eax sSlot) :: is)) s Q := by
  have ww (o n : Nat) (h : o + n ≤ 64) : InRegions s.wr (sc Sc o) n := region_offset _ _ _ o n (by omega) h hws
  refine x_bin rfl rfl fun s₁ u₁ => ?_
  refine g_mov (show s₁.gpr .edx = Sc by rw [u₁.gpr]; exact hdx) fun s₂ u₂ => ?_
  refine g_ld u₂.gpr (show addr Sc sTab = sc Sc 28 from sc_addr sfit (by decide))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact inr_wr (ww 28 4 (by decide)))
    (show s₂.mem.readW (sc Sc 28) 32 = s.syms tableName by rw [u₂.mem, u₁.mem]; exact v28) fun s₃ u₃ => ?_
  refine x_tb (show s₃.gpr .edx = s₃.syms tableName by rw [u₃.gpr, u₃.syms, u₂.syms, u₁.syms]) (by decide)
    fun s₄ u₄ => ?_
  refine x_bin (show s₄.xmm .xmm7 = s.xmm .xmm7 by
    rw [u₄.other _ (by decide), u₃.xmm, u₂.xmm, u₁.other _ (by decide)]) u₄.xmm fun s₅ u₅ => ?_
  refine x_bin (show s₅.xmm .xmm6 = s.xmm .xmm6 by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.xmm, u₂.xmm, u₁.other _ (by decide)]) u₅.xmm
    fun s₆ u₆ => ?_
  refine x_bin (show s₆.xmm .xmm1 = _ from (u₆.other _ (by decide)).trans ((u₅.other _ (by decide)).trans
    ((u₄.other _ (by decide)).trans ((congrFun u₃.xmm _).trans ((congrFun u₂.xmm _).trans u₁.xmm))))) u₆.xmm
    fun s₇ u₇ => ?_
  obtain ax₇ : s₇.gpr .eax = Sc := by
    rw [u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.other _ (by decide)]; exact u₂.gpr
  obtain m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain rd₇ : s₇.rd = s.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr₇ : s₇.wr = s.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine m_movq ax₇ (show addr Sc sSlot = sc Sc 16 from sc_addr sfit (by decide))
    (by rw [wr₇]; exact ww 16 8 (by decide)) u₇.xmm fun s₈ u₈ => ?_
  refine g_movzx ((congrFun u₈.gpr _).trans ax₇)
    (show addr Sc (sSlot + 1) = sc Sc 17 from sc_addr sfit (by decide))
    (by rw [u₈.rd, u₈.wr, rd₇, wr₇]; exact inr_wr (ww 17 1 (by decide)))
    (by rw [u₈.mem, show sc Sc 17 = sc Sc 16 + BitVec.ofNat 64 1 from (Offset.add_add _ 16 1).symm, movq_byte1])
    fun s₉ u₉ => ?_
  refine m_st ((u₉.other _ (by decide)).trans ((congrFun u₈.gpr _).trans ax₇))
    (show addr Sc sSj = sc Sc 32 from sc_addr sfit (by decide))
    (by rw [u₉.wr, u₈.wr, wr₇]; exact ww 32 4 (by decide)) u₉.gpr fun s₁₀ u₁₀ => ?_
  have h16 : ¬ (sc Sc 16 - sc Sc 32).toNat < 4 :=
    Offset.sep (Sc.setWidth 64) (d := 16) (n := 1) (e := 32) (k := 4) (.inl (by decide)) (by decide)
    (by decide) (sc Sc 16) (by
      show ((Sc.setWidth 64 + BitVec.ofNat 64 16) - (Sc.setWidth 64 + BitVec.ofNat 64 16)).toNat < 1
      rw [BitVec.sub_self]; decide)
  refine g_movzx ((congrFun u₁₀.gpr _).trans ((u₉.other _ (by decide)).trans ((congrFun u₈.gpr _).trans ax₇)))
    (show addr Sc sSlot = sc Sc 16 from sc_addr sfit (by decide))
    (by rw [u₁₀.rd, u₁₀.wr, u₉.rd, u₉.wr, u₈.rd, u₈.wr, rd₇, wr₇]; exact inr_wr (ww 16 1 (by decide)))
    (by rw [u₁₀.mem, writeW_byte_off _ _ _ _ (show 32 / 8 ≤ _ by omega), u₉.mem, u₈.mem, movq_byte])
    fun s₁₁ u₁₁ => ?_
  refine k s₁₁ ((XBinOp.eval .por (XBinOp.eval .pshufb (s.xmm .xmm1) (s.xmm .xmm7))
    (XBinOp.eval .pshufb (s.xmm .xmm6) (XBinOp.eval .pxor (s.xmm .xmm7) (cst oH)))).extractLsb' 0 64) u₁₁.gpr
    (fun r h0 h1 h2 => ?_) ?_ ?_ ?_ ?_
  · rw [u₁₁.other _ h0, u₁₀.gpr, u₉.other _ h1, u₈.gpr, u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.other _ h2,
      u₂.other _ h0, u₁.gpr]
  · rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, m₇]
  · rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd]; exact rd₇
  · rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr]; exact wr₇
  · rw [u₁₁.syms, u₁₀.syms, u₉.syms, u₈.syms, u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]

/-- The second pass: `eax` := the table's byte `t`, and the table's byte
`j` to its slot. It writes the working space from its byte 16 on only, and
keeps `S[i]`'s slot and the constants' address. -/
theorem read2_wp {s : State} {P Sc : BitVec 32} {t j : Byte} {is : List Instr} {Q : State → Prop}
    (hax : s.gpr .eax = t.setWidth 32) (hbp : s.gpr .ebp = j.setWidth 32) (hdx : s.gpr .edx = Sc)
    (hdi : s.gpr .edi = P) (fit : P.toNat + 256 ≤ 2 ^ 32) (hrg : InRegions (s.rd ++ s.wr) (P.setWidth 64) 256)
    (sfit : Sc.toNat + 64 ≤ 2 ^ 32) (hws : InRegions s.wr (Sc.setWidth 64) 64)
    (tS : Region.Disjoint ⟨P.setWidth 64, 258⟩ ⟨Sc.setWidth 64, 64⟩)
    (v28 : s.mem.readW (sc Sc 28) 32 = s.syms tableName)
    (k : ∀ s', s'.gpr .eax = (s.mem (P.setWidth 64 + BitVec.ofNat 64 t.toNat)).setWidth 32 →
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) →
      s'.mem.readW (sc Sc 32) 32 = (s.mem (P.setWidth 64 + BitVec.ofNat 64 j.toNat)).setWidth 32 →
      s'.mem.readW (sc Sc 24) 32 = s.mem.readW (sc Sc 24) 32 →
      s'.mem.readW (sc Sc 28) 32 = s.mem.readW (sc Sc 28) 32 → Frame [⟨sc Sc 16, 48⟩] s.mem s'.mem →
      s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (read2 ++ is)) s Q := by
  have ht := t.isLt
  have hj := j.isLt
  have ww (o n : Nat) (h : o + n ≤ 64) : InRegions s.wr (sc Sc o) n := region_offset _ _ _ o n (by omega) h hws
  simp only [read2, List.append_assoc, List.cons_append, List.nil_append]
  refine read2_ix_wp hax hbp hdx sfit hws fun s₁ h7 g₁ m₁ rd₁ wr₁ sy₁ => ?_
  obtain di₁ : s₁.gpr .edi = P := (g₁ _ (by decide) (by decide)).trans hdi
  refine readHalf_wp (h := 0) (n₀ := t.toNat % 16) (n₁ := j.toNat % 16) (by decide) (by omega) (by omega) di₁ fit
    (by rw [rd₁, wr₁]; exact hrg) h7
    fun s₂ c₂ x₂ m₂ g₂ rd₂ wr₂ sy₂ => ?_
  have x7₂ : s₂.xmm .xmm7 = s₁.xmm .xmm7 := x₂ _ fun k => (colReg_ne 0 k).2.symm
  refine readHalf_wp (h := 1) (n₀ := t.toNat % 16) (n₁ := j.toNat % 16) (by decide) (by omega) (by omega)
    (by rw [g₂]; exact di₁) fit
    (by rw [rd₂, wr₂, rd₁, wr₁]; exact hrg) (by rw [x7₂]; exact h7) fun s₃ c₃ x₃ m₃ g₃ rd₃ wr₃ sy₃ => ?_
  -- the halves' columns, by the table as it was
  have C0 (q : Nat) (hq : q < 8) :
      byte (s₃.xmm .xmm1) (2 * q) = s.mem (P.setWidth 64 + BitVec.ofNat 64 (16 * (8 * 0 + q) + t.toNat % 16)) ∧
      byte (s₃.xmm .xmm1) (2 * q + 1) =
        s.mem (P.setWidth 64 + BitVec.ofNat 64 (16 * (8 * 0 + q) + j.toNat % 16)) := by
    have := c₂ q hq
    rw [show colReg 0 7 = XReg.xmm1 from rfl, m₁,
      tbl_sc tS s.mem (t.setWidth 32) (o := 40) (y := 16 * (8 * 0 + q) + t.toNat % 16) (by decide) (by omega),
      tbl_sc tS s.mem (t.setWidth 32) (o := 40) (y := 16 * (8 * 0 + q) + j.toNat % 16) (by decide) (by omega)]
      at this
    rw [x₃ _ colReg1_ne]
    exact this
  have C1 (q : Nat) (hq : q < 8) :
      byte (s₃.xmm .xmm6) (2 * q) = s.mem (P.setWidth 64 + BitVec.ofNat 64 (16 * (8 * 1 + q) + t.toNat % 16)) ∧
      byte (s₃.xmm .xmm6) (2 * q + 1) =
        s.mem (P.setWidth 64 + BitVec.ofNat 64 (16 * (8 * 1 + q) + j.toNat % 16)) := by
    have := c₃ q hq
    rw [show colReg 1 7 = XReg.xmm6 from rfl, m₂, m₁,
      tbl_sc tS s.mem (t.setWidth 32) (o := 40) (y := 16 * (8 * 1 + q) + t.toNat % 16) (by decide) (by omega),
      tbl_sc tS s.mem (t.setWidth 32) (o := 40) (y := 16 * (8 * 1 + q) + j.toNat % 16) (by decide) (by omega)]
      at this
    exact this
  obtain M₃ : s₃.mem = s.mem.writeW (sc Sc 40) (t.setWidth 32) := by rw [m₃, m₂, m₁]
  have g₃' (r : Reg) (h0 : r ≠ .eax) (h1 : r ≠ .ecx) : s₃.gpr r = s.gpr r := by rw [g₃, g₂]; exact g₁ r h0 h1
  obtain rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂, rd₁]
  obtain wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂, wr₁]
  obtain sy₃' : s₃.syms = s.syms := by rw [sy₃, sy₂, sy₁]
  obtain dx₃ : s₃.gpr .edx = Sc := (g₃' _ (by decide) (by decide)).trans hdx
  -- the selectors
  refine g_ld dx₃ (show addr Sc sT = sc Sc 40 from sc_addr sfit (by decide))
    (by rw [rd₃', wr₃']; exact inr_wr (ww 40 4 (by decide)))
    (show s₃.mem.readW (sc Sc 40) 32 = t.setWidth 32 by rw [M₃, Mem.readW_writeW_self32]) fun s₄ u₄ => ?_
  refine sel_wp u₄.gpr fun s₅ ax₅ g₅ x₅ m₅ rd₅ wr₅ sy₅ => ?_
  obtain dx₅ : s₅.gpr .edx = Sc := (g₅ _ (by decide) (by decide)).trans ((u₄.other _ (by decide)).trans dx₃)
  refine m_st dx₅ (show addr Sc sT = sc Sc 40 from sc_addr sfit (by decide))
    (by rw [wr₅, u₄.wr, wr₃']; exact ww 40 4 (by decide)) ax₅ fun s₆ u₆ => ?_
  refine g_mov (show s₆.gpr .ebp = j.setWidth 32 by
    rw [congrFun u₆.gpr _, g₅ _ (by decide) (by decide), u₄.other _ (by decide), g₃' _ (by decide) (by decide)]
    exact hbp) fun s₇ u₇ => ?_
  refine sel_wp u₇.gpr fun s₈ ax₈ g₈ x₈ m₈ rd₈ wr₈ sy₈ => ?_
  refine g_ori ax₈ fun s₉ u₉ => ?_
  refine g_ror (by decide) u₉.gpr fun s₁₀ u₁₀ => ?_
  obtain M₁₀ : s₁₀.mem = (s.mem.writeW (sc Sc 40) (t.setWidth 32)).writeW (sc Sc 40)
      ((BitVec.ofNat 8 (2 * (t.toNat / 16 % 8) + 128 * (t.toNat / 16 / 8))).setWidth 32) := by
    rw [u₁₀.mem, u₉.mem, m₈, u₇.mem, u₆.mem, m₅, u₄.mem, M₃]
  obtain rd₁₀ : s₁₀.rd = s.rd := by rw [u₁₀.rd, u₉.rd, rd₈, u₇.rd, u₆.rd, rd₅, u₄.rd]; exact rd₃'
  obtain wr₁₀ : s₁₀.wr = s.wr := by rw [u₁₀.wr, u₉.wr, wr₈, u₇.wr, u₆.wr, wr₅, u₄.wr]; exact wr₃'
  obtain sy₁₀ : s₁₀.syms = s.syms := by
    rw [u₁₀.syms, u₉.syms, sy₈, u₇.syms, u₆.syms, sy₅, u₄.syms]; exact sy₃'
  have g₁₀ (r : Reg) (h0 : r ≠ .eax) (h1 : r ≠ .ecx) : s₁₀.gpr r = s.gpr r := by
    rw [u₁₀.other _ h0, u₉.other _ h0, g₈ _ h0 h1, u₇.other _ h0, congrFun u₆.gpr _, g₅ _ h0 h1, u₄.other _ h0]
    exact g₃' r h0 h1
  obtain X₁₀ : s₁₀.xmm = s₃.xmm := by rw [u₁₀.xmm, u₉.xmm, x₈, u₇.xmm, u₆.xmm, x₅, u₄.xmm]
  refine g_orm u₁₀.gpr ((g₁₀ _ (by decide) (by decide)).trans hdx)
    (show addr Sc sT = sc Sc 40 from sc_addr sfit (by decide))
    (by rw [rd₁₀, wr₁₀]; exact inr_wr (ww 40 4 (by decide)))
    (show s₁₀.mem.readW (sc Sc 40) 32 = _ by rw [M₁₀, Mem.readW_writeW_self32]) fun s₁₁ u₁₁ => ?_
  refine x_movd u₁₁.gpr fun s₁₂ u₁₂ => ?_
  obtain ⟨_, _, _, _, _, _, _, _, hor⟩ := sel_facts (j.toNat / 16) (by omega)
  obtain I0 : byte (s₁₂.xmm .xmm7) 0 = BitVec.ofNat 8 (2 * (t.toNat / 16 % 8) + 128 * (t.toNat / 16 / 8)) := by
    rw [u₁₂.xmm, byte_movd32 _ (by decide), show (BitVec.ofNat 32 1 : BitVec 32) = 1#32 from rfl, hor,
      BitVec.or_comm]
    exact pack_lo _ _
  obtain I1 : byte (s₁₂.xmm .xmm7) 1 =
      BitVec.ofNat 8 (2 * (j.toNat / 16 % 8) + 128 * (j.toNat / 16 / 8) + 1) := by
    rw [u₁₂.xmm, byte_movd32 _ (by decide), show (BitVec.ofNat 32 1 : BitVec 32) = 1#32 from rfl, hor,
      BitVec.or_comm]
    exact pack_hi _ _
  obtain X1 : s₁₂.xmm .xmm1 = s₃.xmm .xmm1 := by rw [u₁₂.other _ (by decide), u₁₁.xmm, X₁₀]
  obtain X6 : s₁₂.xmm .xmm6 = s₃.xmm .xmm6 := by rw [u₁₂.other _ (by decide), u₁₁.xmm, X₁₀]
  refine read2_out_wp (show s₁₂.gpr .edx = Sc by
      rw [u₁₂.gpr, u₁₁.other _ (by decide)]; exact (g₁₀ _ (by decide) (by decide)).trans hdx) sfit
    (by rw [u₁₂.wr, u₁₁.wr, wr₁₀]; exact hws)
    (by
      rw [u₁₂.mem, u₁₁.mem, M₁₀, u₁₂.syms, u₁₁.syms, sy₁₀, sc_rw _ _ _ (by decide) (by decide) (by decide),
        sc_rw _ _ _ (by decide) (by decide) (by decide)]
      exact v28) fun s₁₃ q ax₁₃ g₁₃ m₁₃ rd₁₃ wr₁₃ sy₁₃ => ?_
  -- the bytes selected
  have pk0 := byte_pick2 (C0 := s₁₂.xmm .xmm1) (C1 := s₁₂.xmm .xmm6) (I := s₁₂.xmm .xmm7) (b := 0)
    (hx := t.toNat / 16) (e := 0) (by decide) (by omega) (by decide) (by rw [Nat.add_zero]; exact I0)
  have pk1 := byte_pick2 (C0 := s₁₂.xmm .xmm1) (C1 := s₁₂.xmm .xmm6) (I := s₁₂.xmm .xmm7) (b := 1)
    (hx := j.toNat / 16) (e := 1) (by decide) (by omega) (by decide) I1
  obtain e0 : byte (XBinOp.eval .por (XBinOp.eval .pshufb (s₁₂.xmm .xmm1) (s₁₂.xmm .xmm7))
      (XBinOp.eval .pshufb (s₁₂.xmm .xmm6) (XBinOp.eval .pxor (s₁₂.xmm .xmm7) (cst oH)))) 0 =
      s.mem (P.setWidth 64 + BitVec.ofNat 64 t.toNat) := by
    rw [pk0, Nat.add_zero, X1, X6]
    by_cases h8 : t.toNat / 16 < 8
    · rw [ite_eq_left h8, (C0 _ (by omega)).1, show 16 * (8 * 0 + t.toNat / 16 % 8) + t.toNat % 16 = t.toNat by omega]
    · rw [ite_eq_right h8, (C1 _ (by omega)).1, show 16 * (8 * 1 + t.toNat / 16 % 8) + t.toNat % 16 = t.toNat by omega]
  obtain e1 : byte (XBinOp.eval .por (XBinOp.eval .pshufb (s₁₂.xmm .xmm1) (s₁₂.xmm .xmm7))
      (XBinOp.eval .pshufb (s₁₂.xmm .xmm6) (XBinOp.eval .pxor (s₁₂.xmm .xmm7) (cst oH)))) 1 =
      s.mem (P.setWidth 64 + BitVec.ofNat 64 j.toNat) := by
    rw [pk1, X1, X6]
    by_cases h8 : j.toNat / 16 < 8
    · rw [ite_eq_left h8, (C0 _ (by omega)).2, show 16 * (8 * 0 + j.toNat / 16 % 8) + j.toNat % 16 = j.toNat by omega]
    · rw [ite_eq_right h8, (C1 _ (by omega)).2, show 16 * (8 * 1 + j.toNat / 16 % 8) + j.toNat % 16 = j.toNat by omega]
  rw [e0] at ax₁₃
  rw [e1, u₁₂.mem, u₁₁.mem, M₁₀] at m₁₃
  have c48 (o n : Nat) (h1 : 16 ≤ o) (h2 : o + n ≤ 64) : (⟨sc Sc 16, 48⟩ : Region).Contains (sc Sc o) n :=
    Offset.contains _ h1 (by omega) (by decide)
  refine k s₁₃ ax₁₃ (fun r h0 h1 h2 => ?_) ?_ ?_ ?_ ?_ (by rw [rd₁₃, u₁₂.rd, u₁₁.rd]; exact rd₁₀)
    (by rw [wr₁₃, u₁₂.wr, u₁₁.wr]; exact wr₁₀) (by rw [sy₁₃, u₁₂.syms, u₁₁.syms]; exact sy₁₀)
  · rw [g₁₃ r h0 h1 h2, u₁₂.gpr, u₁₁.other _ h0]; exact g₁₀ r h0 h1
  · rw [m₁₃, Mem.readW_writeW_self32]
  · rw [m₁₃, sc_rw _ _ _ (by decide) (by decide) (by decide), q16_rw _ _ _ (by decide) (by decide),
      sc_rw _ _ _ (by decide) (by decide) (by decide), sc_rw _ _ _ (by decide) (by decide) (by decide)]
  · rw [m₁₃, sc_rw _ _ _ (by decide) (by decide) (by decide), q16_rw _ _ _ (by decide) (by decide),
      sc_rw _ _ _ (by decide) (by decide) (by decide), sc_rw _ _ _ (by decide) (by decide) (by decide)]
  · rw [m₁₃]
    refine Frame.writeW ?_ (List.mem_singleton_self _) _ (c48 32 (32 / 8) (by decide) (by decide))
    refine Frame.writeW ?_ (List.mem_singleton_self _) _ (c48 16 (64 / 8) (by decide) (by decide))
    refine Frame.writeW ?_ (List.mem_singleton_self _) _ (c48 40 (32 / 8) (by decide) (by decide))
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c48 40 (32 / 8) (by decide) (by decide))

/-! ### An iteration, by its memory -/

/-- The two bytes of an exchange, each exclusive-ored with their
difference: the exchange. -/
theorem xor_swap (m : Mem) (pi pj x : Addr) (a b : Byte) (ha : m pi = a) (hb : m pj = b) :
    ((m.write pi 1 (a ^^^ (b ^^^ a))).write pj 1 ((m.write pi 1 (a ^^^ (b ^^^ a))) pj ^^^ (b ^^^ a))) x =
      ((m.write pj 1 a).write pi 1 b) x := by
  have e1 : a ^^^ (b ^^^ a) = b := by
    rw [BitVec.xor_comm b a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  have e2 : b ^^^ (b ^^^ a) = a := by rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  simp only [write_byte, e1]
  by_cases hj : x = pj
  · by_cases hi : x = pi
    · rw [ite_eq_left hj, ite_eq_left hi, ite_eq_left (hj.symm.trans hi), e2, ← ha, ← hb, ← hi, ← hj]
    · rw [ite_eq_left hj, ite_eq_right hi, ite_eq_left hj, ite_eq_right (fun h => hi (hj.trans h)), hb, e2]
  · rw [ite_eq_right hj]
    by_cases hi : x = pi
    · rw [ite_eq_left hi, ite_eq_left hi]
    · rw [ite_eq_right hi, ite_eq_right hi, ite_eq_right hj]

/-- The byte after `i`, after the exchange at `i` and `j`. -/
theorem swapped_next (m : Mem) (p : Addr) (ii jj a b : Byte) :
    ((m.write (p + BitVec.ofNat 64 jj.toNat) 1 a).write (p + BitVec.ofNat 64 ii.toNat) 1 b)
        (p + BitVec.ofNat 64 (ii + 1#8).toNat) =
      if jj = ii + 1#8 then a else m (p + BitVec.ofNat 64 (ii + 1#8).toNat) := by
  have hi := ii.isLt
  have hj := jj.isLt
  have h1 := (ii + 1#8).isLt
  have e : (ii + 1#8).toNat = (ii.toNat + 1) % 256 := by rw [BitVec.toNat_add]; rfl
  rw [write_byte, ite_eq_right (Offset.add_ofNat_ne p (by omega) (by omega) (by omega)), write_byte]
  by_cases h : jj = ii + 1#8
  · rw [ite_eq_left h, ite_eq_left (by rw [h])]
  · rw [ite_eq_right h, ite_eq_right (Offset.add_ofNat_ne p (by omega) (by omega)
      fun e' => h (BitVec.eq_of_toNat_eq e'.symm))]

/-- What an iteration of the stream loop writes but data: the table, and the
working space from its byte 16 on. -/
def wideRegions (P Sc : BitVec 32) : List Region := [⟨P.setWidth 64, 256⟩, ⟨sc Sc 16, 48⟩]

/-- What the stream loop writes. -/
def stepRegions (P D L Sc : BitVec 32) : List Region :=
  [⟨P.setWidth 64, 256⟩, ⟨sc Sc 16, 48⟩, ⟨D.setWidth 64, L.toNat⟩]

theorem step_sub_apply (P D L Sc : BitVec 32) :
    ∀ r ∈ stepRegions P D L Sc, ∃ r' ∈ applyRegions P D L Sc, Region.Sub r r' := by
  intro r hr
  simp only [stepRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), Offset.sub_base _ (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (Nat.le_refl _)⟩

theorem wide_mem_step (P D L Sc : BitVec 32) : ∀ r ∈ wideRegions P Sc, r ∈ stepRegions P D L Sc := by
  intro r hr
  simp only [wideRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self

/-- One iteration of the stream loop, by its memory: the exchange at `ii` and
`jj`, whose bytes are in their slots; the data byte; the next `i` and `j`,
with their bytes in the slots; and nothing else but the working space from
its byte 16 on. -/
theorem apply_step {s₀ t : State} {P D L Sc : BitVec 32} (hp : ApplyPre s₀ P D L Sc) (ii jj : Byte) {n : Nat}
    (hf : Frame (applyRegions P D L Sc) s₀.mem t.mem) (hsp : t.gpr .esp = s₀.gpr .esp) (hrd : t.rd = s₀.rd)
    (hwr : t.wr = s₀.wr) (hdi : t.gpr .edi = P) (hsi : t.gpr .esi = ii.setWidth 32)
    (hbp : t.gpr .ebp = jj.setWidth 32) (hbx : t.gpr .ebx = BitVec.ofNat 32 n) (hn : n < L.toNat)
    (htab : t.mem.readW (sc Sc 28) 32 = t.syms tableName)
    (v24 : t.mem.readW (sc Sc 24) 32 = (t.mem (P.setWidth 64 + BitVec.ofNat 64 ii.toNat)).setWidth 32)
    (v32 : t.mem.readW (sc Sc 32) 32 = (t.mem (P.setWidth 64 + BitVec.ofNat 64 jj.toNat)).setWidth 32) :
    let a := t.mem (P.setWidth 64 + BitVec.ofNat 64 ii.toNat)
    let b := t.mem (P.setWidth 64 + BitVec.ofNat 64 jj.toNat)
    let swapped := (t.mem.write (P.setWidth 64 + BitVec.ofNat 64 jj.toNat) 1 a).write
      (P.setWidth 64 + BitVec.ofNat 64 ii.toNat) 1 b
    let nx := swapped (P.setWidth 64 + BitVec.ofNat 64 (ii + 1#8).toNat)
    WP isa (.block applyStep) t fun u =>
      (∀ y < 256, u.mem (P.setWidth 64 + BitVec.ofNat 64 y) = swapped (P.setWidth 64 + BitVec.ofNat 64 y)) ∧
      u.mem (D.setWidth 64 + BitVec.ofNat 64 n) =
        t.mem (D.setWidth 64 + BitVec.ofNat 64 n) ^^^ swapped (P.setWidth 64 + BitVec.ofNat 64 (a + b).toNat) ∧
      (∀ x, ¬ (x - P.setWidth 64).toNat < 256 → ¬ (x - sc Sc 16).toNat < 48 →
        x ≠ D.setWidth 64 + BitVec.ofNat 64 n → u.mem x = t.mem x) ∧
      Frame (stepRegions P D L Sc) t.mem u.mem ∧
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.syms = t.syms ∧ u.gpr .edi = P ∧ u.gpr .esp = t.gpr .esp ∧
      u.gpr .esi = (ii + 1#8).setWidth 32 ∧ u.gpr .ebp = (jj + nx).setWidth 32 ∧
      u.mem.readW (sc Sc 24) 32 = nx.setWidth 32 ∧
      u.mem.readW (sc Sc 32) 32 = (swapped (P.setWidth 64 + BitVec.ofNat 64 (jj + nx).toNat)).setWidth 32 ∧
      u.mem.readW (sc Sc 28) 32 = t.mem.readW (sc Sc 28) 32 ∧
      u.gpr .ebx = BitVec.ofNat 32 (n + 1) ∧ u.zf = some (BitVec.ofNat 32 (n + 1) - L == 0#32) := by
  intro a b swapped nx
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
  have hW1 : (⟨P.setWidth 64, 256⟩ : Region) ∈ wideRegions P Sc := List.mem_cons_self
  have hW2 : (⟨sc Sc 16, 48⟩ : Region) ∈ wideRegions P Sc := List.mem_cons_of_mem _ List.mem_cons_self
  have wsub : ∀ r ∈ wideRegions P Sc, ∃ r' ∈ applyRegions P D L Sc, Region.Sub r r' := fun r hr =>
    step_sub_apply P D L Sc r (wide_mem_step P D L Sc r hr)
  have cT (y : Byte) : (⟨P.setWidth 64, 256⟩ : Region).Contains (P.setWidth 64 + BitVec.ofNat 64 y.toNat) 1 :=
    Offset.contains_base _ (by have := y.isLt; omega) (by have := y.isLt; omega)
  have cS (o k : Nat) (h1 : 16 ≤ o) (h2 : o + k ≤ 64) : (⟨sc Sc 16, 48⟩ : Region).Contains (sc Sc o) k :=
    Offset.contains _ h1 (by omega) (by decide)
  have sST (o : Nat) (ho : o + 4 ≤ 64) (y : Byte) :
      Mem.Sep (sc Sc o) 4 (P.setWidth 64 + BitVec.ofNat 64 y.toNat) 1 :=
    sep_of_sub hp.ctxScratch.symm (Offset.contains_base (Sc.setWidth 64) (d := o) (n := 4) (k := 64) ho (by omega))
      (Offset.contains_base _ (by have := y.isLt; omega) (by have := y.isLt; omega))
  have cD : (⟨D.setWidth 64, L.toNat⟩ : Region).Contains (D.setWidth 64 + BitVec.ofNat 64 n) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  have sSD (o : Nat) (ho : o + 4 ≤ 64) : Mem.Sep (sc Sc o) 4 (D.setWidth 64 + BitVec.ofNat 64 n) 1 :=
    sep_of_sub hp.dataScratch.symm (Offset.contains_base (Sc.setWidth 64) (d := o) (n := 4) (k := 64) ho (by omega))
      cD
  obtain hdw : ∀ r ∈ wideRegions P Sc, Region.Disjoint ⟨D.setWidth 64, L.toNat⟩ r := by
    intro r hr
    simp only [wideRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.ctxData.sub_left (Region.sub_prefix (by decide))).symm
    · exact (hp.dataScratch.symm.sub_left (Offset.sub_base _ (by decide))).symm
  obtain hnx : nx = if jj = ii + 1#8 then a else t.mem (P.setWidth 64 + BitVec.ofNat 64 (ii + 1#8).toNat) :=
    swapped_next _ _ _ _ _ _
  simp only [applyStep, List.append_assoc]
  refine nextSi_wp (si := a) hsi hbp hdi fit (inr_wr hT) (by rw [hsp]; exact argin 3 (by decide))
    (by rw [hsp]; exact (hp.arg_eq hf (i := 3) (by decide)).trans hp.aS) hp.scratchFit hS v24
    fun s₁ dx₁ g₁ m₁ rd₁ wr₁ sy₁ => ?_
  rw [← hnx] at m₁
  have rs₁ (o : Nat) (h : o + 4 ≤ 36) : s₁.mem.readW (sc Sc o) 32 = t.mem.readW (sc Sc o) 32 := by
    rw [m₁, sc_rw _ _ _ (.inr h) (by decide) (by omega), sc_rw _ _ _ (.inr h) (by decide) (by omega)]
  have tb₁ (y : Nat) (hy : y < 256) :
      s₁.mem (P.setWidth 64 + BitVec.ofNat 64 y) = t.mem (P.setWidth 64 + BitVec.ofNat 64 y) := by
    rw [m₁, tbl_sc hp.ctxScratch _ _ (o := 36) (by decide) hy, tbl_sc hp.ctxScratch _ _ (o := 36) (by decide) hy]
  obtain F₁ : Frame (wideRegions P Sc) t.mem s₁.mem := by
    rw [m₁]
    exact ((Frame.refl _ _).writeW hW2 _ (cS 36 (32 / 8) (by decide) (by decide))).writeW hW2 _
      (cS 36 (32 / 8) (by decide) (by decide))
  refine iRow_wp (si := a) (sj := b) dx₁ ((g₁ _ (by decide) (by decide) (by decide)).trans hsi)
    ((g₁ _ (by decide) (by decide) (by decide)).trans hdi) fit (by rw [wr₁]; exact hT) hp.scratchFit
    (by rw [wr₁]; exact hS) ((rs₁ 24 (by decide)).trans v24) ((rs₁ 32 (by decide)).trans v32)
    (by rw [rs₁ 28 (by decide), sy₁]; exact htab) fun s₂ cx₂ tb₂ g₂ m₂ rd₂ wr₂ sy₂ => ?_
  rw [tb₁ _ ii.isLt] at m₂
  refine head_wp (j := jj) (a := b ^^^ a)
    ((g₂ _ (by decide) (by decide) (by decide)).trans ((g₁ _ (by decide) (by decide) (by decide)).trans hbp))
    cx₂ tb₂ fun s₃ X₃ S₃ g₃ m₃ rd₃ wr₃ sy₃ => ?_
  refine xorRows_wp (j := jj) (d := b ^^^ a)
    ((g₃ _ (by decide)).trans ((g₂ _ (by decide) (by decide) (by decide)).trans
      ((g₁ _ (by decide) (by decide) (by decide)).trans hdi))) fit (by rw [wr₃, wr₂, wr₁]; exact hT)
    (show s₃.gpr .edx = s₃.syms tableName by rw [g₃ _ (by decide), sy₃]; exact tb₂) X₃ S₃
    fun s₄ m₄ g₄ rd₄ wr₄ sy₄ => ?_
  have G₄ (r : Reg) (h0 : r ≠ .eax) (h1 : r ≠ .ecx) (h2 : r ≠ .edx) : s₄.gpr r = t.gpr r := by
    rw [g₄, g₃ r h0, g₂ r h0 h1 h2, g₁ r h0 h1 h2]
  obtain rd₄' : s₄.rd = t.rd := by rw [rd₄, rd₃, rd₂, rd₁]
  obtain wr₄' : s₄.wr = t.wr := by rw [wr₄, wr₃, wr₂, wr₁]
  obtain sy₄' : s₄.syms = t.syms := by rw [sy₄, sy₃, sy₂, sy₁]
  have T₄ (y : Nat) (hy : y < 256) :
      s₄.mem (P.setWidth 64 + BitVec.ofNat 64 y) = swapped (P.setWidth 64 + BitVec.ofNat 64 y) := by
    rw [m₄, m₃, m₂, xor_swap s₁.mem _ _ _ a b (tb₁ _ ii.isLt) (tb₁ _ jj.isLt)]
    show _ = ((t.mem.write _ 1 a).write _ 1 b) _
    simp only [write_byte]
    rw [tb₁ y hy]
  obtain F₄ : Frame (wideRegions P Sc) t.mem s₄.mem := by
    rw [m₄, m₃, m₂]
    exact (F₁.write hW1 _ (cT ii)).write hW1 _ (cT jj)
  have rs₄ (o : Nat) (ho : o + 4 ≤ 64) : s₄.mem.readW (sc Sc o) 32 = s₁.mem.readW (sc Sc o) 32 := by
    rw [m₄, readW_write1 (sST o ho jj), m₃, m₂, readW_write1 (sST o ho ii)]
  refine advance_wp (i := ii) (j := jj) (si := a) (sj := b) (nx := nx)
    ((G₄ _ (by decide) (by decide) (by decide)).trans hsi) ((G₄ _ (by decide) (by decide) (by decide)).trans hbp)
    (by rw [rd₄', wr₄', G₄ _ (by decide) (by decide) (by decide), hsp]; exact argin 3 (by decide))
    (by
      rw [G₄ _ (by decide) (by decide) (by decide), hsp]
      exact (hp.arg_eq (hf.trans (F₄.sub wsub)) (i := 3) (by decide)).trans hp.aS) hp.scratchFit
    (by rw [wr₄']; exact hS) ((rs₄ 24 (by decide)).trans ((rs₁ 24 (by decide)).trans v24))
    ((rs₄ 32 (by decide)).trans ((rs₁ 32 (by decide)).trans v32))
    ((rs₄ 36 (by decide)).trans (by rw [m₁, Mem.readW_writeW_self32]))
    fun s₅ ax₅ si₅ bp₅ dx₅ g₅ m₅ rd₅ wr₅ sy₅ => ?_
  obtain F₅ : Frame (wideRegions P Sc) t.mem s₅.mem := by
    rw [m₅]; exact F₄.writeW hW2 _ (cS 24 (32 / 8) (by decide) (by decide))
  have T₅ (y : Nat) (hy : y < 256) :
      s₅.mem (P.setWidth 64 + BitVec.ofNat 64 y) = swapped (P.setWidth 64 + BitVec.ofNat 64 y) := by
    rw [m₅, tbl_sc hp.ctxScratch _ _ (o := 24) (by decide) hy]; exact T₄ y hy
  have G₅ (r : Reg) (h0 : r ≠ .eax) (h1 : r ≠ .ecx) (h2 : r ≠ .edx) (h3 : r ≠ .esi) (h4 : r ≠ .ebp) :
      s₅.gpr r = t.gpr r := (g₅ r h0 h1 h2 h3 h4).trans (G₄ r h0 h1 h2)
  refine read2_wp (t := b + a) (j := jj + nx) ax₅ bp₅ dx₅
    ((G₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hdi) fit
    (by rw [rd₅, wr₅, rd₄', wr₄']; exact inr_wr hT) hp.scratchFit (by rw [wr₅, wr₄']; exact hS) hp.ctxScratch
    (by
      rw [m₅, sc_rw _ _ _ (.inl (by decide)) (by decide) (by decide), rs₄ 28 (by decide), rs₁ 28 (by decide), sy₅,
        sy₄']
      exact htab) fun s₆ ax₆ g₆ w32 w24 w28 F₆ rd₆ wr₆ sy₆ => ?_
  rw [T₅ _ (b + a).isLt, BitVec.add_comm b a] at ax₆
  rw [T₅ _ (jj + nx).isLt] at w32
  obtain F₆' : Frame (wideRegions P Sc) t.mem s₆.mem := F₅.trans (F₆.mono fun r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact hW2)
  obtain sp₆ : s₆.gpr .esp = s₀.gpr .esp := by
    rw [g₆ _ (by decide) (by decide) (by decide), G₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hsp
  obtain rd₆' : s₆.rd = t.rd := by rw [rd₆, rd₅]; exact rd₄'
  obtain wr₆' : s₆.wr = t.wr := by rw [wr₆, wr₅]; exact wr₄'
  have hmD : (⟨D.setWidth 64, L.toNat⟩ : Region) ∈ applyRegions P D L Sc :=
    List.mem_cons_of_mem _ List.mem_cons_self
  refine apply_tail_wp (D := D) (L := L) ax₆
    ((g₆ _ (by decide) (by decide) (by decide)).trans
      ((G₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbx)) hn hp.dataFit
    (by rw [rd₆', wr₆', sp₆]; exact argin 1 (by decide))
    (by rw [sp₆]; exact (hp.arg_eq (hf.trans (F₆'.sub wsub)) (i := 1) (by decide)).trans hp.aD)
    (by rw [wr₆']; exact hDn) (by rw [rd₆', wr₆', sp₆]; exact argin 2 (by decide))
    (fun v => by
      rw [sp₆]
      exact (hp.arg_eq (hf.trans ((F₆'.sub wsub).write hmD _ cD)) (i := 2) (by decide)).trans hp.aL)
    fun u m₇ bx₇ z₇ g₇ rd₇ wr₇ sy₇ => ?_
  obtain hd : s₆.mem (D.setWidth 64 + BitVec.ofNat 64 n) = t.mem (D.setWidth 64 + BitVec.ofNat 64 n) :=
    F₆'.bytes (R := ⟨D.setWidth 64, L.toNat⟩) hdw (show L.toNat ≤ 2 ^ 64 by omega) hn
  obtain sTD : Mem.Sep (P.setWidth 64) 256 (D.setWidth 64 + BitVec.ofNat 64 n) 1 :=
    sep_of_sub (hp.ctxData.sub_left (Region.sub_prefix (by decide))) (Region.contains_self _ _) cD
  have T₆ (y : Nat) (hy : y < 256) :
      s₆.mem (P.setWidth 64 + BitVec.ofNat 64 y) = swapped (P.setWidth 64 + BitVec.ofNat 64 y) := by
    obtain e : s₆.mem (P.setWidth 64 + BitVec.ofNat 64 y) = s₅.mem (P.setWidth 64 + BitVec.ofNat 64 y) :=
      F₆.bytes (R := ⟨P.setWidth 64, 256⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        exact (hp.ctxScratch.sub_left (Region.sub_prefix (by decide))).symm.sub_left
          (Offset.sub_base _ (by decide)) |>.symm) (show (256 : Nat) ≤ 2 ^ 64 by decide) hy
    rw [e]; exact T₅ y hy
  have inT (y : Nat) (hy : y < 256) : (P.setWidth 64 + BitVec.ofNat 64 y - P.setWidth 64).toNat < 256 := by
    rw [Mem.sub_ofNat_toNat _ (by omega)]; exact hy
  refine ⟨fun y hy => ?_, ?_, fun x hx1 hx2 hx3 => ?_, ?_, rd₇.trans rd₆', wr₇.trans wr₆', ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, bx₇, z₇⟩
  · rw [m₇, write_byte, ite_eq_right (fun e => sTD _ (inT y hy) (by rw [e, BitVec.sub_self]; decide))]
    exact T₆ y hy
  · rw [m₇, write_byte, ite_eq_left rfl, hd]
  · rw [m₇, write_byte, ite_eq_right hx3]
    refine F₆' x fun r hr hc => ?_
    simp only [wideRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [Region.Contains] at hc <;> omega
  · rw [m₇]
    exact (F₆'.mono (wide_mem_step P D L Sc)).write
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) _ cD
  · rw [sy₇, sy₆, sy₅]; exact sy₄'
  · rw [g₇ _ (by decide) (by decide) (by decide), g₆ _ (by decide) (by decide) (by decide)]
    exact (G₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hdi
  · rw [g₇ _ (by decide) (by decide) (by decide), sp₆, hsp]
  · rw [g₇ _ (by decide) (by decide) (by decide), g₆ _ (by decide) (by decide) (by decide)]; exact si₅
  · rw [g₇ _ (by decide) (by decide) (by decide), g₆ _ (by decide) (by decide) (by decide)]; exact bp₅
  · rw [m₇, readW_write1 (sSD 24 (by decide)), w24, m₅, Mem.readW_writeW_self32]
  · rw [m₇, readW_write1 (sSD 32 (by decide)), w32]
  · rw [m₇, readW_write1 (sSD 28 (by decide)), w28, m₅, sc_rw _ _ _ (.inl (by decide)) (by decide) (by decide),
      rs₄ 28 (by decide), rs₁ 28 (by decide)]

-- QW3-STEP

/-! ## The stream loop -/

theorem table_congr {m m' : Mem} {p : Addr}
    (h : ∀ y < 256, m' (p + BitVec.ofNat 64 y) = m (p + BitVec.ofNat 64 y)) :
    (contextAt m' p).table = (contextAt m p).table := by
  apply Vector.ext
  intro k hk
  simp only [contextAt, Vector.getElem_ofFn]
  exact h k hk

-- QW3-LOOP

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

theorem apply_ok (s : State) {P D L Sc : BitVec 32} (hp : ApplyPre s P D L Sc) (hsp4 : 4 ≤ (s.gpr .esp).toNat)
    (hstk : ∀ r ∈ applyRegions P D L Sc, Region.Disjoint (below (s.gpr .esp) 4) r) :
    WP isa Impl.Rc4.X86.Ssse3.apply s fun t =>
      (contextAt t.mem (P.setWidth 64) = (upd s P D L.toNat).1 ∧
        bytesAt t.mem (D.setWidth 64) L.toNat = (upd s P D L.toNat).2) ∧
      Frame (below (s.gpr .esp) 4 :: applyRegions P D L Sc) s.mem t.mem ∧ t.gpr .ebx = s.gpr .ebx ∧
      t.gpr .esi = s.gpr .esi ∧ t.gpr .edi = s.gpr .edi ∧ t.gpr .ebp = s.gpr .ebp ∧
      t.gpr .esp = s.gpr .esp := by
  sorry

-- QW3-FN

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
