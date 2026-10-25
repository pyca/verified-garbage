module

public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.State
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! Public width checking and setup for the existing byte comparator. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Ffdh.X86.VettedValidation VG.Impl.Ffdh.VettedGroups

theorem arg_read {base src sp table : BitVec 32} {k : Nat} {dom : List Byte} {s : State}
    (h : Context base src sp table k dom s) (i : Nat) (hi : i < 3) :
    InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (4 + 4 * i)) 4 := by
  have read := CallLay.inRegions_sub h.argsRead (off := 4 * i) (l := 4) (by omega) (by decide)
  have pointer : addr (s.gpr .esp) (4 + 4 * i) = argAddr s 0 + BitVec.ofNat 64 (4 * i) := by
    change addr (s.gpr .esp) (4 + 4 * i) = addr (s.gpr .esp) 4 + BitVec.ofNat 64 (4 * i)
    rw [addr_eq (x := s.gpr .esp) (k := 4 + 4 * i)
      (by rw [h.stack]; have := h.stackFits; omega)]
    rw [addr_eq (x := s.gpr .esp) (k := 4) (by rw [h.stack]; have := h.stackFits; omega),
      BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [pointer]
  exact read

theorem header_ok {base src sp table : BitVec 32} {k : Nat} {dom : List Byte} {s : State}
    (h : Context base src sp table k dom s) (g : Group) (fit : g.len < 2 ^ 32) :
    WP isa (.block (header g)) s fun t =>
      t.zf = some (decide (g.len = k)) ∧ t.mem = s.mem ∧ Keeps clobbers s t := by
  unfold header
  have read := arg_read h 2 (by decide)
  refine wp_ldm rfl read fun u U => wp_cmpi fun t T _ zero => WP.block_nil ⟨?_, T.mem.trans U.mem,
    (U.keeps.mono (by decide)).trans (T.keeps clobbers)⟩
  have value : u.gpr .eax = BitVec.ofNat 32 k := U.gpr.trans h.width
  rw [zero, value]
  congr 1
  have hk : k < 2 ^ 32 := by have := h.upper; omega
  simpa only [eq_comm] using sub_beq hk fit

theorem args_ok {base src sp table : BitVec 32} {k offset : Nat} {dom : List Byte} {s : State}
    (h : Context base src sp table k dom s) :
    WP isa (.block (compareArgs offset)) s fun t =>
      t.gpr .esi = src ∧ t.gpr .edi = table + BitVec.ofNat 32 (offset + 8) ∧
      t.gpr .ecx = BitVec.ofNat 32 dom.length ∧ t.mem = s.mem ∧ Keeps clobbers s t := by
  unfold compareArgs
  refine wp_ldm rfl (arg_read h 0 (by decide)) fun u U => ?_
  have read1 : InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) 8) 4 := by
    rw [U.other .esp (by decide), U.rd, U.wr]; exact arg_read h 1 (by decide)
  refine wp_ldm rfl read1 fun v V => ?_
  have readT : InRegions (v.rd ++ v.wr) (addr (v.gpr .ebx) 16) 4 := by
    rw [V.other .ebx (by decide), U.other .ebx (by decide), h.baseReg, V.rd, V.wr, U.rd, U.wr]
    exact h.tableRead
  refine wp_ldm rfl readT fun w W => wp_addi fun t T => WP.block_nil ⟨?_, ?_, ?_,
    T.mem.trans (W.mem.trans (V.mem.trans U.mem)),
    (((U.keeps.mono (by decide)).widen V.keeps).widen W.keeps).widen T.keeps⟩
  · rw [T.other .esi (by decide), W.other .esi (by decide), V.other .esi (by decide), U.gpr]
    exact h.source
  · rw [T.gpr, W.gpr, V.other .ebx (by decide), U.other .ebx (by decide), h.baseReg,
      V.mem, U.mem, h.tableWord]
  · rw [T.other .ecx (by decide), W.other .ecx (by decide), V.gpr, U.other .esp (by decide), U.mem]
    exact h.length

theorem test_ok (s : State) :
    WP isa (.block [.alu .test .ebp (.reg .ebp)]) s fun t =>
      t.zf = some (s.gpr .ebp == 0) ∧ t.mem = s.mem ∧ Keeps clobbers s t := by
  exact wp_test fun t T zero => WP.block_nil ⟨by simpa only [BitVec.and_self] using zero,
    T.mem, T.keeps _⟩

end VG.Proof.Ffdh.X86.VettedValidation
