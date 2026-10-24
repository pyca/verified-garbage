module

public import VerifiedGarbage.Impl.Ffdh.X86.VettedValidation
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.TCB.X86.Target

/-! The scan keeps its scratch base, stack arguments, and all memory intact. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86 VG.X86.Wp
open VG.Impl.Ffdh.VettedGroups

def clobbers : List Reg := [.eax, .ecx, .edx, .esi, .edi, .ebp]

structure Context (base src sp table : BitVec 32) (k : Nat) (dom : List Byte) (s : State) : Prop where
  baseReg : s.gpr .ebx = base
  stack : s.gpr .esp = sp
  source : arg s 0 = src
  length : arg s 1 = BitVec.ofNat 32 dom.length
  width : arg s 2 = BitVec.ofNat 32 k
  argsRead : InRegions (s.rd ++ s.wr) (argAddr s 0) 12
  tableRead : InRegions (s.rd ++ s.wr) (addr base 16) 4
  tableWord : s.mem.readW (addr base 16) 32 = table
  read : InRegions (s.rd ++ s.wr) (byteAddr src) dom.length
  bytes : Spec.Rsa.bytesAt s.mem (byteAddr src) dom.length = dom
  sourceFits : src.toNat + dom.length ≤ 2 ^ 32
  tableFits : table.toNat + 17744 ≤ 2 ^ 32
  stackFits : sp.toNat + 16 ≤ 2 ^ 32
  shape : dom.length = 2 * k ∨ dom.length = 3 * k
  lower : 64 ≤ k
  upper : k ≤ 1024

structure RecordAt (ptr : Addr) (g : Group) (s : State) : Prop where
  len : 0 < g.len
  lenFit : g.len < 2 ^ 32
  read : InRegions (s.rd ++ s.wr) (ptr + BitVec.ofNat 64 8) (3 * g.len)
  bytes : Spec.Rsa.bytesAt s.mem (ptr + BitVec.ofNat 64 8) (3 * g.len) = g.domain

def TableAt (ptr : Addr) : List Group → State → Prop
  | [], _ => True
  | g :: gs, s => RecordAt ptr g s ∧ TableAt (ptr + BitVec.ofNat 64 (8 + 3 * g.len)) gs s

theorem Context.after {base src sp table : BitVec 32} {k : Nat} {dom : List Byte} {s t : State}
    (h : Context base src sp table k dom s) (mem : t.mem = s.mem) (rest : Keeps clobbers s t) :
    Context base src sp table k dom t := by
  have stack := rest.1 .esp (by decide)
  have args (j : Nat) : arg t j = arg s j := by unfold arg argAddr; rw [stack, mem]
  refine ⟨(rest.1 .ebx (by decide)).trans h.baseReg, stack.trans h.stack,
    (args 0).trans h.source, (args 1).trans h.length, (args 2).trans h.width, ?_, ?_, ?_, ?_, ?_,
    h.sourceFits, h.tableFits, h.stackFits, h.shape, h.lower, h.upper⟩
  · unfold argAddr; rw [stack, rest.2.1, rest.2.2]; exact h.argsRead
  · rw [rest.2.1, rest.2.2]; exact h.tableRead
  · rw [mem]; exact h.tableWord
  · rw [rest.2.1, rest.2.2]; exact h.read
  · rw [mem]; exact h.bytes

theorem RecordAt.after {rs : List Reg} {ptr : Addr} {g : Group} {s t : State}
    (h : RecordAt ptr g s) (mem : t.mem = s.mem) (rest : Keeps rs s t) : RecordAt ptr g t := by
  refine ⟨h.len, h.lenFit, ?_, ?_⟩
  · rw [rest.2.1, rest.2.2]; exact h.read
  · rw [mem]; exact h.bytes

theorem TableAt.after {rs : List Reg} {ptr : Addr} {gs : List Group} {s t : State}
    (h : TableAt ptr gs s) (mem : t.mem = s.mem) (rest : Keeps rs s t) : TableAt ptr gs t := by
  induction gs generalizing ptr with
  | nil => trivial
  | cons g gs ih => exact ⟨h.1.after mem rest, ih h.2⟩

end VG.Proof.Ffdh.X86.VettedValidation
