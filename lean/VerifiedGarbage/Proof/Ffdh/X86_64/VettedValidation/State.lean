module

public import VerifiedGarbage.Impl.Ffdh.X86_64.VettedValidation
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Spec.Rsa.Contract

/-! Read-only input and table invariants during exact-domain recognition. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.VettedGroups
open VG.Impl.Ffdh.X86_64.VettedValidation

def clobbers : List Reg := [.rax, .rdx, .rsi, .rcx, .r10, .r11]

structure Context (base src : Addr) (k : Nat) (dom : List Byte) (s : State) : Prop where
  baseReg : s.gpr .r9 = base
  source : s.gpr .rdi = src
  length : s.mem.readW (base + BitVec.ofNat 64 128) 64 = BitVec.ofNat 64 dom.length
  width : s.mem.readW (base + BitVec.ofNat 64 136) 64 = BitVec.ofNat 64 k
  readLength : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 128) 8
  readWidth : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 136) 8
  read : InRegions (s.rd ++ s.wr) src dom.length
  bytes : Spec.Rsa.bytesAt s.mem src dom.length = dom
  shape : dom.length = 2 * k ∨ dom.length = 3 * k
  lower : 64 ≤ k
  upper : k ≤ 1024

structure RecordAt (ptr : Addr) (g : Group) (s : State) : Prop where
  len : 0 < g.len
  lenFit : g.len < 2 ^ 31
  bitsFit : g.bits < 2 ^ 32
  read : InRegions (s.rd ++ s.wr) (ptr + BitVec.ofNat 64 8) (3 * g.len)
  bytes : Spec.Rsa.bytesAt s.mem (ptr + BitVec.ofNat 64 8) (3 * g.len) = g.domain

def TableAt (ptr : Addr) : List Group → State → Prop
  | [], _ => True
  | g :: gs, s => RecordAt ptr g s ∧ TableAt (ptr + BitVec.ofNat 64 (8 + 3 * g.len)) gs s

theorem Context.after {base src : Addr} {k : Nat} {dom : List Byte} {s t : State}
    (h : Context base src k dom s) (mem : t.mem = s.mem) (rest : Keep clobbers s t) :
    Context base src k dom t := by
  refine ⟨(rest.gpr (by decide)).trans h.baseReg, (rest.gpr (by decide)).trans h.source,
    ?_, ?_, ?_, ?_, ?_, ?_ , h.shape, h.lower, h.upper⟩
  · rw [mem]; exact h.length
  · rw [mem]; exact h.width
  · rw [rest.2.1, rest.2.2]; exact h.readLength
  · rw [rest.2.1, rest.2.2]; exact h.readWidth
  · rw [rest.2.1, rest.2.2]; exact h.read
  · rw [mem]; exact h.bytes

theorem RecordAt.after {ptr : Addr} {g : Group} {s t : State}
    (h : RecordAt ptr g s) (mem : t.mem = s.mem) (rest : Keep clobbers s t) :
    RecordAt ptr g t := by
  refine ⟨h.len, h.lenFit, h.bitsFit, ?_, ?_⟩
  · rw [rest.2.1, rest.2.2]; exact h.read
  · rw [mem]; exact h.bytes

theorem TableAt.after {ptr : Addr} {gs : List Group} {s t : State}
    (h : TableAt ptr gs s) (mem : t.mem = s.mem) (rest : Keep clobbers s t) :
    TableAt ptr gs t := by
  induction gs generalizing ptr with
  | nil => trivial
  | cons g gs ih => exact ⟨h.1.after mem rest, ih h.2⟩

end VG.Proof.Ffdh.X86_64.VettedValidation
