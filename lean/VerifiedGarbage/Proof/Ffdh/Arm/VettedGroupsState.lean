module

public import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.CallLay

/-! Read-only memory and register interfaces of the vetted-domain scan. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedGroups
open VG VG.Arm
open VG.Impl.Ffdh.Arm.VettedGroups
open VG.Proof.X25519.Arm (Rest)

structure Source (src : BitVec 32) (k : Nat) (dom : List Byte) (s : State) : Prop where
  positive : 0 < dom.length
  fit : src.toNat + dom.length ≤ 2 ^ 32
  read : InRegions (s.rd ++ s.wr) (State.addr src) dom.length
  bytes : Spec.Rsa.bytesAt s.mem (State.addr src) dom.length = dom
  length : dom.length = 2 * k ∨ dom.length = 3 * k

structure RecordAt (p : BitVec 32) (g : Group) (s : State) : Prop where
  positive : 0 < g.len
  lenFit : g.len < 2 ^ 32
  bitsFit : g.bits < 2 ^ 32
  fit : p.toNat + 8 + 3 * g.len ≤ 2 ^ 32
  readLen : InRegions (s.rd ++ s.wr) (State.addr p) 4
  readBits : InRegions (s.rd ++ s.wr) (State.addr (p + 4)) 4
  len : s.mem.readW (State.addr p) 32 = BitVec.ofNat 32 g.len
  bits : s.mem.readW (State.addr (p + 4)) 32 = BitVec.ofNat 32 g.bits
  read : InRegions (s.rd ++ s.wr) (State.addr (p + 8)) (3 * g.len)
  bytes : Spec.Rsa.bytesAt s.mem (State.addr (p + 8)) (3 * g.len) = g.domain

def TableAt (p : BitVec 32) : List Group → State → Prop
  | [], _ => True
  | g :: gs, s => RecordAt p g s ∧ TableAt (p + BitVec.ofNat 32 (8 + 3 * g.len)) gs s

abbrev clobbers : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r7, .r11, .r12, .lr]

structure Cursor (table src : BitVec 32) (k : Nat) (dom : List Byte) (gs : List Group) (s : State) : Prop where
  ptr : s.gpr .r4 = table
  count : s.gpr .r7 = BitVec.ofNat 32 gs.length
  width : s.gpr .r6 = BitVec.ofNat 32 k
  source : s.gpr .r9 = src
  length : s.gpr .r10 = BitVec.ofNat 32 dom.length

 theorem Source.after {src : BitVec 32} {k : Nat} {dom : List Byte} {s t : State} {rs : List Reg}
    (h : Source src k dom s) (mem : t.mem = s.mem) (rest : Rest rs s t) : Source src k dom t :=
  ⟨h.positive, h.fit, by rw [rest.rd, rest.wr]; exact h.read,
    by rw [mem]; exact h.bytes, h.length⟩

 theorem RecordAt.after {p : BitVec 32} {g : Group} {s t : State} {rs : List Reg}
    (h : RecordAt p g s) (mem : t.mem = s.mem) (rest : Rest rs s t) : RecordAt p g t := by
  refine ⟨h.positive, h.lenFit, h.bitsFit, h.fit, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rest.rd, rest.wr]; exact h.readLen
  · rw [rest.rd, rest.wr]; exact h.readBits
  · rw [mem]; exact h.len
  · rw [mem]; exact h.bits
  · rw [rest.rd, rest.wr]; exact h.read
  · rw [mem]; exact h.bytes

 theorem TableAt.after {p : BitVec 32} {gs : List Group} {s t : State} {rs : List Reg}
    (h : TableAt p gs s) (mem : t.mem = s.mem) (rest : Rest rs s t) : TableAt p gs t := by
  induction gs generalizing p with
  | nil => trivial
  | cons g gs ih => exact ⟨h.1.after mem rest, ih h.2⟩

end VG.Proof.Ffdh.Arm.VettedGroups
