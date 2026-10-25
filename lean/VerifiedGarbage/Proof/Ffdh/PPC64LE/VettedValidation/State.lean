module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.VettedValidation
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Spec.Rsa.Contract

/-! The domain arguments are invariant throughout the read-only recognition scan. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE VG.Impl.Ffdh.VettedGroups

def clobbers : List Reg := [.r0, .r8, .r9, .r10, .r11]

structure Context (src : Addr) (k : Nat) (dom : List Byte) (s : State) : Prop where
  source : s.gpr .r3 = src
  length : s.gpr .r4 = BitVec.ofNat 64 dom.length
  width : s.gpr .r5 = BitVec.ofNat 64 k
  read : InRegions (s.rd ++ s.wr) src dom.length
  bytes : Spec.Rsa.bytesAt s.mem src dom.length = dom
  shape : dom.length = 2 * k ∨ dom.length = 3 * k
  lower : 64 ≤ k
  upper : k ≤ 1024

structure RecordAt (ptr : Addr) (g : Group) (s : State) : Prop where
  len : 0 < g.len
  lenFit : g.len < 2 ^ 15
  bitsFit : g.bits < 2 ^ 15
  read : InRegions (s.rd ++ s.wr) (ptr + BitVec.ofNat 64 8) (3 * g.len)
  bytes : Spec.Rsa.bytesAt s.mem (ptr + BitVec.ofNat 64 8) (3 * g.len) = g.domain

def TableAt (ptr : Addr) : List Group → State → Prop
  | [], _ => True
  | g :: gs, s => RecordAt ptr g s ∧ TableAt (ptr + BitVec.ofNat 64 (8 + 3 * g.len)) gs s

theorem Context.after {src : Addr} {k : Nat} {dom : List Byte} {s t : State}
    (h : Context src k dom s) (mem : t.mem = s.mem) (rest : Keep clobbers s t) :
    Context src k dom t := by
  refine ⟨(rest.gpr (by decide)).trans h.source, (rest.gpr (by decide)).trans h.length,
    (rest.gpr (by decide)).trans h.width, ?_, ?_, h.shape, h.lower, h.upper⟩
  · rw [rest.2.1, rest.2.2]; exact h.read
  · rw [mem]; exact h.bytes

theorem RecordAt.after {rs : List Reg} {ptr : Addr} {g : Group} {s t : State}
    (h : RecordAt ptr g s) (mem : t.mem = s.mem) (rest : Keep rs s t) :
    RecordAt ptr g t := by
  refine ⟨h.len, h.lenFit, h.bitsFit, ?_, ?_⟩
  · rw [rest.2.1, rest.2.2]; exact h.read
  · rw [mem]; exact h.bytes

theorem TableAt.after {rs : List Reg} {ptr : Addr} {gs : List Group} {s t : State}
    (h : TableAt ptr gs s) (mem : t.mem = s.mem) (rest : Keep rs s t) :
    TableAt ptr gs t := by
  induction gs generalizing ptr with
  | nil => trivial
  | cons g gs ih => exact ⟨h.1.after mem rest, ih h.2⟩

theorem keep_trans {s t u : State} (a : Keep clobbers s t) (b : Keep clobbers t u) : Keep clobbers s u :=
  (a.trans b).mono (by intro r hr; simpa only [List.mem_append, or_self] using hr)

end VG.Proof.Ffdh.PPC64LE.VettedValidation
