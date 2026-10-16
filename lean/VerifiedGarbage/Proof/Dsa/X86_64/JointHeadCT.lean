module

public import VerifiedGarbage.Proof.Dsa.X86_64.JointByteHead
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointByteHead
public import VerifiedGarbage.Proof.Dsa.X86_64.JointWindowCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.JointWindowCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Spec.Dsa
meta import VerifiedGarbage.Spec.Dsa

/-! # Public addresses for loading a pair of secret exponent bytes -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure JointBytesPublic where
  x : XPub
  ep : Addr
  fp : Addr
  len : Nat

def JointHeadPre (q : JointBytesPublic × Nat) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (n xc : Nat), CExpCtx s (off q.1.x.B q.1.x.o) q.1.x.wx minv n xc ∧
    word s.mem (off q.1.x.B q.1.x.o) (8 * Crt.sI) = BitVec.ofNat 64 q.2 ∧
    word s.mem (off q.1.x.B q.1.x.o) (8 * Crt.sExp) = q.1.ep ∧
    word s.mem (off q.1.x.B q.1.x.o) (8 * Joint.sExp2) = q.1.fp

def JointHeadRegs (q : JointBytesPublic × Nat) (s : State) : Prop :=
  s.gpr .rdi = off q.1.x.B q.1.x.o ∧ s.gpr .rax = q.1.ep ∧
  s.gpr .rcx = BitVec.ofNat 64 q.2 ∧ s.gpr .rsi = q.1.fp

theorem jointHeadPins : Pins JointHeadRegs [.rdi, .rax, .rcx, .rsi] := by
  rintro q s t ⟨a, b, c, d⟩ ⟨e, f, g, h⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact a.trans e.symm
  · exact b.trans f.symm
  · exact c.trans g.symm
  · exact d.trans h.symm

theorem jointHead_ct : RelCT isa (Two JointHeadPre) (.block Joint.byteHead) (fun _ _ => True) := by
  unfold Joint.byteHead
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := JointHeadRegs) [.rdi]
    (pins_rdi (fun q : JointBytesPublic × Nat => off q.1.x.B q.1.x.o)
      (fun _ _ ⟨_, _, _, hc, _⟩ => hc.good.rdi))
    (by unfold Joint.bytePointers; taint_decide) ?_) ?_
  · rintro q s ⟨minv, n, xc, hc, hi, he, hf⟩
    unfold Joint.bytePointers JointHeadRegs
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hc.ld (i := Crt.sI) (by decide),
      hc.ld (i := Crt.sExp) (by decide), hc.ld (i := Joint.sExp2) (by decide), hi, he, hf]
  · exact two_taint _ jointHeadPins (by unfold Joint.byteValues; taint_decide)

end VG.Proof.Dsa.X86_64
