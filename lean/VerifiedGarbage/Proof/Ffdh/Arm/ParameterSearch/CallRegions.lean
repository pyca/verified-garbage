module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallLayout
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallParams
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Tape
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Params

/-! The candidate's narrowed permissions are covered by the controller's buffers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

theorem call_writes {p : SearchParams} {s : State}
    (output : Workspace s p.c.out p.c.length)
    (control : Workspace s p.control 128)
    (scratch : Workspace s p.c.base (8 * p.c.capacity)) : Covers (callWr p) s.wr := by
  apply Covers.cons (Covers.one ⟨_, output.2, Region.contains_self _ _⟩)
  apply Covers.cons ?_ (Covers.one ⟨_, scratch.2, Region.contains_self _ _⟩)
  apply Covers.one
  rw [p.used_addr]
  exact VG.CallLay.inRegions_sub ⟨_, control.2, Region.contains_self _ _⟩
    (by decide : 112 + 8 ≤ 128) (by decide)

theorem call_reads {p : SearchParams} {used : Nat} {s : State}
    (writes : Covers (callWr p) s.wr)
    (source : InRegions (s.rd ++ s.wr) (State.addr (p.c.tape + BitVec.ofNat 32 used))
      (p.c.bytes.length - used)) (stack : Workspace s s.sp 24) :
    Covers (callRd p used s.sp ++ callWr p) (s.rd ++ s.wr) := by
  apply Covers.append_left ?_ writes.right
  apply Covers.pair (Covers.one source)
  apply Covers.right
  apply Covers.one
  simpa only [VG.Proof.Mont.off, BitVec.add_zero] using VG.CallLay.inRegions_sub
    ⟨_, stack.2, Region.contains_self _ _⟩ (off := 0) (by decide : 0 + 20 ≤ 24) (by decide)

end VG.Proof.Ffdh.Arm.ParameterSearch
