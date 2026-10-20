module

public import VerifiedGarbage.Proof.Bignum.Arm.MontCallEntry
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! Invoke a shared arithmetic kernel with its permissions restricted to
the RSA workspace and its fifth argument. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.FrameStack
open VG.Spec.Rsa.Mont (numAt Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

def CallResult (base : BitVec 32) (len w o a b : Nat) (s t : State) : Prop :=
  numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
  numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % numAt s.mem (State.addr base) w 0 =
    numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w b % numAt s.mem (State.addr base) w 0 ∧
  Keeps (State.addr base) len w o s.mem t.mem

theorem montCallInvoke_ok (name : String) (callee : Prog isa)
    {base : BitVec 32} {len w o a b : Nat}
    (correct : ∀ s, CallInput base len w o a b s →
      WP isa callee s fun t => abiPreserved s t ∧ CallResult base len w o a b s t)
    (stack : armStack callee ≤ 40) (s : State) (h : CallInput base len w o a b s) :
    WP isa (.call name callee) s fun t =>
      CallResult base len w o a b s t ∧
      Frame [⟨State.addr base, 8 * len⟩, belowA s.sp 40] s.mem t.mem ∧ Rest roundClobbers s t := by
  let rd : List Region := [⟨State.addr s.sp, 4⟩]
  let wr : List Region := [⟨State.addr base, 8 * len⟩]
  let k : Contract isa := {
    pre := CallInput base len w o a b
    post := CallResult base len w o a b
    pub := fun _ _ => True }
  have pre : k.pre (s.callEntry.withRegions rd wr) := by
    refine ⟨⟨h.workspace.nowrap, by simp only [State.withRegions_wr, wr, List.mem_singleton]⟩,
      h.layout, h.width, ?_, ?_, ?_, h.bArg, h.inverse, h.operand, h.stackFit, ?_, h.stackWorkspace, h.stackArg⟩
    · exact (State.callEntry_gpr s (by decide)).trans h.ptr
    · exact (State.callEntry_gpr s (by decide)).trans h.outIndex
    · exact (State.callEntry_gpr s (by decide)).trans h.aIndex
    · exact ⟨_, List.mem_append_left _ List.mem_cons_self, Region.contains_self _ _⟩
  have coversWr : Covers wr s.wr := Covers.one ⟨_, h.workspace.writable, Region.contains_self _ _⟩
  have coversRd : Covers rd (s.rd ++ s.wr) := Covers.one h.argRead
  refine WP.callF (k := k) correct pre
    (Covers.append_left coversRd (Covers.right coversWr)) coversWr (by have := h.stackFit; omega) ?_
  intro t rdEq wrEq spEq frame _ result
  refine ⟨result, FrameStack.Frame.belowA_mono frame stack h.stackFit, ?_⟩
  exact ⟨by intro r hr; exact False.elim (hr (by cases r <;> simp [roundClobbers])),
    rdEq, wrEq, spEq⟩

end VG.Proof.Bignum.Arm
