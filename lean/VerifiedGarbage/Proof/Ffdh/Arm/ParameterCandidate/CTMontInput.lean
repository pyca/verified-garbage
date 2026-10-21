module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontPrepare
public import VerifiedGarbage.Proof.Ffdh.Arm.Prepare
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontInputMemory
public import VerifiedGarbage.Proof.Ffdh.Arm.CandidatePrepareCT
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Parameter candidates reuse RSA's public-trace modulus import and precomputation. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm VG.Proof.Mont
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post)

structure MontInputData where
  base : BitVec 32
  src : BitVec 32
  capacity : Nat
  k : Nat

def MontStart (p : MontInputData) (s : State) : Prop := MontPrepInput p.base p.src p.capacity p.k s
def PreparedInput (p : MontInputData) (s : State) : Prop := CandidatePrepareInput p.base p.src p.capacity p.k s

theorem prepareHeader_ok (p : MontInputData) (s : State) (h : MontStart p s) :
    WP isa (.block [.ldrSp .r0 0, .ldrSp .r6 12]) s (PreparedInput p) := by
  have read0 : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4 := by
    simpa only [off, BitVec.add_zero] using h.stack.read (d := 0) (by decide)
  have addr12 : State.addr (s.sp + 12#32) = off (State.addr s.sp) 12 := VG.Arm.addr_add (by have := h.stack.nowrap; omega)
  refine wp_loadStack (a := State.addr s.sp) (by decide) (by simp only [BitVec.add_zero]) read0 fun u first => ?_
  refine wp_loadStack (a := off (State.addr s.sp) 12) (by decide)
    (by rw [first.sp]; exact addr12) (by rw [first.rd, first.wr]; exact h.stack.read (by decide)) fun t second => WP.block_nil ?_
  have memory : t.mem = s.mem := second.mem.trans first.mem
  have rest : Rest [.r0, .r6] s t := (first.rest (by simp)).trans (second.rest (by simp))
  refine ⟨(h.after_memory memory rest).prepare_input
    ((second.other .r0 (by decide)).trans (first.gpr.trans h.stack.savedBase))
    (by rw [second.gpr, first.mem]; exact h.stack.savedCount), ?_⟩
  rw [memory];exact h.normalized

theorem montInput_ct : RelCT isa (Two MontStart)
    (.seq (.block [.ldrSp .r0 0, .ldrSp .r6 12]) VG.Impl.Ffdh.Arm.CandidatePrepare.code) (fun _ _ => True) := by
  have head : RelCT isa (Two MontStart) (.block [.ldrSp .r0 0, .ldrSp .r6 12]) (Two PreparedInput) :=
    two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) prepareHeader_ok
  have prepare : RelCT isa (Two PreparedInput) VG.Impl.Ffdh.Arm.CandidatePrepare.code (fun _ _ => True) := by
    intro s t trS trT u v h runS runT
    obtain ⟨p, left, right, sp⟩ := h
    exact candidatePrepare_ct _ _ _ _ _ _ ⟨left,right,sp⟩ runS runT
  exact head.seq prepare

end VG.Proof.Ffdh.Arm.ParameterCandidate
