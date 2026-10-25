module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.FastR2
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Mont.X86.PowerTiming
import VerifiedGarbage.Proof.Dsa.X86.ValidationBlocksTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Fast R² setup has only public loop counts and fixed operand addresses -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.FastR2
open VG VG.X86 VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.FastR2

theorem doublesAt_trace (M : VG.Impl.Mont.Mod) (e acc out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (doublesAt M e acc out)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  refine RelCT.seq (setConst_relCT _ _ _) ?_
  apply erased_relCT (τ := workspaceTaint false) (σ := workspaceTaint false)
    (.seq (.block [.mov .esi (.imm (BitVec.ofNat 32 (M.n + 64 * M.n - e)))])
      (VG.Impl.Mont.X86.Dynamic.doubleLoop M acc out))
    (.seq (.block [.mov .esi (.imm 1)])
      (VG.Impl.Mont.X86.Dynamic.doubleLoop { n := 1, mo := 0, tmp := 0, minv := 0 } 0 0))
    (.seq (workspaceTaint true) (.block []) (.loop (workspaceTaint true) doubleHint)) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)
  decide +kernel

theorem doubles_trace (M : VG.Impl.Mont.Mod) (acc out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (doubles M acc out)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  doublesAt_trace M _ acc out

theorem squares_trace (square : Prog isa)
    (ct : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) square
      (VG.X86.Taint.Agree (workspaceTaint false))) (n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (VG.Impl.Rsa.X86.Keys.seqs (List.replicate (n + 1) square))
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  induction n with
  | zero => exact ct
  | succ n ih => exact RelCT.seq ct ih

theorem codeAt_trace (M : VG.Impl.Mont.Mod) (e acc out : Nat) (square : Prog isa)
    (ct : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) square
      (VG.X86.Taint.Agree (workspaceTaint false))) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (codeAt M e acc out square)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  RelCT.seq (doublesAt_trace M e acc out) (squares_trace square ct 5)

theorem code_trace (M : VG.Impl.Mont.Mod) (acc out : Nat) (square : Prog isa)
    (ct : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) square
      (VG.X86.Taint.Agree (workspaceTaint false))) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (code M acc out square)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  codeAt_trace M _ acc out square ct

end VG.Proof.RsaKeyGen.X86.FastR2
