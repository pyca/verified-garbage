module

meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Mont.X86.PublicWord

public import VerifiedGarbage.Impl.Mont.X86.PublicPower
public import VerifiedGarbage.Impl.Mont.X86.RepeatSquares
import VerifiedGarbage.Proof.Mont.X86.PublicWord
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Mont.X86.PublicPower
meta import VerifiedGarbage.Impl.Mont.X86.RepeatSquares
meta import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! Setup observes the public high word, and otherwise only public counters and addresses. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86

def publicPowerFlags : VG.X86.Taint.T := {regs := .ofList [.edi],flags := true}

def publicPowerBranches (M : Mod) (acc out : Nat) : Prog isa :=
  .ite .e (highPower M acc out (M.n+1)) (powerTwo M acc out (65*M.n))

theorem publicPowerBranches_relCT (M : Mod) (acc out : Nat) :
    RelCT isa (VG.X86.Taint.Agree publicPowerFlags) (publicPowerBranches M acc out)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply erased_relCT (publicPowerBranches M acc out)
    (publicPowerBranches {n:=1,mo:=0,tmp:=16,minv:=0} 64 128)
    (VG.Taint.hintOf taint publicPowerFlags (publicPowerBranches {n:=1,mo:=0,tmp:=16,minv:=0} 64 128))
    rfl rfl rfl
  taint_decide

theorem publicPower_relCT (M : Mod) (acc out : Nat) (base : Addr) (size : Nat)
    (fit : M.mo+4*(2*M.n-1)+4≤size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      w32 s.mem base (M.mo+4*(2*M.n-1))=w32 t.mem base (M.mo+4*(2*M.n-1)))
      (publicPower M acc out) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  change RelCT isa _ (.seq (.block ([.mov .eax (.mem (sc (M.mo+4*(2*M.n-1))))] ++
    [.shift .shr .eax 31,.alu .cmp .eax (.imm 1)])) _) _
  refine VG.RelCT.seq (R := VG.X86.Taint.Agree publicPowerFlags) ?_ (publicPowerBranches_relCT M acc out)
  apply RelCT.block_append
  refine VG.RelCT.seq (publicWord_relCT base size _ fit) ?_
  exact checkedProgramChange (hint := .block []) rfl rfl

theorem repeatSquaresAt_relCT (M : Mod) (inv acc out count : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (repeatSquaresWith (mul M inv acc out out out) count)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
  apply erased_relCT (repeatSquaresWith (mul M inv acc out out out) count)
    (repeatSquaresWith (mul {n:=1,mo:=0,tmp:=16,minv:=0} 4 64 128 128 128) 6)
    (VG.Taint.hintOf taint (workspaceTaint false)
      (repeatSquaresWith (mul {n:=1,mo:=0,tmp:=16,minv:=0} 4 64 128 128 128) 6)) rfl rfl rfl
  taint_decide

end VG.Proof.Mont.X86.Dynamic
