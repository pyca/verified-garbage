module

public import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Time
meta import VerifiedGarbage.Proof.Rsa.X86.WordRt.Time
import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-! # The taint check of CRT parameter calculation at a run-time width -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86

/-- The arguments, `edi` and `esp`. -/
def τV : VG.X86.Taint.T := { regs := .ofList [.edi, .esp], flags := false, argLen := 68 }

open VG.Impl.Rsa.X86.CrtValuesRt
open VG.Impl.Rsa.X86.CrtValues (sPodd sE1 sE3 sMask aOne aQ aP aDQ aDR aDD aDT aDR2 aDR3 aD nArr)

/-- `∃ hint`, the taint check of `c` from `τ` succeeds. -/
abbrev Ck (τ : VG.X86.Taint.T) (c : Prog isa) : Prop := ∃ hint, (VG.Taint.check sseTaint τ c hint).isSome = true

/-- `τV` with `eax` and `ebx` public too. -/
abbrev τV₂ : VG.X86.Taint.T := { τV with regs := .ofList [.edi, .esp, .eax, .ebx] }

/-- The taint checks of the pieces of `sized`. -/
structure CvCk : Prop where
  loads : Ck τV loads
  block : Ck τV (.block (VG.Impl.Rsa.X86.KeyRt.bitOf lay sPodd aP ++
    VG.Impl.Rsa.X86.WordModRt.balanced lay 7 9 11 aDQ sG))
  r₀ : Ck τV (.seq (.seq (VG.Impl.Rsa.X86.KeyRt.zeroWide lay aDR2) (VG.Impl.Rsa.X86.KeyRt.zeroWide lay (aDR2 + 1)))
    (.block [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc VG.Impl.Rsa.X86.WordModRt.oJ) .eax]))
  r₁ : Ck τV (.block (VG.Proof.Rsa.X86.WordRt.rowHead lay aQ))
  r₂ : Ck τV₂ (.seq (.block (VG.Proof.Rsa.X86.WordRt.rowH₂ lay aDR2 aP)) (VG.Proof.Rsa.X86.WordRt.rowTail lay aDR2 aP aQ none))
  h₀ : Ck τV (.seq (.seq (.seq (VG.Impl.Rsa.X86.KeyRt.zeroWide lay aDR2) (VG.Impl.Rsa.X86.KeyRt.zeroWide lay (aDR2 + 1)))
    (.block (VG.Impl.Rsa.X86.WordModRt.topZero lay aDR2)))
    (.block [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc VG.Impl.Rsa.X86.WordModRt.oJ) .eax]))
  h₂ : Ck τV₂ (.seq (.block (VG.Proof.Rsa.X86.WordRt.rowH₂ lay aDR2 aP true))
    (VG.Proof.Rsa.X86.WordRt.rowTail lay aDR2 aP aQ none true))
  checksA : Ck τV (VG.Impl.Rsa.X86.Keys.seqs checksPrefix)
  suffix : Ck τV (VG.Impl.Rsa.X86.Keys.seqs checksSuffix)
  guard : Ck τV (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc sG)), .alu .cmp .eax (.imm 0)])
  m₀ : Ck τV (.seq (.seq (.block (VG.Impl.Rsa.X86.WordModRt.orTop lay 9 aDD)) (VG.Impl.Rsa.X86.WordModRt.recip lay))
    (VG.Impl.Rsa.X86.WordModRt.seed lay 9 aDQ aDR2 none))
  m₀' : Ck τV (.seq (.seq (.block (VG.Impl.Rsa.X86.WordModRt.orTop lay 9 aDD)) (VG.Impl.Rsa.X86.WordModRt.recip lay))
    (VG.Impl.Rsa.X86.WordModRt.seed lay 9 aDQ aDR3 none))
  m₁ : Ck τV (.block (VG.Proof.Rsa.X86.WordRt.digitHead lay aDQ))
  m₂ : Ck τV₂ (.seq (.block VG.Proof.Rsa.X86.WordRt.digitH₂) (VG.Proof.Rsa.X86.WordRt.digitTail lay 9 aDQ aDR2 aDD aDT))
  m₂' : Ck τV₂ (.seq (.block VG.Proof.Rsa.X86.WordRt.digitH₂) (VG.Proof.Rsa.X86.WordRt.digitTail lay 9 aDQ aDR3 aDD aDT))
  copyD : Ck τV (VG.Impl.Rsa.X86.KeyRt.copy lay aDQ aD)
  copyQ : Ck τV (VG.Impl.Rsa.X86.KeyRt.copy lay aDD aQ)
  clr : Ck τV (.block (VG.Impl.Rsa.X86.KeyRt.clrLow lay aDD))
  bits : Ck τV divRems
  stores : Ck τV stores

theorem cvCk : CvCk := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals exact ⟨_, by taint_decide⟩

end VG.Proof.Rsa.X86.CrtValuesRt
