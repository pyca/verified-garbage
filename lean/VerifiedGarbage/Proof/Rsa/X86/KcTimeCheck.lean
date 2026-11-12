module

public import VerifiedGarbage.Impl.Rsa.X86.KeyCheckRt
public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Time
meta import VerifiedGarbage.Proof.Rsa.X86.WordRt.Time
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
meta import VerifiedGarbage.Impl.Rsa.X86.KeyCheckRt
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-! # The taint checks of the key checks at a run-time width -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86
open VG.Impl.Rsa.X86.KeyCheck VG.Impl.Rsa.X86.KeyCheckRt

/-- The bytes of the return address and the arguments. -/
def argSpan (full : Bool) : Nat := 4 * (VG.Impl.Rsa.X86.KeyCheck.scratchArg full + 3)

/-- The arguments, `edi` and `esp`. -/
def τV (full : Bool) : VG.X86.Taint.T := { regs := .ofList [.edi, .esp], flags := false, argLen := argSpan full }

/-- The taint checks of `mulRows` for `o`, `a`, `b`. -/
structure RowsCk (full : Bool) (o a b : Nat) (rows : Option Nat) : Prop where
  c₀ : ∃ hint, (VG.Taint.check sseTaint (τV full) (.seq (.seq (VG.Impl.Rsa.X86.KeyRt.zeroWide (lay full) o)
    (VG.Impl.Rsa.X86.KeyRt.zeroWide (lay full) (o + 1)))
    (.block [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc VG.Impl.Rsa.X86.WordModRt.oJ) .eax])) hint).isSome = true
  c₁ : ∃ hint, (VG.Taint.check sseTaint (τV full) (.block (VG.Proof.Rsa.X86.WordRt.rowHead (lay full) b)) hint).isSome = true
  c₂ : ∃ hint, (VG.Taint.check sseTaint { τV full with regs := .ofList [.edi, .esp, .eax, .ebx] }
    (.seq (.block (VG.Proof.Rsa.X86.WordRt.rowH₂ (lay full) o a)) (VG.Proof.Rsa.X86.WordRt.rowTail (lay full) o a b rows))
    hint).isSome = true

/-- The taint checks of `mulHalf` for `o`, `a`, `b`. -/
structure HalfCk (full : Bool) (o a b : Nat) : Prop where
  c₀ : ∃ hint, (VG.Taint.check sseTaint (τV full) (.seq (.seq (.seq (VG.Impl.Rsa.X86.KeyRt.zeroWide (lay full) o)
    (VG.Impl.Rsa.X86.KeyRt.zeroWide (lay full) (o + 1))) (.block (VG.Impl.Rsa.X86.WordModRt.topZero (lay full) o)))
    (.block [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc VG.Impl.Rsa.X86.WordModRt.oJ) .eax])) hint).isSome = true
  c₁ : ∃ hint, (VG.Taint.check sseTaint (τV full) (.block (VG.Proof.Rsa.X86.WordRt.rowHead (lay full) b)) hint).isSome = true
  c₂ : ∃ hint, (VG.Taint.check sseTaint { τV full with regs := .ofList [.edi, .esp, .eax, .ebx] }
    (.seq (.block (VG.Proof.Rsa.X86.WordRt.rowH₂ (lay full) o a true))
      (VG.Proof.Rsa.X86.WordRt.rowTail (lay full) o a b none true)) hint).isSome = true

/-- The taint checks of `wordMod` for `x`, `r`, `m`. -/
structure ModCk (full : Bool) (x r m : Nat) (top : Option Nat) : Prop where
  c₀ : ∃ hint, (VG.Taint.check sseTaint (τV full) (.seq (.seq (.block (VG.Impl.Rsa.X86.WordModRt.orTop (lay full) (pLenArg full) m))
      (VG.Impl.Rsa.X86.WordModRt.recip (lay full))) (VG.Impl.Rsa.X86.WordModRt.seed (lay full) (pLenArg full) x r top))
    hint).isSome = true
  c₁ : ∃ hint, (VG.Taint.check sseTaint (τV full) (.block (VG.Proof.Rsa.X86.WordRt.digitHead (lay full) x)) hint).isSome = true
  c₂ : ∃ hint, (VG.Taint.check sseTaint { τV full with regs := .ofList [.edi, .esp, .eax, .ebx] }
    (.seq (.block VG.Proof.Rsa.X86.WordRt.digitH₂) (VG.Proof.Rsa.X86.WordRt.digitTail (lay full) (pLenArg full) x r m aT))
    hint).isSome = true


/-- The taint checks of the word steps. -/
structure WCk (full : Bool) : Prop where
  ltDP : ∃ hint, (VG.Taint.check sseTaint (τV full) (VG.Impl.Rsa.X86.Keys.seqs (ltA full aDP aM1)) hint).isSome = true
  ltDQ : ∃ hint, (VG.Taint.check sseTaint (τV full) (VG.Impl.Rsa.X86.Keys.seqs (ltA full aDQ aM2)) hint).isSome = true
  ltQI : ∃ hint, (VG.Taint.check sseTaint (τV full) (VG.Impl.Rsa.X86.Keys.seqs (ltA full aQI aP)) hint).isSome = true
  ltD : ∃ hint, (VG.Taint.check sseTaint (τV full) (VG.Impl.Rsa.X86.Keys.seqs (ltA full aD aN)) hint).isSome = true
  eqOne : ∃ hint, (VG.Taint.check sseTaint (τV full) (VG.Impl.Rsa.X86.Keys.seqs (eqA full aA aOne)) hint).isSome = true
  eqDP : ∃ hint, (VG.Taint.check sseTaint (τV full) (VG.Impl.Rsa.X86.Keys.seqs (eqA full aVR aDP)) hint).isSome = true
  eqDQ : ∃ hint, (VG.Taint.check sseTaint (τV full) (VG.Impl.Rsa.X86.Keys.seqs (eqA full aVR aDQ)) hint).isSome = true
  rDP : RowsCk full aY aDP aE (some 2)
  rDQ : RowsCk full aY aDQ aE (some 2)
  rQI : HalfCk full aY aQ aQI
  mM1 : ModCk full aY aA aM1 (some 2)
  mM2 : ModCk full aY aA aM2 (some 2)
  mP : ModCk full aY aA aP none
  dM1 : ModCk full aD aVR aM1 none
  dM2 : ModCk full aD aVR aM2 none

/-- The bit-by-bit branch. -/
def bitsBranch (full : Bool) : Prog isa :=
  if full then VG.Impl.Rsa.X86.Keys.seqs [products full, dBits full] else products full

/-- The word branch. -/
def wordBranch (full : Bool) : Prog isa :=
  if full then VG.Impl.Rsa.X86.Keys.seqs [wordProducts full, dWords full] else wordProducts full

/-- The taint checks of the pieces of `sized`. -/
structure KcCk (full : Bool) : Prop where
  loads : ∃ hint, (VG.Taint.check sseTaint (τV full) (loads full) hint).isSome = true
  first : ∃ hint, (VG.Taint.check sseTaint (τV full) (.seq (.block (VG.Impl.Rsa.X86.KeyRt.setOne (lay full) aOne))
    (.block (VG.Impl.Rsa.X86.KeyRt.bitOf (lay full) sMask aP))) hint).isSome = true
  rows : RowsCk full aVQ aP aQ none
  eqAcc : ∃ hint, (VG.Taint.check sseTaint (τV full) (.seq (VG.Impl.Rsa.X86.WordModRt.eqWide (lay full) sF aVQ aN)
    (.block acc)) hint).isSome = true
  pre : ∃ hint, (VG.Taint.check sseTaint (τV full) (VG.Impl.Rsa.X86.Keys.seqs
    [VG.Impl.Rsa.X86.KeyRt.copy (lay full) aM1 aP, .block (VG.Impl.Rsa.X86.KeyRt.clrLow (lay full) aM1),
      VG.Impl.Rsa.X86.KeyRt.copy (lay full) aM2 aQ, .block (VG.Impl.Rsa.X86.KeyRt.clrLow (lay full) aM2),
      .block (VG.Impl.Rsa.X86.WordModRt.balanced (lay full) 1 (pLenArg full) (qLenArg full) aN sG)]) hint).isSome = true
  guard : ∃ hint, (VG.Taint.check sseTaint (τV full)
    (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc sG)), .alu .cmp .eax (.imm 0)]) hint).isSome = true
  bits : ∃ hint, (VG.Taint.check sseTaint (τV full) (bitsBranch full) hint).isSome = true
  word : WCk full
  last : ∃ hint, (VG.Taint.check sseTaint (τV full) (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc sMask))]) hint).isSome = true
  bal : ∃ hint, (VG.Taint.check sseTaint (τV full)
    (.block (VG.Impl.Rsa.X86.WordModRt.balanced (lay full) 1 (pLenArg full) (qLenArg full) aN sG)) hint).isSome = true
  half : HalfCk full aVQ aP aQ

theorem kcCkFull : KcCk true := by
  refine ⟨?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩, ?_, ?_, ⟨?_, ?_, ?_⟩⟩
  all_goals exact ⟨_, by taint_decide⟩

theorem kcCkCrt : KcCk false := by
  refine ⟨?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩, ?_, ?_, ⟨?_, ?_, ?_⟩⟩
  all_goals exact ⟨_, by taint_decide⟩

theorem kcCk (full : Bool) : KcCk full := by
  cases full
  · exact kcCkCrt
  · exact kcCkFull

end VG.Proof.Rsa.X86.KeyCheck
