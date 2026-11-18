module

public import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit
public import VerifiedGarbage.Impl.TripleDes.X86.Ecb
public import VerifiedGarbage.Impl.TripleDes.X86.ExpandKey
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit
meta import VerifiedGarbage.Impl.TripleDes.X86.Ecb
meta import VerifiedGarbage.Impl.TripleDes.X86.ExpandKey
meta import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.Impl.TripleDes.X86

def keyTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [384, 512],
    argLen := 20, argBases := [(12, 0), (16, 1)] }
def ecbTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 1024],
    argLen := 20, argBases := [(8, 0), (16, 1)], room := 16 }

/-! The body of the loop of rounds, which the decryption block function runs
three times (two of them in the decryption direction), and so ECB
decryption, through the block function it calls, analysed once for each
direction as summaries: from what is public at the loop (the pointers and
counters, two of them in public slots of the scratch buffer), in the block
function and in the calls from ECB decryption. The encryption block
function is CMAC's block, whose rounds the analysis runs as they are. -/

/-- What is public at the loop of rounds of a block function. -/
def roundTaint : VG.X86.Taint.T :=
  { regs := .ofList [.eax, .esp, .ebp], flags := false, lens := [8, 512], bases := [(.ebp, 1, 0)],
    slots := [(1, 20, 4), (1, 16, 4)], argLen := 16, argBases := [(8, 0), (12, 1)] }

/-- What is public at the loop of rounds of a block function called by an
ECB function. -/
def ecbRoundTaint : VG.X86.Taint.T :=
  { regs := .ofList [.eax, .esp, .ebp], flags := false, lens := [12, 0, 1024],
    bases := [(.esp, 0, 4), (.ebp, 2, 0)],
    slots := [(2, 20, 4), (2, 16, 4), (2, 12, 4), (2, 8, 4), (2, 4, 4), (2, 0, 4), (0, 8, 4), (0, 4, 4),
      (0, 0, 4)],
    wbases := [(0, 8, 2), (2, 0, 2)], argLen := 20, argBases := [(8, 1), (16, 2)], stk := [none, some 12],
    room := 16 }

taint_summary roundEnc : taint roundTaint (.block (roundBody ++ roundAdvance .encrypt))
taint_summary roundDec : taint roundTaint (.block (roundBody ++ roundAdvance .decrypt))
taint_summary ecbRoundEnc : taint ecbRoundTaint (.block (roundBody ++ roundAdvance .encrypt))
taint_summary ecbRoundDec : taint ecbRoundTaint (.block (roundBody ++ roundAdvance .decrypt))

theorem expandKey_constantTime (pre : State → Prop) (pub : State → State → Prop)
    (h : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → VG.X86.Taint.Agree keyTaint s₁ s₂) :
    ConstantTime isa pre pub Key.expandKey :=
  VG.Taint.constantTime (A := taint) keyTaint h (by taint_decide)

theorem ecbEncrypt_constantTime (pre : State → Prop) (pub : State → State → Prop)
    (h : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → VG.X86.Taint.Agree ecbTaint s₁ s₂) :
    ConstantTime isa pre pub Ecb.encrypt :=
  VG.Taint.constantTime (A := taint) ecbTaint h (by taint_decide)

theorem ecbDecrypt_constantTime (pre : State → Prop) (pub : State → State → Prop)
    (h : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → VG.X86.Taint.Agree ecbTaint s₁ s₂) :
    ConstantTime isa pre pub Ecb.decrypt :=
  let ⟨_, hc⟩ := (by taint_decide_sum [ecbRoundEnc, ecbRoundDec] : ∃ h, (taint.check ecbTaint Ecb.decrypt h).isSome = true)
  VG.Taint.constantTime (A := taint) ecbTaint h hc

end VG.Proof.TripleDes.X86
