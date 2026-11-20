module

public import VerifiedGarbage.Proof.ChaCha20.AArch64.XorVariant
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.XorVariant
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Xor
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Xor
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Lit
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Lit
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Backends
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Backends
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Counter
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Rounds
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Scalar
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Tail
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Check
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Last
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.LoopRounds
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Save
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Tail
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon.Lanes
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Feed
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Rotate
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Transpose
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.CachedAdd
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Counter
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Rounds
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Scalar
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Tail
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Check
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Last
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.LoopRounds
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Save
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Tail
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon.Lanes
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Feed
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Rotate
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Transpose
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.CachedAdd
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.XorImpl

open VG VG.AArch64

/-- A backend's `sealTaint`. -/
def SealTaint (callee : Impl.ChaCha20.AArch64.XorCallee) (stitched : Bool) : Prop :=
  ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7])
    (Impl.ChaCha20Poly1305.AArch64.sealMainCode callee stitched) h).isSome = true

/-- A backend's `openTaint`. -/
def OpenTaint (callee : Impl.ChaCha20.AArch64.XorCallee) (stitched : Bool) : Prop :=
  ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x28])
    (Impl.ChaCha20Poly1305.AArch64.openMainCode callee stitched) h).isSome = true

/-! ChaCha20-Poly1305's `seal` with each backend is one kernel evaluation (`taint_decide_all`),
and so is its `open`: the code around the backend is the same instructions for each, and the
kernel finds again what it analysed of it from the same taint. -/

theorem sealTaints : SealTaint .scalar false ∧ SealTaint .neon true ∧ SealTaint .sve2 true := by
  unfold SealTaint
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

theorem openTaints : OpenTaint .scalar false ∧ OpenTaint .neon true ∧ OpenTaint .sve2 true := by
  unfold OpenTaint
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  taint_decide_all

/-- Scalar stream, also used for the short tail of the eight-block backend. -/
def scalar : XorImpl where
  callee := .scalar
  features := []
  scrub := by lit_decide
  sealSide := by lit_decide
  openSide := by lit_decide
  openToSide := by lit_decide
  ok := Xor.xor_correct BlockImpl.scalar
  ct := Xor.xor_ct BlockImpl.scalar
  noFrames := BlockImpl.scalar.xorNoFrames
  stitched := false
  sealTaint := sealTaints.1
  openTaint := openTaints.1

/-- Eight ChaCha20 blocks interleaved across AdvSIMD and integer registers. -/
def neon : XorImpl where
  callee := .neon
  features := []
  scrub := by lit_decide
  sealSide := by lit_decide
  openSide := by lit_decide
  openToSide := by lit_decide
  ok := Mixed8.xor_correct
  ct := Mixed8.xor_ct
  noFrames := Mixed8.xor_noFrames
  stitched := true
  sealTaint := sealTaints.2.1
  openTaint := openTaints.2.1

/-- The eight-block kernel with SVE2: each AdvSIMD XOR and rotation of the
vector blocks is one XAR. -/
def sve2 : XorImpl where
  callee := .sve2
  features := ["sve2"]
  scrub := by lit_decide
  sealSide := by lit_decide
  openSide := by lit_decide
  openToSide := by lit_decide
  ok := Mixed8.xor_correct
  ct := Mixed8.xor_ct
  noFrames := Mixed8.xor_noFrames
  stitched := true
  sealTaint := sealTaints.2.2
  openTaint := openTaints.2.2

end VG.Proof.ChaCha20.AArch64.XorImpl
