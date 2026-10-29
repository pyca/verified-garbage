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
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.SaveGP
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
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.SaveGP
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

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.XorImpl

open VG VG.AArch64

/-- Scalar stream, also used for the short tail of the eight-block backend. -/
def scalar : XorImpl where
  callee := .scalar
  features := []
  notes := ["Calls `vg_chacha20_block` for each 64 bytes."]
  ok := Xor.xor_correct BlockImpl.scalar
  ct := Xor.xor_ct BlockImpl.scalar
  noFrames := BlockImpl.scalar.xorNoFrames
  stitched := false
  sealTaint := by exact ⟨_, by taint_decide⟩
  openTaint := by exact ⟨_, by taint_decide⟩

/-- Eight ChaCha20 blocks interleaved across AdvSIMD and integer registers. -/
def neon : XorImpl where
  callee := .neon
  features := []
  notes := ["Interleaves six NEON blocks with two integer blocks, processing 512 bytes at a time."]
  ok := Mixed8.xor_correct
  ct := Mixed8.xor_ct
  noFrames := Mixed8.xor_noFrames
  stitched := true
  sealTaint := by exact ⟨_, by taint_decide⟩
  openTaint := by exact ⟨_, by taint_decide⟩

/-- The eight-block kernel with SVE2: each AdvSIMD XOR and rotation of the
vector blocks is one XAR. -/
def sve2 : XorImpl where
  callee := .sve2
  features := ["sve2"]
  notes := ["Interleaves six NEON blocks with two integer blocks, processing 512 bytes at a time; " ++
    "each XOR and rotation of the NEON blocks is one SVE2 XAR."]
  ok := Mixed8.xor_correct
  ct := Mixed8.xor_ct
  noFrames := Mixed8.xor_noFrames
  stitched := true
  sealTaint := by exact ⟨_, by taint_decide⟩
  openTaint := by exact ⟨_, by taint_decide⟩

end VG.Proof.ChaCha20.AArch64.XorImpl
