module

public import VerifiedGarbage.Impl.Ed25519.X86.Comb
meta import VerifiedGarbage.Impl.Ed25519.X86.Comb
import VerifiedGarbage.Proof.Ed25519.X86.CombLit
meta import VerifiedGarbage.Proof.Ed25519.X86.CombLit
public import VerifiedGarbage.Proof.Ed25519.X86.PointCTSupport
meta import VerifiedGarbage.Proof.Ed25519.X86.PointCTSupport
import VerifiedGarbage.Proof.Ed25519.X86.Point32.AddSum
meta import VerifiedGarbage.Proof.Ed25519.X86.Point32.AddSum
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.X86.CommonCT
import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
import VerifiedGarbage.Proof.Ed25519.X86.ScalarStep
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.NativeTaint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.NativeHintData
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.X25519.X86.Fold
import VerifiedGarbage.Proof.X25519.X86.Freeze
meta import VerifiedGarbage.Proof.Ed25519.Bytes
meta import VerifiedGarbage.Proof.Ed25519.X86.CommonCT
meta import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarStep
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.X25519.X86.Fold
meta import VerifiedGarbage.Proof.X25519.X86.Freeze

/-! The comb has a public trace: its loops' counters (`esi`) are public, and every address is
the workspace pointer `edi` plus a constant or `8 esi`, or the tables' address plus
`768 esi` and a constant. The tables' address is the word at byte `combTbl` of the workspace,
which the comb never writes, public (`callTaint combTbl`): the digits only reach masks. The
calls of `vg_ed25519_r32_add_affine` and of `_point_add` are analysed by their summaries, and
those of `_double`, after the loop, as part of the comb. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

theorem combMultiply_ct {x : BitVec 32} : RelCT isa
    (fun s t => PointCTCtx x s ∧ PointCTCtx x t ∧ s.wr = t.wr ∧ s.gpr .esp = t.gpr .esp ∧
      wd s.mem x combTbl = wd t.mem x combTbl) combMultiply (fun _ _ => True) := by
  obtain ⟨_, hc⟩ : ∃ h, (taint.check (callTaint combTbl) combMultiply h).isSome = true := by
    native_taint_decide_sum [affSum, addSum]
  apply VG.RelCT.taint (A := taint) (callTaint combTbl) _ hc
  intro s t ⟨hs, ht, hw, hsp, hv⟩
  exact callTaint_agree hs ht hw hsp (by decide) hv

end VG.Proof.Ed25519.X86
