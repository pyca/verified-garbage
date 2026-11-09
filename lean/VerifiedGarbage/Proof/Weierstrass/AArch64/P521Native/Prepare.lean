module

-- separate module: the original public-buffer bridge is independent of the subsequent table and scalar-multiplication phases

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.PrepareCore
import VerifiedGarbage.Proof.Framework.Block

/-! Full native preparation from the public argument buffers. No valid-peer or
nonzero-coordinate assumption is introduced by its machine-level interface. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native (config)
open VG.Proof.Ed25519.AArch64 (Keeps)

/-- Continuation form exposes the validated loaded-stage witness without
strengthening the incoming public-buffer permission/disjointness requirements. -/
theorem prepare_api_ok (hc : BaseCfgOk config) {s : State} (pre : PrepareApiPre s)
    {Q : State → Prop}
    (next : ∀ args loaded, SetupPre config args →
      Keeps [.x2,.x3,.x4,.x6,.x26] s args →
      args.gpr .x26=s.sp → args.gpr .x4=s.gpr .x3 → args.gpr .x3=s.gpr .x1 →
      St₁ config none args (s.gpr .x3) loaded →
      loaded.gpr .x6=s.gpr .x2 → args.gpr .x2=s.gpr .x2+BitVec.ofNat 64 1 →
      WP isa prepareCore loaded Q) :
    WP isa VG.Impl.Weierstrass.AArch64.P521Native.validateAndPrepare s Q := by
  apply prepare_stages_wp
  change WP isa (.seq (.block _) (.seq prepareLoadBits prepareCore)) s Q
  refine WP.seq (WP.mono (prepare_api_args_ok pre)
    fun args ⟨setup,table,workspace,peer,secretArg,peerPlus,keep⟩ => ?_)
  refine WP.seq (WP.mono (prepare_load_bits_ok hc setup) fun loaded stage => ?_)
  have stage' : St₁ config none args (s.gpr .x3) loaded := by rwa [workspace] at stage
  have peerLoaded : loaded.gpr .x6=s.gpr .x2 := (stage.gpr .x6 (by decide)).trans peer
  exact next args loaded setup keep table workspace secretArg stage' peerLoaded peerPlus

/-- The loaded peer region is still permitted and separate from the workspace;
these are consequences of the original buffers, not new phase preconditions. -/
theorem prepare_api_peer {s args loaded : State} (pre : PrepareApiPre s)
    (keep : Keeps [.x2,.x3,.x4,.x6,.x26] s args)
    (stage : St₁ config none args (s.gpr .x3) loaded) :
    (⟨s.gpr .x2,133⟩ : Region)∈loaded.rd++loaded.wr ∧
      Region.Disjoint ⟨s.gpr .x2,133⟩ ⟨s.gpr .x3,8192⟩ := by
  refine ⟨?_,pre.peer_apart⟩
  rw [stage.rd,stage.wr,keep.rd,keep.wr]
  exact pre.peer

/-- Full preparation provides the machine-ready state and selected point for
both valid and invalid peers, directly from the original API buffers. -/
theorem prepare_api_ready (hc : BaseCfgOk config) {s : State} (pre : PrepareApiPre s) :
    WP isa VG.Impl.Weierstrass.AArch64.P521Native.validateAndPrepare s fun t =>
      ∃ args loaded,
        Keeps [.x2,.x3,.x4,.x6,.x26] s args ∧
        args.gpr .x26=s.sp ∧ args.gpr .x4=s.gpr .x3 ∧ args.gpr .x3=s.gpr .x1 ∧
        St₁ config none args (s.gpr .x3) loaded ∧
        PrepareCorePost args loaded (s.gpr .x3) (s.gpr .x2) t ∧ args.gpr .x2=s.gpr .x2+BitVec.ofNat 64 1 := by
  refine prepare_api_ok hc pre fun args loaded _ keep table workspace secretArg stage peer peerPlus => ?_
  have permissions := prepare_api_peer pre keep stage
  exact WP.mono (prepare_core_ok hc stage peer permissions.1 permissions.2)
    fun t ready => ⟨args,loaded,keep,table,workspace,secretArg,stage,ready,peerPlus⟩

end VG.Proof.Weierstrass.AArch64.P521Native
