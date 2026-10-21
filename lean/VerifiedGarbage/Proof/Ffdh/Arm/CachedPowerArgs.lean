module

import VerifiedGarbage.Proof.Ffdh.Arm.CachedPowerLoad
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedPowerMetadata
import VerifiedGarbage.Proof.Ffdh.Arm.CachedPowerSave
import VerifiedGarbage.Proof.Bignum.Arm.ExpControls
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedPower
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedPower
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpState

/-! Prepare the comb evaluator without rebuilding its public arithmetic context. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CachedPower
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem args_ok (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat}
    (h : SampleContext p l slots s) (context : CachedGenerationContext p s)
    (ready : ArithmeticReady p.base p.len p.w s) (h52 : 52∈slots) :
    WP isa VG.Impl.Ffdh.Arm.CachedPower.args s fun t =>
      ArithmeticReady p.base p.len p.w t ∧ CombExp.Controls p.base l.start (table p) l.width (bits p) t ∧
      (∀q<8,numAt t.mem (State.addr p.base) p.w q=numAt s.mem (State.addr p.base) p.w q) ∧
      Frame [⟨State.addr p.base,8*p.len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.CachedPower.args,WP.seq_iff]
  refine WP.mono (load_ok s h h52) ?_
  rintro u ⟨⟨source,count,pointer,memU⟩,restU⟩
  have ru : Rest roundClobbers s u := restU.mono (by simp [roundClobbers])
  have frameU : Frame [⟨State.addr p.base,8*p.len⟩] s.mem u.mem := by rw [memU]; exact Frame.refl _ _
  have readyU := ready.of_mem memU restU ((restU.gpr .r0 (by simp)).trans ready.ptr)
  have contextU := context.after (frameU.mono (by simp [keyCallWrites,keyWrites])) ru
  rw [WP.seq_iff]
  refine WP.mono (expControls_ok u readyU) ?_
  rintro v ⟨readyV,sourceV,countV,arraysV,frameV,restV⟩
  have rv : Rest roundClobbers u v := restV.mono (by simp)
  have contextV := contextU.after (frameV.mono (by simp [keyCallWrites,keyWrites])) rv
  rw [WP.seq_iff]
  refine WP.mono (metadata_ok v readyV contextV ((restV.gpr .r4 (by simp)).trans pointer)) ?_
  rintro z ⟨bitsZ,rowsZ,tableZ,memZ,restZ⟩
  have rz : Rest roundClobbers v z := restZ.mono (by simp [roundClobbers])
  have frameZ : Frame [⟨State.addr p.base,8*p.len⟩] v.mem z.mem := by rw [memZ]; exact Frame.refl _ _
  have readyZ := readyV.of_mem memZ restZ ((restZ.gpr .r0 (by simp)).trans readyV.ptr)
  have sourceZ : z.mem.readW (off (State.addr p.base) 128) 32=l.start := by rw [memZ,sourceV,source]
  have countZ : z.mem.readW (off (State.addr p.base) 132) 32=BitVec.ofNat 32 l.width := by rw [memZ,countV,count]
  refine WP.mono (save_ok z readyZ sourceZ countZ bitsZ rowsZ tableZ) ?_
  rintro t ⟨readyT,controlsT,arraysT,frameT,restT⟩
  exact ⟨readyT,controlsT,(by intro q hq; rw [arraysT q hq,memZ,arraysV q hq,memU]),
    frameU.trans (frameV.trans (frameZ.trans frameT)),ru.trans (rv.trans (rz.trans (restT.mono (by simp))))⟩

end VG.Proof.Ffdh.Arm.CachedPower
