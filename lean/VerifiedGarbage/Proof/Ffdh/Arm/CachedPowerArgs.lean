module

public import VerifiedGarbage.Proof.Ffdh.Arm.CachedPowerMetadata
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedPower
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpState

import VerifiedGarbage.Proof.Ffdh.Arm.CachedPowerLoad
import VerifiedGarbage.Proof.Bignum.Arm.ExpControls
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.HeaderStore
import VerifiedGarbage.Proof.Framework.Arm.Exec
/-! Prepare the comb evaluator without rebuilding its public arithmetic context. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/CachedPowerSave.lean`, which only this module imported.
section

/-! Save public context metadata without disturbing the arithmetic arrays. -/

section
namespace VG.Proof.Ffdh.Arm.CachedPower
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt)
open VG.Proof.X25519.Arm (Rest wp_str)

theorem save_ok (s : State) {base source table : BitVec 32} {len w bytes N : Nat}
    (h : ArithmeticReady base len w s)
    (sourcePtr : s.mem.readW (off (State.addr base) 128) 32=source)
    (byteCount : s.mem.readW (off (State.addr base) 132) 32=BitVec.ofNat 32 bytes)
    (bits : s.gpr .r1=BitVec.ofNat 32 N)
    (rows : s.gpr .r2=BitVec.ofNat 32 (Spec.Rsa.FixedBaseComb.rows N))
    (tablePtr : s.gpr .r4=table) :
    WP isa (.block VG.Impl.Ffdh.Arm.CachedPower.save) s fun t =>
      ArithmeticReady base len w t ∧ CombExp.Controls base source table bytes N t ∧
      (∀q<8,numAt t.mem (State.addr base) w q=numAt s.mem (State.addr base) w q) ∧
      Frame [⟨State.addr base,8*len⟩] s.mem t.mem ∧ Rest [] s t := by
  have size : 256≤8*len := by
    have fits := h.width ▸ h.layout.2.2.1
    simp only [arrAt,Proof.Rsa.Mont.hdrBytes] at fits
    omega
  have addr (d : Nat) (hd : d≤252) : State.addr (s.gpr .r0+BitVec.ofNat 32 d)=off (State.addr base) d := by
    rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega)
  unfold VG.Impl.Ffdh.Arm.CachedPower.save
  refine wp_str (a:=off (State.addr base) 136) (by decide) (addr 136 (by decide))
    (h.workspace.write (by omega)) fun a one => ?_
  have restA : Rest [] s a := one.rest []
  obtain ⟨readyA,frameA,arraysA⟩ := h.after_header (d:=136) (by decide) (by decide) one.mem restA
    ((restA.gpr .r0 (by simp)).trans h.ptr)
  refine wp_str (a:=off (State.addr base) 204) (by decide)
    (by rw [restA.gpr .r0 (by simp)]; exact addr 204 (by decide))
    (by rw [restA.wr]; exact h.workspace.write (by omega)) fun b two => ?_
  have restB : Rest [] a b := two.rest []
  obtain ⟨readyB,frameB,arraysB⟩ := readyA.after_header (d:=204) (by decide) (by decide) two.mem restB
    ((restB.gpr .r0 (by simp)).trans readyA.ptr)
  have restAB := restA.trans restB
  refine wp_str (a:=off (State.addr base) 232) (by decide)
    (by rw [restAB.gpr .r0 (by simp)]; exact addr 232 (by decide))
    (by rw [restAB.wr]; exact h.workspace.write (by omega)) fun t three => WP.block_nil ?_
  have restT : Rest [] b t := three.rest []
  obtain ⟨readyT,frameT,arraysT⟩ := readyB.after_header (d:=232) (by decide) (by decide) three.mem restT
    ((restT.gpr .r0 (by simp)).trans readyB.ptr)
  have outsideA := writeW32_outside s.mem (State.addr base) (d:=136) (s.gpr .r1) (by decide)
  have outsideB := writeW32_outside a.mem (State.addr base) (d:=204) (a.gpr .r2) (by decide)
  have outsideT := writeW32_outside b.mem (State.addr base) (d:=232) (b.gpr .r4) (by decide)
  rw [←one.mem] at outsideA
  rw [←two.mem] at outsideB
  rw [←three.mem] at outsideT
  have early (d : Nat) (hd : d+4≤136) :
      t.mem.readW (off (State.addr base) d) 32=s.mem.readW (off (State.addr base) d) 32 := by
    rw [outside_read32 outsideT (by omega) (by omega),outside_read32 outsideB (by omega) (by omega),
      outside_read32 outsideA (by omega) (by omega)]
  refine ⟨readyT,⟨(early 128 (by decide)).trans sourcePtr,(early 132 (by decide)).trans byteCount,?_,?_,?_⟩,
    fun q hq=>(arraysT q hq).trans ((arraysB q hq).trans (arraysA q hq)),
    frameA.trans (frameB.trans frameT),restAB.trans restT⟩
  · rw [outside_read32 outsideT (d:=136) (by decide) (by decide),
      outside_read32 outsideB (d:=136) (by decide) (by decide),one.mem,Mem.readW_writeW_self32,bits]
  · rw [outside_read32 outsideT (d:=204) (by decide) (by decide),two.mem,Mem.readW_writeW_self32,
      restA.gpr .r2 (by simp),rows]
  · rw [three.mem,Mem.readW_writeW_self32,restAB.gpr .r4 (by simp),tablePtr]

end VG.Proof.Ffdh.Arm.CachedPower
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CachedPower
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
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
