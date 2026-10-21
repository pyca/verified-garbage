module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.RequestBlocks
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Select
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Framework.Block

/-! The native refill request is exactly the shared bounded doubling policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Controller lowWord)

theorem request_ok {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterSearch.request s fun t =>
      t.mem = requestMem s.mem p.control (Spec.Ffdh.parameterRequest p.c.bits (p.c.bytes.length - used)) ∧
        Rest [.r9, .r10, .r11] s t := by
  let available := p.c.bytes.length - used
  let width := p.c.length
  let cap := Spec.Ffdh.parameterEntropy p.c.bits
  let peak := max available (256 * width)
  have widthBound := p.width_bounds
  have capBound := p.entropy_bound
  have tapeBound : p.c.bytes.length ≤ Spec.Ffdh.parameterEntropy p.c.bits := p.tapeBound
  have doubleFits : 2 * peak < 2 ^ 32 := p.policy.double_fits (by omega)
  have availableFits : available < 2 ^ 32 := by have := p.c.tapeCount; omega
  have peakFits : peak < 2 ^ 32 := by omega
  have widthFits : 256 * width < 2 ^ 32 := by dsimp only [width]; omega
  have control := h.buffers.controller
  have tape := h.saved 10 (by simp [searchSlots])
  have length := h.saved 1 (by simp [searchSlots])
  have capacity := h.saved 2 (by simp [searchSlots])
  simp only [searchValues] at tape length capacity
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.request
  rw [WP.seq_iff]
  refine WP.mono (requestHead_ok s control tape length) ?_
  rintro a ⟨⟨leftA, rightA, memA⟩, restA⟩
  refine WP.seq (WP.mono (selectNat_ok true a availableFits widthFits leftA rightA)
    fun c ⟨⟨peakC, memC⟩, restC⟩ => ?_)
  have restSC : Rest [.r9, .r10, .r11] s c :=
    (restA.mono (by simp)).trans (restC.mono (by simp))
  have memSC : c.mem = s.mem := memC.trans memA
  have controlC : Controller p.control c :=
    ⟨control.space.congr restSC.wr, (restSC.gpr .r4 (by simp)).trans control.ptr⟩
  have capC : lowWord c.mem p.control 2 = BitVec.ofNat 32 cap := by rw [memSC]; exact capacity
  rw [WP.seq_iff]
  refine WP.mono (requestDouble_ok c controlC peakC capC) ?_
  rintro d ⟨⟨leftD, rightD, memD⟩, restD⟩
  refine WP.seq (WP.mono (selectNat_ok false d doubleFits p.entropy_fits leftD rightD)
    fun f ⟨⟨requestF, memF⟩, restF⟩ => ?_)
  have restSF : Rest [.r9, .r10, .r11] s f :=
    (restSC.trans (restD.mono (by simp))).trans (restF.mono (by simp))
  have memSF : f.mem = s.mem := memF.trans (memD.trans memSC)
  have controlF : Controller p.control f :=
    ⟨control.space.congr restSF.wr, (restSF.gpr .r4 (by simp)).trans control.ptr⟩
  refine WP.mono (requestStore_ok f controlF requestF) ?_
  rintro t ⟨memT, restT⟩
  exact ⟨by rw [memT, memSF]; rfl, restSF.trans (restT.mono (by simp))⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
