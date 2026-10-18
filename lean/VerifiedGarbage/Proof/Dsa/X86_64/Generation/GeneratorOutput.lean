module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorStages
public import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Omega

/-! # Accept precisely nontrivial generator powers, preserving their bytes -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem generatorOutputRange_ok {p : GeneratorPlan} {W : Nat → BitVec 64} {s : State}
    (h : GeneratorMemory p W s)
    (hg : Spec.Rsa.bytesAt s.mem (off p.B g) p.len = Spec.Dsa.encodeBE p.len p.value) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorRangeFromFrame p.len true) s fun t =>
      t.gpr .rax = mask (decide (1 < p.value)) ∧ GeneratorMemory p W t ∧
      Spec.Rsa.bytesAt t.mem (off p.B g) p.len = Spec.Dsa.encodeBE p.len p.value ∧
      Frame p.changed s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  have hn : p.len < 2 ^ 64 := by rcases p.width with hh | hh | hh <;> omega
  have hlt : p.value < Spec.Dsa.decodeBE p.pb := VG.Proof.Dsa.powMod_lt _ _ (by have := p.pPositive; omega)
  have hfit : p.value < 256 ^ p.len := Nat.lt_trans hlt (p.pLength ▸ VG.Proof.Dsa.decodeBE_lt p.pb)
  have hdecode := VG.Proof.Dsa.decodeBE_encodeBE hfit
  have src : Src s p.A p.Z (off p.B g) (Spec.Dsa.encodeBE p.len p.value) := by
    have hlen := VG.Proof.Dsa.encodeBE_length p.len p.value
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => p.gArithmeticOutside i (hlen ▸ hi)⟩
    · obtain ⟨r, hr, hc⟩ := h.gWrite i (hlen ▸ hi)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · have eq := congrArg (fun bs : List Byte => bs[i]?) hg
      simpa only [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range,
        show i < p.len from hlen ▸ hi, ↓reduceIte, Option.map_some, List.getElem?_eq_getElem hi,
        Option.some.injEq] using eq
  obtain ⟨V, R⟩ := h.rep
  refine WP.mono (generatorFromFrame_ok (xb := Spec.Dsa.encodeBE p.len p.value) true h.layout R h.arithmetic
    (by rw [h.base]; exact p.arithmeticBase) p.width p.workspaceRoom p.frameHeaders p.frameOutside
    (p.frameSeparate _ (by simp)) (p.hashSeparate _ (by simp))
    (by simpa only [h.base] using h.pArithmetic) (by simpa only [↓reduceIte, h.base] using src)
    p.pLength (VG.Proof.Dsa.encodeBE_length p.len p.value) (fun he => Bool.noConfusion he)
    (fun _ => by change Spec.Dsa.decodeBE _ < _; rw [hdecode]; exact hlt))
    fun t ⟨hr, Lt, Rt, _, ft, kt⟩ => ?_
  have frame : Frame p.changed s.mem t.mem := ft.mono (by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [GeneratorPlan.changed])
  refine ⟨?_, h.frame Lt ⟨V, Rt⟩ h.base h.input frame kt.2.1 kt.2.2, ?_, frame, kt⟩
  · change t.gpr .rax = mask (decide (1 < Spec.Dsa.decodeBE _)) at hr
    rwa [hdecode] at hr
  · rw [VG.Proof.Dsa.Generation.frame_bytesAt ft (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl; exact p.gArithmeticSeparate) (Nat.le_of_lt hn), hg]

end VG.Proof.Dsa.X86_64.Generation
