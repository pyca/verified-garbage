module

import VerifiedGarbage.Proof.Mont.X86.Compact.TimingValue
import VerifiedGarbage.Proof.Mont.X86.Compact.Load
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingLift

/-! # Loading a secret multiplier uses a public candidate-word address -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Dsa.X86

theorem loadA_trace {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g [.ebp, .edi]) (.block Compact.loadA)
      (VG.X86.Taint.Agree (timingTaint [.ecx, .ebp, .edi])) := by
  unfold Compact.loadA
  refine RelCT.block_append (RelCT.seq
    (operandPointer_relCT v .ecx .edx 3 ((g.W.toNat + g.a) % 2 ^ 32) leftPtr_relCT
      (by decide) (by decide) (by decide) (by
        intro s C
        have := C.metadata.aIndex
        have := v.lay.header
        have := v.lay.scr
        omega) (fun _ C => C.metadata.left) (by decide) (by decide)) ?_)
  exact (checkedProgramChange (hint := .block []) (τ' := timingTaint [.ecx, .ebp, .edi] true) rfl rfl).mono
    (fun _ _ H => H.2.2) (fun _ _ H => H)

theorem loadA_relCT {g : Geometry} (v : g.Valid) (i : Nat) (index : i < g.N) :
    RelCT isa (fun s t => Pair g [.ebp, .edi] s t ∧ PtrAt s g.W .edi g.S ∧ PtrAt t g.W .edi g.S ∧
        PtrAt s g.W .ebp (g.S + Compact.accOff + 4 * i) ∧
        PtrAt t g.W .ebp (g.S + Compact.accOff + 4 * i))
      (.block Compact.loadA) (Pair g [.ebp, .edi]) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, A⟩ := loadA_trace v _ _ _ _ _ _ H.1 E G
  have fit := v.lay.scr
  have aFit := v.lay.a_le
  have header := v.lay.header
  have acc : Compact.accOff = 24 := rfl
  have mult : Rt.multOff = 20 := rfl
  obtain ⟨Mu, Ku⟩ := wp_result (loadA_ok H.1.1.ws H.1.1.args v.base
    (by have := H.1.1.metadata.aIndex; omega) H.1.1.metadata.left_word H.2.1 H.2.2.2.1
    (by omega) (by omega)) E
  obtain ⟨Mz, Kz⟩ := wp_result (loadA_ok H.1.2.1.ws H.1.2.1.args v.base
    (by have := H.1.2.1.metadata.aIndex; omega) H.1.2.1.metadata.left_word H.2.2.1 H.2.2.2.2
    (by omega) (by omega)) G
  have writes {m m' : Mem} {value : BitVec 32} (M : m' = m.writeW (off g.W (g.S + Rt.multOff)) value) :
      Outs g.W g.writes m m' := by
    rw [M]
    have O := writeW32_outside m g.W (d := g.S + Rt.multOff) value (by have := H.1.1.ws.nowrap; omega)
    exact Outs.widen (Outs.of_outside O (List.mem_singleton_self _)) fun x hx r hr => by
      have outside := hx _ (List.mem_cons_self ..)
      simp only [List.mem_singleton] at hr
      subst hr
      dsimp only at *
      omega
  refine ⟨trace, H.1.1.keep v Ku (by decide) (writes Mu) (timing_wf_regs A.wf₁),
    H.1.2.1.keep v Kz (by decide) (writes Mz) (timing_wf_regs A.wf₂), ?_⟩
  exact timing_add_regs (timing_forget A) fun r hr => by
    rw [Ku.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> decide),
      Kz.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> decide)]
    exact timing_regs H.1.2.2 hr

theorem loadA_positioned_relCT {g : Geometry} (v : g.Valid) (i : Nat) (index : i < g.N) :
    RelCT isa (WindowPair g (g.S + Compact.accOff + 4 * i)) (.block Compact.loadA)
      (WindowPair g (g.S + Compact.accOff + 4 * i)) := by
  refine preserve_position (loadA_relCT v i index) (rs := [.eax, .ecx, .edx]) ?_ (by decide) (by decide)
  intro s C edi ebp
  have fit := v.lay.scr
  have aFit := v.lay.a_le
  have header := v.lay.header
  have acc : Compact.accOff = 24 := rfl
  refine WP.mono (loadA_ok C.ws C.args v.base (by have := C.metadata.aIndex; omega)
    C.metadata.left_word edi ebp (by omega) (by omega)) ?_
  exact fun _ H => H.2

end VG.Proof.Mont.X86.Compact
