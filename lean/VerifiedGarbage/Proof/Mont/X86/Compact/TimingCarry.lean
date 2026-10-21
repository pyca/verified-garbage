module

import VerifiedGarbage.Proof.Mont.X86.Compact.TimingValue
import VerifiedGarbage.Proof.Mont.X86.Compact.CarryFrame
import VerifiedGarbage.Proof.Mont.X86.Compact.TimingKernels
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingLift

/-! # Carry propagation and restoring the product pointer are constant time -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Dsa.X86

theorem carry_relCT {g : Geometry} (v : g.Valid) (y : Nat)
    (low : g.S ≤ y) (high : y + 8 ≤ g.S + 8 * g.N + 28) :
    RelCT isa (fun s t => Pair g [.ebp, .edi] s t ∧ PtrAt s g.W .ebp y ∧ PtrAt t g.W .ebp y)
      (.block Rt.carryWords) (Pair g [.ebp, .edi]) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, A⟩ := carryWords_relCT _ _ _ _ _ _ H.1.2.2 E G
  have fit := v.lay.scr
  obtain ⟨Ou, Ku⟩ := wp_result (carryWords_frame H.1.1.ws H.2.1 (by omega)) E
  obtain ⟨Oz, Kz⟩ := wp_result (carryWords_frame H.1.2.1.ws H.2.2 (by omega)) G
  have writes {m m' : Mem} (O : Outside g.W y 8 m m') : Outs g.W g.writes m m' :=
    Outs.widen (Outs.of_outside O (List.mem_singleton_self _)) fun x hx r hr => by
      have outside := hx _ (List.mem_cons_self ..)
      simp only [List.mem_singleton] at hr
      subst hr
      dsimp only at *
      omega
  exact ⟨trace, H.1.1.keep v Ku (by decide) (writes Ou) (timing_wf_regs A.wf₁),
    H.1.2.1.keep v Kz (by decide) (writes Oz) (timing_wf_regs A.wf₂), A⟩

theorem restorePointer_relCT {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g [.eax, .ebp, .edi]) (.block [.alu .sub .ebp (.reg .eax)]) (Pair g [.ebp, .edi]) := by
  refine lift_readonly v (checkedProgramChange (hint := .block [])
    (τ' := timingTaint [.eax, .ebp, .edi] true) rfl rfl) ?_
  intro s
  refine wp_subS rfl fun t T _ => WP.block_nil ?_
  exact ⟨T.mem, T.keeps.mono (by decide)⟩

theorem carryUp_relCT {g : Geometry} (v : g.Valid) (y : Nat)
    (low : g.S ≤ y) (high : y + 8 ≤ g.S + 8 * g.N + 28) :
    RelCT isa (fun s t => Pair g [.ebp, .edi] s t ∧ PtrAt s g.W .ebp y ∧ PtrAt t g.W .ebp y)
      (.block Compact.carryUp) (Pair g [.ebp, .edi]) := by
  unfold Compact.carryUp
  rw [List.append_assoc]
  refine RelCT.block_append (RelCT.seq (carry_relCT v y low high)
    (RelCT.block_append (RelCT.seq ?_ (restorePointer_relCT v))))
  exact length_relCT v .eax .edx 0 byteLength_relCT (by decide) (by decide)

end VG.Proof.Mont.X86.Compact
