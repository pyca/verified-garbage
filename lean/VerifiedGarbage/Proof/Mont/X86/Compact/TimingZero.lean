module

public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingValue
import VerifiedGarbage.Proof.Mont.X86.Compact.TimingKernels
import VerifiedGarbage.Proof.Mont.X86.Compact.Zero
public import VerifiedGarbage.Proof.Mont.X86.Rt.Zero
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Zeroing a compact product leaks only public pointers and width -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Dsa.X86

theorem accPointer_relCT {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g [.edi]) (.block Compact.accPtr) (Pair g [.ebp, .edi]) := by
  refine lift_readonly v (checkedProgramChange (hint := .block [])
    (τ' := timingTaint [.edi, .ebp] true) rfl rfl) ?_
  intro s
  unfold Compact.accPtr
  refine wp_movS rfl fun a A _ => wp_addS rfl fun t B _ => WP.block_nil ?_
  exact ⟨B.mem.trans A.mem, (A.keeps.mono (by decide)).trans (B.keeps.mono (by decide))⟩

theorem zeroCounter_relCT {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g [.esi, .ebp, .edi])
      (.block [.alu .add .esi (.imm 4), .mov .eax (.imm 0)]) (Pair g [.esi, .ebp, .edi]) := by
  refine lift_readonly v (checkedProgramChange (hint := .block [])
    (τ' := timingTaint [.esi, .ebp, .edi, .eax] true) rfl rfl) ?_
  intro s
  refine wp_addS rfl fun a A _ => wp_movS rfl fun t B _ => WP.block_nil ?_
  exact ⟨B.mem.trans A.mem, (A.keeps.mono (by decide)).trans (B.keeps.mono (by decide))⟩

theorem zeroLoopPointer_relCT : RelCT isa
    (VG.X86.Taint.Agree (timingTaint [.esi, .ebp, .edi]))
    (.loop (.block zeroBody) .ne) (VG.X86.Taint.Agree (timingTaint [.esi, .ebp, .edi])) :=
  checkedProgramChange (τ' := timingTaint [.esi, .ebp, .edi] true)
    (hint := VG.Taint.hintOf taint (timingTaint [.esi, .ebp, .edi]) (.loop (.block zeroBody) .ne)) rfl rfl

theorem zero_trace {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g [.edi]) Compact.zeroAcc
      (VG.X86.Taint.Agree (timingTaint [.esi, .ebp, .edi])) := by
  unfold Compact.zeroAcc
  simp only [List.append_assoc]
  refine RelCT.seq (RelCT.block_append (RelCT.seq (accPointer_relCT v)
    (RelCT.block_append (RelCT.seq (length_relCT v .esi .eax 1 zeroLength_relCT
      (by decide) (by decide)) (zeroCounter_relCT v))))) ?_
  exact zeroLoopPointer_relCT.mono (fun _ _ H => H.2.2) (fun _ _ H => H)

theorem zero_relCT {g : Geometry} (v : g.Valid) :
    RelCT isa (fun s t => Pair g [.edi] s t ∧ PtrAt s g.W .edi g.S ∧ PtrAt t g.W .edi g.S)
      Compact.zeroAcc (fun s t => Pair g [.edi] s t ∧ PtrAt s g.W .edi g.S ∧ PtrAt t g.W .edi g.S) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, A⟩ := zero_trace v _ _ _ _ _ _ H.1 E G
  have acc : Compact.accOff = 24 := rfl
  have fit := v.lay.scr
  obtain ⟨_, Ou, Ku⟩ := wp_result (zero_ok (N := g.N) H.1.1.ws H.1.1.args v.base
    H.1.1.metadata.width (by have := v.lay.header; omega) (by omega) H.2.1) E
  obtain ⟨_, Oz, Kz⟩ := wp_result (zero_ok (N := g.N) H.1.2.1.ws H.1.2.1.args v.base
    H.1.2.1.metadata.width (by have := v.lay.header; omega) (by omega) H.2.2) G
  have Ou' : Outs g.W g.writes s.mem u.mem := Outs.widen (Outs.of_outside Ou (List.mem_singleton_self _))
    fun x hx r hr => by
      have outside := hx _ (List.mem_cons_self ..)
      simp only [List.mem_singleton] at hr
      subst hr
      dsimp only at *
      omega
  have Oz' : Outs g.W g.writes t.mem z.mem := Outs.widen (Outs.of_outside Oz (List.mem_singleton_self _))
    fun x hx r hr => by
      have outside := hx _ (List.mem_cons_self ..)
      simp only [List.mem_singleton] at hr
      subst hr
      dsimp only at *
      omega
  refine ⟨trace, ⟨H.1.1.keep v Ku (by decide) Ou' (timing_wf_regs A.wf₁),
    H.1.2.1.keep v Kz (by decide) Oz' (timing_wf_regs A.wf₂), ?_⟩, ?_, ?_⟩
  · exact timing_add_regs (timing_forget A) fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      rw [Ku.1 .edi (by decide), Kz.1 .edi (by decide)]
      exact timing_regs H.1.2.2 (by simp)
  · rw [PtrAt, Ku.1 .edi (by decide)]; exact H.2.1
  · rw [PtrAt, Kz.1 .edi (by decide)]; exact H.2.2

end VG.Proof.Mont.X86.Compact
