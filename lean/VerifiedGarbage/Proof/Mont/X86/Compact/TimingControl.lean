module

import VerifiedGarbage.Proof.Mont.X86.Compact.TimingValue
import VerifiedGarbage.Proof.Mont.X86.Compact.Control
import VerifiedGarbage.Proof.Mont.X86.Compact.TimingKernels
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingLift

/-! # The outer CIOS loop advances according to the public prepared width -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Dsa.X86

theorem advance_relCT {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g [.ebp, .edi]) (.block [.alu .add .ebp (.imm 4)]) (Pair g [.ebp, .edi]) := by
  refine lift_readonly v (checkedProgramChange (hint := .block [])
    (τ' := timingTaint [.ebp, .edi] true) rfl rfl) ?_
  intro s
  refine wp_addS rfl fun t T _ => WP.block_nil ⟨T.mem, T.keeps.mono (by decide)⟩

theorem endCompare_relCT {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g [.eax, .ebp, .edi])
      (.block [.alu .add .eax (.reg .edi), .alu .add .eax (.imm (BitVec.ofNat 32 Compact.accOff)),
        .alu .cmp .ebp (.reg .eax)]) (Pair g [.ebp, .edi]) := by
  refine lift_readonly v (checkedProgramChange (hint := .block [])
    (τ' := timingTaint [.eax, .ebp, .edi] true) rfl rfl) ?_
  intro s
  refine wp_addS rfl fun a A _ => wp_addS rfl fun b B _ => wp_cmpS rfl fun t T _ => WP.block_nil ?_
  exact ⟨T.mem.trans (B.mem.trans A.mem),
    ((A.keeps.mono (by decide)).trans (B.keeps.mono (by decide))).trans ((T.keeps []).mono (by decide))⟩

theorem rowEnd_trace {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g [.ebp, .edi]) (.block Compact.rowEnd) (Pair g [.ebp, .edi]) := by
  unfold Compact.rowEnd
  rw [List.append_assoc]
  exact RelCT.block_append (RelCT.seq (advance_relCT v)
    (RelCT.block_append (RelCT.seq
      (length_relCT v .eax .edx 0 byteLength_relCT (by decide) (by decide)) (endCompare_relCT v))))

theorem rowEnd_relCT {g : Geometry} (v : g.Valid) (i : Nat) (index : i < g.N) :
    RelCT isa (WindowPair g (g.S + Compact.accOff + 4 * i)) (.block Compact.rowEnd)
      (fun s t => WindowPair g (g.S + Compact.accOff + 4 * (i + 1)) s t ∧
        s.zf = some (decide (i + 1 = g.N)) ∧ t.zf = some (decide (i + 1 = g.N))) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, P⟩ := rowEnd_trace v _ _ _ _ _ _ H.1 E G
  have fit := v.lay.scr
  have header := v.lay.header
  have acc : Compact.accOff = 24 := rfl
  obtain ⟨Bu, Zu, _, Ku⟩ := wp_result (rowEnd_ok H.1.1.ws H.1.1.args v.base H.1.1.metadata.width
    (by omega) v.n32 H.2.1 H.2.2.2.1 index (by omega)) E
  obtain ⟨Bz, Zz, _, Kz⟩ := wp_result (rowEnd_ok H.1.2.1.ws H.1.2.1.args v.base H.1.2.1.metadata.width
    (by omega) v.n32 H.2.2.1 H.2.2.2.2 index (by omega)) G
  refine ⟨trace, ⟨P, ?_, ?_, Bu, Bz⟩, Zu, Zz⟩
  · rw [PtrAt, Ku.1 .edi (by decide)]; exact H.2.1
  · rw [PtrAt, Kz.1 .edi (by decide)]; exact H.2.2.1

end VG.Proof.Mont.X86.Compact
