import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejValue
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFrame

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def quarterCode (j : Nat) : List Instr :=
 let d := wideRegs[j]!
 [.addImm .x .x6 .x2 (12*j),.ldrq .v0 .x6 0,.vop (.tbl d .v0 .v3),
  .vop (.logic .and d d .v4),.vop (.sub .s4 .v2 d .v5),
  .vop (.shift .ushr .s4 .v2 .v2 31),.vop (.logic .and .v20 .v20 .v2)]

/-- One quarter of a sixteen-candidate probe updates only its own value
vector and the accumulated acceptance mask. Source buffers remain untouched. -/
theorem quarter_ok {s : State} {j : Nat} (hj : j<4)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (12*j)) 16)
    (hi : s.v .v3=gatherIndex) :
    WP isa (.block (quarterCode j)) s fun t =>
      ProbeFrame [.x6] [.v0,wideRegs[j]!, .v2,.v20] s t ∧
      t.v wideRegs[j]! =candidates (s.mem.read (s.gpr .x2+BitVec.ofNat 64 (12*j)) 16) (s.v .v4) ∧
      t.v .v20=s.v .v20 &&&
        accepted (candidates (s.mem.read (s.gpr .x2+BitVec.ofNat 64 (12*j)) 16) (s.v .v4)) (s.v .v5) := by
  let d := wideRegs[j]!
  have hn : d≠.v0 ∧ d≠.v2 ∧ d≠.v3 ∧ d≠.v4 ∧ d≠.v5 ∧ d≠.v20 := by
    rcases (show j=0 ∨ j=1 ∨ j=2 ∨ j=3 by omega) with rfl | rfl | rfl | rfl <;> decide
  have hvpres : ∀r∈preservedV,r∉[.v0,d,.v2,.v20] := by
    rcases (show j=0 ∨ j=1 ∨ j=2 ∨ j=3 by omega) with rfl | rfl | rfl | rfl <;> decide
  have hadd : WP isa (.block [.addImm .x .x6 .x2 (12*j)]) s fun a =>
      Only [.x6] s a ∧ a.gpr .x6=s.gpr .x2+BitVec.ofNat 64 (12*j) := by
    refine wp_addImm (by omega) fun a ha ea => wp_nil ⟨ha,ea⟩
  change WP isa (.block (([.addImm .x .x6 .x2 (12*j)] : List Instr)++_)) s _
  refine wp_scalar (by rfl) hadd fun a ⟨ha,ea⟩ hava => ?_
  refine wp_ldrq (a := s.gpr .x2+BitVec.ofNat 64 (12*j)) (by decide)
    (by rw [ea]; exact ptr_zero _) (by rw [ha.rd,ha.wr]; exact hr) fun b hb => ?_
  rw [show ([Instr.vop (.tbl d .v0 .v3),.vop (.logic .and d d .v4),
      .vop (.sub .s4 .v2 d .v5),.vop (.shift .ushr .s4 .v2 .v2 31),
      .vop (.logic .and .v20 .v20 .v2)] : List Instr)=
      ([.vop (.tbl d .v0 .v3),.vop (.logic .and d d .v4),
      .vop (.sub .s4 .v2 d .v5),.vop (.shift .ushr .s4 .v2 .v2 31)] : List Instr)++
      [.vop (.logic .and .v20 .v20 .v2)] from rfl,WP.block_append_iff]
  refine WP.mono (decode_ok hn.2.1 hn.2.2.2.1 hn.2.2.2.2.1
    (by rw [hb.other .v3 (by decide),hava]; exact hi)) fun c ⟨hc,hval,hbits⟩ => ?_
  refine wp_vop (d := .v20) rfl fun t ht => WP.block_nil_iff.mpr ?_
  have hvc : VChg [.v0,d,.v2,.v20] a t :=
    ((hb.chg.trans hc).trans ht.chg).mono (by
      intro r hr
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
      grind only)
  refine ⟨((ProbeFrame.ofScalar ha hava).trans (ProbeFrame.ofVector hvc hvpres)).mono
    (by simp) (by simp [d]),?_,?_⟩
  · rw [ht.other d hn.2.2.2.2.2,hval,hb.v,ha.mem,hb.other .v4 (by decide),hava]
  · rw [ht.v,hc.get .v20 (by simp [Ne.symm hn.2.2.2.2.2]),
      hb.other .v20 (by decide),hbits,hb.v,ha.mem,hb.other .v4 (by decide),
      hb.other .v5 (by decide),hava]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
