import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourStep
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFrame

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

private theorem scalarConst_frame {s t : State} {r : Reg}
    (hg : ∀g,g≠r → t.gpr g=s.gpr g) (hs : t={s with gpr:=t.gpr}) :
    ProbeFrame [r] [] s t := by
  refine ⟨⟨fun g h => hg g (by simpa using h),?_,?_,?_,?_,?_⟩,?_⟩
  all_goals rw [hs]
  all_goals first | rfl | exact fun _ _ => rfl

def indexSetup : List Instr :=
 imm64 .x6 0xff050403ff020100 ++ imm64 .x7 0xff0b0a09ff080706 ++
 [.vop (.dup .d2 .v3 .x6),.vop (.ins .d2 .v3 1 .x7)]

/-- Exact byte-shuffle index initialization, split at the scalar constant
loads to avoid expanding large nested state updates in the kernel. -/
theorem indexSetup_ok (s : State) :
    WP isa (.block indexSetup) s fun t =>
      ProbeFrame [.x6,.x7] [.v3] s t ∧ t.v .v3=gatherIndex := by
  have h6 : imm64 .x6 0xff050403ff020100=
      VG.Impl.Tbl.AArch64.const64 .x6 0xff050403ff020100 := by decide
  have h7 : imm64 .x7 0xff0b0a09ff080706=
      VG.Impl.Tbl.AArch64.const64 .x7 0xff0b0a09ff080706 := by decide
  rw [indexSetup,h6,h7,List.append_assoc,WP.block_append_iff]
  refine WP.mono (VG.AArch64.Tbl.const64_ok s .x6 0xff050403ff020100)
    fun a ⟨ha,hga,hsa⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.AArch64.Tbl.const64_ok a .x7 0xff0b0a09ff080706)
    fun b ⟨hb,hgb,hsb⟩ => ?_
  refine wp_vop (d := .v3) rfl fun c hc => wp_vop (d := .v3) rfl fun t ht =>
    WP.block_nil_iff.mpr ?_
  have hscalar := (scalarConst_frame hga hsa).trans (scalarConst_frame hgb hsb)
  have hvec := ProbeFrame.ofVector (hc.chg.trans ht.chg) (by decide)
  refine ⟨(hscalar.trans hvec).mono (by simp) (by simp),?_⟩
  rw [ht.v,hc.v,hc.gpr,hb,hgb .x6 (by decide),ha]
  rfl

def maskSetup : List Instr :=
 [.movz .x .x10 65535 0,.movk .x .x10 127 1,.vop (.dup .s4 .v4 .x10)]

theorem maskSetup_ok (s : State) :
    WP isa (.block maskSetup) s fun t => ProbeFrame [.x10] [.v4] s t ∧
      t.gpr .x10=0x7fffff ∧ ∀e<4,vword (t.v .v4) e=0x7fffff := by
  refine WP.of_runBlock ⟨_,rfl,?_,?_,?_⟩
  · refine ⟨⟨?_,rfl,rfl,rfl,rfl,?_⟩,?_⟩
    · intro r hr
      simp only [State.write,State.setV,show r≠.x10 by simpa using hr,ite_false]
    · intro r hr
      have hn : r≠.v4 := by
        simp only [preservedV,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp only [State.write,State.setV,hn,ite_false]
    · intro r hr
      simp only [State.write,State.setV,show r≠.v4 by simpa using hr,ite_false]
  · simp only [State.write,State.read,State.setV,ite_true,Size.bits,BitVec.setWidth_eq]
    decide
  · intro e he
    simp only [State.write,State.read,State.setV,ite_true,Size.bits,BitVec.setWidth_eq]
    have hh : ∀e<4,vword (ofVWords 8388607 8388607 8388607 8388607) e=0x7fffff := by decide +kernel
    exact hh e he

def countSetup : List Instr :=
 [.movz .x .x12 1 0,.movk .x .x12 1 2,.movz .x .x17 4 0,.movz .x .x0 0 0]

theorem countSetup_ok (s : State) :
    WP isa (.block countSetup) s fun t => ProbeFrame [.x12,.x17,.x0] [] s t ∧
      t.gpr .x12=0x100000001 ∧ t.gpr .x17=4 ∧ t.gpr .x0=0 := by
  refine WP.of_runBlock ⟨_,rfl,?_,?_,?_,?_⟩
  · refine ⟨⟨?_,rfl,rfl,rfl,rfl,fun _ _ => rfl⟩,fun _ _ => rfl⟩
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [State.write,hr.1,hr.2.1,hr.2.2,ite_false]
  all_goals
    simp only [State.write,State.read,ite_true,Size.bits,BitVec.setWidth_eq]
    decide

/-- Complete fixed parser initialization, with constants and exact clobbers. -/
theorem vectorSetup_ok (s : State) (hq : (s.gpr .x9).toNat=Spec.MlDsa.q) :
    WP isa (.block vectorSetup) s fun t =>
      ProbeFrame [.x6,.x7,.x10,.x12,.x17,.x0] [.v3,.v4,.v5] s t ∧
      Constants t ∧ t.gpr .x17=4 ∧ t.gpr .x0=0 ∧ t.gpr .x10=0x7fffff := by
  rw [show vectorSetup=indexSetup++maskSetup++
    ([.vop (.dup .s4 .v5 .x9)] : List Instr)++countSetup from rfl,List.append_assoc,
    List.append_assoc,WP.block_append_iff]
  refine WP.mono (indexSetup_ok s) fun a ⟨ha,hindex⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (maskSetup_ok a) fun b ⟨hb,hmaskreg,hmask⟩ => ?_
  simp only [List.cons_append,List.nil_append]
  refine wp_vop (d := .v5) rfl fun c hc => ?_
  refine WP.mono (countSetup_ok c) fun t ⟨ht,hones,h17,h0⟩ => ?_
  have hvc := ProbeFrame.ofVector hc.chg (by decide)
  have hf : ProbeFrame [.x6,.x7,.x10,.x12,.x17,.x0] [.v3,.v4,.v5] s t :=
    (((ha.trans hb).trans hvc).trans ht).mono (by decide) (by decide)
  refine ⟨hf,⟨?_,?_,?_,hones,?_⟩,h17,h0,?_⟩
  · rw [ht.vectors .v3 (by decide),hc.other .v3 (by decide),hb.vectors .v3 (by decide)]
    exact hindex
  · intro e he
    rw [ht.vectors .v4 (by decide),hc.other .v4 (by decide)]
    exact hmask e he
  · intro e he
    rw [ht.vectors .v5 (by decide),hc.v]
    have h9 : b.gpr .x9=8380417 := by
      apply BitVec.eq_of_toNat_eq
      rw [hb.only.get .x9,ha.only.get .x9]
      exact hq
    rw [h9]
    have hh : ∀e<4,vword (ofVWords 8380417 8380417 8380417 8380417) e=8380417 := by decide +kernel
    exact hh e he
  · rw [hf.only.get .x9]; exact hq
  · rw [ht.only.get .x10,hc.gpr]; exact hmaskreg

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
