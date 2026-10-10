import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourStep
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPhase

/-! ## From `ResidentRejInit.lean` -/

section

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

end

/-! ## From `ResidentRejParseFour.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

theorem vectorSetup_inv {s₀ s : State} {b p : Addr} {n d : Nat} {L : List Zq}
    (h : ParseInv s₀ b p n L d s) :
    WP isa (.block vectorSetup) s fun t => ParseInv s₀ b p n L d t ∧ t.gpr .x17=4 := by
  refine WP.mono (vectorSetup_ok (s := s) h.constants.qreg) fun t ⟨ht,hc,h17,h0,h10⟩ => ?_
  refine ⟨⟨(h.keep.trans ht.only.keep).mono (by decide),by rw [ht.only.mem]; exact h.frame,
    hc,h.bound,?_,?_,?_,?_,h10,h0,?_⟩,h17⟩
  · rw [ht.only.get .x2]; exact h.x2
  · rw [ht.only.get .x3]; exact h.x3
  · rw [ht.only.get .x4]; exact h.x4
  · rw [ht.only.get .x5]; exact h.x5
  · rw [ht.only.mem]; exact h.stored

theorem fourSetup_ok {s₀ s : State} {b p : Addr} {n d : Nat} {L : List Zq}
    (h : ParseInv s₀ b p n L d s) :
    WP isa (.block (vectorSetup++guard)) s fun t =>
      ParseInv s₀ b p n L d t ∧ t.gpr .x17=4 ∧
      t.gpr .x16=(if 4≤(t.gpr .x4).toNat then t.gpr .x5 else 0) := by
  rw [WP.block_append_iff]
  refine WP.mono (vectorSetup_inv h) fun a ⟨ha,h17⟩ => ?_
  refine WP.mono (guard_ok h17 ha.zero) fun t ⟨ht,hv,hg⟩ => ?_
  exact ⟨ha.of_control (ht.mono (by decide)) hv,by rw [ht.get .x17]; exact h17,
    by rw [hg,ht.get .x4,ht.get .x5]⟩

/-- Four-candidate processing followed by scalar cleanup consumes the
entire available segment, unless the polynomial becomes full first. -/
theorem parseFour_ok (v : Nat) {s₀ s : State} {b p : Addr} {n d : Nat} {L : List Zq}
    (hl : StreamLayout s₀ b p n) (h : ParseInv s₀ b p n L d s)
    (hL : L.length≤256) (hmod : n%4=d%4) :
    WP isa (parse4 v) s fun t =>
      ∃d',ParseInv s₀ b p n L d' t ∧ d≤d' ∧
        (d'=n ∨ (parsed s₀ b L d').length=256) := by
  refine WP.seq (WP.mono (fourSetup_ok h) fun a ⟨ha,h17,hg⟩ => ?_)
  refine WP.seq (WP.mono (fourPhase_ok hl ha h17 hmod hg)
    fun b ⟨j,hj,hdj,_,_,_⟩ => ?_)
  refine WP.mono (scalarPhase_ok hl hj hL) fun t ⟨k,hk,hjk,hend⟩ => ?_
  exact ⟨k,hk,Nat.le_trans hdj hjk,hend⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejParse.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

theorem wideControl_ok {s₀ s : State} {b p : Addr} {n d : Nat} {L : List Zq}
    (h : ParseInv s₀ b p n L d s) :
    WP isa (.block (([.movz .x .x17 16 0] : List Instr)++wideGuard)) s fun t =>
      ParseInv s₀ b p n L d t ∧ t.gpr .x17=16 ∧
      t.gpr .x16=(if 16≤(t.gpr .x4).toNat ∧ 16≤(t.gpr .x5).toNat then 16 else 0) := by
  have hm : WP isa (.block [.movz .x .x17 16 0]) s fun t =>
      Only [.x17] s t ∧ t.gpr .x17=16 := wp_movz fun t ht et => wp_nil ⟨ht,et⟩
  rw [WP.block_append_iff]
  refine WP.mono (WP.keepV (by decide) hm) fun a ⟨⟨ha,h17⟩,hav⟩ => ?_
  have hi := h.of_control (ha.mono (by decide)) hav
  refine WP.mono (wideGuard_ok h17 hi.zero) fun t ⟨ht,hv,hg⟩ => ?_
  exact ⟨hi.of_control (ht.mono (by decide)) hv,by rw [ht.get .x17]; exact h17,
    by rw [hg,ht.get .x4,ht.get .x5]⟩

/-- The complete selected parser implements the shared byte-stream fold;
wide, narrow, and scalar paths share one accepted-prefix invariant. -/
theorem parse_ok (v : Nat) {s : State} {b p : Addr} {n : Nat} {L : List Zq}
    (hl : StreamLayout s b p n) (hmod : n%4=0) (hL : L.length≤256)
    (h2 : s.gpr .x2=b) (h3 : s.gpr .x3=coeffAddr p L.length)
    (h4 : (s.gpr .x4).toNat=256-L.length) (h5 : (s.gpr .x5).toNat=n)
    (h9 : (s.gpr .x9).toNat=q) (hst : Stored s.mem p L) :
    WP isa (parse v) s fun t => Keep parseRegs s t ∧ Frame [polyR p] s.mem t.mem ∧
      t.gpr .x3=coeffAddr p (rnFold L (candidateBytes s.mem b n)).length ∧
      (t.gpr .x4).toNat=256-(rnFold L (candidateBytes s.mem b n)).length ∧
      Stored t.mem p (rnFold L (candidateBytes s.mem b n)) := by
  unfold parse
  refine WP.seq ?_
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (vectorSetup_ok (s := s) h9) fun a ⟨ha,hc,_,h0,h10⟩ => ?_
  have hi : ParseInv s b p n L 0 a := by
    refine ⟨ha.only.keep.mono (by decide),by rw [ha.only.mem]; exact Frame.refl _ _,hc,
      Nat.zero_le _,?_,?_,?_,?_,h10,h0,?_⟩
    · rw [ha.only.get .x2,h2]; exact (ptr_zero b).symm
    · rw [ha.only.get .x3]; exact h3
    · rw [ha.only.get .x4]; exact h4
    · rw [ha.only.get .x5]; exact h5
    · rw [ha.only.mem]; exact hst
  refine WP.mono (wideControl_ok hi) fun a ⟨ha,h17,hg⟩ => ?_
  refine WP.seq (WP.mono (widePhase_ok hl ha h17 hg) fun a ⟨j,hj,_,hjm,_,_⟩ => ?_)
  refine WP.mono (parseFour_ok v hl hj hL (by rw [hmod,hjm])) fun t ⟨k,hk,_,hend⟩ => ?_
  have he := parsed_done s b L hk.bound hend
  have hp := hk.x3
  have hc := hk.x4
  have hs := hk.stored
  rw [he] at hp hc hs
  exact ⟨hk.keep,hk.frame,hp,hc,hs⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end
