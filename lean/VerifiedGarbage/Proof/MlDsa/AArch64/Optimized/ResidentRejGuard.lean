import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejParser

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

/-- Carry-based unsigned comparison used by both vector-loop guards. -/
theorem compareChooseReg_ok {s : State} (d n m a b : Reg) (ha : a≠d) (hb : b≠d) :
    WP isa (.block [.subs .x d n m,.cselc .x d a b .hs]) s fun t =>
      Only [d] s t ∧ t.v=s.v ∧
      t.gpr d=if (s.gpr m).toNat≤(s.gpr n).toNat then s.gpr a else s.gpr b := by
  let u := s.addWithCarry .x d (s.gpr n) (~~~s.gpr m) true
  have hu : Only [d] s u := by
    refine ⟨?_,rfl,rfl,rfl,rfl,fun _ _ => rfl⟩
    intro r hr
    simp only [u,State.addWithCarry,State.write,show ¬r=d by simpa using hr,ite_false]
  have hc : u.c=decide ((s.gpr m).toNat≤(s.gpr n).toNat) := by
    change decide (2^64≤(s.gpr n).toNat+(~~~s.gpr m).toNat+1)=_
    rw [BitVec.toNat_not]
    congr 1
    apply propext
    have hm := (s.gpr m).isLt
    omega
  refine WP.cons (s' := u) rfl ?_
  have htail : WP isa (.block [.cselc .x d a b .hs]) u fun t =>
      Only [d] u t ∧ t.gpr d=(if u.c then u.gpr a else u.gpr b) := by
    refine wp_x (d := d) (v := if u.c then u.gpr a else u.gpr b) rfl fun t ht hv =>
      wp_nil ⟨ht,hv⟩
  refine WP.mono (WP.keepV (by rfl) htail) fun t ⟨⟨ht,hv⟩,hvec⟩ => ?_
  refine ⟨(hu.trans ht).mono (by simp),hvec,?_⟩
  rw [hv,hc,hu.get a (by simpa using ha),hu.get b (by simpa using hb)]
  simp only [decide_eq_true_eq]

/-- The matrix parser's fixed comparison destination. -/
theorem compareChoose_ok {s : State} (n m a b : Reg) (ha : a≠.x16) (hb : b≠.x16) :
    WP isa (.block [.subs .x .x16 n m,.cselc .x .x16 a b .hs]) s fun t =>
      Only [.x16] s t ∧ t.v=s.v ∧
      t.gpr .x16=if (s.gpr m).toNat≤(s.gpr n).toNat then s.gpr a else s.gpr b :=
  compareChooseReg_ok .x16 n m a b ha hb

/-- The four-candidate loop starts another batch iff capacity permits it
and the remaining segment is nonempty. -/
theorem guard_ok {s : State} (h17 : s.gpr .x17=4) (h0 : s.gpr .x0=0) :
    WP isa (.block guard) s fun t => Only [.x16] s t ∧ t.v=s.v ∧
      t.gpr .x16=if 4≤(s.gpr .x4).toNat then s.gpr .x5 else 0 := by
  refine WP.mono (compareChoose_ok .x4 .x17 .x5 .x0 (by decide) (by decide))
    fun t ⟨hk,hv,hx⟩ => ⟨hk,hv,?_⟩
  rw [h17,h0] at hx
  exact hx

/-- The wider loop checks both output capacity and available candidates. -/
theorem wideGuard_ok {s : State} (h17 : s.gpr .x17=16) (h0 : s.gpr .x0=0) :
    WP isa (.block wideGuard) s fun t => Only [.x16] s t ∧ t.v=s.v ∧
      t.gpr .x16=if 16≤(s.gpr .x4).toNat ∧ 16≤(s.gpr .x5).toNat then 16 else 0 := by
  rw [show wideGuard=([.subs .x .x16 .x4 .x17,.cselc .x .x16 .x5 .x0 .hs] : List Instr)++
      [.subs .x .x16 .x16 .x17,.cselc .x .x16 .x17 .x0 .hs] from rfl,
    WP.block_append_iff]
  refine WP.mono (compareChoose_ok .x4 .x17 .x5 .x0 (by decide) (by decide))
    fun a ⟨ha,hva,hxa⟩ => ?_
  refine WP.mono (compareChoose_ok .x16 .x17 .x17 .x0 (by decide) (by decide))
    fun t ⟨ht,hvt,hxt⟩ => ?_
  refine ⟨(ha.trans ht).mono (by simp),hvt.trans hva,?_⟩
  rw [ha.get .x17,ha.get .x0,h17,h0,hxa,h17,h0] at hxt
  change t.gpr .x16=(if 16≤(if 16≤(s.gpr .x4).toNat then s.gpr .x5 else 0).toNat
    then 16 else 0) at hxt
  rw [hxt]
  by_cases h : 16≤(s.gpr .x4).toNat
  · simp only [h,ite_true,true_and]
  · simp only [h,ite_false,false_and]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
