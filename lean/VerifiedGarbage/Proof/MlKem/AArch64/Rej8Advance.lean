module

public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Store
public import VerifiedGarbage.Proof.MlKem.CoeffW

/-! # Output and input advancement after stable vector compaction -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64

def advanceCode (w16 : Bool := false) : List Instr :=
 [.lsr .x .x6 .x6 8,.movz .x .x7 15 0,.logic .and .x .x6 .x6 .x7,
 .sub .x .x4 .x4 .x6,.lsl .x .x6 .x6 (if w16 then 1 else 2),.add .x .x3 .x3 .x6,
 .addImm .x .x2 .x2 12,.subImm .x .x5 .x5 4]

structure AdvancePost (w16 : Bool) (s t : State) (n : Nat) : Prop where
  only : Only [.x2,.x3,.x4,.x5,.x6,.x7] s t
  output : t.gpr .x3 = s.gpr .x3 + BitVec.ofNat 64 (VG.Proof.MlKem.cs w16*n)
  remain : (t.gpr .x4).toNat = (s.gpr .x4).toNat - n
  input : t.gpr .x2 = s.gpr .x2 + 12
  chunks : (t.gpr .x5).toNat = (s.gpr .x5).toNat - 4

theorem advance_ok (w16 : Bool) (s : State) {n : Nat} (hn : n≤8)
    (h4 : 8 ≤ (s.gpr .x4).toNat) (h5 : 4 ≤ (s.gpr .x5).toNat)
    (hc : ((s.gpr .x6 >>> 8) &&& 15).toNat = n) :
    WP isa (.block (advanceCode w16)) s (fun t => AdvancePost w16 s t n) := by
  refine wp_lsr (by decide) fun a ha ea => wp_movz fun b hb eb =>
    wp_and fun c hc0 ec => wp_sub fun d hd ed => wp_lsl (by cases w16 <;> decide) fun e he ee =>
    wp_add fun f hf ef => wp_addImm (by decide) fun g hg eg =>
    wp_subImm (by decide) fun t ht et => wp_nil ?_
  have cn : (c.gpr .x6).toNat=n := by
    rw [ec,hb.get .x6,ea,eb]
    exact hc
  have dn : (d.gpr .x6).toNat=n := by rw [hd.get .x6,cn]
  have en : e.gpr .x6=BitVec.ofNat 64 (VG.Proof.MlKem.cs w16*n) := by
    apply BitVec.eq_of_toNat_eq
    cases w16 <;>
    · rw [ee,toNat_lsl_n (by rw [dn]; simp only [Bool.false_eq_true, ite_false, ite_true]; omega),dn,
        BitVec.toNat_ofNat]
      simp only [VG.Proof.MlKem.cs_eq, Bool.false_eq_true, ite_false, ite_true]; omega
  refine ⟨(((((((ha.trans hb).trans hc0).trans hd).trans he).trans hf).trans hg).trans ht).mono
    (by decide),?_,?_,?_,?_⟩
  · rw [ht.get .x3,hg.get .x3,ef,en,he.get .x3,hd.get .x3,hc0.get .x3,hb.get .x3,ha.get .x3]
  · rw [ht.get .x4,hg.get .x4,hf.get .x4,he.get .x4,ed,
      hc0.get .x4,hb.get .x4,ha.get .x4,BitVec.toNat_sub,cn]
    have := (s.gpr .x4).isLt
    omega
  · rw [ht.get .x2,eg,hf.get .x2,he.get .x2,hd.get .x2,hc0.get .x2,hb.get .x2,ha.get .x2]
    rfl
  · rw [et,hg.get .x5,hf.get .x5,he.get .x5,hd.get .x5,hc0.get .x5,hb.get .x5,ha.get .x5,
      BitVec.toNat_sub]
    have hb4 : (BitVec.ofNat 64 4).toNat=4 := rfl
    have := (s.gpr .x5).isLt
    simp only [hb4]
    omega

end VG.Proof.MlKem.AArch64.Rej8
