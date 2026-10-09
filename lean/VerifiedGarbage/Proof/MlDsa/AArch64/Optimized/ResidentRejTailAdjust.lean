import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailHead

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample (coeffAddr)

def tailAdjust : List Instr :=
  [.sub .x .x6 .x6 .x7,.lsr .x .x6 .x6 63,.movz .x .x7 1 0,.sub .x .x6 .x7 .x6,
   .sub .x .x4 .x4 .x6,.lsl .x .x6 .x6 2,.add .x .x3 .x3 .x6,.movz .x .x9 0 0]

/-- The final rejected-candidate slot is skipped by either zero or one word;
all accepted coefficients remain strictly before the cleanup cursor. -/
theorem tailAdjust_ok {s : State} {p : Addr} {len : Nat} (hl : len<256)
    (hp : s.gpr .x3=coeffAddr p len) (hc : (s.gpr .x4).toNat=256-len) :
    WP isa (.block tailAdjust) s fun t => Only [.x3,.x4,.x6,.x7,.x9] s t ∧
      ∃skip≤1,t.gpr .x3=coeffAddr p (len+skip) ∧
        (t.gpr .x4).toNat=256-(len+skip) ∧ t.gpr .x9=0 := by
  unfold tailAdjust
  refine wp_sub fun a ha ea => wp_lsr (by decide) fun b hb eb => wp_movz fun c hc' ec =>
    wp_sub fun d hd ed => wp_sub fun e he ee => wp_lsl (by decide) fun f hf ef =>
      wp_add fun g hg eg => wp_movz fun t ht et => wp_nil ?_
  have hb6 : (b.gpr .x6).toNat≤1 := by
    rw [eb,BitVec.toNat_ushiftRight]
    have := (a.gpr .x6).isLt
    omega
  have hc7 : c.gpr .x7=1 := by rw [ec]; rfl
  have hd6 : (d.gpr .x6).toNat≤1 := by
    rw [ed,toNat_sub_n (by rw [hc7,hc'.get .x6]; change (b.gpr .x6).toNat≤1; exact hb6),
      hc7,hc'.get .x6]
    change 1-(b.gpr .x6).toNat≤1
    omega
  let skip := (d.gpr .x6).toNat
  have he4 : (e.gpr .x4).toNat=256-(len+skip) := by
    rw [ee,toNat_sub_n (by
      rw [hd.get .x4,hc'.get .x4,hb.get .x4,ha.get .x4,hc]
      change (d.gpr .x6).toNat≤256-len
      omega),hd.get .x4,hc'.get .x4,hb.get .x4,ha.get .x4,hc]
    change 256-len-skip=256-(len+skip)
    omega
  have hf6 : f.gpr .x6=BitVec.ofNat 64 (4*skip) := by
    apply BitVec.eq_of_toNat_eq
    rw [ef,toNat_lsl_n (by rw [he.get .x6]; change skip*2^2<2^64; dsimp [skip]; omega),he.get .x6,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by dsimp [skip]; omega)]
    change skip*2^2=4*skip
    omega
  refine ⟨(((((((ha.trans hb).trans hc').trans hd).trans he).trans hf).trans hg).trans ht).mono (by decide),
    skip,hd6,?_,?_,?_⟩
  · rw [ht.get .x3,eg,hf.get .x3,he.get .x3,hd.get .x3,hc'.get .x3,hb.get .x3,ha.get .x3,hp,hf6]
    unfold coeffAddr
    rw [Offset.add_add]
    congr 2
    omega
  · rw [ht.get .x4,hg.get .x4,hf.get .x4]; exact he4
  · rw [et]; rfl

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
