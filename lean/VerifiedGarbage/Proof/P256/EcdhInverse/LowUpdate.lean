import VerifiedGarbage.Proof.P256.EcdhInverse.Extract

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Divstep
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

def lowUpdateA : List Instr :=
  [.mul .x .x6 .x8 .x2,
   .mul .x .x7 .x9 .x3,
   .mul .x .x2 .x10 .x2,
   .mul .x .x3 .x11 .x3,
   .add .x .x4 .x6 .x7,
   .add .x .x5 .x2 .x3,
   .lsr .x .x26 .x4 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x2 .x26 .x4 20,
   .lsr .x .x26 .x5 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x3 .x26 .x5 20]

theorem lowUpdateA_run (s : State) (h27 : s.gpr .x27=0) :
    WP isa (.block lowUpdateA) s fun t =>
      t.gpr .x2=(s.gpr .x8*s.gpr .x2+s.gpr .x9*s.gpr .x3).sshiftRight 20 ∧
      t.gpr .x3=(s.gpr .x10*s.gpr .x2+s.gpr .x11*s.gpr .x3).sshiftRight 20 ∧
      Keeps [.x2,.x3,.x4,.x5,.x6,.x7,.x26] s t := by
  apply WP.of_runBlock
  simp only [lowUpdateA,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,Option.some.injEq,
    exists_eq_left',h27,zero_sub,show (63:Nat)<Size.x.bits by decide,
    show (20:Nat)<Size.x.bits by decide]
  refine ⟨?_,?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · exact signed_extract _ (by decide)
  · exact signed_extract _ (by decide)
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    obtain ⟨h2,h3,h4,h5,h6,h7,h26⟩ := hr
    simp only [RegUpd.gpr_write,h2,h3,h4,h5,h6,h7,h26,↓reduceIte]

def lowUpdateB : List Instr :=
  [.mul .x .x6 .x12 .x2,
   .mul .x .x7 .x13 .x3,
   .mul .x .x2 .x14 .x2,
   .mul .x .x3 .x15 .x3,
   .add .x .x4 .x6 .x7,
   .add .x .x5 .x2 .x3,
   .lsr .x .x26 .x4 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x2 .x26 .x4 20,
   .lsr .x .x26 .x5 63,
   .sub .x .x26 .x27 .x26,
   .extr .x .x3 .x26 .x5 20]

theorem lowUpdateB_run (s : State) (h27 : s.gpr .x27=0) :
    WP isa (.block lowUpdateB) s fun t =>
      t.gpr .x2=(s.gpr .x12*s.gpr .x2+s.gpr .x13*s.gpr .x3).sshiftRight 20 ∧
      t.gpr .x3=(s.gpr .x14*s.gpr .x2+s.gpr .x15*s.gpr .x3).sshiftRight 20 ∧
      Keeps [.x2,.x3,.x4,.x5,.x6,.x7,.x26] s t := by
  apply WP.of_runBlock
  simp only [lowUpdateB,runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,↓reduceIte,Option.some.injEq,
    exists_eq_left',h27,zero_sub,show (63:Nat)<Size.x.bits by decide,
    show (20:Nat)<Size.x.bits by decide]
  refine ⟨?_,?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · exact signed_extract _ (by decide)
  · exact signed_extract _ (by decide)
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    obtain ⟨h2,h3,h4,h5,h6,h7,h26⟩ := hr
    simp only [RegUpd.gpr_write,h2,h3,h4,h5,h6,h7,h26,↓reduceIte]

theorem shifted_lincomb (x y : BitVec 64) (u v : Int) :
    (((BitVec.ofInt 64 u*x+BitVec.ofInt 64 v*y).sshiftRight 20).toNat:Int)%2^44 =
      ((u*x.toNat+v*y.toNat)/2^20)%2^44 := by
  have hx : x=BitVec.ofInt 64 x.toNat := by simp
  have hy : y=BitVec.ofInt 64 y.toNat := by simp
  conv_lhs => rw [hx,hy,←BitVec.ofInt_mul,←BitVec.ofInt_mul,←BitVec.ofInt_add]
  exact shifted_low44 _

end VG.Proof.P256.EcdhInverse
