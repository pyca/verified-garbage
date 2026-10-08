import VerifiedGarbage.Proof.Divstep.NegInput
import VerifiedGarbage.Proof.Divstep.Packed

namespace VG.Proof.P256.EcdhInverse
open VG.Proof.Divstep

theorem second_input_cong {d f g a b : Int} (hf : f%2=1)
    (ha : a%2^44=(-f)%2^44) (hb : b%2^44=(-g)%2^44) :
    (msteps 20 (MSt.init d a b)).cong
      (msteps 20 (MSt.init d f g)).negInput 24 := by
  have hodd : a%2=1 := by norm_num at ha; omega
  have hinit : (MSt.init d a b).cong (MSt.init d (-f) (-g)) 44 :=
    ⟨rfl,rfl,rfl,rfl,rfl,ha,hb⟩
  have h := msteps_cong hodd hinit 20 (by decide)
  rw [msteps_init_negInput d f g hf 20] at h
  exact h

theorem second_output_cong {a b c : Int}
    (ha : a%2^44=(-b)%2^44) (hb : b%2^24=(-c)%2^24) :
    a%2^24=c%2^24 := by
  norm_num at *
  omega

theorem third_input_cong {d f g a b : Int} (hf : f%2=1)
    (ha : a%2^24=f%2^24) (hb : b%2^24=g%2^24) :
    (msteps 19 (MSt.init d a b)).cong (msteps 19 (MSt.init d f g)) 5 := by
  have hodd : a%2=1 := by norm_num at ha; omega
  exact msteps_cong (t:=MSt.init d a b) (t':=MSt.init d f g) (N:=24) hodd
    ⟨rfl,rfl,rfl,rfl,rfl,ha,hb⟩ 19 (by decide)

/-- Compose the three transition matrices independently of the low-word representation. -/
theorem matrix59 (d f g : Int) :
    let a := msteps 20 (MSt.init d f g)
    let b := msteps 20 (MSt.init a.d a.f a.g)
    let c := msteps 19 (MSt.init b.d b.f b.g)
    msteps 59 (MSt.init d f g) =
      ⟨c.d,c.f,c.g,
       c.u*(b.u*a.u+b.v*a.q)+c.v*(b.q*a.u+b.r*a.q),
       c.u*(b.u*a.v+b.v*a.r)+c.v*(b.q*a.v+b.r*a.r),
       c.q*(b.u*a.u+b.v*a.q)+c.r*(b.q*a.u+b.r*a.q),
       c.q*(b.u*a.v+b.v*a.r)+c.r*(b.q*a.v+b.r*a.r)⟩ := by
  dsimp only
  rw [show (59:Nat)=40+19 by decide,msteps_add,
    show (40:Nat)=20+20 by decide,msteps_add]
  rw [msteps_gen 20 (msteps 20 (MSt.init d f g)),msteps_gen 19]

end VG.Proof.P256.EcdhInverse
