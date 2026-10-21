module

public import VerifiedGarbage.Proof.Bignum.Arm.Mac
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Full-word UMAAL facts for the two independent carries of an integrated row. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm VG.Arm.RegUpd VG.Proof.Bignum.Arm

/-- Both outputs use the original input state, even when a source aliases a destination. -/
theorem umaal_ok (s : State) (lo hi a b : Reg) (hne : lo ≠ hi) :
    WP isa (.block [.umaal lo hi a b]) s fun t =>
      (t.gpr lo).toNat + 2^32*(t.gpr hi).toNat =
        (s.gpr a).toNat*(s.gpr b).toNat+(s.gpr lo).toNat+(s.gpr hi).toNat ∧
      MacFrame [lo,hi] s t := by
  let v := (s.gpr a).toNat*(s.gpr b).toNat+(s.gpr hi).toNat+(s.gpr lo).toNat
  let t := (s.setReg lo (BitVec.ofNat 32 v)).setReg hi (BitVec.ofNat 32 (v/2^32))
  refine WP.of_runBlock ⟨t,?_,?_,?_⟩
  · simp only [runBlock_cons,exec,hne,↓reduceIte,runStep_some,runBlock_nil]
    rfl
  · simp only [t,gpr_setReg,hne,↓reduceIte]
    change v%2^32+2^32*((v/2^32)%2^32)=_
    have bound := mac_bound (s.gpr a) (s.gpr b) (s.gpr hi) (s.gpr lo)
    have vb : v<2^64 := by dsimp [v];omega
    rw [Nat.mod_eq_of_lt (show v/2^32<2^32 by omega)]
    dsimp [v]
    omega
  · refine ⟨?_,rfl,rfl,rfl,rfl,rfl,rfl⟩
    intro r hr
    have nl : r≠lo := by intro e;subst r;exact hr (by simp)
    have nh : r≠hi := by intro e;subst r;exact hr (by simp)
    simp only [t,gpr_setReg_of_ne _ _ nh,gpr_setReg_of_ne _ _ nl]

/-- Two UMAALs contribute both carries; their sum may exceed one word. -/
theorem two_products {x a q m z cp cr p cp' out cr' : Nat}
    (hp : p+2^32*cp'=a*x+z+cp)
    (hr : out+2^32*cr'=m*q+p+cr) :
    out+2^32*(cp'+cr')=a*x+m*q+z+cp+cr := by omega

end VG.Proof.Bignum.Arm.Fios
