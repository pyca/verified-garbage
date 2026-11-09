module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.ProductMath
import VerifiedGarbage.Proof.Framework.Omega

/-! Pure word arithmetic for the streamed small-constant products. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (value)

theorem cms_addCarry_comm (a b : Word) (c : Bool) : addCarry a b c=addCarry b a c := by
  simp only [addCarry,BitVec.add_comm]

theorem cms_carryOut_comm (a b : Word) (c : Bool) : carryOut a b c=carryOut b a c := by
  simp only [carryOut,Nat.add_comm a.toNat b.toNat]

def cmsChain (a h : Word) (c : Bool) : List Word → List Word
  | [] => [addCarry h 0 c]
  | b::bs => addCarry (a*b) h c :: cmsChain a (mulHi a b) (carryOut (a*b) h c) bs

theorem cmsChain_eq (a h : Word) (c : Bool) (bs : List Word) : cmsChain a h c bs=firstChain a h c bs := by
  induction bs generalizing h c with
  | nil => rfl
  | cons b bs ih => rw [cmsChain,firstChain,cms_addCarry_comm (a*b),cms_carryOut_comm (a*b),ih]

theorem cmsChain_value (a h : Word) (c : Bool) (bs : List Word) (hb : h.toNat+c.toNat<2^64) :
    value (cmsChain a h c bs)=h.toNat+c.toNat+a.toNat*value bs := by
  rw [cmsChain_eq]
  exact firstChain_value a bs h c hb

theorem cmsChain_length (a h : Word) (c : Bool) (bs : List Word) : (cmsChain a h c bs).length=bs.length+1 := by
  induction bs generalizing h c with
  | nil => rfl
  | cons b bs ih => simp only [cmsChain,List.length_cons,ih]

end VG.Proof.Mont.AArch64.P521Field
