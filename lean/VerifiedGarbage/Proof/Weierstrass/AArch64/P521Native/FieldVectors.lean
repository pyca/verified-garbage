module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FieldMul
public import VerifiedGarbage.Proof.Mont.AArch64.P521Linear
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.OrdinaryUpdate
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSaves

-- separate module: Generic no-vector-write checks for the linear instruction generators cost 2.12s proof work versus 0.38s imports; retaining this kernel computation prevents repeating it for field-step composition edits.

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass

theorem field_prime_relation : fieldPrime+1=512*(2^64)^8 := by
  dsimp only [fieldPrime]
  rw [VG.Proof.Mont.AArch64.P521Square.prime_value]

theorem field_add_ok {base : Addr} {W : Nat} {s : State} {loc : Nat → Nat} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat} {o a b : Nat}
    (hs : Scr s base W) (inv : OrdinaryInv base fieldPrime loc V E caps s)
    (readA : a∈V) (readB : b∈V) (capA : caps a=1) (capB : caps b=1)
    (outFits : loc o+72≤W) (inputFits : ∀x∈V,loc x+72≤W)
    (aligned : ∀x∈o::V,loc x%8=0)
    (apart : ∀x∈V,x≠o → loc x+72≤loc o ∨ loc o+72≤loc x) :
    WP isa (.block (VG.Impl.Mont.AArch64.P521Linear.add (loc o) (loc a) (loc b))) s fun t =>
      OrdinaryInv base fieldPrime loc (o::V) (Function.update E o (E a+E b)) (Function.update caps o 1) t ∧
      Scr t base W ∧ KeepRegs (clob 9) s t ∧ Outside base (loc o) 72 s.mem t.mem := by
  have ba := inv.bound a readA
  have bb := inv.bound b readB
  rw [capA,Nat.one_mul] at ba
  rw [capB,Nat.one_mul] at bb
  refine WP.mono (P521Linear.add_ok hs outFits (inputFits a readA) (inputFits b readB)
    (aligned o (by simp)) (aligned a (by simp [readA])) (aligned b (by simp [readB]))
    field_prime_relation (by omega_arith)) fun t ⟨value,bound,k,outside⟩ => ?_
  have ni := inv.add_update readA readB outside apart
    (fun x hx => by have h:=inputFits x hx; have e:=hs.enc; omega_arith)
    (cap:=1) (by simpa only [Nat.one_mul] using bound) value
  exact ⟨ni,hs.of_keepRegs k (by decide),k,outside⟩

theorem field_sub_ok {base : Addr} {W : Nat} {s : State} {loc : Nat → Nat} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat} {o a b : Nat}
    (hs : Scr s base W) (inv : OrdinaryInv base fieldPrime loc V E caps s)
    (readA : a∈V) (readB : b∈V) (capA : caps a=1) (capB : caps b=1)
    (outFits : loc o+72≤W) (inputFits : ∀x∈V,loc x+72≤W)
    (aligned : ∀x∈o::V,loc x%8=0)
    (apart : ∀x∈V,x≠o → loc x+72≤loc o ∨ loc o+72≤loc x) :
    WP isa (.block (VG.Impl.Mont.AArch64.P521Linear.sub (loc o) (loc a) (loc b))) s fun t =>
      OrdinaryInv base fieldPrime loc (o::V) (Function.update E o (E a-E b)) (Function.update caps o 1) t ∧
      Scr t base W ∧ KeepRegs (clob 9) s t ∧ Outside base (loc o) 72 s.mem t.mem := by
  have ba := inv.bound a readA
  have bb := inv.bound b readB
  rw [capA,Nat.one_mul] at ba
  rw [capB,Nat.one_mul] at bb
  refine WP.mono (P521Linear.sub_ok hs outFits (inputFits a readA) (inputFits b readB)
    (aligned o (by simp)) (aligned a (by simp [readA])) (aligned b (by simp [readB]))
    field_prime_relation ba bb) fun t ⟨value,bound,k,outside⟩ => ?_
  have ni := inv.sub_update readA readB outside apart
    (fun x hx => by have h:=inputFits x hx; have e:=hs.enc; omega_arith)
    (cap:=1) (by simpa only [Nat.one_mul] using bound) (by omega_arith) value
  exact ⟨ni,hs.of_keepRegs k (by decide),k,outside⟩

theorem field_cms_ok {base : Addr} {W : Nat} {s : State} {loc : Nat → Nat} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat} {o a b C D : Nat}
    (coeffC : C≤16) (coeffD : D≤16) (hs : Scr s base W) (inv : OrdinaryInv base fieldPrime loc V E caps s)
    (readA : a∈V) (readB : b∈V) (capA : caps a=1) (capB : caps b=1)
    (outFits : loc o+72≤W) (inputFits : ∀x∈V,loc x+72≤W)
    (aligned : ∀x∈o::V,loc x%8=0)
    (apart : ∀x∈V,x≠o → loc x+72≤loc o ∨ loc o+72≤loc x) :
    WP isa (.block (VG.Impl.Mont.AArch64.P521Linear.cms (loc o) C (loc a) D (loc b))) s fun t =>
      OrdinaryInv base fieldPrime loc (o::V) (Function.update E o (VG.Proof.Weierstrass.Cms.smulN C (E a)-VG.Proof.Weierstrass.Cms.smulN D (E b))) (Function.update caps o 1) t ∧
      Scr t base W ∧ KeepRegs (clob 9) s t ∧ Outside base (loc o) 72 s.mem t.mem := by
  have ba := inv.bound a readA
  have bb := inv.bound b readB
  rw [capA,Nat.one_mul] at ba
  rw [capB,Nat.one_mul] at bb
  refine WP.mono (P521Linear.cms_ok hs outFits (inputFits a readA) (inputFits b readB)
    (aligned o (by simp)) (aligned a (by simp [readA])) (aligned b (by simp [readB]))
    field_prime_relation coeffC coeffD ba bb) fun t ⟨value,bound,k,outside⟩ => ?_
  have valueCanon : wordsVal t.mem base (loc o) 9=(C*wordsVal s.mem base (loc a) 9+D*(fieldPrime-wordsVal s.mem base (loc b) 9))%fieldPrime := by
    simpa only [Nat.mul_comm] using value
  have ni := inv.cms_update readA readB outside apart
    (fun x hx => by have h:=inputFits x hx; have e:=hs.enc; omega_arith)
    (cap:=1) (by simpa only [Nat.one_mul] using bound) C D (Nat.le_of_lt bb) valueCanon
  exact ⟨ni,hs.of_keepRegs k (by decide),k,outside⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Mont.AArch64

 theorem field_add_novec (o a b : Nat) :
    ∀i∈P521Linear.add o a b,vdstOf i=none := by
  simp [P521Linear.add,P521Linear.addInit,P521Linear.canonicalStore,P521Linear.canonicalPrefix,
    P521Linear.correctStore,P521Linear.regs,low,acc,loads,chain,zero7,ld,st,vdstOf]

 theorem field_sub_novec (o a b : Nat) :
    ∀i∈P521Linear.sub o a b,vdstOf i=none := by
  simp [P521Linear.sub,P521Linear.maskStoreTop,P521Linear.correctStore,
    P521Linear.regs,low,acc,loads,chain,zero7,ld,st,vdstOf]

 theorem field_cms_novec (o C a D b : Nat) :
    ∀i∈P521Linear.cms o C a D b,vdstOf i=none := by
  simp [P521Linear.cms,P521Linear.cmsInit,P521Linear.cmsRows,P521Linear.cmsRow,P521Linear.cmsMul,
    P521Linear.cmsComplement,P521Linear.cmsFold,P521Linear.cmsFoldPrefix,
    P521Linear.canonicalStore,P521Linear.canonicalPrefix,P521Linear.correctStore,
    P521Linear.regs,low,acc,ld,st,vdstOf]

end VG.Proof.Weierstrass.AArch64.P521Native
