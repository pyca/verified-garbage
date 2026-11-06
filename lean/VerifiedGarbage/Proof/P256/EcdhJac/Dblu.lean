module

public import VerifiedGarbage.Proof.P256.EcdhJac.TableMath
public import VerifiedGarbage.Proof.P256.EcdhJac.DbluCertificate
import VerifiedGarbage.Proof.P256.EcdhJac.ZadduCertificate
import VerifiedGarbage.Proof.P256.EcdhJac.Frame
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.P256.EcdhJac.State
import VerifiedGarbage.Proof.Weierstrass.JacMadd
import VerifiedGarbage.Proof.Weierstrass.WinJacMath

@[expose] public section

/-! ## `Dblu` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

 theorem tbl_val {N : List FOp} {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl (validAfter (N.map (FOp.rename tblσ)) V)
      (runOps (N.map (FOp.rename tblσ)) E) s)
    (he : ∀i,runOps (N.map (FOp.rename tblσ)) E (tblσ i)=runOps N (fun j => E (tblσ j)) i)
    {i : Nat} (ho : i∈N.map FOp.out) :
    tmv C 4 base s (tblσ i)=runOps N (fun j => E (tblσ j)) i ∧ wordsVal s.mem base (tblσ i) 4<C.p := by
  have hv : tblσ i∈validAfter (N.map (FOp.rename tblσ)) V := by
    rw [mem_validAfter]
    right
    obtain ⟨op,hop,rfl⟩ := List.mem_map.mp ho
    exact List.mem_map.mpr ⟨FOp.rename tblσ op,List.mem_map_of_mem hop,FOp.out_rename ..⟩
  exact ⟨(hi.val _ hv).trans (he i),hi.lt _ hv⟩

 theorem tblFrame {base : Addr} {s t : State} (hk : ProgKeep M base tblW s t) : Frame base work s t :=
  AllocatedFrame.of_prog hk clob_regs (by decide +kernel)

end VG.Proof.P256.EcdhJac

end
