module

public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Table
public import VerifiedGarbage.Proof.X448.AArch64.Base.Const
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! The immutable table words are radix-2^56 limbs of its checked affine points. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64.Base (limb)

/-- One of the sixteen words of an odd affine entry. -/
theorem baseWord_entry {e w:Nat} (hw:w<16) :
    baseWord (16*e+w)=limb (if w<8 then (Impl.Ed448.PublicTable.entry e).1
      else (Impl.Ed448.PublicTable.entry e).2) (w%8) := by
  have hd:(16*e+w)/16=e:=by omega
  have hm:(16*e+w)%16=w:=by omega
  have h8:(16*e+w)%8=w%8:=by omega
  rw [baseWord,hd,hm,h8]
  rfl

theorem baseWord_bound (i:Nat) : (baseWord i).toNat<2^56 := by
  have he:i=16*(i/16)+i%16:=by omega
  have hv:=baseWord_entry (e:=i/16) (w:=i%16) (Nat.mod_lt _ (by decide))
  rw [←he] at hv
  rw [hv]
  exact VG.Proof.X448.AArch64.Base.limb_lt _ _

end VG.Proof.Ed448.AArch64.Sparse
