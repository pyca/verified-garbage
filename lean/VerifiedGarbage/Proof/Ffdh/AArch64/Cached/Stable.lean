module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Controls

/-! Comb arithmetic changes only its three private workspace control cells. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Impl.Ffdh.AArch64.Cached VG.Proof.Bignum

def StableHeader (B : Addr) (m m' : Mem) : Prop :=
 ∀ i<32, i≠sI → i≠sD → i≠sTab → word m' B (8*i)=word m B (8*i)

theorem StableHeader.refl (B : Addr) (m : Mem) : StableHeader B m m := fun _ _ _ _ _ => rfl

theorem StableHeader.trans {B : Addr} {m1 m2 m3 : Mem}
 (a : StableHeader B m1 m2) (b : StableHeader B m2 m3) : StableHeader B m1 m3 :=
 fun i hi hI hD hT => (b i hi hI hD hT).trans (a i hi hI hD hT)

theorem StableHeader.of_arrays {B : Addr} {w : Nat} {m m' : Mem} {js : List Nat}
 (frame : Arrays B w js m m') : StableHeader B m m' :=
 fun _ hi _ _ _ => arrays_header frame hi

theorem StableHeader.of_control {B : Addr} {i : Nat} {m m' : Mem}
 (frame : Outside B (8*i) 8 m m') (which : i=sI ∨ i=sD ∨ i=sTab) : StableHeader B m m' := by
 intro j hj hI hD hT
 rcases which with rfl | rfl | rfl
 · exact header_other frame (by decide) hj hI
 · exact header_other frame (by decide) hj hD
 · exact header_other frame (by decide) hj hT

end VG.Proof.Ffdh.AArch64.Cached
