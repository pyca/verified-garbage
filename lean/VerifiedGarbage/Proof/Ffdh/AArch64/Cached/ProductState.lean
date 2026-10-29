module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BuildFrame
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.WorkspaceState
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Basis

import VerifiedGarbage.Proof.Framework.Omega
/-! The invariant for filling the subsets containing one new comb tooth. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/BasisProduct.lean`, which only this module imported.
section

/-! Adding one precomputed tooth to an already constructed subset entry. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem basis_product (M : Mont) {p : Parameters} {s : State} {E F : Nat} (h : Basis p E s)
 (selected : wv s.mem p.B (slot p.w 1) p.w=Spec.Rsa.powMod p.G F p.P*2^(64*p.w)%p.P) :
 WP isa (M.mm 6 5 1) s fun t =>
 Power p (E+F) t ∧ Basis p E t ∧ Arrays p.B p.w [2,3,6] s.mem t.mem ∧ Keep mmRegs s t := by
 have bound1 : wv s.mem p.B (slot p.w 1) p.w<p.P := by
  rw [selected];exact Nat.mod_lt _ (by have := p.modulusPositive;omega)
 refine WP.mono (crtMmN_ok M h.good p.room p.positive p.width (by decide : 6<8)
  (by decide : 5<8) (by decide : 1<8) (by decide) (by decide) (by decide) (by decide) (by decide)
  h.modulus h.inverse bound1) ?_
 rintro t ⟨good,_,_,bound,product,frame,rest⟩
 have mod := h.toModState.after_arrays good frame (by decide) (by decide) (by decide)
 have value := VG.Proof.Rsa.FixedBaseComb.mont_product_encoded p.coprime bound h.value selected product
 exact ⟨⟨mod,bound,value⟩,h.after_arrays good frame (by decide) (by decide) (by decide) (by decide),frame,rest⟩

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure ProductState (p : Parameters) (b j : Nat) (s : State) : Prop where
 tooth : b<5
 position : 1≤j ∧ j≤2^b
 basis : Basis p (2^(b*Spec.Rsa.FixedBaseComb.rows p.N)) s
 space : ContextSpace p s
 context : word s.mem p.B (8*sCtx)=p.ctx
 basisIndex : word s.mem p.B (8*sD)=BitVec.ofNat 64 (2^b)
 index : word s.mem p.B (8*sJ)=BitVec.ofNat 64 j
 table : TablePrefix p (2^b+j) s
 rows : word s.mem p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N)

theorem ProductState.limit {p : Parameters} {b j : Nat} {s : State} (h : ProductState p b j s) : 2^b+j≤32 := by
 have bound : 2^b≤16 := Nat.pow_le_pow_right (by decide) (show b≤4 by have := h.tooth;omega)
 have := h.position
 omega

theorem ProductState.after_arrays {p : Parameters} {b j : Nat} {s t : State} {js : List Nat}
 (h : ProductState p b j s) (basis : Basis p (2^(b*Spec.Rsa.FixedBaseComb.rows p.N)) t)
 (frame : Arrays p.B p.w js s.mem t.mem) (rest : Keep mmRegs s t) (within : ∀ a∈js,a<8) : ProductState p b j t :=
 ⟨h.tooth,h.position,basis,h.space.after rest,(arrays_header frame (by decide)).trans h.context,
  (arrays_header frame (by decide)).trans h.basisIndex,(arrays_header frame (by decide)).trans h.index,
  h.table.after_inscr h.space h.limit (InScr.of_arrays frame p.room within),
  (arrays_header frame (by decide)).trans h.rows⟩

end VG.Proof.Ffdh.AArch64.Cached
