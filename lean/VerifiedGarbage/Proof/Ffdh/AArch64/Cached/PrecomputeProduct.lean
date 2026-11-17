module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeProductIO
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Layout
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BuildFrame
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.WorkspaceState
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Basis

/-! ### `Ffdh.AArch64.Cached.ProductState`, which this module and modules that import it used -/

section

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
  rw [selected];exact Nat.mod_lt _ (by have := p.modulusPositive;omega_using [this])
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
 have bound : 2^b≤16 := Nat.pow_le_pow_right (by decide) (show b≤4 by have := h.tooth;omega_using [this])
 have := h.position
 omega_using [bound, this]

theorem ProductState.after_arrays {p : Parameters} {b j : Nat} {s t : State} {js : List Nat}
 (h : ProductState p b j s) (basis : Basis p (2^(b*Spec.Rsa.FixedBaseComb.rows p.N)) t)
 (frame : Arrays p.B p.w js s.mem t.mem) (rest : Keep mmRegs s t) (within : ∀ a∈js,a<8) : ProductState p b j t :=
 ⟨h.tooth,h.position,basis,h.space.after rest,(arrays_header frame (by decide)).trans h.context,
  (arrays_header frame (by decide)).trans h.basisIndex,(arrays_header frame (by decide)).trans h.index,
  h.table.after_inscr h.space h.limit (InScr.of_arrays frame p.room within),
  (arrays_header frame (by decide)).trans h.rows⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Construct one new subset entry with the shared Montgomery product. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/ProductCounter.lean`, which only this module imported.
section

/-! Advance the public subset index and compare it with the next tooth's table index. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem productCounter_ok {s : State} {B : Addr} {Z w j d : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z)
 (index : word s.mem B (8*sJ)=BitVec.ofNat 64 j) (basis : word s.mem B (8*sD)=BitVec.ofNat 64 d) :
 WP isa (.block Precompute.productNext) s fun t =>
 Good t B Z w mi ∧ word t.mem B (8*sJ)=BitVec.ofNat 64 (j+1) ∧
 t.gpr .x3=BitVec.ofNat 64 (j+1)-BitVec.ofNat 64 d ∧
 Outside B (8*sJ) 8 s.mem t.mem ∧ Keep [.x3,.x4] s t := by
 have increment : BitVec.ofNat 64 j+1#64=BitVec.ofNat 64 (j+1) := (BitVec.ofNat_add _ _).symm
 have frame : Outside B (8*sJ) 8 s.mem (s.mem.writeW (off B (8*sJ)) (BitVec.ofNat 64 (j+1))) :=
  writeW_outside _ _ _ (by decide)
 have basisAfter : word (s.mem.writeW (off B (8*sJ)) (BitVec.ofNat 64 (j+1))) B (8*sD)=BitVec.ofNat 64 d :=
  (frame.word (Or.inl (by decide : 8*sD+8≤8*sJ)) (by decide)).trans basis
 refine WP.mono (WP.keep [.x3,.x4] (Q:=fun t =>
  t.gpr .x3=BitVec.ofNat 64 (j+1)-BitVec.ofNat 64 d ∧
  t.mem=s.mem.writeW (off B (8*sJ)) (BitVec.ofNat 64 (j+1))) ?_ rfl rfl rfl) ?_
 · unfold Precompute.productNext
   brun [good.x0,hdr_enc (show sJ<32 by decide),hdr_enc (show sD<32 by decide),
    header_read good room (show sJ<32 by decide),header_read good room (show sD<32 by decide),
    good.scr.st (d:=8*sJ) (by have := hdr_lt_slot w 8 (show sJ<32 by decide);omega_using [room, this]),index,basisAfter,increment]
 · rintro t ⟨⟨value,mem⟩,rest⟩
   have totalFrame : Outside B (8*sJ) 8 s.mem t.mem := by rw [mem];exact frame
   refine ⟨good_after_header good (by decide) (by decide) totalFrame rest ((rest.gpr .x0 (by decide)).trans good.x0),
    ?_,value,totalFrame,rest⟩
   rw [mem,word_writeW_self]

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem precomputeProduct_ok (M : Mont) {s : State} {p : Parameters} {b j : Nat}
 (h : ProductState p b j s) (more : j<2^b) :
 WP isa (Precompute.product M.mm) s fun t =>
 ProductState p b (j+1) t ∧ t.gpr .x3=BitVec.ofNat 64 (j+1)-BitVec.ofNat 64 (2^b) ∧
 BuildFrame p s.mem t.mem ∧ Keep mmRegs s t := by
 have inside : j<32 := by have := h.limit;omega_using [more, this]
 have destination : j+2^b<32 := by
  have tooth := h.tooth
  have bound : 2^b≤16 := Nat.pow_le_pow_right (by decide) (by omega_using [tooth] : b≤4)
  omega_using [more, bound]
 unfold Precompute.product
 rw [WP.seq_iff]
 refine WP.mono (productLoad_ok h.basis.good h.space h.context h.index inside) ?_
 rintro a ⟨goodA,selectedA,frameA,restA⟩
 have basisA := h.basis.after_arrays goodA frameA (by decide) (by decide) (by decide) (by decide)
 have hA := h.after_arrays basisA frameA restA (by simp)
 have selected : wv a.mem p.B (slot p.w 1) p.w=entryValue p j :=
  selectedA.trans (h.table j (by have := h.position;have := Nat.two_pow_pos b;omega_using [more]))
 rw [WP.seq_iff]
 refine WP.mono (basis_product M basisA selected) ?_
 rintro c ⟨powerC,basisC,frameC,restC⟩
 have hC := hA.after_arrays basisC frameC restC (by simp)
 rw [WP.seq_iff]
 refine WP.mono (productStore_ok basisC.good hC.space hC.context hC.index hC.basisIndex destination) ?_
 rintro d ⟨goodD,valueD,frameD,sameD,restD⟩
 have basisD := basisC.after_workspace goodD sameD
 have contextD := (workspace_header basisC.good sameD (by decide : sCtx<32)).trans hC.context
 have indexD := (workspace_header basisC.good sameD (by decide : sJ<32)).trans hC.index
 have rowsD := (workspace_header basisC.good sameD (by decide : sRows<32)).trans hC.rows
 have toothD := (workspace_header basisC.good sameD (by decide : sD<32)).trans hC.basisIndex
 have exponent : 2^(b*Spec.Rsa.FixedBaseComb.rows p.N)+Spec.Rsa.FixedBaseComb.exponent p.N j=
   Spec.Rsa.FixedBaseComb.exponent p.N (2^b+j) := by
  rw [VG.Proof.Rsa.FixedBaseComb.exponent_add_tooth p.N b j h.tooth more]
  exact Nat.add_comm _ _
 have entry : wv d.mem p.ctx (entryOffset p.w (2^b+j)) p.w=entryValue p (2^b+j) := by
  have value : wv d.mem p.ctx (entryOffset p.w (j+2^b)) p.w=entryValue p (2^b+j) := by
   rw [valueD,powerC.value,exponent]
   rfl
  simpa only [Nat.add_comm j (2^b)] using value
 have tableD : TablePrefix p (2^b+j+1) d := hC.table.extend (by omega_using [destination]) (by
  simpa only [Nat.add_comm j (2^b)] using frameD) entry
 refine WP.mono (productCounter_ok goodD p.room indexD toothD) ?_
 rintro t ⟨goodT,indexT,testT,frameT,restT⟩
 have basisT := basisD.after_header goodT frameT (by decide : sJ<32)
 have tableT := tableD.after_inscr (hC.space.after restD) (by omega_using [destination])
  (InScr.of_outside frameT (by have := hdr_lt_slot p.w 8 (show sJ<32 by decide);have := p.room;omega_arith))
 have stateT : ProductState p b (j+1) t := by
  refine ⟨h.tooth,⟨by omega_using [],by omega_using [more]⟩,basisT,((hC.space.after restD).after restT),
   (header_other frameT (by decide) (by decide) (by decide)).trans contextD,
   (header_other frameT (by decide) (by decide) (by decide)).trans toothD,indexT,?_,
   (header_other frameT (by decide) (by decide) (by decide)).trans rowsD⟩
  simpa only [Nat.add_assoc] using tableT
 have frames : BuildFrame p s.mem t.mem :=
  (((BuildFrame.of_inscr (InScr.of_arrays frameA p.room (by simp))).trans
    (BuildFrame.of_inscr (InScr.of_arrays frameC p.room (by simp)))).trans
    (BuildFrame.of_entry destination frameD)).trans
    (BuildFrame.of_inscr (InScr.of_outside frameT (by have := hdr_lt_slot p.w 8 (show sJ<32 by decide);have := p.room;omega_arith)))
 exact ⟨stateT,testT,frames,(((restA.trans restC).trans restD).trans restT).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached
