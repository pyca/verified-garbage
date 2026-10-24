module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Controls
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Select
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
public import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
import VerifiedGarbage.Proof.Framework.Omega

/-! The same Montgomery residues and bounds used by RSA, with a fixed-base exponent. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure Parameters where
 B : Addr
 Z : Nat
 w : Nat
 mi : BitVec 64
 P : Nat
 G : Nat
 N : Nat
 k : Nat
 src : Addr
 ctx : Addr
 table : Addr
 room : slot w 8≤Z
 positive : 2≤w
 width : w<2^31
 modulusPositive : 1<P
 coprime : Nat.Coprime (2^(64*w)) P

structure ModState (p : Parameters) (s : State) : Prop where
 good : Good s p.B p.Z p.w p.mi
 modulus : wv s.mem p.B (slot p.w 0) p.w=p.P
 inverse : ((word s.mem p.B (slot p.w 0)).toNat*p.mi.toNat+1)%2^64=0
 one : wv s.mem p.B (slot p.w 7) p.w=1
 r2 : wv s.mem p.B (slot p.w 4) p.w=2^(128*p.w)%p.P

structure Power (p : Parameters) (E : Nat) (s : State) : Prop extends ModState p s where
 bound : wv s.mem p.B (slot p.w 6) p.w<p.P
 value : wv s.mem p.B (slot p.w 6) p.w=Spec.Rsa.powMod p.G E p.P*2^(64*p.w)%p.P

theorem ModState.after_arrays {p : Parameters} {s t : State} {js : List Nat}
 (h : ModState p s) (good : Good t p.B p.Z p.w p.mi) (frame : Arrays p.B p.w js s.mem t.mem)
 (zero : 0∉js) (one : 7∉js) (r2 : 4∉js) : ModState p t := by
 have nowrap : p.B.toNat+slot p.w 8≤2^64 := by have := h.good.scr.nowrap;have := p.room;omega
 refine ⟨good,?_,?_,?_,?_⟩
 · exact (frame.wv_of_not_mem (by decide) zero nowrap).trans h.modulus
 · rw [frame.word0_of_not_mem (by decide) zero nowrap (by have := p.positive;omega)]
   exact h.inverse
 · exact (frame.wv_of_not_mem (by decide) one nowrap).trans h.one
 · exact (frame.wv_of_not_mem (by decide) r2 nowrap).trans h.r2

theorem ModState.after_header {p : Parameters} {s t : State} {i : Nat}
 (h : ModState p s) (good : Good t p.B p.Z p.w p.mi)
 (frame : Outside p.B (8*i) 8 s.mem t.mem) (hi : i<32) : ModState p t := by
 have nowrap : slot p.w 8≤2^64 := by have := h.good.scr.nowrap;have := p.room;omega
 have below (j : Nat) : 8*i+8≤slot p.w j := hdr_lt_slot _ _ hi
 refine ⟨good,?_,?_,?_,?_⟩
 · exact (frame.wv (Or.inr (below 0)) (by have := slot_le (w:=p.w) (by decide : 0<8);omega)).trans h.modulus
 · rw [frame.word (Or.inr (below 0)) (by have := slot_le (w:=p.w) (by decide : 0<8);omega)]
   exact h.inverse
 · exact (frame.wv (Or.inr (below 7)) (by have := slot_le (w:=p.w) (by decide : 7<8);omega)).trans h.one
 · exact (frame.wv (Or.inr (below 4)) (by have := slot_le (w:=p.w) (by decide : 4<8);omega)).trans h.r2

theorem Power.after_arrays {p : Parameters} {E : Nat} {s t : State} {js : List Nat}
 (h : Power p E s) (good : Good t p.B p.Z p.w p.mi) (frame : Arrays p.B p.w js s.mem t.mem)
 (zero : 0∉js) (one : 7∉js) (r2 : 4∉js) (y : 6∉js) : Power p E t := by
 have nowrap : p.B.toNat+slot p.w 8≤2^64 := by have := h.good.scr.nowrap;have := p.room;omega
 have same := frame.wv_of_not_mem (by decide : 6<8) y nowrap
 exact ⟨h.toModState.after_arrays good frame zero one r2,by rw [same];exact h.bound,by rw [same];exact h.value⟩

theorem Power.after_header {p : Parameters} {E : Nat} {s t : State} {i : Nat}
 (h : Power p E s) (good : Good t p.B p.Z p.w p.mi)
 (frame : Outside p.B (8*i) 8 s.mem t.mem) (hi : i<32) : Power p E t := by
 have nowrap : slot p.w 8≤2^64 := by have := h.good.scr.nowrap;have := p.room;omega
 have same : wv t.mem p.B (slot p.w 6) p.w=wv s.mem p.B (slot p.w 6) p.w :=
  frame.wv (Or.inr (hdr_lt_slot _ _ hi)) (by have := slot_le (w:=p.w) (by decide : 6<8);omega)
 exact ⟨h.toModState.after_header good frame hi,by rw [same];exact h.bound,by rw [same];exact h.value⟩

/-- One genuine Montgomery square doubles the encoded exponent. -/
theorem power_square (M : Mont) {p : Parameters} {E : Nat} {s : State} (h : Power p E s) :
 WP isa (M.mm 6 6 6) s fun t =>
 Power p (2*E) t ∧ Arrays p.B p.w [2,3,6] s.mem t.mem ∧ Keep mmRegs s t := by
 refine WP.mono (crtMmN_ok M h.good p.room p.positive p.width (by decide : 6<8)
  (by decide : 6<8) (by decide : 6<8) (by decide) (by decide) (by decide) (by decide) (by decide)
  h.modulus h.inverse h.bound) ?_
 rintro t ⟨goodT,modulusT,inverseT,boundT,productT,frame,rest⟩
 have modT := h.toModState.after_arrays goodT frame (by decide) (by decide) (by decide)
 have valueT := VG.Proof.Rsa.FixedBaseComb.mont_square_encoded p.coprime boundT h.value productT
 exact ⟨⟨modT,boundT,valueT⟩,frame,rest⟩

/-- A selected residue adds its canonical comb exponent. -/
theorem power_product (M : Mont) {p : Parameters} {E F : Nat} {s : State} (h : Power p E s)
 (selected : wv s.mem p.B (slot p.w 5) p.w=Spec.Rsa.powMod p.G F p.P*2^(64*p.w)%p.P) :
 WP isa (M.mm 6 6 5) s fun t =>
 Power p (E+F) t ∧ Arrays p.B p.w [2,3,6] s.mem t.mem ∧ Keep mmRegs s t := by
 have bound5 : wv s.mem p.B (slot p.w 5) p.w<p.P := by rw [selected];exact Nat.mod_lt _ (by have := p.modulusPositive;omega)
 refine WP.mono (crtMmN_ok M h.good p.room p.positive p.width (by decide : 6<8)
  (by decide : 6<8) (by decide : 5<8) (by decide) (by decide) (by decide) (by decide) (by decide)
  h.modulus h.inverse bound5) ?_
 rintro t ⟨goodT,modulusT,inverseT,boundT,productT,frame,rest⟩
 have modT := h.toModState.after_arrays goodT frame (by decide) (by decide) (by decide)
 have valueT := VG.Proof.Rsa.FixedBaseComb.mont_product_encoded p.coprime boundT h.value selected productT
 exact ⟨⟨modT,boundT,valueT⟩,frame,rest⟩

end VG.Proof.Ffdh.AArch64.Cached
