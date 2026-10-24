module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PowerState
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Copy
import VerifiedGarbage.Proof.Framework.Omega

/-! A comb tooth's reduced Montgomery residue in array 5. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure Basis (p : Parameters) (E : Nat) (s : State) : Prop extends ModState p s where
 bound : wv s.mem p.B (slot p.w 5) p.w<p.P
 value : wv s.mem p.B (slot p.w 5) p.w=Spec.Rsa.powMod p.G E p.P*2^(64*p.w)%p.P

theorem Basis.after_arrays {p : Parameters} {E : Nat} {s t : State} {js : List Nat}
 (h : Basis p E s) (good : Good t p.B p.Z p.w p.mi) (frame : Arrays p.B p.w js s.mem t.mem)
 (zero : 0∉js) (one : 7∉js) (r2 : 4∉js) (basis : 5∉js) : Basis p E t := by
 have nowrap : p.B.toNat+slot p.w 8≤2^64 := by have := h.good.scr.nowrap;have := p.room;omega
 have same := frame.wv_of_not_mem (by decide : 5<8) basis nowrap
 exact ⟨h.toModState.after_arrays good frame zero one r2,same ▸ h.bound,same.trans h.value⟩

theorem basis_to_power {p : Parameters} {E : Nat} {s : State} (h : Basis p E s) :
 WP isa (copy 6 5) s fun t => Power p E t ∧ Basis p E t ∧ Arrays p.B p.w [6] s.mem t.mem ∧ Keep mmRegs s t := by
 refine WP.mono (copy_ok h.good p.room (by have := p.positive;omega) p.width
  (by decide : 6<8) (by decide : 5<8) (by decide)) ?_
 rintro t ⟨good,value,frame,rest⟩
 have mod := h.toModState.after_arrays good frame (by decide) (by decide) (by decide)
 refine ⟨⟨mod,?_,value.trans h.value⟩,h.after_arrays good frame (by decide) (by decide) (by decide) (by decide),frame,rest⟩
 rw [value];exact h.bound

theorem power_to_basis {p : Parameters} {E : Nat} {s : State} (h : Power p E s) :
 WP isa (copy 5 6) s fun t => Basis p E t ∧ Power p E t ∧ Arrays p.B p.w [5] s.mem t.mem ∧ Keep mmRegs s t := by
 refine WP.mono (copy_ok h.good p.room (by have := p.positive;omega) p.width
  (by decide : 5<8) (by decide : 6<8) (by decide)) ?_
 rintro t ⟨good,value,frame,rest⟩
 have mod := h.toModState.after_arrays good frame (by decide) (by decide) (by decide)
 refine ⟨⟨mod,?_,value.trans h.value⟩,h.after_arrays good frame (by decide) (by decide) (by decide) (by decide),frame,rest⟩
 rw [value];exact h.bound

end VG.Proof.Ffdh.AArch64.Cached
