module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Step
import VerifiedGarbage.Proof.Framework.Omega

/-! Functional boundaries shared by the complete correctness and timing compositions. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem Running.after_mem {p : Parameters} {bs : List Byte} {E i : Nat} {s t : State}
 (h : Running p bs E i s) (mem : t.mem=s.mem) (rest : Keep mmRegs s t) : Running p bs E i t := by
 have frame : Arrays p.B p.w [] s.mem t.mem := fun x _ => by rw [mem]
 have good := good_after_arrays h.power.good frame rest ((rest.gpr .x0 (by decide)).trans h.power.good.x0)
 have power := h.power.after_arrays good frame (by simp) (by simp) (by simp) (by simp)
 exact h.after_arrays power frame rest (by simp)

theorem running_square (M : Mont) {p : Parameters} {bs : List Byte} {E i : Nat} {s : State}
 (h : Running p bs E i s) : WP isa (M.mm 6 6 6) s fun t =>
 Running p bs (2*E) i t :=
 WP.mono (power_square M h.power) fun _ ⟨power,frame,rest⟩ => h.after_arrays power frame rest (by simp)

theorem running_digit {p : Parameters} {bs : List Byte} {E i : Nat} {s : State}
 (h : Running p bs E (i+1) s) (size : bs.length<2^31) (widthBound : p.N≤8*bs.length)
 (positions : i+5*Spec.Rsa.FixedBaseComb.rows p.N<2^63) (bound : Spec.Rsa.os2ip bs<2^p.N) :
 WP isa Comb.digit s fun t =>
 Running p bs E (i+1) t ∧
 word t.mem p.B (8*sD)=BitVec.ofNat 64 (VG.Proof.Rsa.FixedBaseComb.digit p.N (Spec.Rsa.os2ip bs) i) := by
 refine WP.mono (digit_ok h.power.good p.room h.controls h.counter h.reads.source size widthBound positions bound) ?_
 rintro t ⟨good,controls,counter,digit,frame,rest⟩
 exact ⟨⟨h.power.after_header good frame (by decide),controls,counter,
  (header_other frame (by decide) (by decide) (by decide)).trans h.tablePointer,
  h.reads.after_header frame rest (by decide)⟩,digit⟩

theorem running_select {p : Parameters} {bs : List Byte} {E i v : Nat} {s : State}
 (h : Running p bs E i s) (hv : v<32) (digit : word s.mem p.B (8*sD)=BitVec.ofNat 64 v) :
 WP isa Comb.select s fun t =>
 Running p bs E i t ∧ wv t.mem p.B (slot p.w 5) p.w=
  Spec.Rsa.powMod p.G (Spec.Rsa.FixedBaseComb.exponent p.N v) p.P*2^(64*p.w)%p.P := by
 refine WP.mono (select_ok h.power.good p.room (by have := p.positive;omega) p.width hv h.tablePointer digit
  h.reads.tableRead h.reads.tableOutside) ?_
 rintro t ⟨good,selected,frame,rest⟩
 have power := h.power.after_arrays good frame (by decide) (by decide) (by decide) (by decide)
 exact ⟨h.after_arrays power frame rest (by simp),selected.trans (h.reads.table v hv)⟩

theorem running_product (M : Mont) {p : Parameters} {bs : List Byte} {E F i : Nat} {s : State}
 (h : Running p bs E i s)
 (selected : wv s.mem p.B (slot p.w 5) p.w=Spec.Rsa.powMod p.G F p.P*2^(64*p.w)%p.P) :
 WP isa (M.mm 6 6 5) s fun t => Running p bs (E+F) i t :=
 WP.mono (power_product M h.power selected) fun _ ⟨power,frame,rest⟩ => h.after_arrays power frame rest (by simp)

end VG.Proof.Ffdh.AArch64.Cached
