module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PowerState
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Initialize Montgomery one, shared by context creation and cached exponentiation. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure FieldInitial (p : Parameters) (s : State) : Prop where
 good : Good s p.B p.Z p.w p.mi
 modulus : wv s.mem p.B (slot p.w 0) p.w=p.P
 inverse : ((word s.mem p.B (slot p.w 0)).toNat*p.mi.toNat+1)%2^64=0
 r2 : wv s.mem p.B (slot p.w 4) p.w=2^(128*p.w)%p.P

theorem field_initial_power (M : Mont) {p : Parameters} {s : State} (h : FieldInitial p s) :
 WP isa (.seq (const 7 1) (M.mm 6 4 7)) s fun t =>
 Power p 0 t ∧ Arrays p.B p.w [7,2,3,6] s.mem t.mem ∧ Keep mmRegs s t := by
 rw [WP.seq_iff]
 refine WP.mono (const_ok h.good p.room (by have := p.positive;omega) p.width
  (by decide : 7<8) (by decide : 1<2^16)) ?_
 rintro u ⟨goodU,oneU,frameU,keepU⟩
 have arraysU : Arrays p.B p.w [7] s.mem u.mem := Arrays.of_outside (j:=7) (by simp) frameU (by omega) (by omega)
 have nowrap : p.B.toNat+slot p.w 8≤2^64 := by have := h.good.scr.nowrap;have := p.room;omega
 have modU : ModState p u := by
  refine ⟨goodU,(arraysU.wv_of_not_mem (by decide) (by decide) nowrap).trans h.modulus,?_,oneU,?_⟩
  · rw [arraysU.word0_of_not_mem (by decide) (by decide) nowrap (by have := p.positive;omega)]
    exact h.inverse
  · exact (arraysU.wv_of_not_mem (by decide) (by decide) nowrap).trans h.r2
 have bound7 : wv u.mem p.B (slot p.w 7) p.w<p.P := by rw [oneU];exact p.modulusPositive
 refine WP.mono (crtMmN_ok M goodU p.room p.positive p.width (by decide : 6<8)
  (by decide : 4<8) (by decide : 7<8) (by decide) (by decide) (by decide) (by decide) (by decide)
  modU.modulus modU.inverse bound7) ?_
 rintro t ⟨goodT,modulusT,inverseT,boundT,productT,frameT,keepT⟩
 have modT := modU.after_arrays goodT frameT (by decide) (by decide) (by decide)
 have r2Eq : 2^(128*p.w)=2^(64*p.w)*2^(64*p.w) := by
  rw [←Nat.pow_add]
  congr 1
  omega
 have eq : wv t.mem p.B (slot p.w 6) p.w*2^(64*p.w)%p.P=
  2^(64*p.w)*2^(64*p.w)%p.P := by
  simpa only [modU.r2,modU.one,Nat.mul_one,Nat.mod_mod,r2Eq] using productT
 have cancel := VG.Proof.Bignum.mont_cancel p.coprime eq
 rw [Nat.mod_eq_of_lt boundT] at cancel
 have encoded : wv t.mem p.B (slot p.w 6) p.w=Spec.Rsa.powMod p.G 0 p.P*2^(64*p.w)%p.P := by
  simpa only [VG.Proof.Bignum.powMod_eq,Nat.pow_zero,Nat.mod_eq_of_lt p.modulusPositive,Nat.one_mul] using cancel
 have frame : Arrays p.B p.w [7,2,3,6] s.mem t.mem :=
  (arraysU.mono (by simp)).trans (frameT.mono (by simp [Public.aAcc,Public.aTmp]))
 exact ⟨⟨modT,boundT,encoded⟩,frame,(keepU.trans keepT).mono (by decide)⟩

end VG.Proof.Ffdh.AArch64.Cached
