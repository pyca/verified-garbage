module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ReadEnv
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.MontgomeryOne
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Stable

/-! Initialize Montgomery one from the cached R²; no initial scratch value is assumed. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure Initial (p : Parameters) (bs : List Byte) (s : State) : Prop extends FieldInitial p s where
 controls : Controls p.B p.src p.ctx bs.length p.N s
 reads : ReadEnv p bs s

theorem initial_power (M : Mont) {p : Parameters} {bs : List Byte} {s : State} (h : Initial p bs s) :
 WP isa (.seq (const 7 1) (M.mm 6 4 7)) s fun t =>
 Power p 0 t ∧ Controls p.B p.src p.ctx bs.length p.N t ∧ ReadEnv p bs t ∧
 StableHeader p.B s.mem t.mem ∧ Keep mmRegs s t := by
 refine WP.mono (field_initial_power M h.toFieldInitial) ?_
 rintro t ⟨power,frame,rest⟩
 exact ⟨power,h.controls.after_arrays frame,h.reads.after_arrays frame rest (by simp),
  StableHeader.of_arrays frame,rest⟩

end VG.Proof.Ffdh.AArch64.Cached
