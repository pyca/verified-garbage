module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.TapeLoop
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf

/-! # Advance one complete chunk and retain its input pointer -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Dsa.X86_64.Generation

theorem chunkTake_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (slots : TapeSlots) {width used : Nat}
    (hb : slots.base < 37) (hu : slots.used < 37) (hp : slots.pointer < 37)
    (hu14 : slots.used ≠ 14) (hp14 : slots.pointer ≠ 14) (hw : width < 2 ^ 31)
    (hused : W slots.used = BitVec.ofNat 64 used) :
    WP isa (.block (tapeTake slots width)) s fun t =>
      Lay t F S ∧ Rep t.mem F S V
        (upd (upd W slots.pointer (off (W slots.base) used)) slots.used (BitVec.ofNat 64 (used + width))) ∧
      Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.rax, .rcx] s t := by
  have hadd : BitVec.ofNat 64 used + BitVec.ofNat 64 width = BitVec.ofNat 64 (used + width) :=
    (BitVec.ofNat_add _ _).symm
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t =>
      t.mem = (s.mem.writeW (off F (8 * slots.pointer)) (off (W slots.base) used)).writeW
        (off F (8 * slots.used)) (BitVec.ofNat 64 (used + width))) (by
    xrun [tapeTake, ea_sp, L.rsp,
      L.ld (d := 8 * slots.base) (by unfold frameBytes; omega),
      L.ld (d := 8 * slots.used) (by unfold frameBytes; omega),
      L.st (d := 8 * slots.pointer) (by unfold frameBytes; omega),
      L.st (d := 8 * slots.used) (by unfold frameBytes; omega),
      R.slot (d := 8 * slots.base) (k := slots.base) rfl hb rfl,
      R.slot (d := 8 * slots.used) (k := slots.used) rfl hu hused, sx_ofNat hw, hadd]) rfl)
    fun t ⟨hm, hk⟩ => ?_
  have Rt : Rep t.mem F S V
      (upd (upd W slots.pointer (off (W slots.base) used)) slots.used (BitVec.ofNat 64 (used + width))) := by
    rw [hm]
    exact (R.wf L.geo hp _).wf L.geo hu _
  refine ⟨lay_of_rep L R Rt (by simp [upd, Ne.symm hu14, Ne.symm hp14])
    (hk.gpr (by decide)) hk.2.2, Rt, ?_, hk⟩
  have ff : Outside F 0 frameBytes s.mem t.mem := by
    rw [hm]
    exact ((writeW_outside _ F _ (d := 8 * slots.pointer) (by omega)).mono (by omega) (by unfold frameBytes; omega)).trans
      ((writeW_outside _ F _ (d := 8 * slots.used) (by omega)).mono (by omega) (by unfold frameBytes; omega))
  intro a ha
  apply ff a
  right
  have hn := ha ⟨F, frameBytes⟩ (by simp)
  change ¬ ofs F a < frameBytes at hn
  omega

end VG.Proof.Dsa.X86_64.Generation
