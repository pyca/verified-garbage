module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.TapeLoop
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Reset, retry-status checking, and exhaustion in the persistent tape frame. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Bignum (Outside writeW_outside)
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.Bignum.AArch64 VG.Impl.Dsa.AArch64.Generation

theorem tapeReset_frame_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (slots : TapeSlots)
    (hu : slots.used < 34) (hu12 : slots.used ≠ 12) :
    WP isa (.block (tapeReset slots)) s fun t =>
      Lay t F S ∧ Rep t.mem F S V (upd W slots.used 0) ∧
      Outside F (8 * slots.used) 8 s.mem t.mem ∧ Keep [.x0, .x15] s t := by
  refine WP.mono (WP.keep [.x0, .x15] (Q := fun t =>
    t.mem = s.mem.writeW (off F (8 * slots.used)) (0 : BitVec 64)) (by
    unfold tapeReset Impl.Dsa.AArch64.Random.store
    brun [exec_addSp (show 8 * slots.used < 4096 by omega), L.sp,
      L.st (d := 8 * slots.used) (n := 8) (by unfold frameBytes; omega)]
    rfl) rfl rfl rfl) fun t ⟨hm, hk⟩ => ?_
  have Rt : Rep t.mem F S V (upd W slots.used 0) := by
    rw [hm]; exact R.wf L.geo hu _
  refine ⟨lay_of_rep L R Rt (by simp [upd, Ne.symm hu12]) hk.sp hk.wr, Rt, ?_, hk⟩
  rw [hm]
  exact writeW_outside _ _ _ (by omega)

theorem tapeStatus_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) :
    WP isa (.block tapeStatus) s fun t =>
      eval (.zero .x .x0) t = some (W 19 == (3#64)) ∧ t.mem = s.mem ∧ Keep [.x0] s t := by
  have hw : s.mem.readW (F + BitVec.ofNat 64 152) 64 = W 19 := R.fr 19 (by decide)
  refine WP.mono (WP.keep [.x0] (Q := fun t =>
    eval (.zero .x .x0) t = some (W 19 == (3#64)) ∧ t.mem = s.mem) (by
    unfold tapeStatus
    brun [exec_ldrSp (off := 152) (by decide), L.sp,
      L.ld (d := 152) (n := 8) (by decide), hw, eval]
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, beq_iff_eq, BitVec.sub_eq_iff_eq_add]
    change W 19 = (3#64) ↔ W 19 = (3#64)
    rfl) rfl rfl rfl) fun _ ⟨⟨hz, hm⟩, hk⟩ => ⟨hz, hm, hk⟩

theorem tapeExhausted_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) :
    WP isa (.block ([movi .x0 3] ++ Impl.Dsa.AArch64.Random.store 152 .x0 ++ [movi .x0 1])) s fun t =>
      eval (.zero .x .x0) t = some false ∧ Lay t F S ∧ Rep t.mem F S V (upd W 19 3) ∧
      Outside F 152 8 s.mem t.mem ∧ Keep [.x0, .x15] s t := by
  refine WP.mono (WP.keep [.x0, .x15] (Q := fun t =>
    eval (.zero .x .x0) t = some false ∧ t.mem = s.mem.writeW (off F 152) (3 : BitVec 64)) (by
    unfold Impl.Dsa.AArch64.Random.store
    brun [exec_addSp (show 152 < 4096 by decide), L.sp,
      L.st (d := 152) (n := 8) (by decide), eval]
    rfl) rfl rfl rfl) fun t ⟨⟨hz, hm⟩, hk⟩ => ?_
  have Rt : Rep t.mem F S V (upd W 19 3) := by
    rw [hm]; exact R.wf L.geo (by decide : 19 < nW) _
  refine ⟨hz, lay_of_rep L R Rt (by simp [upd]) hk.sp hk.wr, Rt, ?_, hk⟩
  rw [hm]; exact writeW_outside _ _ _ (by decide)

end VG.Proof.Dsa.AArch64.Generation
