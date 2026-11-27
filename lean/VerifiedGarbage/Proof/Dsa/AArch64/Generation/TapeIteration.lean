module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.TapeLoop
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! ### `Dsa.AArch64.Generation.TapeState`, which this module and modules that import it used -/

section

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
    brun [exec_addSp (show 8 * slots.used < 4096 by omega_using [hu]), L.sp,
      L.st (d := 8 * slots.used) (n := 8) (by unfold frameBytes; omega_using [hu])]
    rfl) rfl rfl rfl) fun t ⟨hm, hk⟩ => ?_
  have Rt : Rep t.mem F S V (upd W slots.used 0) := by
    rw [hm]; exact R.wf L.geo hu _
  refine ⟨lay_of_rep L R Rt (by simp [upd, Ne.symm hu12]) hk.sp hk.wr, Rt, ?_, hk⟩
  rw [hm]
  exact writeW_outside _ _ _ (by omega_using [hu])

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

end

end

/-! ### `Dsa.AArch64.Generation.ChunkTake`, which this module and modules that import it used -/

section

/-! # Advance one complete chunk and retain its input pointer -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem chunkTake_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (slots : TapeSlots) {width used : Nat}
    (hb : slots.base < 34) (hu : slots.used < 34) (hp : slots.pointer < 34)
    (hu12 : slots.used ≠ 12) (hp12 : slots.pointer ≠ 12) (hw : width < 65536)
    (hused : W slots.used = BitVec.ofNat 64 used) :
    WP isa (.block (tapeTake slots width)) s fun t =>
      Lay t F S ∧ Rep t.mem F S V
        (upd (upd W slots.pointer (VG.Proof.Bignum.off (W slots.base) used)) slots.used (BitVec.ofNat 64 (used + width))) ∧
      Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.x3, .x4, .x5, .x15] s t := by
  have hadd : BitVec.ofNat 64 used + BitVec.ofNat 64 width = BitVec.ofNat 64 (used + width) :=
    (BitVec.ofNat_add _ _).symm
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x15] (Q := fun t =>
      t.mem = (s.mem.writeW (VG.Proof.Bignum.off F (8 * slots.pointer)) (VG.Proof.Bignum.off (W slots.base) used)).writeW
        (VG.Proof.Bignum.off F (8 * slots.used)) (BitVec.ofNat 64 (used + width))) (by
    have himm : (BitVec.ofNat 16 width).setWidth 64 = BitVec.ofNat 64 width := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega_using [hw]
    have hwb : s.mem.readW (F + BitVec.ofNat 64 (8 * slots.base)) 64 = W slots.base := R.fr slots.base hb
    have hwu : s.mem.readW (F + BitVec.ofNat 64 (8 * slots.used)) 64 = BitVec.ofNat 64 used :=
      (R.fr slots.used hu).trans hused
    unfold tapeTake Impl.Dsa.AArch64.Random.store
    brun [exec_ldrSp (off := 8 * slots.base) ⟨by omega_using [], by omega_using [hb]⟩,
      exec_ldrSp (off := 8 * slots.used) ⟨by omega_using [], by omega_using [hu]⟩,
      exec_addSp (show 8 * slots.pointer < 4096 by omega_using [hp]), exec_addSp (show 8 * slots.used < 4096 by omega_using [hu]), L.sp,
      L.ld (d := 8 * slots.base) (n := 8) (by unfold frameBytes; omega_using [hb]),
      L.ld (d := 8 * slots.used) (n := 8) (by unfold frameBytes; omega_using [hu]),
      L.st (d := 8 * slots.pointer) (n := 8) (by unfold frameBytes; omega_using [hp]),
      L.st (d := 8 * slots.used) (n := 8) (by unfold frameBytes; omega_using [hu]), hwb, hwu, himm, hadd]) rfl rfl rfl)
    fun t ⟨hm, hk⟩ => ?_
  have Rt : Rep t.mem F S V
      (upd (upd W slots.pointer (VG.Proof.Bignum.off (W slots.base) used)) slots.used (BitVec.ofNat 64 (used + width))) := by
    rw [hm]
    exact (R.wf L.geo hp _).wf L.geo hu _
  refine ⟨lay_of_rep L R Rt (by simp [upd, Ne.symm hu12, Ne.symm hp12])
    hk.sp hk.wr, Rt, ?_, hk⟩
  have ff : Outside F 0 frameBytes s.mem t.mem := by
    rw [hm]
    exact ((writeW_outside _ F _ (d := 8 * slots.pointer) (by omega_using [hp])).mono (by omega_using []) (by unfold frameBytes; omega_using [hp])).trans
      ((writeW_outside _ F _ (d := 8 * slots.used) (by omega_using [hu])).mono (by omega_using []) (by unfold frameBytes; omega_using [hu]))
  intro a ha
  apply ff a
  right
  have hn := ha ⟨F, frameBytes⟩ (by simp)
  change ¬ ofs F a < frameBytes at hn
  omega_using [hn]

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.ChunkCheck`, which this module and modules that import it used -/

section

/-! Complete-chunk checking from the retained hash-frame representation. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.AArch64.Generation

theorem chunkCheck_frame_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (slots : TapeSlots) {width used total : Nat}
    (ht : slots.total < 34) (hu : slots.used < 34) (hw : width < 65536)
    (hused : W slots.used = BitVec.ofNat 64 used) (htotal : W slots.total = BitVec.ofNat 64 total)
    (hle : used ≤ total) (hmax : total < 2 ^ 64) :
    WP isa (.block (chunkCheck slots width)) s fun t =>
      t.gpr .x0 = (if width ≤ total - used then 0 else 1) ∧ t.mem = s.mem ∧
      Keep [.x0, .x3, .x4, .x5] s t := by
  have hsub : BitVec.ofNat 64 total - BitVec.ofNat 64 used = BitVec.ofNat 64 (total - used) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_using [hle]
  have himm : (BitVec.ofNat 16 width).setWidth 64 = BitVec.ofNat 64 width := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using [hw]
  have hwt : s.mem.readW (F + BitVec.ofNat 64 (8 * slots.total)) 64 = BitVec.ofNat 64 total :=
    (R.fr slots.total ht).trans htotal
  have hwu : s.mem.readW (F + BitVec.ofNat 64 (8 * slots.used)) 64 = BitVec.ofNat 64 used :=
    (R.fr slots.used hu).trans hused
  refine WP.mono (WP.keep [.x0, .x3, .x4, .x5] (Q := fun t =>
    t.gpr .x0 = (if width ≤ total - used then 0 else 1) ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun _ ⟨⟨hc, hm⟩, hk⟩ => ⟨hc, hm, hk⟩
  unfold chunkCheck
  brun [exec_ldrSp (off := 8 * slots.total) ⟨by omega_using [], by omega_using [ht]⟩,
    exec_ldrSp (off := 8 * slots.used) ⟨by omega_using [], by omega_using [hu]⟩, L.sp,
    L.ld (d := 8 * slots.total) (n := 8) (by unfold frameBytes; omega_using [ht]),
    L.ld (d := 8 * slots.used) (n := 8) (by unfold frameBytes; omega_using [hu]), hwt, hwu, hsub, himm,
    subs_ge (show total - used < 2 ^ 64 by omega_using [hmax]) (show width < 2 ^ 64 by omega_using [hw])]
  simp only [decide_eq_true_eq]
  rfl

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Complete native tape iteration, including exhaustion and retry -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.Dsa.AArch64.Generation

/-- Payloads can depend on memory and preserved registers, but not the
comparison's volatile registers or flags. -/
def TapeStable (P : State → Prop) : Prop :=
  ∀ {s t}, P s → t.mem = s.mem → Keep [.x0, .x3, .x4, .x5, .x15] s t → P t

def TapeView (slots : TapeSlots) (F S : Addr) (used total : Nat) (s : State) : Prop :=
  ∃ V W, Lay s F S ∧ Rep s.mem F S V W ∧
    W slots.used = BitVec.ofNat 64 used ∧ W slots.total = BitVec.ofNat 64 total

theorem tapeIteration_ok {slots : TapeSlots} {width total used : Nat} {F S : Addr}
    {body : Prog isa} {I : Nat → State → Prop} {Q : State → Prop}
    (hb : slots.base < 34) (ht : slots.total < 34) (hu : slots.used < 34) (hp : slots.pointer < 34)
    (hu12 : slots.used ≠ 12) (hp12 : slots.pointer ≠ 12)
    (hw : width < 65536) (hmax : total < 2 ^ 64)
    (stable : ∀ n, TapeStable (I n)) (finish : TapeStable Q)
    (view : ∀ n s, I n s → TapeView slots F S n total s)
    (done : ∀ s t V W, I used s → total - used < width →
      Lay s F S → Rep s.mem F S V W →
      Lay t F S → Rep t.mem F S V (upd W 19 3) →
      Outside F 152 8 s.mem t.mem → Keep [.x0, .x15] s t → Q t)
    (step : ∀ s t V W, I used s → width ≤ total - used →
      Lay s F S → Rep s.mem F S V W → W slots.used = BitVec.ofNat 64 used →
      Lay t F S → Rep t.mem F S V
        (upd (upd W slots.pointer (VG.Proof.Bignum.off (W slots.base) used)) slots.used (BitVec.ofNat 64 (used + width))) →
      Frame [⟨F, frameBytes⟩] s.mem t.mem → Keep [.x3, .x4, .x5, .x15] s t →
      WP isa body t fun u => ∃ V' W', Lay u F S ∧ Rep u.mem F S V' W' ∧
        (if W' 19 = 3 then I (used + width) u else Q u))
    {s : State} (hle : used ≤ total) (hi : I used s) :
    WP isa (tapeIteration slots width body) s fun t =>
      (eval (.zero .x .x0) t = some false ∧ Q t) ∨
      (eval (.zero .x .x0) t = some true ∧ I (used + width) t ∧ used + width ≤ total) := by
  obtain ⟨V, W, L, R, hused, htotal⟩ := view used s hi
  unfold tapeIteration
  refine WP.seq (WP.mono (chunkCheck_frame_ok L R slots ht hu hw hused htotal hle hmax)
    fun u ⟨hcf, hm, ku⟩ => ?_)
  have Ru : Rep u.mem F S V W := hm ▸ R
  have Lu := lay_of_rep L R Ru rfl ku.sp ku.wr
  have hiu := stable used hi hm (ku.mono (by decide))
  by_cases exhausted : total - used < width
  · refine WP.ite true (by
      have hav : ¬ width ≤ total - used := by omega_using [exhausted]
      simp [eval, State.read, hcf, hav]) (fun _ => ?_) (fun he => Bool.noConfusion he)
    refine WP.mono (tapeExhausted_ok Lu Ru) fun t ⟨hz, Lt, Rt, ft, kt⟩ => ?_
    exact Or.inl ⟨hz, done u t V W hiu exhausted Lu Ru Lt Rt ft kt⟩
  · have available : width ≤ total - used := by omega_using [exhausted]
    refine WP.ite false (by simp [eval, State.read, hcf, available]) (fun he => Bool.noConfusion he) (fun _ => ?_)
    refine WP.seq (WP.mono (chunkTake_ok Lu Ru slots hb hu hp hu12 hp12 hw hused)
      fun v ⟨Lv, Rv, fv, kv⟩ => ?_)
    refine WP.seq (WP.mono (step u v V W hiu available Lu Ru hused Lv Rv fv kv)
      fun w ⟨Vw, Ww, Lw, Rw, outcome⟩ => ?_)
    refine WP.mono (tapeStatus_ok Lw Rw) fun t ⟨hz, hmt, kt⟩ => ?_
    by_cases retry : Ww 19 = 3
    · have hit : I (used + width) t := stable _ (by simpa only [retry, ite_true, ite_false] using outcome) hmt (kt.mono (by decide))
      exact Or.inr ⟨by simp [hz, retry], hit, by omega_using [hle, exhausted]⟩
    · have hqt : Q t := finish (by simpa only [retry, ite_true, ite_false] using outcome) hmt (kt.mono (by decide))
      exact Or.inl ⟨by rw [hz]; exact congrArg some (beq_eq_false_iff_ne.mpr retry), hqt⟩

end VG.Proof.Dsa.AArch64.Generation
