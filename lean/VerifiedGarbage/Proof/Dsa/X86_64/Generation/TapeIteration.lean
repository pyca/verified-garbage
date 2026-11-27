module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.TapeLoop
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! ### `Dsa.X86_64.Generation.TapeState`, which this module and modules that import it used -/

section

/-! # Initialize and test native seed and generator tape cursors -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Dsa.X86_64.Generation

theorem tapeReset_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (slots : TapeSlots)
    (hu : slots.used < 37) (hu14 : slots.used ≠ 14) :
    WP isa (.block (tapeReset slots)) s fun t =>
      Lay t F S ∧ Rep t.mem F S V (upd W slots.used 0) ∧
      Outside F (8 * slots.used) 8 s.mem t.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = s.mem.writeW (off F (8 * slots.used)) (0 : BitVec 64)) (by
    xrun [tapeReset, ea_sp, L.rsp,
      L.st (d := 8 * slots.used) (by unfold frameBytes; omega_using [hu])]
    rfl) rfl) fun t ⟨hm, hk⟩ => ?_
  have Rt : Rep t.mem F S V (upd W slots.used 0) := by
    rw [hm]; exact R.wf L.geo hu _
  refine ⟨lay_of_rep L R Rt (by simp [upd, Ne.symm hu14])
    (hk.gpr (by decide)) hk.2.2, Rt, ?_, hk⟩
  rw [hm]
  exact writeW_outside _ _ _ (by omega_using [hu])

theorem tapeStatus_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) :
    WP isa (.block tapeStatus) s fun t =>
      t.zf = some (W 19 == 3) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.zf = some (W 19 == 3) ∧ t.mem = s.mem) (by
    xrun [tapeStatus, ea_sp, L.rsp, L.ld (d := 152) (by decide),
      R.slot (d := 152) (k := 19) rfl (by decide) rfl]
    rw [sub_beq_zero]) rfl) fun _ ⟨⟨hz, hm⟩, hk⟩ => ⟨hz, hm, hk⟩

theorem tapeExhausted_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) :
    WP isa (.block (stackStatus 3 ++ ([.mov32 .rax (.imm 1), .alu .test .rax (.reg .rax)] : List Instr))) s fun t =>
      t.zf = some false ∧ Lay t F S ∧ Rep t.mem F S V (upd W 19 3) ∧
      Outside F 152 8 s.mem t.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.zf = some false ∧ t.mem = s.mem.writeW (off F 152) (3 : BitVec 64)) (by
    xrun [stackStatus, List.cons_append, List.nil_append, ea_sp, L.rsp,
      L.st (d := 152) (by decide)]
    rfl) rfl) fun t ⟨⟨hz, hm⟩, hk⟩ => ?_
  have Rt : Rep t.mem F S V (upd W 19 3) := by
    rw [hm]; exact R.wf L.geo (by decide : 19 < nW) _
  refine ⟨hz, lay_of_rep L R Rt (by simp [upd]) (hk.gpr (by decide)) hk.2.2, Rt, ?_, hk⟩
  rw [hm]; exact writeW_outside _ _ _ (by decide)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.ChunkTake`, which this module and modules that import it used -/

section

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
      L.ld (d := 8 * slots.base) (by unfold frameBytes; omega_using [hb]),
      L.ld (d := 8 * slots.used) (by unfold frameBytes; omega_using [hu]),
      L.st (d := 8 * slots.pointer) (by unfold frameBytes; omega_using [hp]),
      L.st (d := 8 * slots.used) (by unfold frameBytes; omega_using [hu]),
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
    exact ((writeW_outside _ F _ (d := 8 * slots.pointer) (by omega_using [hp])).mono (by omega_using []) (by unfold frameBytes; omega_using [hp])).trans
      ((writeW_outside _ F _ (d := 8 * slots.used) (by omega_using [hu])).mono (by omega_using []) (by unfold frameBytes; omega_using [hu]))
  intro a ha
  apply ff a
  right
  have hn := ha ⟨F, frameBytes⟩ (by simp)
  change ¬ ofs F a < frameBytes at hn
  omega_using [hn]

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.ChunkCheck`, which this module and modules that import it used -/

section

/-! # Check a complete seed or h chunk without cursor overflow -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Dsa.X86_64.Generation

theorem chunkCheck_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (slots : TapeSlots) {width used total : Nat}
    (ht : slots.total < 37) (hu : slots.used < 37) (hw : width < 2 ^ 31)
    (hused : W slots.used = BitVec.ofNat 64 used) (htotal : W slots.total = BitVec.ofNat 64 total)
    (hle : used ≤ total) (hmax : total < 2 ^ 64) :
    WP isa (.block (chunkCheck slots width)) s fun t =>
      t.cf = some (decide (total - used < width)) ∧ t.mem = s.mem ∧ Keep [.rax, .rcx] s t := by
  have hsub : BitVec.ofNat 64 total - BitVec.ofNat 64 used = BitVec.ofNat 64 (total - used) :=
    by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le (by
        rw [BitVec.le_def]
        simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmax, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hmax)] using hle)]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmax,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hmax), Nat.mod_eq_of_lt (by omega_using [hmax] : total - used < 2 ^ 64)]
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t =>
      t.cf = some (decide (total - used < width)) ∧ t.mem = s.mem) (by
    xrun [chunkCheck, ea_sp, L.rsp,
      L.ld (d := 8 * slots.total) (by unfold frameBytes; omega_using [ht]),
      L.ld (d := 8 * slots.used) (by unfold frameBytes; omega_using [hu]),
      R.slot (d := 8 * slots.total) (k := slots.total) rfl ht htotal,
      R.slot (d := 8 * slots.used) (k := slots.used) rfl hu hused, sx_ofNat hw, hsub]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hmax] : total - used < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega_using [hw] : width < 2 ^ 64)]) rfl)
    fun _ ⟨⟨hc, hm⟩, hk⟩ => ⟨hc, hm, hk⟩

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Complete native tape iteration, including exhaustion and retry -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Dsa.X86_64.Generation

/-- Payloads can depend on memory and preserved registers, but not the
comparison's volatile registers or flags. -/
def TapeStable (P : State → Prop) : Prop :=
  ∀ {s t}, P s → t.mem = s.mem → Keep [.rax, .rcx] s t → P t

def TapeView (slots : TapeSlots) (F S : Addr) (used total : Nat) (s : State) : Prop :=
  ∃ V W, Lay s F S ∧ Rep s.mem F S V W ∧
    W slots.used = BitVec.ofNat 64 used ∧ W slots.total = BitVec.ofNat 64 total

theorem tapeIteration_ok {slots : TapeSlots} {width total used : Nat} {F S : Addr}
    {body : Prog isa} {I : Nat → State → Prop} {Q : State → Prop}
    (hb : slots.base < 37) (ht : slots.total < 37) (hu : slots.used < 37) (hp : slots.pointer < 37)
    (hu14 : slots.used ≠ 14) (hp14 : slots.pointer ≠ 14)
    (hw : width < 2 ^ 31) (hmax : total < 2 ^ 64)
    (stable : ∀ n, TapeStable (I n)) (finish : TapeStable Q)
    (view : ∀ n s, I n s → TapeView slots F S n total s)
    (done : ∀ s t V W, I used s → total - used < width →
      Lay s F S → Rep s.mem F S V W →
      Lay t F S → Rep t.mem F S V (upd W 19 3) →
      Outside F 152 8 s.mem t.mem → Keep [.rax] s t → Q t)
    (step : ∀ s t V W, I used s → width ≤ total - used →
      Lay s F S → Rep s.mem F S V W → W slots.used = BitVec.ofNat 64 used →
      Lay t F S → Rep t.mem F S V
        (upd (upd W slots.pointer (off (W slots.base) used)) slots.used (BitVec.ofNat 64 (used + width))) →
      Frame [⟨F, frameBytes⟩] s.mem t.mem → Keep [.rax, .rcx] s t →
      WP isa body t fun u => ∃ V' W', Lay u F S ∧ Rep u.mem F S V' W' ∧
        (if W' 19 = 3 then I (used + width) u else Q u))
    {s : State} (hle : used ≤ total) (hi : I used s) :
    WP isa (tapeIteration slots width body) s fun t =>
      (eval .e t = some false ∧ Q t) ∨
      (eval .e t = some true ∧ I (used + width) t ∧ used + width ≤ total) := by
  obtain ⟨V, W, L, R, hused, htotal⟩ := view used s hi
  unfold tapeIteration
  refine WP.seq (WP.mono (chunkCheck_ok L R slots ht hu hw hused htotal hle hmax)
    fun u ⟨hcf, hm, ku⟩ => ?_)
  have Ru : Rep u.mem F S V W := hm ▸ R
  have Lu := lay_of_rep L R Ru rfl (ku.gpr (by decide)) ku.2.2
  have hiu := stable used hi hm ku
  by_cases exhausted : total - used < width
  · refine WP.ite true (by simp [eval, hcf, exhausted]) (fun _ => ?_) (fun he => Bool.noConfusion he)
    refine WP.mono (tapeExhausted_ok Lu Ru) fun t ⟨hz, Lt, Rt, ft, kt⟩ => ?_
    exact Or.inl ⟨by simpa [eval] using hz, done u t V W hiu exhausted Lu Ru Lt Rt ft kt⟩
  · have available : width ≤ total - used := by omega_using [exhausted]
    refine WP.ite false (by simp [eval, hcf, exhausted]) (fun he => Bool.noConfusion he) (fun _ => ?_)
    refine WP.seq (WP.mono (chunkTake_ok Lu Ru slots hb hu hp hu14 hp14 hw hused)
      fun v ⟨Lv, Rv, fv, kv⟩ => ?_)
    refine WP.seq (WP.mono (step u v V W hiu available Lu Ru hused Lv Rv fv kv)
      fun w ⟨Vw, Ww, Lw, Rw, outcome⟩ => ?_)
    refine WP.mono (tapeStatus_ok Lw Rw) fun t ⟨hz, hmt, kt⟩ => ?_
    by_cases retry : Ww 19 = 3
    · have hit : I (used + width) t := stable _ (by simpa only [retry, ite_true, ite_false] using outcome) hmt (kt.mono (by decide))
      exact Or.inr ⟨by simp [eval, hz, retry], hit, by omega_using [hle, exhausted]⟩
    · have hqt : Q t := finish (by simpa only [retry, ite_true, ite_false] using outcome) hmt (kt.mono (by decide))
      exact Or.inl ⟨by simp only [eval, hz, beq_eq_false_iff_ne.mpr retry], hqt⟩

end VG.Proof.Dsa.X86_64.Generation
