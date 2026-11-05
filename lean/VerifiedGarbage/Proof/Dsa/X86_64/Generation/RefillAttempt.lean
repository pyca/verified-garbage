module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Refill
public import VerifiedGarbage.Proof.Dsa.Generation.RefillSeed
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillOutcome
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedAttempt

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedSubgroup
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPrime
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedGenerator
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPack
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedValidate
import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.Omega

/-! # One seed of the refillable-tape search on x86-64

`refillAttempt_ok`: the native seed attempt of the refillable-tape search
(`Impl.Dsa.X86_64.Generation.Refill.refillAttempt`) computes
`Proof.Dsa.Generation.refillAttempt`. It is the finite search's attempt
(`seedAttempt_ok`) with the generator's `h` tape pointed at the window of
the witness tape after `p`'s witnesses (`window`), whose candidates it
reads count as consumed (`windowConsumed`), and a window cut short without
a generator ran out (`windowShort`). -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Mgf1.X86_64 (sp)

variable {checkName : String}

/-- Without a generator, `generator` reads every candidate. -/
theorem generatorCount_of_none {p q : Nat} :
    ∀ {hs : List Nat}, Spec.Dsa.generator p q hs = none →
      VG.Proof.Dsa.Generation.generatorCount p q hs = hs.length
  | [], _ => rfl
  | h :: hs, hn => by
    rw [VG.Proof.Dsa.Generation.generator_cons'] at hn
    cases hit : VG.Proof.Dsa.Generation.generatorHit p q h
    · simp only [hit, Bool.false_eq_true, ite_false] at hn
      simp only [VG.Proof.Dsa.Generation.generatorCount, hit, Bool.false_eq_true, ite_false,
        List.length_cons, generatorCount_of_none hn]
    · simp [hit] at hn

/-- A context's memory, with another `h` tape whose words are saved. -/
theorem GenerationMemory.withHs {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (hs : GenerationTape p.geo) (hm : GenerationTapeMemory hs s)
    (h11 : W 11 = hs.ptr) (h12 : W 12 = BitVec.ofNat 64 hs.bytes.length) :
    GenerationMemory (p.withHs hs) W s where
  layout := h.layout
  rep := h.rep
  slots k hk := by
    by_cases e11 : k = 11
    · subst e11; simpa [GenerationContext.withHs] using h11
    · by_cases e12 : k = 12
      · subst e12; simpa [GenerationContext.withHs] using h12
      · simp only [GenerationContext.withHs, e11, e12, ite_false]
        exact h.slots k hk
  scratch := h.scratch
  seeds := h.seeds
  hs := hm
  rand := h.rand

theorem GenerationMemory.withHs_self {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) : GenerationMemory (p.withHs p.hs) W s :=
  h.withHs p.hs h.hs ((h.slots 11 (by simp [generationSlots])).trans p.hSlot)
    ((h.slots 12 (by simp [generationSlots])).trans p.hLengthSlot)

theorem frame_of_outside {F : Addr} {d n : Nat} {m m' : Mem} (h : Outside F d n m m')
    (hd : d + n ≤ frameBytes) : Frame [⟨F, frameBytes⟩] m m' := by
  intro a ha
  apply h a
  right
  have hn := ha ⟨F, frameBytes⟩ (by simp)
  change ¬ ofs F a < frameBytes at hn
  omega

theorem GenerationGeometry.frame_bytes {g : GenerationGeometry} {m m' : Mem}
    (hf : Frame [⟨g.F, frameBytes⟩] m m') {d n : Nat} (hd : d + n ≤ usedBytes g.pLen) :
    Spec.Rsa.bytesAt m' (off g.B d) n = Spec.Rsa.bytesAt m (off g.B d) n := by
  have pn : g.pLen ≤ 384 := by rcases g.width with hh | hh | hh <;> omega
  apply VG.Proof.Dsa.Generation.frame_bytesAt hf
  · intro r hr
    rcases List.mem_singleton.mp hr with rfl
    exact (g.frame_part hd).symm
  · unfold usedBytes domainCheck at hd; omega

theorem refillSlots_search {k : Nat} (h : k ∈ refillSlots) : k ∈ searchSlots := by
  simp only [refillSlots, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [searchSlots]

theorem RefillFinished.prepend {p : GenerationContext} {Wi Wm : Nat → BitVec 64}
    {res : Option (Option Spec.Dsa.Params × List Byte)} {s u t : State}
    (h : RefillFinished p Wm res u t) (slots : ∀ k ∈ searchSlots, Wm k = Wi k)
    (hf : Frame p.changed s.mem u.mem) (hr : u.rd = s.rd) (hw : u.wr = s.wr) :
    RefillFinished p Wi res s t := by
  obtain ⟨hs, W, used, mt, hu, h16, hsl, outcome, ft, rt, wt⟩ := h
  exact ⟨hs, W, used, mt, hu, h16, fun k hk => (hsl k hk).trans (slots k (refillSlots_search hk)), outcome,
    hf.trans ft, rt.trans hr, wt.trans hw⟩

/-- An attempt that ends with the context's own `h` tape. -/
theorem refillFinished_of {p : GenerationContext} {W Wt : Nat → BitVec 64} {used : Nat}
    {res : Option (Option Spec.Dsa.Params × List Byte)} {s t : State}
    (h : GenerationMemory p Wt t) (hu : used ≤ p.rand.bytes.length) (h16 : Wt 16 = BitVec.ofNat 64 used)
    (slots : ∀ k ∈ searchSlots, Wt k = W k) (outcome : SeedOutcome p res Wt used t)
    (hf : Frame p.changed s.mem t.mem) (hr : t.rd = s.rd) (hw : t.wr = s.wr) :
    RefillFinished p W res s t :=
  ⟨p.hs, Wt, used, h.withHs_self, hu, h16, fun k hk => slots k (refillSlots_search hk), outcome, hf, hr, hw⟩

/-! ## The window -/

theorem windowHead_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {base : Addr} {used total width : Nat}
    (h13 : W 13 = base) (h16 : W 16 = BitVec.ofNat 64 used) (h15 : W 15 = BitVec.ofNat 64 total)
    (hle : used ≤ total) (hmax : total < 2 ^ 64) (hw : width < 2 ^ 31) :
    WP isa (.block [.mov .rax (.mem (sp 104)), .alu .add .rax (.mem (sp 128)), .store (sp 88) .rax,
      .mov .rcx (.mem (sp 120)), .alu .sub .rcx (.mem (sp 128)),
      .alu .cmp .rcx (.imm (BitVec.ofNat 32 width))]) s fun t =>
      t.cf = some (decide (total - used < width)) ∧ t.gpr .rcx = BitVec.ofNat 64 (total - used) ∧
      t.mem = s.mem.writeW (off F 88) (off base used) ∧ Keep [.rax, .rcx] s t := by
  have hsub : BitVec.ofNat 64 total - BitVec.ofNat 64 used = BitVec.ofNat 64 (total - used) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def]
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmax, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hmax)] using hle)]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmax,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hmax), Nat.mod_eq_of_lt (by omega : total - used < 2 ^ 64)]
  have R1 := R.wf L.geo (k := 11) (by decide) (off base used)
  have r120 : (s.mem.writeW (off F 88) (off base used)).readW (off F 120) 64 = BitVec.ofNat 64 total :=
    R1.slot (d := 120) (k := 15) rfl (by decide) (by simp [upd, h15])
  have r128 : (s.mem.writeW (off F 88) (off base used)).readW (off F 128) 64 = BitVec.ofNat 64 used :=
    R1.slot (d := 128) (k := 16) rfl (by decide) (by simp [upd, h16])
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t =>
      t.cf = some (decide (total - used < width)) ∧ t.gpr .rcx = BitVec.ofNat 64 (total - used) ∧
      t.mem = s.mem.writeW (off F 88) (off base used)) (by
    xrun [ea_sp, L.rsp, L.ld (d := 104) (by decide), L.ld (d := 128) (by decide), L.st (d := 88) (by decide),
      L.ld (d := 120) (by decide),
      R.slot (d := 104) (k := 13) rfl (by decide) h13, R.slot (d := 128) (k := 16) rfl (by decide) h16,
      r120, r128, sx_ofNat hw, hsub]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : total - used < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : width < 2 ^ 64)]) rfl)
    fun _ ⟨⟨hc, hr, hm⟩, hk⟩ => ⟨hc, hr, hm, hk⟩

theorem window_rep_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {base : Addr} {used total pLen : Nat}
    (h13 : W 13 = base) (h16 : W 16 = BitVec.ofNat 64 used) (h15 : W 15 = BitVec.ofNat 64 total)
    (hle : used ≤ total) (hmax : total < 2 ^ 64) (hw : 128 * pLen < 2 ^ 31) :
    WP isa (Impl.Dsa.X86_64.Generation.Refill.window pLen) s fun t =>
      Lay t F S ∧ Rep t.mem F S V
        (upd (upd W 11 (off base used)) 12 (BitVec.ofNat 64 (min (total - used) (128 * pLen)))) ∧
      Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold Impl.Dsa.X86_64.Generation.Refill.window Impl.Dsa.X86_64.Generation.Refill.windowBytes
  refine WP.seq (WP.mono (windowHead_ok L R h13 h16 h15 hle hmax hw) fun u ⟨hc, hrcx, hm, ku⟩ => ?_)
  have Ru : Rep u.mem F S V (upd W 11 (off base used)) := by
    rw [hm]; exact R.wf L.geo (by decide : 11 < nW) _
  have Lu := lay_of_rep L R Ru (by simp [upd]) (ku.gpr (by decide)) ku.2.2
  have done : ∀ t, t.mem = u.mem.writeW (off F 96) (BitVec.ofNat 64 (min (total - used) (128 * pLen))) →
      Keep [.rax] u t →
      Lay t F S ∧ Rep t.mem F S V
        (upd (upd W 11 (off base used)) 12 (BitVec.ofNat 64 (min (total - used) (128 * pLen)))) ∧
      Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
    intro t ht kt
    have Rt : Rep t.mem F S V
        (upd (upd W 11 (off base used)) 12 (BitVec.ofNat 64 (min (total - used) (128 * pLen)))) := by
      rw [ht]; exact Ru.wf L.geo (by decide : 12 < nW) _
    refine ⟨lay_of_rep L R Rt (by simp [upd]) ((kt.gpr (by decide)).trans (ku.gpr (by decide)))
      (kt.2.2.trans ku.2.2), Rt, ?_, kt.2.1.trans ku.2.1, kt.2.2.trans ku.2.2⟩
    rw [ht, hm]
    exact frame_of_outside (n := frameBytes)
      (((writeW_outside _ F _ (d := 88) (by decide)).mono (o' := 0) (n' := frameBytes) (by decide) (by decide)).trans
      ((writeW_outside _ F _ (d := 96) (by decide)).mono (by decide) (by decide))) (by decide)
  by_cases hlt : total - used < 128 * pLen
  · refine WP.ite true (by simp [eval, hc, hlt]) (fun _ => ?_) (fun he => Bool.noConfusion he)
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = u.mem.writeW (off F 96) (BitVec.ofNat 64 (total - used))) (by
      xrun [ea_sp, Lu.rsp, Lu.st (d := 96) (by decide), hrcx]) rfl)
      fun t ⟨ht, kt⟩ => done t (by rw [ht, Nat.min_eq_left (by omega)]) kt
  · have cast : (BitVec.ofNat 32 (128 * pLen)).setWidth 64 = BitVec.ofNat 64 (128 * pLen) := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 128 * pLen < 2 ^ 32)]
    refine WP.ite false (by simp [eval, hc, hlt]) (fun he => Bool.noConfusion he) (fun _ => ?_)
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = u.mem.writeW (off F 96) (BitVec.ofNat 64 (128 * pLen))) (by
      xrun [ea_sp, Lu.rsp, Lu.st (d := 96) (by decide), cast]) rfl)
      fun t ⟨ht, kt⟩ => done t (by rw [ht, Nat.min_eq_right (by omega)]) kt

/-- `window`: the `h` tape is the window of `rand` after its first `used`
octets. -/
theorem refillWindow_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) {used n : Nat} (h16 : W 16 = BitVec.ofNat 64 used)
    (hu : used ≤ p.rand.bytes.length) (hn : n = min (p.rand.bytes.length - used) (128 * p.geo.pLen)) :
    WP isa (Impl.Dsa.X86_64.Generation.Refill.window p.geo.pLen) s fun t =>
      GenerationMemory (p.withHs (p.rand.window used n (by omega)))
        (upd (upd W 11 (off p.rand.ptr used)) 12 (BitVec.ofNat 64 n)) t ∧
      Frame [⟨p.geo.F, frameBytes⟩] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨V, R⟩ := h.rep
  have h13 : W 13 = p.rand.ptr := (h.slots 13 (by simp [generationSlots])).trans p.randSlot
  have h15 : W 15 = BitVec.ofNat 64 p.rand.bytes.length :=
    (h.slots 15 (by simp [generationSlots])).trans p.randLengthSlot
  have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega
  refine WP.mono (window_rep_ok h.layout R h13 h16 h15 hu p.rand.size (by omega))
    fun t ⟨Lt, Rt, ft, rt, wt⟩ => ?_
  subst hn
  have fc : Frame p.changed s.mem t.mem := GenerationContext.frame_single ft
  refine ⟨⟨Lt, ⟨V, Rt⟩, ?_, h.scratch.congr wt, h.seeds.frame fc rt wt,
    (h.rand.frame fc rt wt).window (by omega), h.rand.frame fc rt wt⟩, ft, rt, wt⟩
  intro k hk
  by_cases e11 : k = 11
  · subst e11; simp [upd, GenerationContext.withHs, GenerationTape.window]
  by_cases e12 : k = 12
  · subst e12; simp [upd, GenerationContext.withHs, GenerationTape.window_length]
  simp only [upd, GenerationContext.withHs, e11, e12, ite_false]
  exact h.slots k hk

/-! ## The generator's candidates and the status -/

theorem windowConsumed_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) :
    WP isa (.block Impl.Dsa.X86_64.Generation.Refill.windowConsumed) s fun t =>
      Lay t F S ∧ Rep t.mem F S V (upd W 16 (W 16 + W 20)) ∧
      Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off F 128) (W 16 + W 20)) (by
    xrun [Impl.Dsa.X86_64.Generation.Refill.windowConsumed, ea_sp, L.rsp, L.ld (d := 128) (by decide),
      L.ld (d := 160) (by decide), L.st (d := 128) (by decide),
      R.slot (d := 128) (k := 16) rfl (by decide) rfl, R.slot (d := 160) (k := 20) rfl (by decide) rfl]) rfl)
    fun t ⟨hm, kt⟩ => ?_
  have Rt : Rep t.mem F S V (upd W 16 (W 16 + W 20)) := by
    rw [hm]; exact R.wf L.geo (by decide : 16 < nW) _
  refine ⟨lay_of_rep L R Rt (by simp [upd]) (kt.gpr (by decide)) kt.2.2, Rt, ?_, kt⟩
  rw [hm]
  exact frame_of_outside (writeW_outside _ F _ (d := 128) (by decide)) (by decide)

theorem refillConsumed_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) :
    WP isa (.block Impl.Dsa.X86_64.Generation.Refill.windowConsumed) s fun t =>
      GenerationMemory p (upd W 16 (W 16 + W 20)) t ∧
      Frame [⟨p.geo.F, frameBytes⟩] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨V, R⟩ := h.rep
  refine WP.mono (windowConsumed_ok h.layout R) fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  refine ⟨h.frame Lt ⟨V, Rt⟩ (fun k hk => ?_) (GenerationContext.frame_single ft) kt.2.1 kt.2.2,
    ft, kt.2.1, kt.2.2⟩
  have : k ≠ 16 := by rintro rfl; exact absurd hk (by decide)
  simp [upd, this]

theorem shortCheck_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {n width : Nat} (h12 : W 12 = BitVec.ofNat 64 n)
    (hn : n < 2 ^ 64) (hw : width < 2 ^ 31) :
    WP isa (.block [.mov .rax (.mem (sp 96)), .alu .cmp .rax (.imm (BitVec.ofNat 32 width))]) s fun t =>
      t.cf = some (decide (n < width)) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.cf = some (decide (n < width)) ∧ t.mem = s.mem) (by
    xrun [ea_sp, L.rsp, L.ld (d := 96) (by decide), R.slot (d := 96) (k := 12) rfl (by decide) h12, sx_ofNat hw]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega : width < 2 ^ 64)]) rfl)
    fun _ ⟨⟨hc, hm⟩, hk⟩ => ⟨hc, hm, hk⟩

/-- `windowShort`: status 0 for a window shorter than `128 * pLen` without
a generator. -/
theorem refillShort_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) {n : Nat} (h12 : W 12 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    WP isa (Impl.Dsa.X86_64.Generation.Refill.windowShort p.geo.pLen) s fun t =>
      GenerationMemory p (if W 19 ≠ 1 ∧ n < 128 * p.geo.pLen then upd W 19 0 else W) t ∧
      Frame [⟨p.geo.F, frameBytes⟩] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega
  unfold Impl.Dsa.X86_64.Generation.Refill.windowShort Impl.Dsa.X86_64.Generation.Refill.windowBytes
  obtain ⟨V, R⟩ := h.rep
  refine WP.seq (WP.mono (successStatus_ok h.layout R) fun u ⟨hz, hm, ku⟩ => ?_)
  have hu := h.congr hm ku
  by_cases e : W 19 = 1
  · refine WP.ite true (by simp only [eval, hz, e, beq_self_eq_true]) (fun _ => WP.block_nil ?_)
      (fun he => Bool.noConfusion he)
    refine ⟨by simpa [e] using hu, by rw [hm]; exact Frame.refl _ _, ku.2.1, ku.2.2⟩
  · refine WP.ite false (by simp only [eval, hz, beq_eq_false_iff_ne.mpr e]) (fun he => Bool.noConfusion he)
      (fun _ => ?_)
    obtain ⟨Vu, Ru⟩ := hu.rep
    refine WP.seq (WP.mono (shortCheck_ok hu.layout Ru h12 hn (by omega)) fun v ⟨hc, hmv, kv⟩ => ?_)
    have hv := hu.congr hmv kv
    have fv : Frame [⟨p.geo.F, frameBytes⟩] s.mem v.mem := by rw [hmv, hm]; exact Frame.refl _ _
    by_cases short : n < 128 * p.geo.pLen
    · refine WP.ite true (by simp [eval, hc, short]) (fun _ => ?_) (fun he => Bool.noConfusion he)
      obtain ⟨Vv, Rv⟩ := hv.rep
      refine WP.mono (stackStatus_ok hv.layout Rv 0 (by decide)) fun t ⟨Lt, Rt, ft, kt⟩ => ?_
      have ff := frame_of_outside ft (by decide)
      refine ⟨?_, fv.trans ff, kt.2.1.trans (kv.2.1.trans ku.2.1), kt.2.2.trans (kv.2.2.trans ku.2.2)⟩
      rw [ite_eq_left ⟨e, short⟩]
      refine hv.frame Lt ⟨Vv, Rt⟩ (fun k hk => ?_) (GenerationContext.frame_single ff) kt.2.1 kt.2.2
      have : k ≠ 19 := by rintro rfl; exact absurd hk (by decide)
      simp [upd, this]
    · refine WP.ite false (by simp [eval, hc, short]) (fun he => Bool.noConfusion he) (fun _ => WP.block_nil ?_)
      refine ⟨by rw [ite_eq_right (fun hh => short hh.2)]; exact hv, fv, kv.2.1.trans ku.2.1, kv.2.2.trans ku.2.2⟩

/-! ## After `p`: the window, the generator and the parameters -/
