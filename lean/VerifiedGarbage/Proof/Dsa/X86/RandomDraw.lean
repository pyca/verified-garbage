module

public import VerifiedGarbage.Proof.Dsa.X86.RandomCandidate
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Mont.X86.Instr

/-!
# One draw (x86)

The sampler's state between draws (`Smp`): what `prepare` stored, the
consumed bytes `used` and the remaining draws, and the nonce's zero
padding. `draw` either finds the tape short, accepts a candidate, or
rejects it and spends a draw of the budget, as FIPS 186-4's sampling does
(`Spec.Dsa.Random.sample`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random

/-- The sampler's state. -/
structure Smp (s₀ : State) (used draws : Nat) (t : State) : Prop where
  ready : Ready s₀ t
  q : slot t.mem (rBase s₀) oQ = rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀)
  width : slot t.mem (rBase s₀) oWidth = BitVec.ofNat 32 (rWidth s₀)
  mask : slot t.mem (rBase s₀) oMask = maskValue (rLead s₀).toNat
  usedW : slot t.mem (rBase s₀) oUsed = BitVec.ofNat 32 used
  drawsW : slot t.mem (rBase s₀) oDraws = BitVec.ofNat 32 draws
  pad : ∀ i < (rQBytes s₀).length - rWidth s₀, t.mem (off (rBase s₀) (oNonce + i)) = 0
  usedBound : used ≤ (rInput s₀).rand.length

/-- Where the sampler writes. -/
def sampleRanges : List (Nat × Nat) := [(oUsed, 4), (oDraws, 4), (oStatus, 4), (oNonce, 32)]

theorem slot_outs {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 4 < 2 ^ 64) : slot m' B d = slot m B d :=
  Mem.readW_congr fun i hi => h _ fun r hr => by
    have := hd r hr
    have hi' : i < 4 := hi
    rw [ofs_off B (show d + i < 2 ^ 64 by omega)]; omega

/-- The slots and bytes the sampler changes. -/
abbrev drawRanges (s₀ : State) : List (Nat × Nat) :=
  [(oUsed, 4), (oDraws, 4), (oStatus, 4), (drawPlace s₀, rWidth s₀)]

/-- A memory change apart from the rest of the sampler's state. -/
theorem Smp.of {s₀ t u : State} (A : RandomSignABI s₀) {used draws used' draws' : Nat}
    (S : Smp s₀ used draws t) (hr : Ready s₀ u) (hm : Outs (rBase s₀) (drawRanges s₀) t.mem u.mem)
    (hu : slot u.mem (rBase s₀) oUsed = BitVec.ofNat 32 used')
    (hdw : slot u.mem (rBase s₀) oDraws = BitVec.ofNat 32 draws')
    (hub : used' ≤ (rInput s₀).rand.length) : Smp s₀ used' draws' u := by
  have hfit : rWidth s₀ ≤ (rQBytes s₀).length := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  have hql := rQBytes_le A
  have hd : ∀ d, oDraws + 4 ≤ d → d + 4 ≤ oStatus → slot u.mem (rBase s₀) d = slot t.mem (rBase s₀) d :=
    fun d h₁ h₂ => slot_outs hm (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      unfold oDraws oStatus at *
      rcases hr with rfl | rfl | rfl | rfl
      · right; unfold oUsed; omega
      · right; omega
      · left; omega
      · left; unfold drawPlace oNonce; omega) (by unfold oStatus at h₂; omega)
  refine ⟨hr, (hd _ (by decide) (by decide)).trans S.q, (hd _ (by decide) (by decide)).trans S.width,
    (hd _ (by decide) (by decide)).trans S.mask, hu, hdw, fun i hi => ?_, hub⟩
  rw [hm _ fun r hr => ?_]
  · exact S.pad i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [ofs_off0 _ (by unfold oNonce; omega)]
  rcases hr with rfl | rfl | rfl | rfl
  · right; unfold oUsed oNonce; omega
  · right; unfold oDraws oNonce; omega
  · right; unfold oStatus oNonce; omega
  · left; unfold drawPlace; omega

theorem Smp.congr {s₀ t u : State} (A : RandomSignABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
    (hr : Ready s₀ u) (hm : Outs (rBase s₀) (drawRanges s₀) t.mem u.mem)
    (hu : slot u.mem (rBase s₀) oUsed = slot t.mem (rBase s₀) oUsed)
    (hdw : slot u.mem (rBase s₀) oDraws = slot t.mem (rBase s₀) oDraws) : Smp s₀ used draws u :=
  S.of A hr hm (hu.trans S.usedW) (hdw.trans S.drawsW) S.usedBound

/-- A store to a frame slot. -/
theorem store_outs (B : Addr) (m : Mem) {d : Nat} (v : BitVec 32) {rs : List (Nat × Nat)}
    (hd : (d, 4) ∈ rs) (hb : d + 4 ≤ 2 ^ 64 := by decide) : Outs B rs m (m.writeW (off B d) v) :=
  Outs.of_outside (writeW32_outside m B v hb) hd

/-- Spend a draw of the budget. -/
theorem drawDec_ok {s₀ t : State} (A : RandomSignABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
    (hd : 1 ≤ draws) (hdb : draws ≤ 128) :
    WP isa (.block [.mov .eax (.mem (sp oDraws)), .alu .sub .eax (.imm 1), .store (sp oDraws) .eax]) t fun u =>
      Keeps [.eax] t u ∧ u.gpr .eax = BitVec.ofNat 32 (draws - 1) ∧
      u.mem = t.mem.writeW (off (rBase s₀) oDraws) (BitVec.ofNat 32 (draws - 1)) ∧ Ready s₀ u ∧
      u.zf = some (decide (draws - 1 = 0)) ∧ Smp s₀ used (draws - 1) u := by
  have h := S.ready
  refine (wp_movS (v := BitVec.ofNat 32 draws) (by rw [h.rf.readSlot (by decide)]; exact congrArg some S.drawsW)
    fun t₁ u₁ _ => wp_subi fun t₂ u₂ _ z₂ => ?_)
  have v₂ : t₂.gpr .eax = BitVec.ofNat 32 (draws - 1) := by
    rw [u₂.gpr, u₁.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat hd]
  have f₂ := h.rf.of_keeps ((u₁.keeps.mono (by decide)).trans u₂.keeps)
  refine wp_slot f₂ (by decide) v₂ fun t₃ f₃ m₃ g₃ r₃ w₃ zf₃ _ => WP.block_nil ?_
  have k₃ : Keeps [.eax] t t₃ := ((u₁.keeps.mono (by decide)).trans u₂.keeps).trans ⟨fun r _ => by rw [g₃], r₃, w₃⟩
  have hm₃ : t₃.mem = t.mem.writeW (off (rBase s₀) oDraws) (BitVec.ofNat 32 (draws - 1)) := by
    rw [m₃, u₂.mem, u₁.mem]
  have h₃ : Ready s₀ t₃ := h.congr k₃ (by rw [hm₃]; exact frame_store s₀ _ (by decide) _)
  have z₃ : t₃.zf = some (decide (draws - 1 = 0)) := by
    rw [zf₃, z₂, u₁.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq (by omega) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega))
  have S₃ : Smp s₀ used (draws - 1) t₃ :=
    S.of A h₃ (by rw [hm₃]; exact store_outs _ _ _ (by simp only [drawRanges, List.mem_cons, true_or, or_true]))
      (by rw [hm₃, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]; exact S.usedW)
      (by rw [hm₃, slot_write_self]) S.usedBound
  exact ⟨k₃, by rw [g₃, v₂], hm₃, h₃, z₃, S₃⟩

/-- Accept, or spend a draw. -/
theorem drawFinish_ok {s₀ t : State} (A : RandomSignABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
    (hd : 1 ≤ draws) (hdb : draws ≤ 128) {acc : Bool} (hz : t.zf = some (!acc)) :
    WP isa drawFinish t fun u => Keeps [.eax] t u ∧ Ready s₀ u ∧
      Outs (rBase s₀) [(oDraws, 4), (oStatus, 4)] t.mem u.mem ∧
      (acc → Smp s₀ used draws u ∧ slot u.mem (rBase s₀) oStatus = 1) ∧
      (acc = false → Smp s₀ used (draws - 1) u ∧
        slot u.mem (rBase s₀) oStatus = (if draws - 1 = 0 then 0 else slot t.mem (rBase s₀) oStatus)) := by
  have hF : Random.frameBytes = 120 := rfl
  have h := S.ready
  unfold drawFinish
  cases acc with
  | true =>
    refine WP.ite true (by simp only [eval, hz, Bool.not_true, Option.map_some, Bool.not_false])
      (fun _ => wp_movS rfl fun t₁ u₁ _ => ?_) (fun e => Bool.noConfusion e)
    refine wp_slot (h.rf.of_keeps u₁.keeps) (by decide) u₁.gpr fun t₂ f₂ m₂ g₂ r₂ w₂ _ _ => WP.block_nil ?_
    have k₂ : Keeps [.eax] t t₂ := u₁.keeps.trans ⟨fun r _ => by rw [g₂], r₂, w₂⟩
    have hm : t₂.mem = t.mem.writeW (off (rBase s₀) oStatus) (1 : BitVec 32) := by rw [m₂, u₁.mem]
    have h₂ : Ready s₀ t₂ := h.congr k₂ (by rw [hm]; exact frame_store s₀ _ (by decide) _)
    refine ⟨k₂, h₂, by rw [hm]; exact store_outs _ _ _ (by decide), fun _ => ⟨S.congr A h₂ ?_ ?_ ?_, ?_⟩,
      fun e => Bool.noConfusion e⟩
    · rw [hm]; exact store_outs _ _ _ (by simp only [drawRanges, List.mem_cons, true_or, or_true])
    · rw [hm, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]
    · rw [hm, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]
    · rw [hm, slot_write_self]
  | false =>
    refine WP.ite false (by simp only [eval, hz, Bool.not_false, Option.map_some, Bool.not_true])
      (fun e => Bool.noConfusion e) (fun _ => ?_)
    refine WP.seq (WP.mono (drawDec_ok A S hd hdb) fun t₃ ⟨k₃, v₃, hm₃, h₃, z₃, S₃⟩ => ?_)
    have f₃ := h₃.rf
    by_cases h0 : draws - 1 = 0
    · refine WP.ite true (by simp only [eval, z₃, h0, decide_true]) (fun _ => ?_) (fun e => Bool.noConfusion e)
      refine wp_slot f₃ (by decide) (by rw [v₃, h0]) fun t₄ f₄ m₄ g₄ r₄ w₄ _ _ => WP.block_nil ?_
      have hm₄ : t₄.mem = t₃.mem.writeW (off (rBase s₀) oStatus) (0 : BitVec 32) := m₄
      have k₄ : Keeps [.eax] t t₄ := k₃.trans ⟨fun r _ => by rw [g₄], r₄, w₄⟩
      have h₄ : Ready s₀ t₄ := h.congr k₄ (by
        rw [hm₄, hm₃]; exact (frame_store s₀ _ (by decide) _).trans (frame_store s₀ _ (by decide) _))
      refine ⟨k₄, h₄, ?_, fun e => Bool.noConfusion e, fun _ => ⟨S₃.congr A h₄ ?_ ?_ ?_, ?_⟩⟩
      · rw [hm₄, hm₃]
        exact (store_outs _ _ _ (by decide)).trans (store_outs _ _ _ (by decide))
      · rw [hm₄]; exact store_outs _ _ _ (by simp only [drawRanges, List.mem_cons, true_or, or_true])
      · rw [hm₄, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]
      · rw [hm₄, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]
      · rw [hm₄, slot_write_self, h0]; rfl
    · refine WP.ite false (by simp only [eval, z₃, h0, decide_false]) (fun e => Bool.noConfusion e)
        (fun _ => WP.block_nil ?_)
      refine ⟨k₃, h₃, by rw [hm₃]; exact store_outs _ _ _ (by decide), fun e => Bool.noConfusion e,
        fun _ => ⟨S₃, ?_⟩⟩
      rw [hm₃, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]
      simp only [h0, ↓reduceIte]

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `cmp d, src`, and the borrow. -/
theorem wp_cmpSc {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, Fupd s t → t.cf = some (decide ((s.gpr d).toNat < v.toNat)) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .cmp d src :: is)) s Q :=
  cons (s' := arithFlags s (s.gpr d - v) (decide ((s.gpr d).toNat < v.toNat)) (subOverflow (s.gpr d) v (s.gpr d - v)))
    (by simp only [exec, execAlu, h, Option.bind_some])
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)
end

/-- The specification's sampling from `used` on, with `draws` draws. -/
abbrev spl (s₀ : State) (draws used : Nat) : Spec.Dsa.Random.Sample :=
  Spec.Dsa.Random.sample (rq s₀) draws ((rInput s₀).rand.drop used)

/-- A sampling `S` that started at `base` is the one from `used` on. -/
structure SampleRel (s₀ : State) (S : Spec.Dsa.Random.Sample) (base used draws : Nat) : Prop where
  scalarEq : S.scalar = (spl s₀ draws used).scalar
  usedEq : base + S.used = used + (spl s₀ draws used).used
  statusEq : VG.Proof.Dsa.Random.sampleStatus S = VG.Proof.Dsa.Random.sampleStatus (spl s₀ draws used)

/-- What a sampling `S` that started at `base` leaves. -/
structure SampleOut (s₀ : State) (base : Nat) (S : Spec.Dsa.Random.Sample) (u : State) : Prop where
  smp : ∃ d, Smp s₀ (base + S.used) d u
  status : slot u.mem (rBase s₀) oStatus = BitVec.ofNat 32 (VG.Proof.Dsa.Random.sampleStatus S)
  nonce : ∀ k, S.scalar = some k → Spec.Rsa.bytesAt u.mem (off (rBase s₀) oNonce) (rQBytes s₀).length =
    Spec.Dsa.encodeBE (rQBytes s₀).length k

theorem sampleStatus_le (S : Spec.Dsa.Random.Sample) : VG.Proof.Dsa.Random.sampleStatus S ≤ 2 := by
  unfold VG.Proof.Dsa.Random.sampleStatus; split
  · decide
  · split <;> decide

abbrev sampleRegs : List Reg := [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp]

/-- The tape's remaining bytes against the width. -/
theorem drawHead_ok {s₀ t : State} (A : RandomSignABI s₀) {used draws : Nat} (S : Smp s₀ used draws t) :
    WP isa (.block [.mov .eax (.mem (arg aRandLen)), .alu .sub .eax (.mem (sp oUsed)),
      .alu .cmp .eax (.mem (sp oWidth))]) t fun u => Smp s₀ used draws u ∧ u.mem = t.mem ∧
      Keeps sampleRegs t u ∧ u.cf = some (decide ((rInput s₀).rand.length - used < rWidth s₀)) := by
  have h := S.ready
  have hub := S.usedBound
  have hfit : rWidth s₀ ≤ (rQBytes s₀).length := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  have hql := rQBytes_le A
  have hrl : (rInput s₀).rand.length = (X86.arg s₀ 10).toNat := by simp only [rInput, rBytes_length]
  refine wp_movS (h.argSrc A (j := 10) (by decide)) fun t₁ u₁ _ => ?_
  have h₁ := h.upd u₁ (by decide)
  refine wp_subS (v := BitVec.ofNat 32 used)
    (by rw [h₁.rf.readSlot (by decide), u₁.mem]; exact congrArg some S.usedW) fun t₂ u₂ _ => ?_
  have h₂ := h₁.upd u₂ (by decide)
  refine wp_cmpSc (v := BitVec.ofNat 32 (rWidth s₀))
    (by rw [h₂.rf.readSlot (by decide), u₂.mem, u₁.mem]; exact congrArg some S.width) fun t₃ f₃ c₃ => WP.block_nil ?_
  have h₃ := h₂.fupd f₃
  have k₃ : Keeps sampleRegs t t₃ := ((u₁.keeps.mono (by decide)).trans (u₂.keeps.mono (by decide))).trans (f₃.keeps _)
  have m₃ : t₃.mem = t.mem := by rw [f₃.mem, u₂.mem, u₁.mem]
  have e10 : X86.arg s₀ 10 = BitVec.ofNat 32 (rInput s₀).rand.length := by
    rw [hrl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [u₂.gpr, u₁.gpr, e10, sub_ofNat hub, toNat_ofNat_lt (by have := (X86.arg s₀ 10).isLt; omega),
    toNat_ofNat_lt (by omega)] at c₃
  exact ⟨S.congr A h₃ (by rw [m₃]; exact Outs.refl _ _ _) (by rw [m₃]) (by rw [m₃]), m₃, k₃, c₃⟩

/-- Consume a complete draw. -/
theorem drawUsed_ok {s₀ t : State} (A : RandomSignABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
    (hfull : used + rWidth s₀ ≤ (rInput s₀).rand.length) :
    WP isa (.block [.mov .eax (.mem (sp oUsed)), .alu .add .eax (.mem (sp oWidth)), .store (sp oUsed) .eax]) t
      fun u => Smp s₀ (used + rWidth s₀) draws u ∧
        u.mem = t.mem.writeW (off (rBase s₀) oUsed) (BitVec.ofNat 32 (used + rWidth s₀)) ∧
        Keeps sampleRegs t u := by
  have h₄ := S.ready
  refine wp_movS (v := BitVec.ofNat 32 used)
    (by rw [h₄.rf.readSlot (by decide)]; exact congrArg some S.usedW) fun t₅ u₅ _ => ?_
  have h₅ := h₄.upd u₅ (by decide)
  refine wp_addS (v := BitVec.ofNat 32 (rWidth s₀))
    (by rw [h₅.rf.readSlot (by decide), u₅.mem]; exact congrArg some S.width) fun t₆ u₆ _ => ?_
  have h₆ := h₅.upd u₆ (by decide)
  refine wp_slot h₆.rf (by decide) (v := BitVec.ofNat 32 (used + rWidth s₀))
    (by rw [u₆.gpr, u₅.gpr, BitVec.ofNat_add]) fun t₇ f₇ m₇ g₇ r₇ w₇ _ _ => WP.block_nil ?_
  have hm₇ : t₇.mem = t.mem.writeW (off (rBase s₀) oUsed) (BitVec.ofNat 32 (used + rWidth s₀)) := by
    rw [m₇, u₆.mem, u₅.mem]
  have k₇ : Keeps sampleRegs t t₇ :=
    ((u₅.keeps.mono (by decide)).trans (u₆.keeps.mono (by decide))).trans ⟨fun r _ => by rw [g₇], r₇, w₇⟩
  have h₇ : Ready s₀ t₇ := h₄.congr k₇ (by rw [hm₇]; exact frame_store s₀ _ (by decide) _)
  have o₇ : Outs (rBase s₀) [(oUsed, 4)] t.mem t₇.mem := by rw [hm₇]; exact store_outs _ _ _ (by decide)
  exact ⟨S.of A h₇ (o₇.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [drawRanges])
    (by rw [hm₇, slot_write_self]) (by rw [hm₇, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]; exact S.drawsW)
    hfull, hm₇, k₇⟩

/-- The copy, apart from the rest of the sampler's state. -/
theorem drawCopy_ok {s₀ t : State} (A : RandomSignABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
    (hfull : used + rWidth s₀ ≤ (rInput s₀).rand.length) (hw1 : 1 ≤ rWidth s₀) :
    WP isa copy t fun u => Smp s₀ used draws u ∧
      (∀ i < rWidth s₀, u.mem (off (rBase s₀) (drawPlace s₀ + i)) =
        copied (drawBytes s₀ used) (maskValue (rLead s₀).toNat) i) ∧
      Outside (rBase s₀) (drawPlace s₀) (rWidth s₀) t.mem u.mem ∧
      Keeps [.eax, .ecx, .edx, .esi] t u := by
  have hql := rQBytes_le A
  have hfit : rWidth s₀ ≤ (rQBytes s₀).length := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  refine WP.mono (copy_ok A S.ready S.usedW S.width S.mask hfull hw1) fun t₄ ⟨h₄, hc₄, ho₄, k₄⟩ => ?_
  have o₄ : Outs (rBase s₀) (drawRanges s₀) t.mem t₄.mem :=
    Outs.of_outside ho₄ (by simp only [drawRanges, List.mem_cons, true_or, or_true])
  have sl₄ : ∀ d, d + 4 ≤ oNonce → slot t₄.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d hd' =>
    slot_outs (Outs.of_outside ho₄ (List.mem_singleton_self _)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; left; unfold drawPlace; omega) (by unfold oNonce at hd'; omega)
  exact ⟨S.congr A h₄ o₄ (sl₄ _ (by decide)) (sl₄ _ (by decide)), hc₄, ho₄, k₄⟩

/-- The nonce's bytes survive the store of `used`. -/
theorem drawUsed_bytes {s₀ : State} (A : RandomSignABI s₀) {t u : State} {used v : Nat}
    (hm : u.mem = t.mem.writeW (off (rBase s₀) oUsed) (BitVec.ofNat 32 v))
    (hc : ∀ i < rWidth s₀, t.mem (off (rBase s₀) (drawPlace s₀ + i)) =
      copied (drawBytes s₀ used) (maskValue (rLead s₀).toNat) i) :
    ∀ i < rWidth s₀, u.mem (off (rBase s₀) (drawPlace s₀ + i)) =
      copied (drawBytes s₀ used) (maskValue (rLead s₀).toNat) i := fun i hi => by
  have hql := rQBytes_le A
  have hfit : rWidth s₀ ≤ (rQBytes s₀).length := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  have o₇ : Outs (rBase s₀) [(oUsed, 4)] t.mem u.mem := by rw [hm]; exact store_outs _ _ _ (by decide)
  rw [o₇ _ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [ofs_off0 _ (by unfold drawPlace oNonce; omega)]; right; unfold drawPlace oNonce oUsed; omega]
  exact hc i hi

theorem draw_ok {s₀ t : State} (A : RandomSignABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
    (hd : 1 ≤ draws) (hdb : draws ≤ 128) (hq : 1 < rq s₀)
    (hst : slot t.mem (rBase s₀) oStatus = 4) :
    WP isa draw t fun u => Ready s₀ u ∧ Outs (rBase s₀) sampleRanges t.mem u.mem ∧ Keeps sampleRegs t u ∧
      ((slot u.mem (rBase s₀) oStatus = 4 ∧ 2 ≤ draws ∧ Smp s₀ (used + rWidth s₀) (draws - 1) u ∧
          (∀ S' base, SampleRel s₀ S' base used draws → SampleRel s₀ S' base (used + rWidth s₀) (draws - 1)) ∧
          (spl s₀ draws used).trace = 0 :: (spl s₀ (draws - 1) (used + rWidth s₀)).trace) ∨
        (slot u.mem (rBase s₀) oStatus ≠ 4 ∧
          (∀ S' base, SampleRel s₀ S' base used draws → SampleOut s₀ base S' u) ∧
          ((spl s₀ draws used).trace.head? ≠ some 0 ∨ draws = 1))) := by
  have hF : Random.frameBytes = 120 := rfl
  have hql := rQBytes_le A
  have hfit : rWidth s₀ ≤ (rQBytes s₀).length := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  have hw1 : 1 ≤ rWidth s₀ := by
    exact Nat.pos_of_ne_zero ((VG.Proof.Dsa.random_valid_scan (rQBytes s₀)).mp hq).1
  have h := S.ready
  have hrl : (rInput s₀).rand.length = (X86.arg s₀ 10).toNat := by simp only [rInput, rBytes_length]
  have hub := S.usedBound
  obtain ⟨d', rfl⟩ : ∃ d', draws = d' + 1 := ⟨draws - 1, by omega⟩
  have hdw : Spec.Dsa.Random.drawBytes (rq s₀) = rWidth s₀ := rWidth_eq s₀
  have hrlen : ((rInput s₀).rand.drop used).length = (rInput s₀).rand.length - used := List.length_drop
  unfold draw
  refine WP.seq (WP.mono (drawHead_ok A S) fun t₃ ⟨S₃, m₃, k₃, c₃⟩ => ?_)
  have h₃ := S₃.ready
  by_cases hshort : (rInput s₀).rand.length - used < rWidth s₀
  · -- The tape is short.
    refine WP.ite true (by simp only [eval, c₃, hshort, decide_true]) (fun _ => ?_) (fun e => Bool.noConfusion e)
    refine wp_movS rfl fun t₄ u₄ _ => wp_slot (h₃.rf.of_keeps u₄.keeps) (by decide) u₄.gpr
      fun t₅ f₅ m₅ g₅ r₅ w₅ _ _ => WP.block_nil ?_
    have k₅ : Keeps sampleRegs t t₅ := (k₃.trans (u₄.keeps.mono (by decide))).trans ⟨fun r _ => by rw [g₅], r₅, w₅⟩
    have hm₅ : t₅.mem = t.mem.writeW (off (rBase s₀) oStatus) (2 : BitVec 32) := by rw [m₅, u₄.mem, m₃]
    have h₅ : Ready s₀ t₅ := h.congr k₅ (by rw [hm₅]; exact frame_store s₀ _ (by decide) _)
    have S₅ : Smp s₀ used (d' + 1) t₅ := S.congr A h₅
      (by rw [hm₅]; exact store_outs _ _ _ (by simp only [drawRanges, List.mem_cons, true_or, or_true]))
      (by rw [hm₅, slot_write_ne _ _ _ (by decide) (by decide) (by decide)])
      (by rw [hm₅, slot_write_ne _ _ _ (by decide) (by decide) (by decide)])
    have hspl : spl s₀ (d' + 1) used = ⟨none, 0, [2]⟩ :=
      VG.Proof.Dsa.Random.sample_short _ _ _ hq (by rw [hdw, hrlen]; exact hshort)
    refine ⟨h₅, by rw [hm₅]; exact store_outs _ _ _ (by decide), k₅, .inr ⟨?_, fun S' base R => ⟨?_, ?_, ?_⟩,
      .inl (by rw [hspl]; simp)⟩⟩
    · rw [hm₅, slot_write_self]; decide
    · exact ⟨d' + 1, by rw [R.usedEq, hspl]; exact S₅⟩
    · rw [hm₅, slot_write_self, R.statusEq, hspl]; rfl
    · intro k hk; rw [R.scalarEq, hspl] at hk; simp at hk
  · -- A complete draw.
    refine WP.ite false (by simp only [eval, c₃, hshort, decide_false]) (fun e => Bool.noConfusion e) (fun _ => ?_)
    have hfull : used + rWidth s₀ ≤ (rInput s₀).rand.length := by omega
    have hdl : (drawBytes s₀ used).length = rWidth s₀ := by
      simp only [drawBytes, List.length_take, List.length_drop]; omega
    have hnp : ∀ i, i < rWidth s₀ → oNonce ≤ drawPlace s₀ + i ∧ drawPlace s₀ + i < oNonce + 32 := by
      intro i hi; unfold drawPlace; omega
    -- The copy.
    refine WP.seq (WP.mono (drawCopy_ok A S₃ hfull hw1) fun t₄ ⟨S₄, hc₄, ho₄, k₄⟩ => ?_)
    -- The consumption.
    refine WP.seq (WP.mono (drawUsed_ok A S₄ hfull) fun t₇ ⟨S₇, hm₇, k₇⟩ => ?_)
    have h₇ := S₇.ready
    have o₇ : Outs (rBase s₀) [(oUsed, 4)] t₄.mem t₇.mem := by rw [hm₇]; exact store_outs _ _ _ (by decide)
    have hc₇ := drawUsed_bytes A hm₇ hc₄
    -- The comparison.
    let cs := copiedList (drawBytes s₀ used) (maskValue (rLead s₀).toNat) (rWidth s₀)
    refine WP.seq (WP.mono (inRange_ok A h₇ (cs := cs) S₇.q S₇.width (copiedList_length _ _ _) hw1
      fun i hi => by rw [copiedList_getD _ _ hi]; exact hc₇ i hi) fun t₈ ⟨_, z₈, m₈, h₈, k₈⟩ => ?_)
    have S₈ : Smp s₀ (used + rWidth s₀) (d' + 1) t₈ :=
      S₇.congr A h₈ (by rw [m₈]; exact Outs.refl _ _ _) (by rw [m₈]) (by rw [m₈])
    have hacc : accepts s₀ cs = decide (0 < Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used) ∧
        Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used) < rq s₀) := accepts_candidate s₀ hdl hw1
    have htake : ((rInput s₀).rand.drop used).take (Spec.Dsa.Random.drawBytes (rq s₀)) = drawBytes s₀ used := by
      rw [hdw]
    refine WP.mono (drawFinish_ok A S₈ (by omega) hdb z₈) fun u ⟨k₉, h₉, o₉, hT, hF'⟩ => ?_
    have outs : Outs (rBase s₀) sampleRanges t.mem u.mem := by
      have e₁ : Outs (rBase s₀) sampleRanges t.mem t₃.mem := by rw [m₃]; exact Outs.refl _ _ _
      have e₂ : Outs (rBase s₀) sampleRanges t₃.mem t₄.mem := fun x hx => ho₄ x (by
        have := hx (oNonce, 32) (by decide)
        rw [Nat.lt_iff_add_one_le] at this ⊢
        unfold drawPlace oNonce at *; omega)
      have e₃ : Outs (rBase s₀) sampleRanges t₄.mem t₇.mem := o₇.mono (by decide)
      have e₄ : Outs (rBase s₀) sampleRanges t₇.mem t₈.mem := by rw [m₈]; exact Outs.refl _ _ _
      exact (((e₁.trans e₂).trans e₃).trans e₄).trans (o₉.mono (by decide))
    have keeps : Keeps sampleRegs t u :=
      (((k₃.trans (k₄.mono (by decide))).trans k₇).trans k₈).trans (k₉.mono (by decide))
    -- The nonce's bytes survive the stores of the slots.
    have hc₉ : ∀ i < rWidth s₀, u.mem (off (rBase s₀) (drawPlace s₀ + i)) =
        copied (drawBytes s₀ used) (maskValue (rLead s₀).toNat) i := fun i hi => by
      have hle : ∀ r ∈ ([(oDraws, 4), (oStatus, 4)] : List (Nat × Nat)), r.1 + r.2 ≤ oNonce := by decide
      rw [o₉ _ fun r hr => by
        have := hle r hr
        rw [ofs_off0 _ (by unfold drawPlace oNonce; omega)]
        right; unfold drawPlace oNonce at *; omega, m₈]
      exact hc₇ i hi
    have st₈ : slot t₈.mem (rBase s₀) oStatus = 4 := by
      rw [m₈, hm₇, slot_write_ne _ _ _ (by decide) (by decide) (by decide),
        slot_outs (Outs.of_outside ho₄ (List.mem_singleton_self _)) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; left; unfold drawPlace oNonce oStatus; omega) (by decide),
        m₃, hst]
    cases ha : accepts s₀ cs with
    | true =>
      obtain ⟨S₉, st₉⟩ := hT ha
      have hk : 0 < Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used) ∧
          Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used) < rq s₀ := by
        rw [hacc] at ha; exact of_decide_eq_true ha
      have hspl : spl s₀ (d' + 1) used =
          ⟨some (Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used)), rWidth s₀, [1]⟩ := by
        rw [spl, VG.Proof.Dsa.Random.sample_accept _ _ _ hq (by rw [hdw, hrlen]; omega) (by rw [htake]; exact hk),
          htake, hdw]
      refine ⟨h₉, outs, keeps, .inr ⟨by rw [st₉]; decide, fun S' base R => ⟨?_, ?_, ?_⟩,
        .inl (by rw [hspl]; simp)⟩⟩
      · exact ⟨d' + 1, by rw [R.usedEq, hspl]; exact S₉⟩
      · rw [st₉, R.statusEq, hspl]; rfl
      · intro k hk'
        rw [R.scalarEq, hspl] at hk'
        cases hk'
        exact nonce_encodes A hdl hw1 S₉.pad hc₉
    | false =>
      obtain ⟨S₉, st₉⟩ := hF' ha
      have hk : ¬ (0 < Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used) ∧
          Spec.Dsa.Random.candidate (rq s₀) (drawBytes s₀ used) < rq s₀) := by
        rw [hacc] at ha; exact of_decide_eq_false ha
      have hnext : ((rInput s₀).rand.drop used).drop (Spec.Dsa.Random.drawBytes (rq s₀)) =
          (rInput s₀).rand.drop (used + rWidth s₀) := by
        rw [List.drop_drop, hdw]
      have hspl : spl s₀ (d' + 1) used =
          { spl s₀ d' (used + rWidth s₀) with
            used := rWidth s₀ + (spl s₀ d' (used + rWidth s₀)).used,
            trace := 0 :: (spl s₀ d' (used + rWidth s₀)).trace } := by
        rw [spl, VG.Proof.Dsa.Random.sample_reject _ _ _ hq (by rw [hdw, hrlen]; omega) (by rw [htake]; exact hk),
          hnext, hdw]
      have hstatus : VG.Proof.Dsa.Random.sampleStatus (spl s₀ (d' + 1) used) =
          VG.Proof.Dsa.Random.sampleStatus (spl s₀ d' (used + rWidth s₀)) := by
        rw [hspl]; exact VG.Proof.Dsa.Random.sampleStatus_reject _ _ _ _
      have rel : ∀ S' base, SampleRel s₀ S' base used (d' + 1) → SampleRel s₀ S' base (used + rWidth s₀) d' :=
        fun S' base R => ⟨by rw [R.scalarEq, hspl], by rw [R.usedEq, hspl]; dsimp only; omega,
          R.statusEq.trans hstatus⟩
      by_cases h0 : d' = 0
      · subst h0
        refine ⟨h₉, outs, keeps, .inr ⟨by rw [st₉]; simp only [Nat.add_sub_cancel, ↓reduceIte]; decide,
          fun S' base R => ?_, .inr rfl⟩⟩
        have R' := rel S' base R
        have h0s : spl s₀ 0 (used + rWidth s₀) = ⟨none, 0, [3]⟩ := rfl
        refine ⟨⟨0, by rw [R'.usedEq, h0s]; exact S₉⟩, ?_, ?_⟩
        · rw [st₉, R'.statusEq, h0s]; simp only [Nat.add_sub_cancel, ↓reduceIte]; rfl
        · intro k hk'; rw [R'.scalarEq, h0s] at hk'; simp at hk'
      · refine ⟨h₉, outs, keeps, .inl ⟨?_, by omega, by simpa using S₉, fun S' base R => by simpa using rel S' base R,
          by rw [hspl, Nat.add_sub_cancel]⟩⟩
        rw [st₉]; simp only [Nat.add_sub_cancel, h0, ↓reduceIte]; exact st₈

end VG.Proof.Dsa.X86
