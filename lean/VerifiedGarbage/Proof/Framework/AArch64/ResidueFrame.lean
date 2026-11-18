module

public import VerifiedGarbage.Proof.Framework.AArch64.ResidueBound
public import VerifiedGarbage.Proof.Framework.AArch64.MemIn
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# What a function leaves in its registers, through calls and frames (AArch64)

`rtaintF W` is `rtaintB` (`ResidueBound.lean`) through the calls, returns and
frames of the code, for code whose frames stay within the `W` bytes below
the stack pointer on entry (the *window*). It does not follow what the
frames hold: a frame the code releases may hold a secret, which is then
below the stack pointer, outside every region. So the two runs agree on
the memory outside the regions only outside the window (`AgreeF`), which
the code clears before it returns (`Impl.Residue.AArch64.withScrub`,
`Scrub.lean`).

`rtaintB`'s instructions relate the two runs' states through their
memories outside the regions (`RTaint.Rest`), where they now differ in the
window. They are run instead on the first run's state and on the second
run's with the first run's memory outside its regions (`ghost`), which
runs as the second run's state does (`Residue.exec_in`): code reads and
writes memory only inside its regions.

The analysis knows how deep in the window the code is (`depth`), from its
frames, so that the frames stay within the window and the window is where
the stack pointer on entry says. Where two paths meet at different depths
(which the frames of structured code do not allow), it forgets the depth,
and fails on the next frame.

A call makes the return address (`x30`), `x16`, `x17` and the flags
public: the model takes them from the unknowns, which the two runs share. A
return checks `x30` in each run, and changes nothing. The pop of a register
makes it secret: the analysis does not know what the frame holds.
-/

@[expose] public section

namespace VG.AArch64.RTaintF

open VG.AArch64 VG.AArch64.Residue

/-! ## The ghost state -/

/-- `m₂` inside the regions `rs`, `m₁` outside them. -/
def blend (rs : List Region) (m₂ m₁ : Mem) : Mem :=
  fun x => if rs.any (fun r => decide (r.Contains x 1)) then m₂ x else m₁ x

/-- `s₂`, with `s₁`'s memory outside its regions. -/
def ghost (s₁ s₂ : State) : State := s₂.withM (blend (s₂.rd ++ s₂.wr) s₂.mem s₁.mem)

theorem blend_in {rs : List Region} {m₂ m₁ : Mem} : MemIn rs m₂ (blend rs m₂ m₁) := by
  intro x ⟨r, hr, hc⟩
  have : rs.any (fun r => decide (r.Contains x 1)) = true :=
    List.any_eq_true.mpr ⟨r, hr, decide_eq_true hc⟩
  simp only [blend, this, ↓reduceIte]

theorem blend_off {rs : List Region} {m₂ m₁ : Mem} : MemOff rs m₁ (blend rs m₂ m₁) := by
  intro x hx
  have : rs.any (fun r => decide (r.Contains x 1)) = false := by
    rw [Bool.eq_false_iff]
    intro h
    obtain ⟨r, hr, hc⟩ := List.any_eq_true.mp h
    exact hx r hr (of_decide_eq_true hc)
  simp only [blend, this, Bool.false_eq_true, ↓reduceIte]

theorem ghost_in (s₁ s₂ : State) : MemIn (s₂.rd ++ s₂.wr) s₂.mem (ghost s₁ s₂).mem := blend_in

theorem ghost_off {s₁ s₂ : State} (hrd : s₁.rd = s₂.rd) (hwr : s₁.wr = s₂.wr) :
    MemOff (s₁.rd ++ s₁.wr) s₁.mem (ghost s₁ s₂).mem := by
  rw [hrd, hwr]; exact blend_off

/-- `RTaintB.Agree` holds of states that agree with two that it holds of on
everything but the memory and what the hypotheses say. -/
theorem agree_of {τ : RTaintB.T} {s₁ s₂ t₁ t₂ : State} (h : RTaintB.Agree τ s₁ s₂)
    (hg₁ : t₁.gpr = s₁.gpr) (hg₂ : t₂.gpr = s₂.gpr) (hv₁ : t₁.v = s₁.v) (hv₂ : t₂.v = s₂.v)
    (hc₁ : t₁.c = s₁.c) (hc₂ : t₂.c = s₂.c) (hn₁ : t₁.nf = s₁.nf) (hn₂ : t₂.nf = s₂.nf)
    (hz₁ : t₁.zf = s₁.zf) (hz₂ : t₂.zf = s₂.zf) (hvf₁ : t₁.vf = s₁.vf) (hvf₂ : t₂.vf = s₂.vf)
    (hsp : t₁.sp = t₂.sp) (hrd : t₁.rd = t₂.rd) (hwr : t₁.wr = t₂.wr) (hd : t₁.dit = t₂.dit)
    (hu : t₁.unknowns = t₂.unknowns) (hm : MemOff (t₁.rd ++ t₁.wr) t₁.mem t₂.mem) :
    RTaintB.Agree τ t₁ t₂ := by
  obtain ⟨⟨⟨⟨⟨-, hgr⟩, hvr⟩, hfl, hx0, -⟩, hq⟩, hb₁, hb₂⟩ := h
  refine ⟨⟨⟨⟨⟨hsp, fun r hr => ?_⟩, fun w hw => ?_⟩, fun hf => ?_, ?_, hrd, hwr, hd, hu, hm⟩,
    fun b w hw => ?_⟩, fun e he => ?_, fun e he => ?_⟩
  · rw [hg₁, hg₂]; exact hgr r hr
  · rw [hv₁, hv₂]; exact hvr w hw
  · obtain ⟨a, b, c, d⟩ := hfl hf
    exact ⟨by rw [hc₁, hc₂, a], by rw [hn₁, hn₂, b], by rw [hz₁, hz₂, c], by rw [hvf₁, hvf₂, d]⟩
  · rw [hg₁, hg₂]; exact hx0
  · rw [hv₁, hv₂]; exact hq b w hw
  · rw [hg₁]; exact hb₁ e he
  · rw [hg₂]; exact hb₂ e he

/-! ## The analysis -/

/-- `rtaintB`'s taint, and how deep in the window the code is (`none` where
two paths met at different depths). -/
abbrev T := RTaintB.T × Option Nat

/-- The window: the `W` bytes below `e`, the stack pointer on entry. -/
def window (e : Addr) (W : Nat) : Region := ⟨e - BitVec.ofNat 64 W, W⟩

/-- The two runs agree as `τ` says, `d` bytes deep in the window: their
memories agree outside the regions but in the window, whose top is `d` bytes
above the stack pointer. -/
def AgreeD (W : Nat) (τ : RTaintB.T) (d : Nat) (s₁ s₂ : State) : Prop :=
  RTaintB.Agree τ s₁ (ghost s₁ s₂) ∧ d ≤ W ∧ W < 2 ^ 64 ∧
    ∀ x, (∀ r ∈ s₂.rd ++ s₂.wr, ¬ r.Contains x 1) →
      ¬ (window (s₂.sp + BitVec.ofNat 64 d) W).Contains x 1 → s₁.mem x = s₂.mem x

def Agree (W : Nat) (τ : T) (s₁ s₂ : State) : Prop :=
  ∃ d, (τ.2 = some d ∨ τ.2 = none) ∧ AgreeD W τ.1 d s₁ s₂

theorem ghost_sp (s₁ s₂ : State) : (ghost s₁ s₂).sp = s₂.sp := rfl
theorem ghost_rd (s₁ s₂ : State) : (ghost s₁ s₂).rd = s₂.rd := rfl
theorem ghost_wr (s₁ s₂ : State) : (ghost s₁ s₂).wr = s₂.wr := rfl

/-- The two runs' states agree on their regions, stack pointer, PSTATE.DIT
and unknowns. -/
theorem AgreeD.rest {W : Nat} {τ : RTaintB.T} {d : Nat} {s₁ s₂ : State} (h : AgreeD W τ d s₁ s₂) :
    s₁.sp = s₂.sp ∧ s₁.rd = s₂.rd ∧ s₁.wr = s₂.wr ∧ s₁.dit = s₂.dit ∧
      s₁.unknowns = s₂.unknowns := by
  obtain ⟨⟨⟨⟨⟨⟨hsp, -⟩, -⟩, -, -, hrd, hwr, hd, hu, -⟩, -⟩, -, -⟩, -⟩ := h
  exact ⟨hsp, hrd, hwr, hd, hu⟩

theorem step_sound {W : Nat} {τ τ' : RTaintB.T} {d : Nat} {i : Instr} {s₁ s₂ s₁' s₂' : State}
    (ha : AgreeD W τ d s₁ s₂) (hs : RTaintB.step τ i = some τ') (e₁ : exec i s₁ = some s₁')
    (e₂ : exec i s₂ = some s₂') (hadr : addrs i s₁ = addrs i s₂) : AgreeD W τ' d s₁' s₂' := by
  obtain ⟨hb, hdW, hW, hout⟩ := ha
  obtain ⟨hsp, hrd, hwr, -, -⟩ := AgreeD.rest ⟨hb, hdW, hW, hout⟩
  obtain ⟨m', eg, r₂, w₂, y₂, i₂, -⟩ := exec_in (ghost_in s₁ s₂) e₂
  have hb' := RTaintB.step_sound hb hs e₁ eg (by rw [hadr]; exact (addrs_withMS i s₂ _ _).symm)
  obtain ⟨r₁, w₁, sp₁, f₁⟩ := exec_regions e₁
  obtain ⟨-, -, sp₂, f₂⟩ := exec_regions e₂
  refine ⟨agree_of hb' rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_, hdW, hW, ?_⟩
  · rw [sp₁, ghost_sp, sp₂, hsp]
  · rw [r₁, ghost_rd, r₂, hrd]
  · rw [w₁, ghost_wr, w₂, hwr]
  · obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, -, -, -, -, hd, -, -⟩, -⟩, -, -⟩ := hb'
    exact hd
  · obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, -, -, -, -, -, hu, -⟩, -⟩, -, -⟩ := hb'
    exact hu
  · exact ghost_off (by rw [r₁, r₂, hrd]) (by rw [w₁, w₂, hwr])
  · intro x hx hw
    rw [r₂, w₂] at hx
    rw [sp₂] at hw
    have hxw : ∀ r ∈ s₂.wr, ¬ r.Contains x 1 := fun r hr => hx r (List.mem_append_right _ hr)
    have hxw₁ : ∀ r ∈ s₁.wr, ¬ r.Contains x 1 := by rw [hwr]; exact hxw
    rw [f₁ x hxw₁, f₂ x hxw]
    exact hout x hx hw

/-! ## Calls, returns and frames -/

/-- `τ`, with `r` secret: what a load from a frame leaves in it. -/
def eraseT (τ : RTaintB.T) (r : Reg) : RTaintB.T :=
  ((((τ.1.1.1.1.erase r, τ.1.1.1.2), τ.1.1.2.1, if r == .x0 then 64 else τ.1.1.2.2), τ.1.2),
    τ.2.filter (fun e => e.1 != r))

theorem agree_write_erase {τ : RTaintB.T} {s₁ s₂ : State} (h : RTaintB.Agree τ s₁ s₂) (r : Reg)
    (v₁ v₂ : BitVec 64) : RTaintB.Agree (eraseT τ r) (s₁.write .x r v₁) (s₂.write .x r v₂) := by
  obtain ⟨⟨⟨⟨⟨hsp, hgr⟩, hvr⟩, hfl, hx0, hrest⟩, hq⟩, hb₁, hb₂⟩ := h
  obtain ⟨hrd, hwr, hd, hu, hm⟩ := hrest
  refine ⟨⟨⟨⟨⟨hsp, fun q hq' => ?_⟩, hvr⟩, hfl, ?_, hrd, hwr, hd, hu, hm⟩, hq⟩, fun e he => ?_,
    fun e he => ?_⟩
  · obtain ⟨hne, hq'⟩ := RegSet.mem_erase.mp hq'
    rw [RegUpd.gpr_write_of_ne s₁ .x v₁ hne, RegUpd.gpr_write_of_ne s₂ .x v₂ hne]
    exact hgr q hq'
  · show (s₁.write .x r v₁).gpr .x0 >>> (if r == .x0 then 64 else τ.1.1.2.2) =
      (s₂.write .x r v₂).gpr .x0 >>> (if r == .x0 then 64 else τ.1.1.2.2)
    by_cases hr : r = .x0
    · subst hr
      simp only [beq_self_eq_true, ↓reduceIte, RTaint.shift64]
    · have : (r == .x0) = false := by simpa using hr
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      rw [RegUpd.gpr_write_of_ne s₁ .x v₁ (Ne.symm hr),
        RegUpd.gpr_write_of_ne s₂ .x v₂ (Ne.symm hr)]
      exact hx0
  · obtain ⟨he, hne⟩ := List.mem_filter.mp he
    have hne' : ¬ e.1 = r := by simpa using hne
    show ((s₁.write .x r v₁).gpr e.1).toNat < 2 ^ e.2
    rw [RegUpd.gpr_write_of_ne s₁ .x v₁ hne']
    exact hb₁ e he
  · obtain ⟨he, hne⟩ := List.mem_filter.mp he
    have hne' : ¬ e.1 = r := by simpa using hne
    show ((s₂.write .x r v₂).gpr e.1).toNat < 2 ^ e.2
    rw [RegUpd.gpr_write_of_ne s₂ .x v₂ hne']
    exact hb₂ e he

/-- `τ` after a call: the return address, `x16`, `x17` and the flags are public. -/
def callT (τ : RTaintB.T) : RTaintB.T :=
  let g := ((τ.1.1.1.1.insert .x30).insert .x16).insert .x17
  ((((g, τ.1.1.1.2), true, τ.1.1.2.2), τ.1.2),
    τ.2.filter (fun e => e.1 != .x30 && e.1 != .x16 && e.1 != .x17))

theorem agree_call {τ : RTaintB.T} {s₁ s₂ : State} (h : RTaintB.Agree τ s₁ s₂)
    {t₁ t₂ : State} (e₁ : call s₁ = some t₁) (e₂ : call s₂ = some t₂) :
    RTaintB.Agree (callT τ) t₁ t₂ := by
  obtain ⟨⟨⟨⟨⟨hsp, hgr⟩, hvr⟩, -, hx0, hrest⟩, hq⟩, hb₁, hb₂⟩ := h
  obtain ⟨hrd, hwr, hd, hu, hm⟩ := hrest
  simp only [call, Option.some.injEq] at e₁ e₂
  subst e₁ e₂
  refine ⟨⟨⟨⟨⟨hsp, fun q hq' => ?_⟩, hvr⟩, fun _ => ?_, ?_, hrd, hwr, hd, by simp only [hu], hm⟩,
    hq⟩, fun e he => ?_, fun e he => ?_⟩
  · simp only
    by_cases h30 : q = .x30
    · simp only [h30, ↓reduceIte, hu]
    by_cases h16 : q = .x16
    · simp only [h16, reduceCtorEq, ↓reduceIte, hu]
    by_cases h17 : q = .x17
    · simp only [h17, reduceCtorEq, ↓reduceIte, hu]
    simp only [h30, h16, h17, ↓reduceIte]
    rcases RegSet.mem_insert.mp hq' with rfl | hq'
    · exact absurd rfl h17
    rcases RegSet.mem_insert.mp hq' with rfl | hq'
    · exact absurd rfl h16
    rcases RegSet.mem_insert.mp hq' with rfl | hq'
    · exact absurd rfl h30
    exact hgr q hq'
  · simp only [hu]; exact ⟨rfl, rfl, rfl, rfl⟩
  · show (_ : BitVec 64) >>> τ.1.1.2.2 = (_ : BitVec 64) >>> τ.1.1.2.2
    simpa using hx0
  · obtain ⟨he, hne⟩ := List.mem_filter.mp he
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hne
    show ((if e.1 = .x30 then _ else if e.1 = .x16 then _ else if e.1 = .x17 then _ else
      s₁.gpr e.1).toNat < 2 ^ e.2)
    simp only [hne.1.1, hne.1.2, hne.2, ↓reduceIte]
    exact hb₁ e he
  · obtain ⟨he, hne⟩ := List.mem_filter.mp he
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hne
    show ((if e.1 = .x30 then _ else if e.1 = .x16 then _ else if e.1 = .x17 then _ else
      s₂.gpr e.1).toNat < 2 ^ e.2)
    simp only [hne.1.1, hne.1.2, hne.2, ↓reduceIte]
    exact hb₂ e he

theorem sp_sub_add {sp : Addr} {b d : Nat} :
    sp - BitVec.ofNat 64 b + BitVec.ofNat 64 (d + b) = sp + BitVec.ofNat 64 d := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem sp_sub16_add {sp : Addr} {d : Nat} :
    sp - 16 + BitVec.ofNat 64 (d + 16) = sp + BitVec.ofNat 64 d := sp_sub_add (b := 16)

theorem sp_add_sub {sp : Addr} {b d : Nat} (h : b ≤ d) :
    sp + BitVec.ofNat 64 b + BitVec.ofNat 64 (d - b) = sp + BitVec.ofNat 64 d := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- A byte of the frame at `sp`, of `b ≤ d` bytes, is in the window whose top
is `d` bytes above `sp`. -/
theorem in_window {sp x : Addr} {b d W : Nat} (hx : (x - sp).toNat < b) (hb : b ≤ d)
    (hd : d ≤ W) (hW : W < 2 ^ 64) : (window (sp + BitVec.ofNat 64 d) W).Contains x 1 := by
  unfold window Region.Contains
  simp only
  have hxs := (x - sp).isLt
  have e : x - (sp + BitVec.ofNat 64 d - BitVec.ofNat 64 W) =
      (x - sp) + BitVec.ofNat 64 (W - d) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := Nat.mod_le ((x - sp).toNat + (W - d) % 2 ^ 64) (2 ^ 64)
  have := Nat.mod_le (W - d) (2 ^ 64)
  omega

theorem lose_out {m : Mem} {a x : Addr} {n : Nat} {u : Nat → BitVec 64} (h : ¬ (x - a).toNat < n) :
    lose m a n u x = m x := by
  simp only [lose, h, ↓reduceIte]

/-! ## The analysis as a `TaintCT` -/

def stepF (τ : T) (i : Instr) : Option T := (RTaintB.step τ.1 i).map (·, τ.2)

def pushF (W : Nat) (τ : T) (i : Instr) : Option T :=
  match τ.2, i with
  | some d, .alloc b => if d + b ≤ W then some (τ.1, some (d + b)) else none
  | some d, .push _ => if d + 16 ≤ W then some (τ.1, some (d + 16)) else none
  | _, _ => none

def popF (τ : T) (j : Instr) : Option T :=
  match τ.2, j with
  | some d, .free b => if b ≤ d then some (τ.1, some (d - b)) else none
  | some d, .pop r => if 16 ≤ d then some (eraseT τ.1 r, some (d - 16)) else none
  | _, _ => none

def meetF (τ σ : T) : T := (rtaintB.meet τ.1 σ.1, if τ.2 = σ.2 then τ.2 else none)

def leF (τ σ : T) : Bool := rtaintB.le τ.1 σ.1 && (τ.2 == σ.2 || τ.2 == none)

theorem stepF_sound {W : Nat} {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree W τ s₁ s₂)
    (hs : stepF τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂')
    (hadr : addrs i s₁ = addrs i s₂) : Agree W τ' s₁' s₂' := by
  obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.mp hs
  obtain ⟨d, hd, ha⟩ := ha
  exact ⟨d, hd, step_sound ha hσ e₁ e₂ hadr⟩

theorem meetF_left {W : Nat} {τ σ : T} {s₁ s₂ : State} (h : Agree W τ s₁ s₂) :
    Agree W (meetF τ σ) s₁ s₂ := by
  obtain ⟨d, hd, hb, hr⟩ := h
  refine ⟨d, ?_, rtaintB.meet_left hb, hr⟩
  simp only [meetF]
  split
  · exact hd
  · exact Or.inr rfl

theorem meetF_right {W : Nat} {τ σ : T} {s₁ s₂ : State} (h : Agree W σ s₁ s₂) :
    Agree W (meetF τ σ) s₁ s₂ := by
  obtain ⟨d, hd, hb, hr⟩ := h
  refine ⟨d, ?_, rtaintB.meet_right hb, hr⟩
  simp only [meetF]
  split
  · rename_i he; rw [he]; exact hd
  · exact Or.inr rfl

theorem leF_sound {W : Nat} {τ σ : T} {s₁ s₂ : State} (hl : leF τ σ = true) (h : Agree W σ s₁ s₂) :
    Agree W τ s₁ s₂ := by
  simp only [leF, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hl
  obtain ⟨hle, hd'⟩ := hl
  obtain ⟨d, hd, hb, hr⟩ := h
  refine ⟨d, ?_, rtaintB.le_sound hle hb, hr⟩
  rcases hd' with he | he
  · rw [he]; exact hd
  · exact Or.inr he

theorem callF_sound {W : Nat} {τ : T} {s₁ s₂ s₁' s₂' : State} (ha : Agree W τ s₁ s₂)
    (e₁ : call s₁ = some s₁') (e₂ : call s₂ = some s₂') : Agree W (callT τ.1, τ.2) s₁' s₂' := by
  obtain ⟨d, hd, hb, hdW, hW, hout⟩ := ha
  obtain ⟨hsp, hrd, hwr, -, -⟩ := AgreeD.rest ⟨hb, hdW, hW, hout⟩
  have eg : call (ghost s₁ s₂) = some (ghost s₁' s₂') := by
    simp only [call, Option.some.injEq] at e₁ e₂ ⊢
    subst e₁ e₂; rfl
  refine ⟨d, hd, ?_, hdW, hW, ?_⟩
  · have := agree_call hb e₁ eg
    simp only [call, Option.some.injEq] at e₁
    subst e₁
    exact this
  · simp only [call, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    exact hout

theorem pushF_sound {W : Nat} {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State}
    (ha : Agree W τ s₁ s₂) (hs : pushF W τ i = some τ') (e₁ : push i s₁ = some s₁')
    (e₂ : push i s₂ = some s₂') : Agree W τ' s₁' s₂' := by
  obtain ⟨d₀, hd, hb, hdW, hW, hout⟩ := ha
  obtain ⟨hsp, hrd, hwr, hdi, hu⟩ := AgreeD.rest ⟨hb, hdW, hW, hout⟩
  obtain ⟨τb, od⟩ := τ
  cases od with
  | none => simp only [pushF] at hs; cases hs
  | some d =>
    have hd0 : d₀ = d := by
      rcases hd with h | h
      · exact (Option.some.inj h).symm
      · cases h
    subst hd0
    cases i <;> simp only [pushF, reduceCtorEq] at hs
    case alloc b =>
      split at hs <;> [rename_i hle; cases hs]
      obtain rfl := Option.some.inj hs
      simp only [push] at e₁ e₂
      split at e₁ <;> [skip; cases e₁]
      split at e₂ <;> [skip; cases e₂]
      obtain rfl := Option.some.inj e₁
      obtain rfl := Option.some.inj e₂
      refine ⟨d₀ + b, Or.inl rfl, ?_, hle, hW, fun x hx hw => ?_⟩
      · exact agree_of hb rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by simp only [ghost, hsp])
          (by simp only [ghost, hrd]) (by simp only [ghost, hsp, hwr]) hdi hu
          (ghost_off (by simp only [hrd]) (by simp only [hsp, hwr]))
      · simp only [sp_sub_add] at hw
        exact hout x (fun r hr => hx r (by
          simp only [List.mem_append, List.mem_cons] at hr ⊢
          rcases hr with hr | hr
          · exact Or.inl hr
          · exact Or.inr (Or.inr hr))) hw
    case push r =>
      split at hs <;> [rename_i hle; cases hs]
      obtain rfl := Option.some.inj hs
      simp only [push] at e₁ e₂
      split at e₁ <;> [skip; cases e₁]
      split at e₂ <;> [skip; cases e₂]
      obtain rfl := Option.some.inj e₁
      obtain rfl := Option.some.inj e₂
      refine ⟨d₀ + 16, Or.inl rfl, ?_, hle, hW, fun x hx hw => ?_⟩
      · exact agree_of hb rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by simp only [ghost, hsp])
          (by simp only [ghost, hrd]) (by simp only [ghost, hsp, hwr]) hdi hu
          (ghost_off (by simp only [hrd]) (by simp only [hsp, hwr]))
      · simp only [sp_sub16_add] at hw
        have hfr : ¬ (⟨s₂.sp - 16, 16⟩ : Region).Contains x 1 :=
          hx _ (List.mem_append_right _ (List.mem_cons_self ..))
        have hin : InRegions [⟨s₂.sp - 16, 16⟩] (s₂.sp - 16) 8 :=
          ⟨_, List.mem_singleton_self _, by simp [Region.Contains]⟩
        have hnot : ∀ r ∈ [(⟨s₂.sp - 16, 16⟩ : Region)], ¬ r.Contains x 1 := by
          intro r hr; rw [List.mem_singleton] at hr; subst hr; exact hfr
        have hin₁ : InRegions [⟨s₁.sp - 16, 16⟩] (s₁.sp - 16) 8 := by rw [hsp]; exact hin
        have hnot₁ : ∀ r ∈ [(⟨s₁.sp - 16, 16⟩ : Region)], ¬ r.Contains x 1 := by rw [hsp]; exact hnot
        simp only
        rw [← memOff_write_in hin₁ s₁.mem _ x hnot₁, ← memOff_write_in hin s₂.mem _ x hnot]
        exact hout x (fun r hr => hx r (by
          simp only [List.mem_append, List.mem_cons] at hr ⊢
          rcases hr with hr | hr
          · exact Or.inl hr
          · exact Or.inr (Or.inr hr))) hw

theorem popF_sound {W : Nat} {τ τ' : T} {j : Instr} {a₁ a₂ b₁ b₂ c₁ c₂ : State}
    (ha : Agree W τ b₁ b₂) (hs : popF τ j = some τ') (e₁ : pop j a₁ b₁ = some c₁)
    (e₂ : pop j a₂ b₂ = some c₂) : Agree W τ' c₁ c₂ := by
  obtain ⟨d₀, hd, hb, hdW, hW, hout⟩ := ha
  obtain ⟨hsp, hrd, hwr, hdi, hu⟩ := AgreeD.rest ⟨hb, hdW, hW, hout⟩
  obtain ⟨τb, od⟩ := τ
  cases od with
  | none => simp only [popF] at hs; cases hs
  | some d =>
    have hd0 : d₀ = d := by
      rcases hd with h | h
      · exact (Option.some.inj h).symm
      · cases h
    subst hd0
    -- The window, and what the released frame's bytes are not.
    have outFrame : ∀ (n : Nat), n ≤ d₀ → b₂.wr.head? = some ⟨b₂.sp, n⟩ → ∀ x,
        (∀ r ∈ b₂.rd ++ b₂.wr.tail, ¬ r.Contains x 1) →
        ¬ (window (b₂.sp + BitVec.ofNat 64 n + BitVec.ofNat 64 (d₀ - n)) W).Contains x 1 →
        ¬ (x - b₂.sp).toNat < n ∧ b₁.mem x = b₂.mem x := by
      intro n hn hh x hx hw
      rw [sp_add_sub hn] at hw
      have hnx : ¬ (x - b₂.sp).toNat < n := fun hlt => hw (in_window hlt hn hdW hW)
      refine ⟨hnx, hout x (fun r hr => ?_) hw⟩
      have hcons : b₂.wr = ⟨b₂.sp, n⟩ :: b₂.wr.tail := by
        cases hl : b₂.wr with
        | nil => rw [hl] at hh; cases hh
        | cons f t => rw [hl] at hh; simp only [List.head?_cons, Option.some.injEq] at hh; rw [hh]; rfl
      rw [hcons] at hr
      simp only [List.mem_append, List.mem_cons] at hr
      rcases hr with hr | rfl | hr
      · exact hx r (List.mem_append_left _ hr)
      · intro hc; exact hnx (by unfold Region.Contains at hc; simp only at hc; omega)
      · exact hx r (List.mem_append_right _ hr)
    cases j <;> simp only [popF, reduceCtorEq] at hs
    case free n =>
      split at hs <;> [rename_i hle; cases hs]
      obtain rfl := Option.some.inj hs
      simp only [pop] at e₁ e₂
      split at e₁ <;> [rename_i h₁; cases e₁]
      split at e₂ <;> [rename_i h₂; cases e₂]
      obtain rfl := Option.some.inj e₁
      obtain rfl := Option.some.inj e₂
      have hh : b₂.wr.head? = some ⟨b₂.sp, n⟩ := by rw [h₂.2.2.2.2.1, h₂.2.2.2.1]; exact h₂.2.2.2.2.2
      refine ⟨d₀ - n, Or.inl rfl, ?_, Nat.le_trans (Nat.sub_le _ _) hdW, hW, fun x hx hw => ?_⟩
      · exact agree_of hb rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          (by simp only [ghost, hsp]) (by simp only [ghost, hrd]) (by simp only [ghost, hwr]) hdi
          (by simp only [ghost, hu]) (ghost_off (by simp only [hrd]) (by simp only [hwr]))
      · obtain ⟨hnx, hm⟩ := outFrame n hle hh x hx hw
        simp only
        rw [lose_out (by rw [hsp]; exact hnx), lose_out hnx]
        exact hm
    case pop r =>
      split at hs <;> [rename_i hle; cases hs]
      obtain rfl := Option.some.inj hs
      simp only [pop] at e₁ e₂
      split at e₁ <;> [rename_i h₁; cases e₁]
      split at e₂ <;> [rename_i h₂; cases e₂]
      obtain rfl := Option.some.inj e₁
      obtain rfl := Option.some.inj e₂
      have hh : b₂.wr.head? = some ⟨b₂.sp, 16⟩ := by rw [h₂.2.1, h₂.1]; exact h₂.2.2
      have hw' := agree_write_erase hb r (b₁.mem.read b₁.sp 8) (b₂.mem.read b₂.sp 8)
      refine ⟨d₀ - 16, Or.inl rfl, ?_, Nat.le_trans (Nat.sub_le _ _) hdW, hW, fun x hx hw => ?_⟩
      · exact agree_of hw' rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          (by simp only [ghost, State.write, hsp]) (by simp only [ghost, State.write, hrd])
          (by simp only [ghost, State.write, hwr]) (by simp only [ghost, State.write, hdi])
          (by simp only [ghost, State.write, hu])
          (ghost_off (by simp only [State.write, hrd]) (by simp only [hwr]))
      · obtain ⟨hnx, hm⟩ := outFrame 16 hle hh x hx (by simpa [State.write] using hw)
        show lose b₁.mem b₁.sp 16 b₁.unknowns x = lose b₂.mem b₂.sp 16 b₂.unknowns x
        rw [lose_out (by rw [hsp]; exact hnx), lose_out hnx]
        exact hm

end RTaintF

open RTaintF in
/-- `rtaintB` through calls and frames, for code whose frames stay within the
`W` bytes below the stack pointer on entry (see `RTaintF`). -/
def rtaintF (W : Nat) : VG.TaintCT isa where
  T := RTaintF.T
  Agree := RTaintF.Agree W
  step := stepF
  step_sound ha hs e₁ e₂ hadr := stepF_sound ha hs e₁ e₂ hadr
  addrs_length := RTaintCT.addrs_length
  meet := meetF
  meet_left := meetF_left
  meet_right := meetF_right
  le := leF
  le_sound := leF_sound
  call τ := some (callT τ.1, τ.2)
  call_sound ha hs e₁ e₂ _ := by
    obtain rfl := Option.some.inj hs
    exact callF_sound ha e₁ e₂
  callAddrs_length _ _ := rfl
  ret τ := some τ
  ret_sound ha hs e₁ e₂ _ := by
    obtain rfl := Option.some.inj hs
    simp only [isa, ret] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    obtain rfl := Option.some.inj e₁
    obtain rfl := Option.some.inj e₂
    exact ha
  retAddrs_length _ _ := rfl
  push := pushF W
  push_sound ha hs e₁ e₂ _ := pushF_sound ha hs e₁ e₂
  pop := popF
  pop_sound ha hs e₁ e₂ _ := popF_sound ha hs e₁ e₂

namespace RTaintF

end VG.AArch64.RTaintF
