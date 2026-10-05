import VerifiedGarbage.Proof.MlKem.AArch64.KeyGen
import VerifiedGarbage.Impl.MlKem.AArch64.Decaps
import VerifiedGarbage.Impl.MlKem.AArch64.Encaps

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.KemCommon`. -/
section

/-!
# ML-KEM on AArch64: what the proofs of `encaps` and `decaps` share

For a well-formed parameter set `P` (`KemLay.Wf`), stated once.

A function's buffers (`Layout`): its `nb` pointer arguments (`kA`), the first
`nrd` read and the others written, and the four it keeps in `x25`–`x28`
(`slot`, with `scratch` in `x28`). What holds from the prologue to the
epilogue (`KB`): the pointers, our caller's registers saved in `scratch`, the
other callee-saved registers, and the buffers the function only reads. Then
the region facts the calls need, reduced to arithmetic on offsets, and the
prologue and epilogue.
-/

namespace VG.Proof.MlKem.AArch64.Kem

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

/-- A function's buffers: `nb` pointer arguments of lengths `len`, the
first `nrd` read and the others written; argument `slot k` is kept in
`slotReg k` (`scratch` is `slot 3`). -/
structure Layout where
  nb : Nat
  nrd : Nat
  len : Nat → Nat
  slot : Nat → Nat

/-- `scratch`. -/
abbrev Layout.sc (L : VG.Proof.MlKem.AArch64.Kem.Layout) : Nat := L.slot 3

/-- Argument `b`. -/
def kA (s₀ : State) (b : Nat) : Addr := s₀.gpr (argReg b)

/-- The arguments' regions `⟨A b, len b⟩` (for `b < nb`) are disjoint if one
of them is written (`nrd ≤ b`), less than 64 KiB, and apart from the 16 bytes
below `sp`. -/
structure KArgs (A : Nat → Addr) (ln : Nat → Nat) (nb nrd : Nat) (sp : Addr) : Prop where
  disj : ∀ b < nb, ∀ c < nb, b ≠ c → nrd ≤ b ∨ nrd ≤ c → Region.Disjoint ⟨A b, ln b⟩ ⟨A c, ln c⟩
  len : ∀ b < nb, ln b < 65536
  stk : ∀ b < nb, Region.Disjoint ⟨sp - 16, 16⟩ ⟨A b, ln b⟩

theorem KArgs.rdisj {A : Nat → Addr} {ln : Nat → Nat} {nb nrd : Nat} {sp : Addr} (h : VG.Proof.MlKem.AArch64.Kem.KArgs A ln nb nrd sp)
    {b₁ o₁ l₁ b₂ o₂ l₂ : Nat} (hb₁ : b₁ < nb) (hb₂ : b₂ < nb) (f₁ : o₁ + l₁ ≤ ln b₁)
    (f₂ : o₂ + l₂ ≤ ln b₂) (hw : b₁ = b₂ ∨ nrd ≤ b₁ ∨ nrd ≤ b₂) (hs : b₁ ≠ b₂ ∨ o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁) :
    (R A b₁ o₁ l₁).Disjoint (R A b₂ o₂ l₂) := by
  by_cases hb : b₁ = b₂
  · subst hb
    have hl := h.len b₁ hb₁
    have hs' : o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁ := hs.resolve_left (fun h => h rfl)
    intro x h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    exact sep_off (A b₁) hs' (by omega) (by omega) x (Nat.lt_of_succ_le h₁) (Nat.lt_of_succ_le h₂)
  · exact ((h.disj b₁ hb₁ b₂ hb₂ hb (hw.resolve_left hb)).sub_left (R.sub f₁)).sub_right (R.sub f₂)

theorem KArgs.stkR {A : Nat → Addr} {ln : Nat → Nat} {nb nrd : Nat} {sp : Addr} (h : VG.Proof.MlKem.AArch64.Kem.KArgs A ln nb nrd sp)
    {b o l : Nat} (hb : b < nb) (f : o + l ≤ ln b) : Region.Disjoint ⟨sp - 16, 16⟩ (R A b o l) :=
  (h.stk b hb).sub_right (R.sub f)

structure Pre (P : KemLay) (L : VG.Proof.MlKem.AArch64.Kem.Layout) (s₀ : State) : Prop where
  rd : s₀.rd = (List.range L.nrd).map fun b => ⟨VG.Proof.MlKem.AArch64.Kem.kA s₀ b, L.len b⟩
  wr : s₀.wr = (List.range' L.nrd (L.nb - L.nrd)).map fun b => ⟨VG.Proof.MlKem.AArch64.Kem.kA s₀ b, L.len b⟩
  args : VG.Proof.MlKem.AArch64.Kem.KArgs (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.len L.nb L.nrd s₀.sp
  sp16 : 16 ≤ s₀.sp.toNat
  slots : ∀ k < 4, L.slot k < L.nb
  scw : L.nrd ≤ L.sc
  scl : L.len L.sc = P.scl
  wf : P.Wf

/-- Our caller's `x24`–`x28` and `x30`, saved in `scratch`. -/
def Saved (P : KemLay) (L : VG.Proof.MlKem.AArch64.Kem.Layout) (s₀ : State) (m : Mem) : Prop :=
  ∀ k < 6, m.readW (VG.Proof.MlKem.AArch64.Kem.kA s₀ L.sc + BitVec.ofNat 64 (SV P + 8 * k)) 64 = s₀.gpr (kemOwn.getD k .x0)

/-- From the prologue on. -/
structure KB (P : KemLay) (L : VG.Proof.MlKem.AArch64.Kem.Layout) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  ptr : ∀ k < 4, s.gpr (slotReg k) = VG.Proof.MlKem.AArch64.Kem.kA s₀ (L.slot k)
  cs : ∀ r ∈ preserved, r ∉ kemOwn → s.gpr r = s₀.gpr r
  sv : VG.Proof.MlKem.AArch64.Kem.Saved P L s₀ s.mem
  ro : ∀ b < L.nrd, bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ b) (L.len b) = bytesAt s₀.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ b) (L.len b)
  lens : ∀ b < L.nb, L.len b < 65536
  nrd : ∀ {b}, b < L.nrd → b < L.nb
  vcs : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64

variable {L : VG.Proof.MlKem.AArch64.Kem.Layout}

theorem KB.x28 {s₀ s : State} (h : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) : s.gpr .x28 = VG.Proof.MlKem.AArch64.Kem.kA s₀ L.sc := h.ptr 3 (by decide)
theorem KB.x25 {s₀ s : State} (h : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) : s.gpr .x25 = VG.Proof.MlKem.AArch64.Kem.kA s₀ (L.slot 0) := h.ptr 0 (by decide)
theorem KB.x26 {s₀ s : State} (h : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) : s.gpr .x26 = VG.Proof.MlKem.AArch64.Kem.kA s₀ (L.slot 1) := h.ptr 1 (by decide)
theorem KB.x27 {s₀ s : State} (h : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) : s.gpr .x27 = VG.Proof.MlKem.AArch64.Kem.kA s₀ (L.slot 2) := h.ptr 2 (by decide)

theorem slotReg_mem : ∀ k < 4, slotReg k ∈ [Reg.x25, .x26, .x27, .x28] := by decide

theorem slot_pres {k : Nat} (hk : k < 4) : slotReg k ∈ preserved ∧ slotReg k ≠ .x30 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> decide

/-- The saved registers are bytes `[SV, SV + 48)` of `scratch`. -/
abbrev svR (P : KemLay) (L : VG.Proof.MlKem.AArch64.Kem.Layout) (s₀ : State) : Region := R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc (SV P) 48

theorem Saved.frame {s₀ : State} {m m' : Mem} (h : VG.Proof.MlKem.AArch64.Kem.Saved P L s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (VG.Proof.MlKem.AArch64.Kem.svR P L s₀).Disjoint r) : VG.Proof.MlKem.AArch64.Kem.Saved P L s₀ m' := fun k hk => by
  rw [← h k hk]
  refine hf.readW (r := VG.Proof.MlKem.AArch64.Kem.svR P L s₀) ?_ hd (by decide)
  rw [show VG.Proof.MlKem.AArch64.Kem.kA s₀ L.sc + BitVec.ofNat 64 (SV P + 8 * k) = VG.Proof.MlKem.AArch64.Kem.kA s₀ L.sc + BitVec.ofNat 64 (SV P) + BitVec.ofNat 64 (8 * k)
    by rw [ptr_add]]
  exact contains_off (by omega) (by decide)

/-- A region apart from the saved registers and from the buffers the function only reads. -/
abbrev Safe (P : KemLay) (L : VG.Proof.MlKem.AArch64.Kem.Layout) (s₀ : State) (r : Region) : Prop :=
  (VG.Proof.MlKem.AArch64.Kem.svR P L s₀).Disjoint r ∧ ∀ b < L.nrd, Region.Disjoint ⟨VG.Proof.MlKem.AArch64.Kem.kA s₀ b, L.len b⟩ r

theorem pres_kept : ∀ r ∈ preserved, r ∉ kemOwn → r ∉ [Reg.x25, .x26, .x27, .x28] := by decide

/-- The callee-saved registers but `x24` and `x30`. -/
abbrev keptK : List Reg := [.x19, .x20, .x21, .x22, .x23, .x25, .x26, .x27, .x28]

theorem pres_keptK : ∀ r ∈ preserved, r ∉ kemOwn → r ∈ VG.Proof.MlKem.AArch64.Kem.keptK := by decide

theorem slot_keptK : ∀ k < 4, slotReg k ∈ VG.Proof.MlKem.AArch64.Kem.keptK := by decide

/-- Memory changes only in safe regions, and no register the function keeps. -/
theorem KB.frame {s₀ s s' : State} (h : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) {rs : List Region} {regs : List Reg}
    (hk : Keep regs s s') (hf : Frame rs s.mem s'.mem) (hr : ∀ r ∈ VG.Proof.MlKem.AArch64.Kem.keptK, r ∉ regs)
    (hd : ∀ r ∈ rs, VG.Proof.MlKem.AArch64.Kem.Safe P L s₀ r) : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp],
    fun k hk' => by rw [hk.get _ (hr _ (VG.Proof.MlKem.AArch64.Kem.slot_keptK k hk')), h.ptr k hk'],
    fun r hp ho => by rw [hk.get r (hr r (VG.Proof.MlKem.AArch64.Kem.pres_keptK r hp ho)), h.cs r hp ho],
    h.sv.frame hf fun r hr => (hd r hr).1,
    fun b hb => by
      rw [bytesAt_frame hf (fun r hr => (hd r hr).2 b hb) (by have := h.lens b (h.nrd hb); omega), h.ro b hb],
    h.lens, h.nrd, fun r hr => (hk.vcs r hr).trans (h.vcs r hr)⟩

theorem KB.block {s₀ s s' : State} (h : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) {regs : List Reg} (hk : Keep regs s s')
    (hm : s'.mem = s.mem) (hr : ∀ r ∈ VG.Proof.MlKem.AArch64.Kem.keptK, r ∉ regs) : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s' :=
  h.frame (rs := []) hk (by rw [hm]; exact Frame.refl _ _) hr (fun _ h => by cases h)

/-- A call, which changes only memory in safe regions and registers that are
not callee-saved. -/
theorem KB.call {s₀ s s' : State} (h : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) {rs : List Region} (hk : Kept rs s s')
    (hd : ∀ r ∈ rs, VG.Proof.MlKem.AArch64.Kem.Safe P L s₀ r) : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp],
    fun k hk' => by rw [hk.cs _ (VG.Proof.MlKem.AArch64.Kem.slot_pres hk').1 (VG.Proof.MlKem.AArch64.Kem.slot_pres hk').2, h.ptr k hk'],
    fun r hp ho => by rw [hk.cs r hp (fun e => ho (by rw [e]; decide)), h.cs r hp ho],
    h.sv.frame hk.frame fun r hr => (hd r hr).1,
    fun b hb => by
      rw [bytesAt_frame hk.frame (fun r hr => (hd r hr).2 b hb) (by have := h.lens b (h.nrd hb); omega),
        h.ro b hb],
    h.lens, h.nrd, fun r hr => (hk.vcs r hr).trans (h.vcs r hr)⟩

/-- Arithmetic on the offsets, with the facts of `‹Pre _ _ _›`. -/
macro "kom" : tactic => `(tactic| ((try have := (‹Pre _ _ _›).wf.facts); lom))

/-! ## Regions -/

theorem Pre.lt {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {k : Nat} (hk : k < 4) : L.slot k < L.nb := hp.slots k hk

theorem Pre.scb {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) : L.sc < L.nb := hp.slots 3 (by decide)

/-- The saved registers are in `scratch`. -/
theorem Pre.sv {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) : SV P + 48 ≤ L.len L.sc := by
  have := hp.wf; rw [hp.scl]; lom

/-- A buffer of `scratch`. -/
theorem Pre.fs {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {o l : Nat} (h : o + l ≤ SV P + 48) : o + l ≤ L.len L.sc :=
  Nat.le_trans h hp.sv

/-- A written buffer is safe, if apart from the saved registers. -/
theorem safe_R {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {b o l : Nat} (hb : L.nrd ≤ b ∧ b < L.nb) (f : o + l ≤ L.len b)
    (hs : b ≠ L.sc ∨ SV P + 48 ≤ o ∨ o + l ≤ SV P) : VG.Proof.MlKem.AArch64.Kem.Safe P L s₀ (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) b o l) :=
  ⟨hp.args.rdisj hp.scb hb.2 hp.sv f (.inr (.inl hp.scw)) (by
      rcases hs with hs | hs
      · exact .inl (Ne.symm hs)
      · exact .inr (by omega)),
    fun c hc => (hp.args.disj c (by omega) b hb.2 (by omega) (.inr hb.1)).sub_right (R.sub f)⟩

theorem below_R {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {b o l : Nat} (hb : b < L.nb) (f : o + l ≤ L.len b) :
    (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) b o l).Disjoint (below s₀.sp 16) := by
  rw [below16]; exact (hp.args.stkR hb f).symm

theorem safe_below {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) : VG.Proof.MlKem.AArch64.Kem.Safe P L s₀ (below s₀.sp 16) :=
  ⟨VG.Proof.MlKem.AArch64.Kem.below_R hp hp.scb hp.sv, fun c hc => by
    rw [below16]; exact (hp.args.stk c (by have := hp.scw; have := hp.scb; omega)).symm⟩

/-- A buffer of `scratch` below the saved registers is safe. -/
theorem safe_scr {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {o l : Nat} (h : o + l ≤ SV P) : VG.Proof.MlKem.AArch64.Kem.Safe P L s₀ (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc o l) :=
  VG.Proof.MlKem.AArch64.Kem.safe_R hp ⟨hp.scw, hp.scb⟩ (hp.fs (by omega)) (.inr (.inr h))

theorem stk_R {s₀ s : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) (h : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) {b o l : Nat} (hb : b < L.nb)
    (f : o + l ≤ L.len b) : (stk s).Disjoint (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) b o l) := by
  rw [stk_sp h.sp]; exact hp.args.stkR hb f

/-- Regions a callee may write. -/
theorem cov_w {s₀ s : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) (h : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) {b o l : Nat} (hb : L.nrd ≤ b ∧ b < L.nb)
    (f : o + l ≤ L.len b) : Covers [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) b o l] s.wr := by
  rw [h.wr, hp.wr]
  exact R.cov (List.mem_map.mpr ⟨b, List.mem_range'_1.mpr ⟨hb.1, by omega⟩, rfl⟩) f

/-- Regions a callee may read. -/
theorem cov_r {s₀ s : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) (h : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) {b o l : Nat} (hb : b < L.nb)
    (f : o + l ≤ L.len b) : Covers [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) b o l] (s.rd ++ s.wr) := by
  rw [h.rd, h.wr, hp.rd, hp.wr]
  by_cases hr : b < L.nrd
  · exact R.cov (List.mem_append_left _ (List.mem_map.mpr ⟨b, List.mem_range.mpr hr, rfl⟩)) f
  · exact R.cov (List.mem_append_right _
      (List.mem_map.mpr ⟨b, List.mem_range'_1.mpr ⟨by omega, by omega⟩, rfl⟩)) f

/-- Scratch buffers. -/
theorem cov_s {s₀ s : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) (h : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) {o l : Nat} (f : o + l ≤ SV P + 48) :
    Covers [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc o l] s.wr :=
  VG.Proof.MlKem.AArch64.Kem.cov_w hp h ⟨hp.scw, hp.scb⟩ (hp.fs f)

theorem cov_sr {s₀ s : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) (h : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) {o l : Nat} (f : o + l ≤ SV P + 48) :
    Covers [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc o l] (s.rd ++ s.wr) :=
  VG.Proof.MlKem.AArch64.Kem.cov_r hp h hp.scb (hp.fs f)

/-- Two buffers of `scratch`. -/
theorem sdisj {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {o₁ l₁ o₂ l₂ : Nat} (f₁ : o₁ + l₁ ≤ SV P + 48)
    (f₂ : o₂ + l₂ ≤ SV P + 48) (h : o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁) :
    (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc o₁ l₁).Disjoint (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc o₂ l₂) :=
  hp.args.rdisj hp.scb hp.scb (hp.fs f₁) (hp.fs f₂) (.inl rfl) (.inr h)

theorem hsetup {s₀ s : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) (h : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) {rate : Nat} (hr : rate ∈ Spec.Sha3.rates) :
    HSetup .x28 ST WK rate s := by
  have hw := hp.wf
  have f : ∀ {o l : Nat}, o + l ≤ 840 → o + l ≤ SV P + 48 := fun h => by lom
  have e : ∀ o l, (⟨s.gpr .x28 + BitVec.ofNat 64 o, l⟩ : Region) = R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc o l := fun o l => by
    rw [h.x28]
  refine ⟨by decide, by decide, by decide, hr, ?_, by rw [h.sp]; exact hp.sp16, ?_, ?_, ?_⟩
  · rw [e, e]; exact VG.Proof.MlKem.AArch64.Kem.sdisj hp (f (by decide)) (f (by decide)) (by decide)
  · rw [e]; exact VG.Proof.MlKem.AArch64.Kem.stk_R hp h hp.scb (hp.fs (f (by decide)))
  · rw [e]; exact VG.Proof.MlKem.AArch64.Kem.stk_R hp h hp.scb (hp.fs (f (by decide)))
  · rw [e, e]; exact covers_cons (VG.Proof.MlKem.AArch64.Kem.cov_s hp h (f (by decide))) (VG.Proof.MlKem.AArch64.Kem.cov_s hp h (f (by decide)))

/-- A piece at bytes `[o, o + l)` of the buffer in `slotReg k`, apart from the
Keccak state and working space. -/
theorem pieceOk {s₀ s : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) (h : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) {w : Bool} {k o l : Nat} (hk : k < 4)
    (f : o + l ≤ L.len (L.slot k)) (hs : L.slot k ≠ L.sc ∨ 840 ≤ o) (hl : l < 65536)
    (hw : w = true → L.nrd ≤ L.slot k) : PieceOk .x28 ST WK s w ⟨slotReg k, o, l⟩ := by
  have hb := hp.lt hk
  have eb : preg s ⟨slotReg k, o, l⟩ = R (VG.Proof.MlKem.AArch64.Kem.kA s₀) (L.slot k) o l := by simp only [preg, h.ptr k hk]
  have e : ∀ o l, (⟨s.gpr .x28 + BitVec.ofNat 64 o, l⟩ : Region) = R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc o l := fun o l => by
    rw [h.x28]
  have ho : o < 65536 := by have := hp.args.len _ hb; omega
  have fs : ∀ {o l : Nat}, o + l ≤ 840 → o + l ≤ L.len L.sc := fun h => hp.fs (by have := hp.wf; lom)
  refine ⟨VG.Proof.MlKem.AArch64.Kem.slot_pres hk, ho, hl, ?_, ?_, ?_, ?_⟩
  · rw [eb, VG.Proof.MlKem.AArch64.STr, e]
    exact hp.args.rdisj hb hp.scb f (fs (by decide)) (.inr (.inr hp.scw)) (by
      rcases hs with hs | hs
      · exact .inl hs
      · exact .inr (.inr (by simp only [KEM.ST]; omega)))
  · rw [eb, VG.Proof.MlKem.AArch64.WKr, e]
    exact hp.args.rdisj hb hp.scb f (fs (by decide)) (.inr (.inr hp.scw)) (by
      rcases hs with hs | hs
      · exact .inl hs
      · exact .inr (.inr (by simp only [KEM.WK]; omega)))
  · rw [eb]; exact VG.Proof.MlKem.AArch64.Kem.stk_R hp h hb f
  · rw [eb]
    cases w
    · exact VG.Proof.MlKem.AArch64.Kem.cov_r hp h hb f
    · exact VG.Proof.MlKem.AArch64.Kem.cov_w hp h ⟨hw rfl, hb⟩ f

/-- An output of a hash: bytes `[o, o + l)` of a written buffer, apart from
the saved registers. -/
def OutOk (P : KemLay) (L : VG.Proof.MlKem.AArch64.Kem.Layout) (p : Piece) : Prop :=
  ∃ k o l, p = ⟨slotReg k, o, l⟩ ∧ k < 4 ∧ L.nrd ≤ L.slot k ∧ o + l ≤ L.len (L.slot k) ∧
    (L.slot k ≠ L.sc ∨ SV P + 48 ≤ o ∨ o + l ≤ SV P)

/-- A hash keeps what holds throughout. -/
theorem KB.hash {s₀ s s' : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) (h : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) {outs : List Piece}
    (hk : Kept (STr .x28 ST s :: WKr .x28 WK s :: below s.sp 16 :: outs.map (preg s)) s s')
    (ho : ∀ p ∈ outs, VG.Proof.MlKem.AArch64.Kem.OutOk P L p) : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s' := by
  have hw := hp.wf
  refine h.call hk fun r hr => ?_
  have e : ∀ o l, (⟨s.gpr .x28 + BitVec.ofNat 64 o, l⟩ : Region) = R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc o l := fun o l => by
    rw [h.x28]
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [VG.Proof.MlKem.AArch64.STr, e]; exact VG.Proof.MlKem.AArch64.Kem.safe_scr hp (by lom)
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [VG.Proof.MlKem.AArch64.WKr, e]; exact VG.Proof.MlKem.AArch64.Kem.safe_scr hp (by lom)
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [h.sp]; exact VG.Proof.MlKem.AArch64.Kem.safe_below hp
  obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr
  obtain ⟨k, o, l, rfl, hk, hw, f, hs⟩ := ho p hp'
  simp only [preg, h.ptr k hk]
  exact VG.Proof.MlKem.AArch64.Kem.safe_R hp ⟨hw, hp.lt hk⟩ f hs

/-! ## The prologue and the epilogue -/

theorem argReg_not (b : Nat) : argReg b ≠ .x24 ∧ argReg b ≠ .x25 ∧ argReg b ≠ .x26 ∧ argReg b ≠ .x27 ∧
    argReg b ≠ .x28 := by
  unfold argReg
  rcases b with _ | _ | _ | _ | _ | b <;> simp

theorem cov_w₀ {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {b o l : Nat} (hb : L.nrd ≤ b ∧ b < L.nb)
    (f : o + l ≤ L.len b) : Covers [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) b o l] s₀.wr := by
  rw [hp.wr]
  exact R.cov (List.mem_map.mpr ⟨b, List.mem_range'_1.mpr ⟨hb.1, by omega⟩, rfl⟩) f

/-- What the prologue leaves. -/
structure AfterPro (P : KemLay) (L : VG.Proof.MlKem.AArch64.Kem.Layout) (s₀ s : State) : Prop where
  kb : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s
  x24 : s.gpr .x24 = 1
  keep : Keep [.x25, .x26, .x27, .x28, .x24] s₀ s
  mem : s.mem = s₀.mem ∨ Frame [VG.Proof.MlKem.AArch64.Kem.svR P L s₀] s₀.mem s.mem

theorem pres_pro : ∀ r ∈ preserved, r ∉ kemOwn → r ∉ [Reg.x25, .x26, .x27, .x28, .x24] := by decide

theorem prologue_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) :
    WP isa (.block (P.kemPrologue L.sc [L.slot 0, L.slot 1, L.slot 2, L.slot 3])) s₀ (VG.Proof.MlKem.AArch64.Kem.AfterPro P L s₀) := by
  have hw := hp.wf
  rw [KemLay.kemPrologue, List.append_assoc, WP.block_append_iff]
  have hin : ∀ k < kemOwn.length, InRegions s₀.wr (VG.Proof.MlKem.AArch64.Kem.kA s₀ L.sc + BitVec.ofNat 64 (SV P + 8 * k)) 8 :=
    fun k hk => in_R (VG.Proof.MlKem.AArch64.Kem.cov_w₀ hp ⟨hp.scw, hp.scb⟩ (o := SV P) (l := 48) hp.sv) (k := 8 * k)
      (n := 8) (by simp only [kemOwn, List.length_cons, List.length_nil] at hk; omega) (by decide)
  have hsv : SV P + 8 * kemOwn.length ≤ 32768 := by simp only [kemOwn, List.length_cons, List.length_nil]; lom
  refine WP.mono (WP.preservedV (KeyGen.saves_ok (VG.Proof.MlKem.AArch64.Kem.kA s₀ L.sc) (argReg L.sc) (SV P) kemOwn hsv (by lom) 6
    (by decide) rfl hin) (hc := rfl))
    fun s₁ ⟨⟨g₁, r₁, w₁, p₁, z₁, f₁⟩, hv₁⟩ => ?_
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD_cons_zero,
    List.getD_cons_succ]
  refine wp_mov fun s₂ h₂ e₂ => wp_mov fun s₃ h₃ e₃ => wp_mov fun s₄ h₄ e₄ => wp_mov fun s₅ h₅ e₅ =>
    wp_movz fun s₆ h₆ e₆ => wp_nil ?_
  have o₆ : Only [.x25, .x26, .x27, .x28, .x24] s₁ s₆ := ((((h₂.trans h₃).trans h₄).trans h₅).trans h₆).mono
  have k₆ : Keep [.x25, .x26, .x27, .x28, .x24] s₀ s₆ :=
    ⟨fun r hr => by rw [o₆.get r hr, g₁], by rw [o₆.rd, r₁], by rw [o₆.wr, w₁], by rw [o₆.sp, p₁], fun r hr => (o₆.vcs r hr).trans (hv₁ r hr)⟩
  have a : ∀ (b : Nat) {w w' : State} {r : Reg}, Only [r] w w' → r ∈ [Reg.x24, .x25, .x26, .x27, .x28] →
      w'.gpr (argReg b) = w.gpr (argReg b) := fun b _ _ r h hr => h.get _ fun h' => by
    have e := List.mem_singleton.mp h'
    have := VG.Proof.MlKem.AArch64.Kem.argReg_not b
    rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
    exacts [this.1 e, this.2.1 e, this.2.2.1 e, this.2.2.2.1 e, this.2.2.2.2 e]
  have v₁ : ∀ b, s₁.gpr (argReg b) = VG.Proof.MlKem.AArch64.Kem.kA s₀ b := fun b => by rw [g₁]; rfl
  refine ⟨⟨k₆.rd, k₆.wr, k₆.sp, fun k hk => ?_, fun r hr ho => k₆.get r (VG.Proof.MlKem.AArch64.Kem.pres_pro r hr ho), fun k hk => ?_,
    fun b hb => ?_, hp.args.len, (fun hb => by have := hp.scw; have := hp.scb; omega), k₆.vcs⟩, by rw [e₆]; rfl, k₆,
    .inr (by rw [o₆.mem]; exact f₁)⟩
  · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · rw [h₆.get (slotReg 0) (by decide), h₅.get (slotReg 0) (by decide), h₄.get (slotReg 0) (by decide),
        h₃.get (slotReg 0) (by decide), e₂, v₁]
    · rw [h₆.get (slotReg 1) (by decide), h₅.get (slotReg 1) (by decide), h₄.get (slotReg 1) (by decide),
        e₃, a _ h₂ (by decide), v₁]
    · rw [h₆.get (slotReg 2) (by decide), h₅.get (slotReg 2) (by decide), e₄, a _ h₃ (by decide),
        a _ h₂ (by decide), v₁]
    · rw [h₆.get (slotReg 3) (by decide), e₅, a _ h₄ (by decide), a _ h₃ (by decide), a _ h₂ (by decide), v₁]
  · rw [o₆.mem]; exact z₁ k hk
  · rw [o₆.mem]
    exact bytesAt_frame f₁ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (hp.args.disj b (by have := hp.scw; have := hp.scb; omega) L.sc hp.scb
        (by have := hp.scw; omega) (.inr hp.scw)).sub_right (R.sub hp.sv)) (by
          have := hp.args.len b (by have := hp.scw; have := hp.scb; omega); omega)

/-- Our caller's registers back, and the result. -/
theorem epilogue_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {u : State} (hk : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ u) :
    WP isa (.block P.kemEpilogue) u fun u' =>
      abiPreserved s₀ u' ∧ u'.gpr .x0 = u.gpr .x24 ∧ u'.mem = u.mem := by
  have hw := hp.wf
  have h8 : SV P % 8 = 0 ∧ SV P + 48 ≤ 32768 := by lom
  have cv := VG.Proof.MlKem.AArch64.Kem.cov_sr hp hk (o := SV P) (l := 48) (Nat.le_refl _)
  have ld : ∀ k < 6, ∀ {w : State}, w.rd = u.rd ∧ w.wr = u.wr ∧ w.mem = u.mem ∧ w.gpr .x28 = VG.Proof.MlKem.AArch64.Kem.kA s₀ L.sc →
      w.gpr .x28 + BitVec.ofNat 64 (SV P + 8 * k) = VG.Proof.MlKem.AArch64.Kem.kA s₀ L.sc + BitVec.ofNat 64 (SV P + 8 * k) ∧
      InRegions (w.rd ++ w.wr) (VG.Proof.MlKem.AArch64.Kem.kA s₀ L.sc + BitVec.ofNat 64 (SV P + 8 * k)) 8 ∧
      w.mem.readW (VG.Proof.MlKem.AArch64.Kem.kA s₀ L.sc + BitVec.ofNat 64 (SV P + 8 * k)) 64 = s₀.gpr (kemOwn.getD k .x0) :=
    fun k hk' {w} ⟨hr, hw, hm, h28⟩ =>
      ⟨by rw [h28], by rw [hr, hw]; exact in_R cv (by omega) (by decide), by rw [hm]; exact hk.sv k hk'⟩
  have st : ∀ {w w' : State} {r : Reg}, Only [r] w w' → r ≠ .x28 →
      w.rd = u.rd ∧ w.wr = u.wr ∧ w.mem = u.mem ∧ w.gpr .x28 = VG.Proof.MlKem.AArch64.Kem.kA s₀ L.sc →
      w'.rd = u.rd ∧ w'.wr = u.wr ∧ w'.mem = u.mem ∧ w'.gpr .x28 = VG.Proof.MlKem.AArch64.Kem.kA s₀ L.sc :=
    fun h hr ⟨a, b, c, d⟩ => ⟨by rw [h.rd, a], by rw [h.wr, b], by rw [h.mem, c],
      by rw [h.get .x28 (by simpa using Ne.symm hr), d]⟩
  rw [KemLay.kemEpilogue, show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl]
  simp only [List.map_cons, List.map_nil]
  refine wp_mov fun s₁ h₁ e₁ => ?_
  have g₁ := st h₁ (by decide) ⟨rfl, rfl, rfl, hk.x28⟩
  have l₁ := ld 0 (by decide) g₁
  refine wp_ldrx (a := VG.Proof.MlKem.AArch64.Kem.kA s₀ L.sc + BitVec.ofNat 64 (SV P + 8 * 0)) (by lom) l₁.1 l₁.2.1 fun s₂ h₂ e₂ => ?_
  have g₂ := st h₂ (by decide) g₁
  have l₂ := ld 1 (by decide) g₂
  refine wp_ldrx (a := VG.Proof.MlKem.AArch64.Kem.kA s₀ L.sc + BitVec.ofNat 64 (SV P + 8 * 1)) (by lom) l₂.1 l₂.2.1 fun s₃ h₃ e₃ => ?_
  have g₃ := st h₃ (by decide) g₂
  have l₃ := ld 2 (by decide) g₃
  refine wp_ldrx (a := VG.Proof.MlKem.AArch64.Kem.kA s₀ L.sc + BitVec.ofNat 64 (SV P + 8 * 2)) (by lom) l₃.1 l₃.2.1 fun s₄ h₄ e₄ => ?_
  have g₄ := st h₄ (by decide) g₃
  have l₄ := ld 3 (by decide) g₄
  refine wp_ldrx (a := VG.Proof.MlKem.AArch64.Kem.kA s₀ L.sc + BitVec.ofNat 64 (SV P + 8 * 3)) (by lom) l₄.1 l₄.2.1 fun s₅ h₅ e₅ => ?_
  have g₅ := st h₅ (by decide) g₄
  have l₅ := ld 4 (by decide) g₅
  refine wp_ldrx (a := VG.Proof.MlKem.AArch64.Kem.kA s₀ L.sc + BitVec.ofNat 64 (SV P + 8 * 4)) (by lom) l₅.1 l₅.2.1 fun s₆ h₆ e₆ => ?_
  have g₆ := st h₆ (by decide) g₅
  have l₆ := ld 5 (by decide) g₆
  refine wp_ldrx (a := VG.Proof.MlKem.AArch64.Kem.kA s₀ L.sc + BitVec.ofNat 64 (SV P + 8 * 5)) (by lom) l₆.1 l₆.2.1 fun s₇ h₇ e₇ =>
    wp_nil ?_
  have o₇ : Only [.x0, .x24, .x30, .x25, .x26, .x27, .x28] u s₇ :=
    ((((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).mono
  refine ⟨⟨fun r hr => ?_, by rw [o₇.sp, hk.sp], fun r hr => (o₇.vcs r hr).trans (hk.vcs r hr)⟩, ?_, o₇.mem⟩
  · by_cases ho : r ∈ kemOwn
    · rcases mem6 ho with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h₇.get .x24 (by decide), h₆.get .x24 (by decide), h₅.get .x24 (by decide),
          h₄.get .x24 (by decide), h₃.get .x24 (by decide)]
        exact e₂.trans l₁.2.2
      · rw [h₇.get .x30 (by decide), h₆.get .x30 (by decide), h₅.get .x30 (by decide),
          h₄.get .x30 (by decide)]
        exact e₃.trans l₂.2.2
      · rw [h₇.get .x25 (by decide), h₆.get .x25 (by decide), h₅.get .x25 (by decide)]
        exact e₄.trans l₃.2.2
      · rw [h₇.get .x26 (by decide), h₆.get .x26 (by decide)]
        exact e₅.trans l₄.2.2
      · rw [h₇.get .x27 (by decide)]
        exact e₆.trans l₅.2.2
      · exact e₇.trans l₆.2.2
    · rw [o₇.get r (by revert r; decide), hk.cs r hr ho]
  · rw [h₇.get .x0 (by decide), h₆.get .x0 (by decide), h₅.get .x0 (by decide), h₄.get .x0 (by decide),
      h₃.get .x0 (by decide), h₂.get .x0 (by decide), e₁]

end VG.Proof.MlKem.AArch64.Kem

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.KemOps`. -/
section

/-!
# ML-KEM on AArch64: the building blocks of `encaps` and `decaps`

Each building block (`prfCbdWith keccak.callee`, `nttAt`, `nttInvAt`, `mulAt`,
`addAt`, `subAt`, `ceAt`, `ddAt`, `dec12At`, and `ceLAt` and `ddLAt` at the
widths `d_u` and `d_v`): what it needs, what it computes, what it keeps (`KB`,
`x24`), and the only memory it changes (`Frame`), so that the facts
established before it survive it. The functions at the widths `d_u` and `d_v`
are a parameter set's own (`KemLay.Calls`).
-/

namespace VG.Proof.MlKem.AArch64.Kem

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay} {L : VG.Proof.MlKem.AArch64.Kem.Layout}

/-- The functions of `P` at the widths `d_u` and `d_v` meet their contracts. -/
structure Calls (P : KemLay) : Prop where
  ce : ∀ {s : State} {f o : Addr} {d : Nat}, s.gpr .x0 = f → ((s.gpr .x1).setWidth 32).toNat = d →
    s.gpr .x2 = o → (s.gpr .x3).toNat = 32 * d → (d = P.du ∨ d = P.dv) →
    Region.Disjoint ⟨f, 1024⟩ ⟨o, 32 * d⟩ → Reduced s.mem f → Covers [⟨f, 1024⟩, ⟨o, 32 * d⟩] (s.rd ++ s.wr) →
    Covers [⟨o, 32 * d⟩] s.wr → ∀ {Q : State → Prop},
    (∀ s', Kept [⟨o, 32 * d⟩] s s' → bytesAt s'.mem o (32 * d) = compressEncode d (polyAt s.mem f) → Q s') →
    WP isa (.call P.ceName P.ce) s Q
  dd : ∀ {s : State} {b f : Addr} {d : Nat}, s.gpr .x0 = b → (s.gpr .x1).toNat = 32 * d →
    ((s.gpr .x2).setWidth 32).toNat = d → s.gpr .x3 = f → (d = P.du ∨ d = P.dv) →
    Region.Disjoint ⟨b, 32 * d⟩ ⟨f, 1024⟩ → Covers [⟨b, 32 * d⟩, ⟨f, 1024⟩] (s.rd ++ s.wr) →
    Covers [⟨f, 1024⟩] s.wr → ∀ {Q : State → Prop},
    (∀ s', Kept [⟨f, 1024⟩] s s' → PolyIs s'.mem f (decodeDecompress d (bytesAt s.mem b (32 * d))) → Q s') →
    WP isa (.call P.ddName P.dd) s Q

/-- Buffer `o` of `scratch`. -/
abbrev sA (L : VG.Proof.MlKem.AArch64.Kem.Layout) (s₀ : State) (o : Nat) : Addr := VG.Proof.MlKem.AArch64.Kem.kA s₀ L.sc + BitVec.ofNat 64 o

/-- A polynomial buffer in `scratch`, past the NTT's working space and below the saved registers. -/
def PO (P : KemLay) (off : Nat) : Prop := AH ≤ off ∧ off + 1024 ≤ SV P

theorem PO.le {off : Nat} (h : VG.Proof.MlKem.AArch64.Kem.PO P off) : off + 1024 ≤ SV P + 48 := by
  obtain ⟨-, h⟩ := h; omega

theorem PO.safe {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {off : Nat} (h : VG.Proof.MlKem.AArch64.Kem.PO P off) :
    VG.Proof.MlKem.AArch64.Kem.Safe P L s₀ (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc off 1024) :=
  VG.Proof.MlKem.AArch64.Kem.safe_scr hp h.2

theorem PO.ns {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {off : Nat} (h : VG.Proof.MlKem.AArch64.Kem.PO P off) :
    (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc off 1024).Disjoint (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc NS 1024) :=
  VG.Proof.MlKem.AArch64.Kem.sdisj hp h.le (by kom) (.inr (by obtain ⟨h, -⟩ := h; kom))

theorem e28 {s₀ s : State} (hk : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) (o : Nat) :
    s.gpr .x28 + BitVec.ofNat 64 o = VG.Proof.MlKem.AArch64.Kem.sA L s₀ o := by rw [hk.x28]

/-- What `(prfCbdWith keccak.callee)` writes. -/
abbrev pcW (L : VG.Proof.MlKem.AArch64.Kem.Layout) (s₀ : State) (off : Nat) : List Region :=
  [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc ST 200, R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc WK 640, below s₀.sp 16, R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc (RB + 32) 1,
    R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc PB 128, R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc off 1024]

/-- `SamplePolyCBD₂(PRF₂(r, N))`, with `r` at `RB`. -/
theorem prfCbd_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {N off : Nat} (hN : N < 256) (ho : VG.Proof.MlKem.AArch64.Kem.PO P off) {s : State}
    (hk : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) {rv : List Byte} (hr : bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ RB) 32 = rv) :
    WP isa ((prfCbdWith keccak.callee) N off) s fun s' => VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s' ∧ Frame (VG.Proof.MlKem.AArch64.Kem.pcW L s₀ off) s.mem s'.mem ∧
      PolyIs s'.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ off) (cbd rv N) ∧ s'.gpr .x24 = s.gpr .x24 := by
  have fo := ho.le
  have hsl : ∀ {o l : Nat}, o + l ≤ SV P + 48 → o + l ≤ L.len L.sc := hp.fs
  -- `N` after `r`
  refine WP.seq (wp_movz fun s₁ h₁ e₁ => wp_strb (a := VG.Proof.MlKem.AArch64.Kem.sA L s₀ (RB + 32)) (by decide)
    (by rw [h₁.get .x28, VG.Proof.MlKem.AArch64.Kem.e28 hk]) (by
      rw [h₁.wr]; exact in_R (VG.Proof.MlKem.AArch64.Kem.cov_s hp hk (o := RB + 32) (l := 1) (by kom)) (k := 0) (by decide)
        (by decide)) fun s₂ h₂ => wp_nil ?_)
  have m₂ : s₂.mem = s.mem.writeW (VG.Proof.MlKem.AArch64.Kem.sA L s₀ (RB + 32)) ((s₁.gpr .x9).setWidth 8) := by
    rw [h₂.mem, h₁.mem]
  have f₂ : Frame [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc (RB + 32) 1] s.mem s₂.mem := by
    rw [m₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (R.contains (k := 0) (by decide)
      (by decide))
  have kb₂ : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s₂ := hk.frame (h₁.keep.trans h₂.keep) f₂ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact VG.Proof.MlKem.AArch64.Kem.safe_scr hp (by kom)
  have msg : bytesAt s₂.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ RB) 33 = rv ++ [BitVec.ofNat 8 N] := by
    rw [show 33 = 32 + 1 from rfl, bytesAt_add, bytesAt_frame (p := VG.Proof.MlKem.AArch64.Kem.sA L s₀ RB) (len := 32)
      f₂ (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact VG.Proof.MlKem.AArch64.Kem.sdisj hp (by kom) (by kom) (by decide)) (by decide), hr]
    refine congrArg (rv ++ ·) (bytesAt_eq rfl fun k hk' => ?_)
    have : k = 0 := by omega
    subst this
    rw [ptr_zero, ptr_add, m₂, VG.WriteBytes.writeW8_apply, ite_eq_left rfl, e₁]
    exact sfx8 hN
  -- `PRF₂(r, N)`
  refine WP.seq (WP.mono (hashWith_ok keccak (VG.Proof.MlKem.AArch64.Kem.hsetup hp kb₂ (by decide : 136 ∈ Spec.Sha3.rates)) (sfx := 0x1f)
    (by decide) (ins := [⟨.x28, RB, 33⟩]) (outs := [⟨.x28, PB, 128⟩]) (by simp)
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact VG.Proof.MlKem.AArch64.Kem.pieceOk (k := 3) hp kb₂ (by decide) (hsl (by kom)) (.inr (by decide)) (by decide)
        (fun _ => hp.scw))
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact VG.Proof.MlKem.AArch64.Kem.pieceOk (k := 3) hp kb₂ (by decide) (hsl (by kom)) (.inr (by decide)) (by decide)
        (fun _ => hp.scw))
    (List.pairwise_singleton _ _)) fun s₃ ⟨k₃, o₃⟩ => ?_)
  have kb₃ : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s₃ := kb₂.hash hp k₃ fun p hp' => by
    rw [List.mem_singleton.mp hp']
    exact ⟨3, PB, 128, rfl, by decide, hp.scw, hsl (by kom), .inr (.inr (by kom))⟩
  have prf₃ : bytesAt s₃.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ PB) 128 = prf 2 rv (BitVec.ofNat 8 N) := by
    obtain ⟨o, -⟩ := o₃
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      VG.Proof.MlKem.AArch64.Kem.e28 kb₂] at o
    rw [msg] at o
    rw [o, prf_eq]; rfl
  have k₃' := k₃
  simp only [VG.Proof.MlKem.AArch64.STr, VG.Proof.MlKem.AArch64.WKr, preg, List.map_cons, List.map_nil,
    kb₂.x28, kb₂.sp] at k₃'
  -- `SamplePolyCBD₂`
  refine WP.seq (wp_ptrTo (by decide) (by decide) fun s₄ h₄ e₄ => wp_ptrTo' (by decide)
    (by obtain ⟨-, h⟩ := ho; kom) fun s₅ h₅ e₅ => ?_)
  have kb₅ := kb₃.block (h₄.trans h₅).keep (by rw [h₅.mem, h₄.mem]) (by decide)
  refine cbd2_call (b := VG.Proof.MlKem.AArch64.Kem.sA L s₀ PB) (f := VG.Proof.MlKem.AArch64.Kem.sA L s₀ off)
    (by rw [h₅.get .x0, e₄, VG.Proof.MlKem.AArch64.Kem.e28 kb₃]) (by rw [e₅, h₄.get .x28, VG.Proof.MlKem.AArch64.Kem.e28 kb₃])
    (VG.Proof.MlKem.AArch64.Kem.sdisj hp (by kom) fo (.inl (by obtain ⟨h, -⟩ := ho; kom)))
    (covers_cons (VG.Proof.MlKem.AArch64.Kem.cov_sr hp kb₅ (o := PB) (l := 128) (by kom)) (VG.Proof.MlKem.AArch64.Kem.cov_sr hp kb₅ fo))
    (VG.Proof.MlKem.AArch64.Kem.cov_s hp kb₅ fo) fun s₆ k₆ p₆ => ?_
  have kb₆ := kb₅.call k₆ fun r hr => by rw [List.mem_singleton.mp hr]; exact ho.safe hp
  rw [show s₅.mem = s₃.mem by rw [h₅.mem, h₄.mem], prf₃] at p₆
  have m₅ : s₅.mem = s₃.mem := by rw [h₅.mem, h₄.mem]
  have F₁ : Frame (VG.Proof.MlKem.AArch64.Kem.pcW L s₀ off) s.mem s₂.mem := f₂.mono fun r hr => by
    rw [List.mem_singleton.mp hr]; simp
  have F₂ : Frame (VG.Proof.MlKem.AArch64.Kem.pcW L s₀ off) s₂.mem s₃.mem := k₃'.frame.mono fun r hr => by
    rcases mem4 hr with rfl | rfl | rfl | rfl <;> simp
  have F₃ : Frame (VG.Proof.MlKem.AArch64.Kem.pcW L s₀ off) s₅.mem s₆.mem := k₆.frame.mono fun r hr => by
    rw [List.mem_singleton.mp hr]; simp
  rw [m₅] at F₃
  refine ⟨kb₆, F₁.trans (F₂.trans F₃), p₆, ?_⟩
  rw [k₆.cs _ (by decide) (by decide), h₅.get .x24, h₄.get .x24, k₃.cs _ (by decide) (by decide), h₂.gpr,
    h₁.get .x24]

/-- The NTT, or its inverse, of the polynomial at `off`. -/
theorem inPlace_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {t : VG.Spec.MlKem.Poly → VG.Spec.MlKem.Poly} {c : Prog isa} {name : String}
    (hc : ∀ {s : State} {f w : Addr}, s.gpr .x0 = f → s.gpr .x1 = w → Region.Disjoint ⟨f, 1024⟩ ⟨w, 1024⟩ →
      Reduced s.mem f → Covers [⟨f, 1024⟩, ⟨w, 1024⟩] s.wr → ∀ {Q : State → Prop},
      (∀ s', Kept [⟨f, 1024⟩, ⟨w, 1024⟩] s s' → PolyIs s'.mem f (t (polyAt s.mem f)) → Q s') →
      WP isa (.call name c) s Q)
    {off : Nat} (ho : VG.Proof.MlKem.AArch64.Kem.PO P off) {s : State} (hk : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) (hr : Reduced s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ off)) :
    WP isa (.seq (.block (ptrTo .x0 .x28 off ++ ptrTo .x1 .x28 NS)) (.call name c)) s fun s' =>
      VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s' ∧ Frame [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc off 1024, R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc NS 1024] s.mem s'.mem ∧
      PolyIs s'.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ off) (t (polyAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ off))) ∧ s'.gpr .x24 = s.gpr .x24 := by
  have fo := ho.le
  refine WP.seq (wp_ptrTo (by decide) (by obtain ⟨-, h⟩ := ho; kom) fun s₁ h₁ e₁ => wp_ptrTo'
    (by decide) (by decide) fun s₂ h₂ e₂ => ?_)
  have kb₂ := hk.block (h₁.trans h₂).keep (by rw [h₂.mem, h₁.mem]) (by decide)
  have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  refine hc (f := VG.Proof.MlKem.AArch64.Kem.sA L s₀ off) (w := VG.Proof.MlKem.AArch64.Kem.sA L s₀ NS) (by rw [h₂.get .x0, e₁, VG.Proof.MlKem.AArch64.Kem.e28 hk])
    (by rw [e₂, h₁.get .x28, VG.Proof.MlKem.AArch64.Kem.e28 hk]) (ho.ns hp) (by rw [m₂]; exact hr)
    (covers_cons (VG.Proof.MlKem.AArch64.Kem.cov_s hp kb₂ fo) (VG.Proof.MlKem.AArch64.Kem.cov_s hp kb₂ (o := NS) (l := 1024) (by kom))) fun s₃ k₃ p₃ => ?_
  refine ⟨kb₂.call k₃ fun r hr => by
      rcases mem2' hr with rfl | rfl
      · exact ho.safe hp
      · exact VG.Proof.MlKem.AArch64.Kem.safe_scr hp (by kom),
    by rw [← m₂]; exact k₃.frame, by rw [← m₂]; exact p₃,
    by rw [k₃.cs _ (by decide) (by decide), h₂.get .x24, h₁.get .x24]⟩

theorem ntt_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {off : Nat} (ho : VG.Proof.MlKem.AArch64.Kem.PO P off) {s : State} (hk : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s)
    (hr : Reduced s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ off)) :
    WP isa (nttAt off) s fun s' =>
      VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s' ∧ Frame [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc off 1024, R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc NS 1024] s.mem s'.mem ∧
      PolyIs s'.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ off) (ntt (polyAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ off))) ∧ s'.gpr .x24 = s.gpr .x24 :=
  VG.Proof.MlKem.AArch64.Kem.inPlace_ok hp (fun h0 h1 hd hr hw => ntt_call h0 h1 hd hr hw) ho hk hr

theorem nttInv_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {off : Nat} (ho : VG.Proof.MlKem.AArch64.Kem.PO P off) {s : State} (hk : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s)
    (hr : Reduced s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ off)) :
    WP isa (nttInvAt off) s fun s' =>
      VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s' ∧ Frame [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc off 1024, R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc NS 1024] s.mem s'.mem ∧
      PolyIs s'.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ off) (nttInv (polyAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ off))) ∧ s'.gpr .x24 = s.gpr .x24 :=
  VG.Proof.MlKem.AArch64.Kem.inPlace_ok hp (fun h0 h1 hd hr hw => nttInv_call h0 h1 hd hr hw) ho hk hr

/-- `h ← f ×_T g`, for polynomials in `scratch`. -/
theorem mul_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {h f g : Nat} (hh : VG.Proof.MlKem.AArch64.Kem.PO P h) (hf : VG.Proof.MlKem.AArch64.Kem.PO P f) (hg : VG.Proof.MlKem.AArch64.Kem.PO P g)
    (d₁ : h + 1024 ≤ f ∨ f + 1024 ≤ h) (d₂ : h + 1024 ≤ g ∨ g + 1024 ≤ h) {s : State} (hk : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s)
    (rf : Reduced s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ f)) (rg : Reduced s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ g)) :
    WP isa (mulAt h f g) s fun s' =>
      VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s' ∧ Frame [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc h 1024, R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc NS 1024] s.mem s'.mem ∧
      PolyIs s'.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ h) (multiplyNTTs (polyAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ f)) (polyAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ g))) ∧
      s'.gpr .x24 = s.gpr .x24 := by
  have fh := hh.le
  have ff := hf.le
  have fg := hg.le
  rw [mulAt, List.append_assoc, List.append_assoc]
  refine WP.seq (wp_ptrTo (by decide) (by kom) fun s₁ h₁ e₁ => wp_ptrTo (by decide) (by kom)
    fun s₂ h₂ e₂ => wp_ptrTo (by decide) (by kom) fun s₃ h₃ e₃ => wp_ptrTo' (by decide) (by decide)
    fun s₄ h₄ e₄ => ?_)
  have kb₄ := hk.block (((h₁.trans h₂).trans h₃).trans h₄).keep (by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem])
    (by decide)
  have m₄ : s₄.mem = s.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine mul_call (h := VG.Proof.MlKem.AArch64.Kem.sA L s₀ h) (f := VG.Proof.MlKem.AArch64.Kem.sA L s₀ f) (g := VG.Proof.MlKem.AArch64.Kem.sA L s₀ g) (w := VG.Proof.MlKem.AArch64.Kem.sA L s₀ NS)
    (by rw [h₄.get .x0, h₃.get .x0, h₂.get .x0, e₁, VG.Proof.MlKem.AArch64.Kem.e28 hk])
    (by rw [h₄.get .x1, h₃.get .x1, e₂, h₁.get .x28, VG.Proof.MlKem.AArch64.Kem.e28 hk])
    (by rw [h₄.get .x2, e₃, h₂.get .x28, h₁.get .x28, VG.Proof.MlKem.AArch64.Kem.e28 hk])
    (by rw [e₄, h₃.get .x28, h₂.get .x28, h₁.get .x28, VG.Proof.MlKem.AArch64.Kem.e28 hk])
    (VG.Proof.MlKem.AArch64.Kem.sdisj hp fh ff d₁) (VG.Proof.MlKem.AArch64.Kem.sdisj hp fh fg d₂) (hh.ns hp) (hf.ns hp) (hg.ns hp)
    (by rw [m₄]; exact rf) (by rw [m₄]; exact rg)
    (covers_cons (VG.Proof.MlKem.AArch64.Kem.cov_sr hp kb₄ ff) (covers_cons (VG.Proof.MlKem.AArch64.Kem.cov_sr hp kb₄ fg)
      (covers_cons (VG.Proof.MlKem.AArch64.Kem.cov_sr hp kb₄ fh) (VG.Proof.MlKem.AArch64.Kem.cov_sr hp kb₄ (o := NS) (l := 1024) (by kom)))))
    (covers_cons (VG.Proof.MlKem.AArch64.Kem.cov_s hp kb₄ fh) (VG.Proof.MlKem.AArch64.Kem.cov_s hp kb₄ (o := NS) (l := 1024) (by kom)))
    fun s₅ k₅ p₅ => ?_
  refine ⟨kb₄.call k₅ fun r hr => by
      rcases mem2' hr with rfl | rfl
      · exact hh.safe hp
      · exact VG.Proof.MlKem.AArch64.Kem.safe_scr hp (by kom),
    by rw [← m₄]; exact k₅.frame, by rw [← m₄]; exact p₅,
    by rw [k₅.cs _ (by decide) (by decide), h₄.get .x24, h₃.get .x24, h₂.get .x24, h₁.get .x24]⟩

/-- `f ← f + g` or `f ← f - g`, for polynomials in `scratch`. -/
theorem acc_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {op : VG.Spec.MlKem.Poly → VG.Spec.MlKem.Poly → VG.Spec.MlKem.Poly} {c : Prog isa} {name : String}
    (hc : ∀ {s : State} {f g : Addr}, s.gpr .x0 = f → s.gpr .x1 = g → Region.Disjoint ⟨f, 1024⟩ ⟨g, 1024⟩ →
      Reduced s.mem f → Reduced s.mem g → Covers [⟨g, 1024⟩, ⟨f, 1024⟩] (s.rd ++ s.wr) →
      Covers [⟨f, 1024⟩] s.wr → ∀ {Q : State → Prop},
      (∀ s', Kept [⟨f, 1024⟩] s s' → PolyIs s'.mem f (op (polyAt s.mem f) (polyAt s.mem g)) → Q s') →
      WP isa (.call name c) s Q)
    {f g : Nat} (hf : VG.Proof.MlKem.AArch64.Kem.PO P f) (hg : VG.Proof.MlKem.AArch64.Kem.PO P g) (d : f + 1024 ≤ g ∨ g + 1024 ≤ f) {s : State} (hk : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s)
    (rf : Reduced s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ f)) (rg : Reduced s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ g)) :
    WP isa (.seq (.block (ptrTo .x0 .x28 f ++ ptrTo .x1 .x28 g)) (.call name c)) s fun s' =>
      VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s' ∧ Frame [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc f 1024] s.mem s'.mem ∧
      PolyIs s'.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ f) (op (polyAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ f)) (polyAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ g))) ∧
      s'.gpr .x24 = s.gpr .x24 := by
  have ff := hf.le
  have fg := hg.le
  refine WP.seq (wp_ptrTo (by decide) (by kom) fun s₁ h₁ e₁ => wp_ptrTo' (by decide) (by kom)
    fun s₂ h₂ e₂ => ?_)
  have kb₂ := hk.block (h₁.trans h₂).keep (by rw [h₂.mem, h₁.mem]) (by decide)
  have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  refine hc (f := VG.Proof.MlKem.AArch64.Kem.sA L s₀ f) (g := VG.Proof.MlKem.AArch64.Kem.sA L s₀ g) (by rw [h₂.get .x0, e₁, VG.Proof.MlKem.AArch64.Kem.e28 hk]) (by rw [e₂, h₁.get .x28, VG.Proof.MlKem.AArch64.Kem.e28 hk])
    (VG.Proof.MlKem.AArch64.Kem.sdisj hp ff fg d) (by rw [m₂]; exact rf) (by rw [m₂]; exact rg)
    (covers_cons (VG.Proof.MlKem.AArch64.Kem.cov_sr hp kb₂ fg) (VG.Proof.MlKem.AArch64.Kem.cov_sr hp kb₂ ff)) (VG.Proof.MlKem.AArch64.Kem.cov_s hp kb₂ ff) fun s₃ k₃ p₃ => ?_
  refine ⟨kb₂.call k₃ fun r hr => by rw [List.mem_singleton.mp hr]; exact hf.safe hp,
    by rw [← m₂]; exact k₃.frame, by rw [← m₂]; exact p₃,
    by rw [k₃.cs _ (by decide) (by decide), h₂.get .x24, h₁.get .x24]⟩

theorem add_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {f g : Nat} (hf : VG.Proof.MlKem.AArch64.Kem.PO P f) (hg : VG.Proof.MlKem.AArch64.Kem.PO P g)
    (d : f + 1024 ≤ g ∨ g + 1024 ≤ f) {s : State} (hk : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s)
    (rf : Reduced s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ f)) (rg : Reduced s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ g)) :
    WP isa (addAt f g) s fun s' => VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s' ∧ Frame [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc f 1024] s.mem s'.mem ∧
      PolyIs s'.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ f) (add (polyAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ f)) (polyAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ g))) ∧
      s'.gpr .x24 = s.gpr .x24 :=
  VG.Proof.MlKem.AArch64.Kem.acc_ok hp (fun h0 h1 hd rf rg hc hw => add_call h0 h1 hd rf rg hc hw) hf hg d hk rf rg

theorem sub_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {f g : Nat} (hf : VG.Proof.MlKem.AArch64.Kem.PO P f) (hg : VG.Proof.MlKem.AArch64.Kem.PO P g)
    (d : f + 1024 ≤ g ∨ g + 1024 ≤ f) {s : State} (hk : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s)
    (rf : Reduced s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ f)) (rg : Reduced s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ g)) :
    WP isa (subAt f g) s fun s' => VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s' ∧ Frame [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc f 1024] s.mem s'.mem ∧
      PolyIs s'.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ f) (sub (polyAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ f)) (polyAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ g))) ∧
      s'.gpr .x24 = s.gpr .x24 :=
  VG.Proof.MlKem.AArch64.Kem.acc_ok hp (fun h0 h1 hd rf rg hc hw => sub_call h0 h1 hd rf rg hc hw) hf hg d hk rf rg

theorem width_imm : ∀ d < 12, (((BitVec.ofNat 16 d).setWidth 64).setWidth 32).toNat = d ∧ 32 * d < 65536 := by
  decide

theorem slot_ne {k : Nat} (hk : k < 4) (r : Reg) (hr : r ∈ [Reg.x0, .x1, .x2, .x3]) : r ≠ slotReg k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  rcases mem4 hr with rfl | rfl | rfl | rfl <;> decide

theorem slot_off {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {k o l : Nat} (hk : k < 4) (f : o + l ≤ L.len (L.slot k)) :
    o < 65536 := by
  have := hp.args.len _ (hp.lt hk); omega

/-- `ByteEncode_d(Compress_d(f))` of the polynomial at `off` into bytes
`[o, o + 32d)` of the buffer in `slotReg k`, by a function meeting the
contract of compression and encoding at the widths `W`. -/
theorem ceWith_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {name : String} {code : Prog isa} {W : Nat → Prop}
    (hW : ∀ {d}, W d → d < 12)
    (hc : ∀ {s : State} {f o : Addr} {d : Nat}, s.gpr .x0 = f → ((s.gpr .x1).setWidth 32).toNat = d →
      s.gpr .x2 = o → (s.gpr .x3).toNat = 32 * d → W d →
      Region.Disjoint ⟨f, 1024⟩ ⟨o, 32 * d⟩ → Reduced s.mem f → Covers [⟨f, 1024⟩, ⟨o, 32 * d⟩] (s.rd ++ s.wr) →
      Covers [⟨o, 32 * d⟩] s.wr → ∀ {Q : State → Prop},
      (∀ s', Kept [⟨o, 32 * d⟩] s s' → bytesAt s'.mem o (32 * d) = compressEncode d (polyAt s.mem f) → Q s') →
      WP isa (.call name code) s Q)
    {off d k o : Nat} (ho : VG.Proof.MlKem.AArch64.Kem.PO P off) (hd : W d)
    (hk4 : k < 4) (hw : L.nrd ≤ L.slot k) (f : o + 32 * d ≤ L.len (L.slot k))
    (hs : L.slot k ≠ L.sc ∨ (o + 32 * d ≤ SV P ∧ (o + 32 * d ≤ off ∨ off + 1024 ≤ o))) {s : State}
    (hk : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) (hr : Reduced s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ off)) :
    WP isa (ceWith name code off d (slotReg k) o) s fun s' =>
      VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s' ∧ Frame [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) (L.slot k) o (32 * d)] s.mem s'.mem ∧
      bytesAt s'.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ (L.slot k) + BitVec.ofNat 64 o) (32 * d) =
        compressEncode d (polyAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ off)) ∧ s'.gpr .x24 = s.gpr .x24 := by
  have fo := ho.le
  have hb := hp.lt hk4
  have ⟨wd, wd'⟩ := VG.Proof.MlKem.AArch64.Kem.width_imm d (hW hd)
  rw [ceWith, List.append_assoc, List.cons_append]
  refine WP.seq (wp_ptrTo (by decide) (by kom) fun s₁ h₁ e₁ => wp_movz fun s₂ h₂ e₂ =>
    wp_ptrTo (VG.Proof.MlKem.AArch64.Kem.slot_ne hk4 .x2 (by decide)) (VG.Proof.MlKem.AArch64.Kem.slot_off hp hk4 f) fun s₃ h₃ e₃ => wp_movz fun s₄ h₄ e₄ =>
    wp_nil ?_)
  have kb₄ := hk.block (((h₁.trans h₂).trans h₃).trans h₄).keep (by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem])
    (by decide)
  have m₄ : s₄.mem = s.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have g : ∀ {r : Reg}, r ∈ [Reg.x0, .x1, .x2, .x3] → slotReg k ∉ [r] := fun hr h =>
    VG.Proof.MlKem.AArch64.Kem.slot_ne hk4 _ hr (List.mem_singleton.mp h).symm
  refine hc (f := VG.Proof.MlKem.AArch64.Kem.sA L s₀ off) (o := VG.Proof.MlKem.AArch64.Kem.kA s₀ (L.slot k) + BitVec.ofNat 64 o) (d := d)
    (by rw [h₄.get .x0, h₃.get .x0, h₂.get .x0, e₁, VG.Proof.MlKem.AArch64.Kem.e28 hk])
    (by rw [h₄.get .x1, h₃.get .x1, e₂]; exact wd)
    (by rw [h₄.get .x2, e₃, h₂.get _ (g (by decide)), h₁.get _ (g (by decide)), hk.ptr k hk4])
    (by rw [e₄]; exact imm16 wd') hd
    (hp.args.rdisj hp.scb hb (hp.fs fo) f (.inr (.inl hp.scw)) (by
      rcases hs with hs | ⟨-, hs⟩
      · exact .inl (Ne.symm hs)
      · exact .inr hs.symm))
    (by rw [m₄]; exact hr)
    (covers_cons (VG.Proof.MlKem.AArch64.Kem.cov_sr hp kb₄ fo) (VG.Proof.MlKem.AArch64.Kem.cov_r hp kb₄ hb f)) (VG.Proof.MlKem.AArch64.Kem.cov_w hp kb₄ ⟨hw, hb⟩ f) fun s₅ k₅ p₅ => ?_
  refine ⟨kb₄.call k₅ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact VG.Proof.MlKem.AArch64.Kem.safe_R hp ⟨hw, hb⟩ f (by
        rcases hs with hs | ⟨hs, -⟩
        · exact .inl hs
        · exact .inr (.inr hs)),
    by rw [← m₄]; exact k₅.frame, by rw [p₅, m₄],
    by rw [k₅.cs _ (by decide) (by decide), h₄.get .x24, h₃.get .x24, h₂.get .x24, h₁.get .x24]⟩

theorem mem_widths {d : Nat} (hd : d ∈ compressWidths) : d < 12 := by
  simp only [compressWidths, List.mem_cons, List.not_mem_nil, or_false] at hd; omega

/-- `ByteEncode_d(Compress_d(f))` for the widths of ML-KEM-768 (`d = 1`). -/
theorem ce_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {off d k o : Nat} (ho : VG.Proof.MlKem.AArch64.Kem.PO P off) (hd : d ∈ compressWidths)
    (hk4 : k < 4) (hw : L.nrd ≤ L.slot k) (f : o + 32 * d ≤ L.len (L.slot k))
    (hs : L.slot k ≠ L.sc ∨ (o + 32 * d ≤ SV P ∧ (o + 32 * d ≤ off ∨ off + 1024 ≤ o))) {s : State}
    (hk : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) (hr : Reduced s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ off)) :
    WP isa (ceAt off d (slotReg k) o) s fun s' =>
      VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s' ∧ Frame [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) (L.slot k) o (32 * d)] s.mem s'.mem ∧
      bytesAt s'.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ (L.slot k) + BitVec.ofNat 64 o) (32 * d) =
        compressEncode d (polyAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ off)) ∧ s'.gpr .x24 = s.gpr .x24 :=
  VG.Proof.MlKem.AArch64.Kem.ceWith_ok hp VG.Proof.MlKem.AArch64.Kem.mem_widths (fun h0 h1 h2 h3 hw hd hr hc hw' => compressEncode_call h0 h1 h2 h3 hw hd hr hc hw')
    ho hd hk4 hw f hs hk hr

/-- `ByteEncode_d(Compress_d(f))` at the widths `d_u` and `d_v`. -/
theorem ceL_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) (hc : VG.Proof.MlKem.AArch64.Kem.Calls P) {off d k o : Nat} (ho : VG.Proof.MlKem.AArch64.Kem.PO P off)
    (hd : d = P.du ∨ d = P.dv)
    (hk4 : k < 4) (hw : L.nrd ≤ L.slot k) (f : o + 32 * d ≤ L.len (L.slot k))
    (hs : L.slot k ≠ L.sc ∨ (o + 32 * d ≤ SV P ∧ (o + 32 * d ≤ off ∨ off + 1024 ≤ o))) {s : State}
    (hk : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) (hr : Reduced s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ off)) :
    WP isa (P.ceLAt off d (slotReg k) o) s fun s' =>
      VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s' ∧ Frame [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) (L.slot k) o (32 * d)] s.mem s'.mem ∧
      bytesAt s'.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ (L.slot k) + BitVec.ofNat 64 o) (32 * d) =
        compressEncode d (polyAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ off)) ∧ s'.gpr .x24 = s.gpr .x24 :=
  VG.Proof.MlKem.AArch64.Kem.ceWith_ok hp (fun h => by have := hp.wf.facts; omega) hc.ce ho hd hk4 hw f hs hk hr

/-- `Decompress_d(ByteDecode_d(·))` of bytes `[o, o + 32d)` of the buffer in
`slotReg k`, into the polynomial at `off`, by a function meeting the contract
of decoding and decompression at the widths `W`. -/
theorem ddWith_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {name : String} {code : Prog isa} {W : Nat → Prop}
    (hW : ∀ {d}, W d → d < 12)
    (hc : ∀ {s : State} {b f : Addr} {d : Nat}, s.gpr .x0 = b → (s.gpr .x1).toNat = 32 * d →
      ((s.gpr .x2).setWidth 32).toNat = d → s.gpr .x3 = f → W d →
      Region.Disjoint ⟨b, 32 * d⟩ ⟨f, 1024⟩ → Covers [⟨b, 32 * d⟩, ⟨f, 1024⟩] (s.rd ++ s.wr) →
      Covers [⟨f, 1024⟩] s.wr → ∀ {Q : State → Prop},
      (∀ s', Kept [⟨f, 1024⟩] s s' → PolyIs s'.mem f (decodeDecompress d (bytesAt s.mem b (32 * d))) → Q s') →
      WP isa (.call name code) s Q)
    {k o d off : Nat} (hk4 : k < 4)
    (f : o + 32 * d ≤ L.len (L.slot k)) (hd : W d) (ho : VG.Proof.MlKem.AArch64.Kem.PO P off)
    (hs : L.slot k ≠ L.sc ∨ o + 32 * d ≤ off ∨ off + 1024 ≤ o) {s : State} (hk : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) :
    WP isa (ddWith name code (slotReg k) o d off) s fun s' =>
      VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s' ∧ Frame [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc off 1024] s.mem s'.mem ∧
      PolyIs s'.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ off)
        (decodeDecompress d (bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ (L.slot k) + BitVec.ofNat 64 o) (32 * d))) ∧
      s'.gpr .x24 = s.gpr .x24 := by
  have fo := ho.le
  have hb := hp.lt hk4
  have ⟨wd, wd'⟩ := VG.Proof.MlKem.AArch64.Kem.width_imm d (hW hd)
  rw [ddWith, List.append_assoc, List.cons_append, List.cons_append, List.nil_append]
  refine WP.seq (wp_ptrTo (VG.Proof.MlKem.AArch64.Kem.slot_ne hk4 .x0 (by decide)) (VG.Proof.MlKem.AArch64.Kem.slot_off hp hk4 f) fun s₁ h₁ e₁ =>
    wp_movz fun s₂ h₂ e₂ => wp_movz fun s₃ h₃ e₃ => wp_ptrTo' (by decide)
    (by obtain ⟨-, h⟩ := ho; kom) fun s₄ h₄ e₄ => ?_)
  have kb₄ := hk.block (((h₁.trans h₂).trans h₃).trans h₄).keep (by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem])
    (by decide)
  have m₄ : s₄.mem = s.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine hc (b := VG.Proof.MlKem.AArch64.Kem.kA s₀ (L.slot k) + BitVec.ofNat 64 o) (f := VG.Proof.MlKem.AArch64.Kem.sA L s₀ off) (d := d)
    (by rw [h₄.get .x0, h₃.get .x0, h₂.get .x0, e₁, hk.ptr k hk4])
    (by rw [h₄.get .x1, h₃.get .x1, e₂]; exact imm16 wd')
    (by rw [h₄.get .x2, e₃]; exact wd)
    (by rw [e₄, h₃.get .x28, h₂.get .x28, h₁.get .x28, VG.Proof.MlKem.AArch64.Kem.e28 hk]) hd
    (hp.args.rdisj hb hp.scb f (hp.fs fo) (.inr (.inr hp.scw)) hs)
    (covers_cons (VG.Proof.MlKem.AArch64.Kem.cov_r hp kb₄ hb f) (VG.Proof.MlKem.AArch64.Kem.cov_sr hp kb₄ fo)) (VG.Proof.MlKem.AArch64.Kem.cov_s hp kb₄ fo) fun s₅ k₅ p₅ => ?_
  refine ⟨kb₄.call k₅ fun r hr => by rw [List.mem_singleton.mp hr]; exact ho.safe hp,
    by rw [← m₄]; exact k₅.frame, by rw [← m₄]; exact p₅,
    by rw [k₅.cs _ (by decide) (by decide), h₄.get .x24, h₃.get .x24, h₂.get .x24, h₁.get .x24]⟩

/-- `Decompress_d(ByteDecode_d(·))` for the widths of ML-KEM-768 (`d = 1`). -/
theorem dd_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {k o d off : Nat} (hk4 : k < 4)
    (f : o + 32 * d ≤ L.len (L.slot k)) (hd : d ∈ compressWidths) (ho : VG.Proof.MlKem.AArch64.Kem.PO P off)
    (hs : L.slot k ≠ L.sc ∨ o + 32 * d ≤ off ∨ off + 1024 ≤ o) {s : State} (hk : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) :
    WP isa (ddAt (slotReg k) o d off) s fun s' =>
      VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s' ∧ Frame [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc off 1024] s.mem s'.mem ∧
      PolyIs s'.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ off)
        (decodeDecompress d (bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ (L.slot k) + BitVec.ofNat 64 o) (32 * d))) ∧
      s'.gpr .x24 = s.gpr .x24 :=
  VG.Proof.MlKem.AArch64.Kem.ddWith_ok hp VG.Proof.MlKem.AArch64.Kem.mem_widths (fun h0 h1 h2 h3 hw hd hc hw' => decodeDecompress_call h0 h1 h2 h3 hw hd hc hw')
    hk4 f hd ho hs hk

/-- `Decompress_d(ByteDecode_d(·))` at the widths `d_u` and `d_v`. -/
theorem ddL_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) (hc : VG.Proof.MlKem.AArch64.Kem.Calls P) {k o d off : Nat} (hk4 : k < 4)
    (f : o + 32 * d ≤ L.len (L.slot k)) (hd : d = P.du ∨ d = P.dv) (ho : VG.Proof.MlKem.AArch64.Kem.PO P off)
    (hs : L.slot k ≠ L.sc ∨ o + 32 * d ≤ off ∨ off + 1024 ≤ o) {s : State} (hk : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) :
    WP isa (P.ddLAt (slotReg k) o d off) s fun s' =>
      VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s' ∧ Frame [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc off 1024] s.mem s'.mem ∧
      PolyIs s'.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ off)
        (decodeDecompress d (bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ (L.slot k) + BitVec.ofNat 64 o) (32 * d))) ∧
      s'.gpr .x24 = s.gpr .x24 :=
  VG.Proof.MlKem.AArch64.Kem.ddWith_ok hp (fun h => by have := hp.wf.facts; omega) hc.dd hk4 f hd ho hs hk

/-- `ByteDecode₁₂` of bytes `[o, o + 384)` of the buffer in `slotReg k`, into
the polynomial at `off`. -/
theorem dec12_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {k o off : Nat} (hk4 : k < 4)
    (f : o + 384 ≤ L.len (L.slot k)) (ho : VG.Proof.MlKem.AArch64.Kem.PO P off) (hs : L.slot k ≠ L.sc ∨ o + 384 ≤ off ∨ off + 1024 ≤ o)
    {s : State} (hk : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) :
    WP isa (dec12At (slotReg k) o off) s fun s' =>
      VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s' ∧ Frame [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc off 1024] s.mem s'.mem ∧
      PolyIs s'.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ off) (decode12 (bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ (L.slot k) + BitVec.ofNat 64 o) 384)) ∧
      s'.gpr .x24 = s.gpr .x24 := by
  have fo := ho.le
  have hb := hp.lt hk4
  refine WP.seq (wp_ptrTo (VG.Proof.MlKem.AArch64.Kem.slot_ne hk4 .x0 (by decide)) (VG.Proof.MlKem.AArch64.Kem.slot_off hp hk4 f) fun s₁ h₁ e₁ =>
    wp_ptrTo' (by decide) (by obtain ⟨-, h⟩ := ho; kom) fun s₂ h₂ e₂ => ?_)
  have kb₂ := hk.block (h₁.trans h₂).keep (by rw [h₂.mem, h₁.mem]) (by decide)
  have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  refine decode12_call (b := VG.Proof.MlKem.AArch64.Kem.kA s₀ (L.slot k) + BitVec.ofNat 64 o) (f := VG.Proof.MlKem.AArch64.Kem.sA L s₀ off)
    (by rw [h₂.get .x0, e₁, hk.ptr k hk4]) (by rw [e₂, h₁.get .x28, VG.Proof.MlKem.AArch64.Kem.e28 hk])
    (hp.args.rdisj hb hp.scb f (hp.fs fo) (.inr (.inr hp.scw)) hs)
    (covers_cons (VG.Proof.MlKem.AArch64.Kem.cov_r hp kb₂ hb f) (VG.Proof.MlKem.AArch64.Kem.cov_sr hp kb₂ fo)) (VG.Proof.MlKem.AArch64.Kem.cov_s hp kb₂ fo) fun s₃ k₃ p₃ => ?_
  refine ⟨kb₂.call k₃ fun r hr => by rw [List.mem_singleton.mp hr]; exact ho.safe hp,
    by rw [← m₂]; exact k₃.frame, by rw [← m₂]; exact p₃,
    by rw [k₃.cs _ (by decide) (by decide), h₂.get .x24, h₁.get .x24]⟩

end VG.Proof.MlKem.AArch64.Kem

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.KemB`. -/
section

/-!
# ML-KEM on AArch64: the matrix `Â` of `encaps` and `decaps`

`Â[i, j]` for the `k²` entries `(i, j)` (entry `e = k i + j`), from the seed `ρ` at
`SB`, each with `sample_ntt`'s stronger contract: it is reduced, and the
result is 1 exactly when `SampleNTT` with 280 iterations succeeds; `x24` is
the AND of the results. The matrix writes only the last two bytes of the seed,
`Â`, `sample_ntt`'s working space and the stack below the stack pointer
(`bW`).

Constant time, relating two runs with the same pointers and the same `ρ`:
the arguments of each call by the taint analysis, and the calls by
`sample_ntt`'s own constant time (`matrix_rct`).
-/

namespace VG.Proof.MlKem.AArch64.Kem

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)
open VG.Proof.MlKem.AArch64.KeyGen (and_acc)

variable {P : KemLay} {L : VG.Proof.MlKem.AArch64.Kem.Layout}

/-- Whether the first `n` `SampleNTT`s from `ρ` succeed. -/
def okR (P : KemLay) (ρ : List Byte) (n : Nat) : Prop :=
  ∀ e < n, (sampleNTT 280 (matSeed ρ (e / P.k) (e % P.k))).isSome

instance (ρ : List Byte) (n : Nat) : Decidable (VG.Proof.MlKem.AArch64.Kem.okR P ρ n) := by unfold VG.Proof.MlKem.AArch64.Kem.okR; infer_instance

theorem okR_succ {ρ : List Byte} {k : Nat} :
    VG.Proof.MlKem.AArch64.Kem.okR P ρ (k + 1) ↔ VG.Proof.MlKem.AArch64.Kem.okR P ρ k ∧ (sampleNTT 280 (matSeed ρ (k / P.k) (k % P.k))).isSome := by
  constructor
  · intro h; exact ⟨fun e he => h e (by omega), h k (by omega)⟩
  · rintro ⟨h, hk⟩ e he
    rcases (by omega : e < k ∨ e = k) with he | rfl
    · exact h e he
    · exact hk

/-- What the matrix writes. -/
abbrev bW (P : KemLay) (L : VG.Proof.MlKem.AArch64.Kem.Layout) (s₀ : State) : List Region :=
  [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc (SB + 32) 2, R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc AH (1024 * (P.k * P.k)), R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc SS 2048, below s₀.sp 16]

/-- Entry `e` of `Â`. -/
abbrev aP (L : VG.Proof.MlKem.AArch64.Kem.Layout) (s₀ : State) (e : Nat) : Addr := VG.Proof.MlKem.AArch64.Kem.sA L s₀ (AH + 1024 * e)

/-- After `n` entries of `Â`, from memory `mA`. -/
structure BInv (P : KemLay) (L : VG.Proof.MlKem.AArch64.Kem.Layout) (s₀ : State) (mA : Mem) (ρ : List Byte) (n : Nat) (s : State) :
    Prop where
  kb : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s
  fr : Frame (VG.Proof.MlKem.AArch64.Kem.bW P L s₀) mA s.mem
  rho : bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ SB) 32 = ρ
  acc : s.gpr .x24 = if VG.Proof.MlKem.AArch64.Kem.okR P ρ n then 1 else 0
  red : ∀ e < n, Reduced s.mem (VG.Proof.MlKem.AArch64.Kem.aP L s₀ e)
  res : ∀ e < n, sampleNTT 280 (matSeed ρ (e / P.k) (e % P.k)) = none ∨
    sampleNTT 280 (matSeed ρ (e / P.k) (e % P.k)) = some (polyAt s.mem (VG.Proof.MlKem.AArch64.Kem.aP L s₀ e))

theorem BInv.zero {s₀ s : State} {ρ : List Byte} (hk : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) (h24 : s.gpr .x24 = 1)
    (hρ : bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ SB) 32 = ρ) : VG.Proof.MlKem.AArch64.Kem.BInv P L s₀ s.mem ρ 0 s :=
  ⟨hk, Frame.refl _ _, hρ, by rw [h24, ite_eq_left (show VG.Proof.MlKem.AArch64.Kem.okR P ρ 0 from fun e he => absurd he (Nat.not_lt_zero e))],
    fun e he => absurd he (Nat.not_lt_zero e), fun e he => absurd he (Nat.not_lt_zero e)⟩

/-- Before `SampleNTT(ρ ‖ j ‖ i)`: its seed, and its arguments. -/
structure Mid (P : KemLay) (L : VG.Proof.MlKem.AArch64.Kem.Layout) (s₀ : State) (mA : Mem) (ρ : List Byte) (i j : Nat) (s : State) :
    Prop where
  b : VG.Proof.MlKem.AArch64.Kem.BInv P L s₀ mA ρ (P.k * i + j) s
  seed : bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ SB) 34 = matSeed ρ i j
  x0 : s.gpr .x0 = VG.Proof.MlKem.AArch64.Kem.sA L s₀ SB
  x1 : s.gpr .x1 = VG.Proof.MlKem.AArch64.Kem.sA L s₀ (aOff P i j)
  x2 : s.gpr .x2 = VG.Proof.MlKem.AArch64.Kem.sA L s₀ SS

theorem setup_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {mA : Mem} {ρ : List Byte} {i j : Nat} (hi : i < P.k)
    (hj : j < P.k) {s : State} (h : VG.Proof.MlKem.AArch64.Kem.BInv P L s₀ mA ρ (P.k * i + j) s) :
    WP isa (.block (P.kemSetup i j)) s (VG.Proof.MlKem.AArch64.Kem.Mid P L s₀ mA ρ i j) := by
  have hw := hp.wf
  have hij := ij_lt hi hj
  have e := VG.Proof.MlKem.AArch64.Kem.e28 h.kb
  rw [KemLay.kemSetup, List.append_assoc, List.append_assoc]
  have in₁ : ∀ {u : State}, u.wr = s.wr → InRegions u.wr (VG.Proof.MlKem.AArch64.Kem.sA L s₀ (SB + 32)) 1 :=
    fun hu => by
      rw [hu]
      exact in_R (VG.Proof.MlKem.AArch64.Kem.cov_s hp h.kb (o := SB + 32) (l := 2) (by kom)) (k := 0) (by decide) (by decide)
  have in₂ : ∀ {u : State}, u.wr = s.wr → InRegions u.wr (VG.Proof.MlKem.AArch64.Kem.sA L s₀ (SB + 33)) 1 :=
    fun hu => by
      rw [hu]
      exact in_R (VG.Proof.MlKem.AArch64.Kem.cov_s hp h.kb (o := SB + 32) (l := 2) (by kom)) (k := 1) (by decide) (by decide)
  refine wp_movz fun s₁ h₁ e₁ => wp_strb (a := VG.Proof.MlKem.AArch64.Kem.sA L s₀ (SB + 32)) (by decide)
    (by rw [h₁.get .x28, e]) (in₁ h₁.wr) fun s₂ h₂ => ?_
  refine wp_movz fun s₃ h₃ e₃ => wp_strb (a := VG.Proof.MlKem.AArch64.Kem.sA L s₀ (SB + 33)) (by decide)
    (by rw [h₃.get .x28, h₂.gpr, h₁.get .x28, e]) (in₂ (by rw [h₃.wr, h₂.wr, h₁.wr])) fun s₄ h₄ => ?_
  refine wp_ptrTo (by decide) (by decide) fun s₅ h₅ e₅ => wp_ptrTo (by decide)
    (by lom) fun s₆ h₆ e₆ => wp_ptrTo' (by decide) (by decide)
    fun s₇ h₇ e₇ => ?_
  have g28 : s₄.gpr .x28 = VG.Proof.MlKem.AArch64.Kem.kA s₀ L.sc := by rw [h₄.gpr, h₃.get .x28, h₂.gpr, h₁.get .x28, h.kb.x28]
  have k₇ := (((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).trans h₆.keep).trans
    h₇.keep
  have m₇ : s₇.mem = (s.mem.writeW (VG.Proof.MlKem.AArch64.Kem.sA L s₀ (SB + 32)) ((s₁.gpr .x9).setWidth 8)).writeW
      (VG.Proof.MlKem.AArch64.Kem.sA L s₀ (SB + 33)) ((s₃.gpr .x9).setWidth 8) := by
    rw [h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have f₇ : Frame [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc (SB + 32) 2] s.mem s₇.mem := by
    rw [m₇]
    have hm : R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc (SB + 32) 2 ∈ [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc (SB + 32) 2] := List.mem_singleton_self _
    exact ((Frame.refl _ _).writeW hm _ (R.contains (k := 0) (by decide) (by decide))).writeW hm _
      (R.contains (k := 1) (by decide) (by decide))
  have kb₇ : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s₇ := h.kb.frame k₇ f₇ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact VG.Proof.MlKem.AArch64.Kem.safe_scr hp (by lom)
  have sd : ∀ o, o < 32 → s₇.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ SB + BitVec.ofNat 64 o) = s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ SB + BitVec.ofNat 64 o) :=
    fun o ho => by
      rw [ptr_add]
      exact f₇ _ fun r hr hc => by
        rw [List.mem_singleton.mp hr] at hc
        exact VG.Proof.MlKem.AArch64.Kem.sdisj hp (o₁ := SB + o) (l₁ := 1) (by lom) (by lom)
          (by simp only [SB]; omega) _ (Region.contains_self _ _) hc
  have ae : ∀ {e : Nat}, e < P.k * i + j →
      ∀ r ∈ [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc (SB + 32) 2], (polyRegion (VG.Proof.MlKem.AArch64.Kem.aP L s₀ e)).Disjoint r :=
    fun he r hr => by
      rw [List.mem_singleton.mp hr]
      exact VG.Proof.MlKem.AArch64.Kem.sdisj hp (by lom) (by lom) (by simp only [AH, SB]; omega)
  refine ⟨⟨kb₇, h.fr.trans (f₇.mono (by simp)), by rw [bytesAt_congr sd]; exact h.rho,
    by rw [k₇.get .x24]; exact h.acc, fun e he => reduced_frame f₇ (ae he) (h.red e he), fun e he => ?_⟩,
    ?_, ?_, ?_, ?_⟩
  · rw [polyAt_frame f₇ (ae he)]; exact h.res e he
  · refine seed_eq (by rw [bytesAt_congr sd]; exact h.rho) ?_ ?_
    · rw [m₇, ptr_add, VG.WriteBytes.writeW8_apply, ite_eq_right (addr_ne _ (by decide) (by decide) (by decide)),
        VG.WriteBytes.writeW8_apply, ite_eq_left rfl, e₁]
      exact sfx8 (by lom)
    · rw [m₇, ptr_add, VG.WriteBytes.writeW8_apply, ite_eq_left rfl, e₃]
      exact sfx8 (by lom)
  · rw [h₇.get .x0, h₆.get .x0, e₅, g28]
  · rw [h₇.get .x1, e₆, h₅.get .x28, g28]
  · rw [e₇, h₆.get .x28, h₅.get .x28, g28]

/-- The arguments of `SampleNTT` for `Â[i, j]`. -/
theorem Mid.args {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {mA : Mem} {ρ : List Byte} {i j : Nat} (hi : i < P.k)
    (hj : j < P.k) {s : State} (h : VG.Proof.MlKem.AArch64.Kem.Mid P L s₀ mA ρ i j s) :
    SampleArgs s (VG.Proof.MlKem.AArch64.Kem.sA L s₀ SB) (VG.Proof.MlKem.AArch64.Kem.sA L s₀ (aOff P i j)) (VG.Proof.MlKem.AArch64.Kem.sA L s₀ SS) := by
  have hw := hp.wf
  have hij := ij_lt hi hj
  have kb := h.b.kb
  have f : ∀ {o l : Nat}, o + l ≤ 4248 → o + l ≤ SV P + 48 := fun h => by lom
  have fa : aOff P i j + 1024 ≤ SV P + 48 := by lom
  have fs : ∀ {o l : Nat}, o + l ≤ SV P + 48 → o + l ≤ L.len L.sc := hp.fs
  exact ⟨h.x0, h.x1, h.x2,
    VG.Proof.MlKem.AArch64.Kem.sdisj hp (f (by decide)) fa (.inl (by lom)),
    VG.Proof.MlKem.AArch64.Kem.sdisj hp (f (by decide)) (f (by decide)) (by decide),
    VG.Proof.MlKem.AArch64.Kem.sdisj hp fa (f (by decide)) (.inr (by lom)),
    by rw [kb.sp]; exact hp.sp16, VG.Proof.MlKem.AArch64.Kem.stk_R hp kb hp.scb (fs (f (by decide))), VG.Proof.MlKem.AArch64.Kem.stk_R hp kb hp.scb (fs fa),
    VG.Proof.MlKem.AArch64.Kem.stk_R hp kb hp.scb (fs (f (by decide))),
    covers_cons (VG.Proof.MlKem.AArch64.Kem.cov_sr hp kb (f (by decide))) (covers_cons (VG.Proof.MlKem.AArch64.Kem.cov_sr hp kb fa) (VG.Proof.MlKem.AArch64.Kem.cov_sr hp kb (f (by decide)))),
    covers_cons (VG.Proof.MlKem.AArch64.Kem.cov_s hp kb fa) (VG.Proof.MlKem.AArch64.Kem.cov_s hp kb (f (by decide)))⟩

theorem call_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {mA : Mem} {ρ : List Byte} {i j : Nat} (hi : i < P.k)
    (hj : j < P.k) {s : State} (h : VG.Proof.MlKem.AArch64.Kem.Mid P L s₀ mA ρ i j s) :
    WP isa (kgCallWith keccak.callee) s (VG.Proof.MlKem.AArch64.Kem.BInv P L s₀ mA ρ (P.k * i + j + 1)) := by
  have hw := hp.wf
  have hij := ij_lt hi hj
  have kb := h.b.kb
  have f : ∀ {o l : Nat}, o + l ≤ 4248 → o + l ≤ SV P + 48 := fun h => by lom
  have fa : aOff P i j + 1024 ≤ SV P + 48 := by lom
  have A := h.args hp hi hj
  refine WP.seq <| sample_callWith keccak A.h0 A.h1 A.h2 A.d₁ A.d₂ A.d₃ A.hsp A.k₁ A.k₂ A.k₃ A.hc A.hw
    fun s₈ k₈ r₈ o₈ => ?_
  rw [kb.sp] at k₈
  have kb₈ : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s₈ := kb.call k₈ fun r hr => by
    rcases mem3 hr with rfl | rfl | rfl
    · exact VG.Proof.MlKem.AArch64.Kem.safe_scr hp (by lom)
    · exact VG.Proof.MlKem.AArch64.Kem.safe_scr hp (by lom)
    · exact VG.Proof.MlKem.AArch64.Kem.safe_below hp
  refine wp_and fun s₉ h₉ e₉ => wp_nil ?_
  have kb₉ := kb₈.block h₉.keep h₉.mem (by decide)
  have fr : Frame [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc (aOff P i j) 1024, R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc SS 2048, below s₀.sp 16] s.mem s₉.mem := by
    rw [h₉.mem]; exact k₈.frame
  have far : ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ aOff P i j ∨ aOff P i j + 1024 ≤ o) →
      (o + l ≤ SS ∨ SS + 2048 ≤ o) →
      ∀ r ∈ [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc (aOff P i j) 1024, R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc SS 2048, below s₀.sp 16],
        (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc o l).Disjoint r := fun fo h2 h3 r hr => by
    rcases mem3 hr with rfl | rfl | rfl
    · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp fo fa h2
    · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp fo (f (by decide)) h3
    · exact VG.Proof.MlKem.AArch64.Kem.below_R hp hp.scb (hp.fs fo)
  have hke := ij_div (i := i) hj
  have ae : ∀ {e : Nat}, e < P.k * i + j →
      ∀ r ∈ [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc (aOff P i j) 1024, R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc SS 2048, below s₀.sp 16],
        (polyRegion (VG.Proof.MlKem.AArch64.Kem.aP L s₀ e)).Disjoint r :=
    fun he => far (by lom) (by lom) (by lom)
  rw [h.seed] at o₈
  have x0v : (s₈.gpr .x0 = 1 ∧ (sampleNTT 280 (matSeed ρ i j)).isSome) ∨
      (s₈.gpr .x0 = 0 ∧ ¬ (sampleNTT 280 (matSeed ρ i j)).isSome) := by
    rcases o₈ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨h1, by rw [h2]; rfl⟩
    · exact .inr ⟨h1, by rw [h2]; simp⟩
  have g24 : s₈.gpr .x24 = s.gpr .x24 := k₈.cs _ (by decide) (by decide)
  have acc : s₉.gpr .x24 = if VG.Proof.MlKem.AArch64.Kem.okR P ρ (P.k * i + j) ∧ (sampleNTT 280 (matSeed ρ i j)).isSome then 1 else 0 := by
    rw [e₉, g24, and_acc h.b.acc x0v]
  refine ⟨kb₉, h.b.fr.trans (fr.sub fun r hr => ?_), ?_, ?_, fun e he => ?_, fun e he => ?_⟩
  · rcases mem3 hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..),
        R.sub2 (by simp only [aOff]; omega) (by simp only [aOff]; omega)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rw [bytesAt_frame fr (far (f (by decide)) (.inl (by lom)) (by decide)) (by decide)]
    exact h.b.rho
  · rw [acc]
    by_cases hA : VG.Proof.MlKem.AArch64.Kem.okR P ρ (P.k * i + j + 1)
    · have hA' := okR_succ.mp hA
      rw [hke.1, hke.2] at hA'
      rw [ite_eq_left hA', ite_eq_left hA]
    · have hA' : ¬ (VG.Proof.MlKem.AArch64.Kem.okR P ρ (P.k * i + j) ∧ (sampleNTT 280 (matSeed ρ i j)).isSome) := fun h' =>
        hA (okR_succ.mpr (by rw [hke.1, hke.2]; exact h'))
      rw [ite_eq_right hA', ite_eq_right hA]
  · rcases (by omega : e < P.k * i + j ∨ e = P.k * i + j) with he | rfl
    · exact reduced_frame fr (ae he) (h.b.red e he)
    · rw [h₉.mem]; simpa only [aOff] using r₈
  · rcases (by omega : e < P.k * i + j ∨ e = P.k * i + j) with he | rfl
    · rw [polyAt_frame fr (ae he)]; exact h.b.res e he
    · rw [hke.1, hke.2, h₉.mem]
      rcases o₈ with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact .inr (by simpa only [aOff] using h2)
      · exact .inl h2

theorem sample_step {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {mA : Mem} {ρ : List Byte} {i j : Nat} (hi : i < P.k)
    (hj : j < P.k) {s : State} (h : VG.Proof.MlKem.AArch64.Kem.BInv P L s₀ mA ρ (P.k * i + j) s) :
    WP isa (P.kemSampleWith keccak.callee i j) s (VG.Proof.MlKem.AArch64.Kem.BInv P L s₀ mA ρ (P.k * i + j + 1)) :=
  WP.seq (WP.mono (VG.Proof.MlKem.AArch64.Kem.setup_ok hp hi hj h) fun _ m => VG.Proof.MlKem.AArch64.Kem.call_ok hp hi hj m)

theorem matrix_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {mA : Mem} {ρ : List Byte} {s : State}
    (h : VG.Proof.MlKem.AArch64.Kem.BInv P L s₀ mA ρ 0 s) : WP isa (P.kemMatrixWith keccak.callee) s (VG.Proof.MlKem.AArch64.Kem.BInv P L s₀ mA ρ (P.k * P.k)) :=
  WPs.seqs (matrix_ne_nil hp.wf.facts.1)
    (WPs.matrix (fun _ hi _ hj _ h => VG.Proof.MlKem.AArch64.Kem.sample_step hp hi hj h) (Nat.le_refl _) h)

/-! ## After the matrix -/

/-- `SampleNTT` succeeds on every entry exactly when `x24` is 1; then its
entries are `Â`'s. -/
theorem BInv.outcome {s₀ : State} {mA : Mem} {ρ : List Byte} {s : State}
    (h : VG.Proof.MlKem.AArch64.Kem.BInv P L s₀ mA ρ (P.k * P.k) s) :
    (s.gpr .x24 = 1 ∧ ∀ i < P.k, ∀ j < P.k,
      sampleNTT 280 (matSeed ρ i j) = some (polyAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ (aOff P i j)))) ∨
    (s.gpr .x24 = 0 ∧ ∃ i < P.k, ∃ j < P.k, sampleNTT 280 (matSeed ρ i j) = none) := by
  by_cases hA : VG.Proof.MlKem.AArch64.Kem.okR P ρ (P.k * P.k)
  · refine .inl ⟨by rw [h.acc, ite_eq_left hA], fun i hi j hj => ?_⟩
    have he : P.k * i + j < P.k * P.k := ij_lt hi hj
    have hke := ij_div (i := i) hj
    have r := h.res (P.k * i + j) he
    have ok := hA (P.k * i + j) he
    rw [hke.1, hke.2] at r ok
    rcases r with r | r
    · rw [r] at ok; simp at ok
    · exact r
  · refine .inr ⟨by rw [h.acc, ite_eq_right hA], ?_⟩
    obtain ⟨e, he, hn⟩ : ∃ e, e < P.k * P.k ∧ ¬ (sampleNTT 280 (matSeed ρ (e / P.k) (e % P.k))).isSome :=
      Classical.byContradiction fun hc => hA fun e he => Classical.byContradiction fun hn => hc ⟨e, he, hn⟩
    exact ⟨e / P.k, div_lt he, e % P.k, mod_lt he, Option.not_isSome_iff_eq_none.mp hn⟩

theorem BInv.reduced {s₀ : State} {mA : Mem} {ρ : List Byte} {s : State} (h : VG.Proof.MlKem.AArch64.Kem.BInv P L s₀ mA ρ (P.k * P.k) s)
    {i j : Nat} (hi : i < P.k) (hj : j < P.k) : Reduced s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ (aOff P i j)) :=
  h.red (P.k * i + j) (ij_lt hi hj)

/-! ## Constant time -/

/-- The arguments of `sample_ntt` depend only on the pointer to `scratch`:
decided for each parameter set. -/
def SetupTaint (P : KemLay) : Prop := ∀ i < P.k, ∀ j < P.k, ∃ hc : Taint.Hint taint.T,
    (taint.check (Taint.ofRegs [.x28]) (.block (P.kemSetup i j)) hc).isSome = true

/-- Two runs with the same pointer to `scratch` and the same stack pointer. -/
structure Two (P : KemLay) (L : VG.Proof.MlKem.AArch64.Kem.Layout) (σ₁ σ₂ : State) : Prop where
  p₁ : VG.Proof.MlKem.AArch64.Kem.Pre P L σ₁
  p₂ : VG.Proof.MlKem.AArch64.Kem.Pre P L σ₂
  sc : VG.Proof.MlKem.AArch64.Kem.kA σ₁ L.sc = VG.Proof.MlKem.AArch64.Kem.kA σ₂ L.sc
  sp : σ₁.sp = σ₂.sp

theorem call_rct {σ₁ σ₂ : State} (ht : VG.Proof.MlKem.AArch64.Kem.Two P L σ₁ σ₂) {m₁ m₂ : Mem} {ρ : List Byte} {i j : Nat} (hi : i < P.k)
    (hj : j < P.k) :
    RelCT isa (fun s₁ s₂ => VG.Proof.MlKem.AArch64.Kem.Mid P L σ₁ m₁ ρ i j s₁ ∧ VG.Proof.MlKem.AArch64.Kem.Mid P L σ₂ m₂ ρ i j s₂) (kgCallWith keccak.callee)
      fun _ _ => True := by
  refine RelCT.seq (RelCT.wp (F₁ := fun s : State => s.sp = σ₁.sp) (F₂ := fun s : State => s.sp = σ₂.sp)
    (sample_ctWith keccak (sd := VG.Proof.MlKem.AArch64.Kem.sA L σ₁ SB) (a := VG.Proof.MlKem.AArch64.Kem.sA L σ₁ (aOff P i j)) (w := VG.Proof.MlKem.AArch64.Kem.sA L σ₁ SS) fun s₁ s₂ h => ?_)
      fun s₁ s₂ h => ⟨?_, ?_⟩)
    (RelCT.taint (A := taint) (Taint.ofRegs []) (fun s₁ s₂ h => agree_of (by rw [h.2.1, h.2.2, ht.sp])
      fun r hr => by cases hr) (by taint_decide))
  · have A₂ := h.2.args ht.p₂ hi hj
    simp only [VG.Proof.MlKem.AArch64.Kem.sA, ← ht.sc] at A₂
    refine ⟨h.1.args ht.p₁ hi hj, A₂, ?_, by rw [h.1.b.kb.sp, h.2.b.kb.sp, ht.sp]⟩
    rw [h.1.seed]
    have s₂ := h.2.seed
    simp only [VG.Proof.MlKem.AArch64.Kem.sA, ← ht.sc] at s₂
    rw [s₂]
  · exact WP.mono ((h.1.args ht.p₁ hi hj).spWith keccak) fun s' e => by rw [e, h.1.b.kb.sp]
  · exact WP.mono ((h.2.args ht.p₂ hi hj).spWith keccak) fun s' e => by rw [e, h.2.b.kb.sp]

theorem sample_rct (hs : VG.Proof.MlKem.AArch64.Kem.SetupTaint P) {σ₁ σ₂ : State} (ht : VG.Proof.MlKem.AArch64.Kem.Two P L σ₁ σ₂) {m₁ m₂ : Mem} {ρ : List Byte}
    {i j : Nat} (hi : i < P.k) (hj : j < P.k) :
    RelCT isa (fun s₁ s₂ => VG.Proof.MlKem.AArch64.Kem.BInv P L σ₁ m₁ ρ (P.k * i + j) s₁ ∧ VG.Proof.MlKem.AArch64.Kem.BInv P L σ₂ m₂ ρ (P.k * i + j) s₂)
      (P.kemSampleWith keccak.callee i j)
      fun s₁ s₂ => VG.Proof.MlKem.AArch64.Kem.BInv P L σ₁ m₁ ρ (P.k * i + j + 1) s₁ ∧ VG.Proof.MlKem.AArch64.Kem.BInv P L σ₂ m₂ ρ (P.k * i + j + 1) s₂ := by
  have hck := (hs i hi j hj).choose_spec
  refine RelCT.seq (R := fun s₁ s₂ => VG.Proof.MlKem.AArch64.Kem.Mid P L σ₁ m₁ ρ i j s₁ ∧ VG.Proof.MlKem.AArch64.Kem.Mid P L σ₂ m₂ ρ i j s₂)
    (RelCT.mono (RelCT.wp (F₁ := VG.Proof.MlKem.AArch64.Kem.Mid P L σ₁ m₁ ρ i j) (F₂ := VG.Proof.MlKem.AArch64.Kem.Mid P L σ₂ m₂ ρ i j)
      (RelCT.taint (A := taint) (Taint.ofRegs [.x28]) (fun s₁ s₂ h =>
        agree_of (by rw [h.1.kb.sp, h.2.kb.sp, ht.sp]) fun r hr => by
          rw [List.mem_singleton.mp hr, h.1.kb.x28, h.2.kb.x28, ht.sc]) hck)
      fun s₁ s₂ h => ⟨VG.Proof.MlKem.AArch64.Kem.setup_ok ht.p₁ hi hj h.1, VG.Proof.MlKem.AArch64.Kem.setup_ok ht.p₂ hi hj h.2⟩) (fun _ _ h => h) fun _ _ h => h.2)
    (RelCT.mono (RelCT.wp (F₁ := VG.Proof.MlKem.AArch64.Kem.BInv P L σ₁ m₁ ρ (P.k * i + j + 1)) (F₂ := VG.Proof.MlKem.AArch64.Kem.BInv P L σ₂ m₂ ρ (P.k * i + j + 1))
      (VG.Proof.MlKem.AArch64.Kem.call_rct ht hi hj) fun s₁ s₂ h => ⟨VG.Proof.MlKem.AArch64.Kem.call_ok ht.p₁ hi hj h.1, VG.Proof.MlKem.AArch64.Kem.call_ok ht.p₂ hi hj h.2⟩)
      (fun _ _ h => h) fun _ _ h => h.2)

theorem matrix_rct (hs : VG.Proof.MlKem.AArch64.Kem.SetupTaint P) {σ₁ σ₂ : State} (ht : VG.Proof.MlKem.AArch64.Kem.Two P L σ₁ σ₂) {m₁ m₂ : Mem} {ρ : List Byte} :
    RelCT isa (fun s₁ s₂ => VG.Proof.MlKem.AArch64.Kem.BInv P L σ₁ m₁ ρ 0 s₁ ∧ VG.Proof.MlKem.AArch64.Kem.BInv P L σ₂ m₂ ρ 0 s₂) (P.kemMatrixWith keccak.callee)
      fun s₁ s₂ => VG.Proof.MlKem.AArch64.Kem.BInv P L σ₁ m₁ ρ (P.k * P.k) s₁ ∧ VG.Proof.MlKem.AArch64.Kem.BInv P L σ₂ m₂ ρ (P.k * P.k) s₂ :=
  RelCTs.seqs (matrix_ne_nil ht.p₁.wf.facts.1)
    (RelCTs.matrix (I := fun e s₁ s₂ => VG.Proof.MlKem.AArch64.Kem.BInv P L σ₁ m₁ ρ e s₁ ∧ VG.Proof.MlKem.AArch64.Kem.BInv P L σ₂ m₂ ρ e s₂)
      (fun _ hi _ hj => VG.Proof.MlKem.AArch64.Kem.sample_rct hs ht hi hj) (Nat.le_refl _))

end VG.Proof.MlKem.AArch64.Kem

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.KemEnc`. -/
section

/-!
# ML-KEM on AArch64: K-PKE.Encrypt after the matrix

`ŷ` (`y_step`), `u` into the ciphertext (`u_step`), and `v` into it (`v_ok`),
with `r` at `RB`, `m` at `MB`, `Â` as the matrix left it, `t̂` decoded from
the bytes of `ek` in a buffer the function only reads, and the ciphertext in a
written buffer (`EncArgs`). What each step establishes survives the steps
after it (`EInv`), as they write only apart from it (`Far`). The steps over
`i < k` are loops (`WPs.range`), and the sums of products in `u[i]` and `v`
loops over `j < k` (`WPs.dot`).
-/

namespace VG.Proof.MlKem.AArch64.Kem

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay} {L : VG.Proof.MlKem.AArch64.Kem.Layout}

/-- `u[i]`'s bytes end within the first `k` ones. -/
theorem du_le {P : KemLay} {i : Nat} (hi : i < P.k) : 32 * P.du * i + 32 * P.du ≤ 32 * (P.du * P.k) := by
  rw [← Nat.mul_assoc]; exact mul_succ_le hi

/-- Where `ek` and the ciphertext are: bytes `[eo, eo + 384 k)` of the read
buffer in `slotReg kE`, and bytes `[co, co + ctLen)` of the written buffer in
`slotReg kC` (in `scratch`, at `CB`). -/
structure EncArgs (P : KemLay) (L : VG.Proof.MlKem.AArch64.Kem.Layout) (kE eo kC co : Nat) : Prop where
  hkE : kE < 4
  rE : L.slot kE < L.nrd
  fE : eo + 384 * P.k ≤ L.len (L.slot kE)
  hkC : kC < 4
  wC : L.nrd ≤ L.slot kC
  fC : co + P.ctLen ≤ L.len (L.slot kC)
  sC : L.slot kC ≠ L.sc ∨ co = CB P

/-- `Â` as the matrix left it in `mB`. -/
abbrev aM (P : KemLay) (L : VG.Proof.MlKem.AArch64.Kem.Layout) (s₀ : State) (mB : Mem) (i j : Nat) : VG.Spec.MlKem.Poly :=
  polyAt mB (VG.Proof.MlKem.AArch64.Kem.sA L s₀ (aOff P i j))

/-- All that `K-PKE.Encrypt` writes: the Keccak state and working space,
`N`, `scratch` past `r ‖ N` and `K'` and `K̄`, the stack below the stack
pointer, and the ciphertext. -/
abbrev encW (P : KemLay) (L : VG.Proof.MlKem.AArch64.Kem.Layout) (s₀ : State) (kC co : Nat) : List Region :=
  [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc 0 840, R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc (RB + 32) 1, R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc PB (SV P - PB), below s₀.sp 16,
    R (VG.Proof.MlKem.AArch64.Kem.kA s₀) (L.slot kC) co P.ctLen]

/-- After `ŷ[j]` for `j < nY` and `u[i]` for `i < nU`, from memory `mE`. -/
structure EInv (P : KemLay) (L : VG.Proof.MlKem.AArch64.Kem.Layout) (s₀ : State) (kC co : Nat) (mE mB : Mem) (v : BitVec 64)
    (rv mv : List Byte) (nY nU : Nat) (s : State) : Prop where
  kb : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s
  x24 : s.gpr .x24 = v
  r : bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ RB) 32 = rv
  m : bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ MB) 32 = mv
  a : ∀ i < P.k, ∀ j < P.k, Reduced s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ (aOff P i j)) ∧
    polyAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ (aOff P i j)) = VG.Proof.MlKem.AArch64.Kem.aM P L s₀ mB i j
  y : ∀ j < nY, PolyIs s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ (yOff P j)) (encY rv j)
  u : ∀ i < nU, bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ (L.slot kC) + BitVec.ofNat 64 (co + 32 * P.du * i)) (32 * P.du) =
    compressEncode P.du (KPke.encU P.params (VG.Proof.MlKem.AArch64.Kem.aM P L s₀ mB) rv i)
  fr : Frame (VG.Proof.MlKem.AArch64.Kem.encW P L s₀ kC co) mE s.mem

/-- A region apart from what `EInv` describes. -/
def Far (P : KemLay) (L : VG.Proof.MlKem.AArch64.Kem.Layout) (s₀ : State) (kC co nY nU : Nat) (r : Region) : Prop :=
  (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc RB 32).Disjoint r ∧ (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc MB 32).Disjoint r ∧
    (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc AH (1024 * (P.k * P.k))).Disjoint r ∧ (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc (YH P) (1024 * nY)).Disjoint r ∧
    (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) (L.slot kC) co (32 * P.du * nU)).Disjoint r ∧ ∃ r' ∈ VG.Proof.MlKem.AArch64.Kem.encW P L s₀ kC co, Region.Sub r r'

theorem EInv.frame {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {kC co : Nat} {mE mB : Mem} {v : BitVec 64}
    {rv mv : List Byte} {nY nU : Nat} {s s' : State} (h : VG.Proof.MlKem.AArch64.Kem.EInv P L s₀ kC co mE mB v rv mv nY nU s)
    (hk : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region} (hf : Frame W s.mem s'.mem)
    (hW : ∀ r ∈ W, VG.Proof.MlKem.AArch64.Kem.Far P L s₀ kC co nY nU r) : VG.Proof.MlKem.AArch64.Kem.EInv P L s₀ kC co mE mB v rv mv nY nU s' := by
  have hw := hp.wf
  refine ⟨hk, by rw [hx, h.x24], ?_, ?_, fun i hi j hj => ?_, fun j hj => ?_, fun i hi => ?_,
    h.fr.trans (hf.sub fun r hr => (hW r hr).2.2.2.2.2)⟩
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).1) (by decide)]; exact h.r
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.1) (by decide)]; exact h.m
  · have hij := ij_lt hi hj
    have hd : ∀ r ∈ W, (polyRegion (VG.Proof.MlKem.AArch64.Kem.sA L s₀ (aOff P i j))).Disjoint r := fun r hr =>
      (hW r hr).2.2.1.sub_left (R.sub2 (by lom) (by lom))
    exact ⟨reduced_frame hf hd (h.a i hi j hj).1, by rw [polyAt_frame hf hd]; exact (h.a i hi j hj).2⟩
  · exact polyIs_frame hf (fun r hr => (hW r hr).2.2.2.1.sub_left
      (R.sub2 (by simp only [yOff]; omega) (by simp only [yOff]; omega))) (h.y j hj)
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.2.2.2.1.sub_left
      (R.sub2 (by omega) (by have := mul_succ_le (a := 32 * P.du) hi; omega))) (by kom)]
    exact h.u i hi

/-- A buffer of `scratch` apart from what `EInv` describes. -/
theorem far_s {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {kE eo kC co : Nat} (A : VG.Proof.MlKem.AArch64.Kem.EncArgs P L kE eo kC co)
    {nY nU o l : Nat} (hnY : nY ≤ P.k) (hnU : nU ≤ P.k) (f : o + l ≤ SV P)
    (h : (o + l ≤ RB ∨ RB + 32 ≤ o) ∧ (o + l ≤ MB ∨ MB + 32 ≤ o) ∧
      (o + l ≤ AH ∨ AH + 1024 * (P.k * P.k) ≤ o) ∧ (o + l ≤ YH P ∨ YH P + 1024 * nY ≤ o) ∧ (o + l ≤ CB P) ∧
      (o + l ≤ 840 ∨ (o = RB + 32 ∧ l = 1) ∨ PB ≤ o)) :
    VG.Proof.MlKem.AArch64.Kem.Far P L s₀ kC co nY nU (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc o l) := by
  have hw := hp.wf
  have f' : o + l ≤ SV P + 48 := by omega
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hu := Nat.mul_le_mul_left (32 * P.du) hnU
  refine ⟨VG.Proof.MlKem.AArch64.Kem.sdisj hp (by lom) f' (by omega), VG.Proof.MlKem.AArch64.Kem.sdisj hp (by lom) f' (by omega),
    VG.Proof.MlKem.AArch64.Kem.sdisj hp (by lom) f' (by omega), VG.Proof.MlKem.AArch64.Kem.sdisj hp (by lom) f' (by omega),
    hp.args.rdisj (hp.lt A.hkC) hp.scb (by have := A.fC; have := Nat.mul_assoc 32 P.du P.k; lom)
      (hp.fs f') (.inr (.inr hp.scw)) ?_, ?_⟩
  · rcases A.sC with hC | hC
    · exact .inl hC
    · exact .inr (.inr (by subst hC; omega))
  · rcases h6 with h6 | ⟨rfl, rfl⟩ | h6
    · exact ⟨_, List.mem_cons_self .., R.sub2 (by omega) (by omega)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
        R.sub2 h6 (by simp only [PB] at h6 ⊢; omega)⟩

theorem far_below {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {kE eo kC co : Nat} (A : VG.Proof.MlKem.AArch64.Kem.EncArgs P L kE eo kC co)
    {nY nU : Nat} (hnY : nY ≤ P.k) (hnU : nU ≤ P.k) : VG.Proof.MlKem.AArch64.Kem.Far P L s₀ kC co nY nU (below s₀.sp 16) := by
  have hw := hp.wf
  have hu := Nat.mul_le_mul_left (32 * P.du) hnU
  exact ⟨VG.Proof.MlKem.AArch64.Kem.below_R hp hp.scb (hp.fs (by lom)), VG.Proof.MlKem.AArch64.Kem.below_R hp hp.scb (hp.fs (by lom)),
    VG.Proof.MlKem.AArch64.Kem.below_R hp hp.scb (hp.fs (by lom)), VG.Proof.MlKem.AArch64.Kem.below_R hp hp.scb (hp.fs (by lom)),
    VG.Proof.MlKem.AArch64.Kem.below_R hp (hp.lt A.hkC) (by have := A.fC; have := Nat.mul_assoc 32 P.du P.k; lom),
    ⟨_, by simp, fun _ h => h⟩⟩

/-- Bytes of a buffer the function only reads, as they were. -/
theorem KB.ro_bytes {s₀ s : State} (h : VG.Proof.MlKem.AArch64.Kem.KB P L s₀ s) {b o n : Nat} (hb : b < L.nrd) (f : o + n ≤ L.len b) :
    bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ b + BitVec.ofNat 64 o) n = bytesAt s₀.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ b + BitVec.ofNat 64 o) n := by
  rw [← bytesAt_slice _ _ f, ← bytesAt_slice _ _ f, h.ro b hb]

theorem po_a (hP : P.Wf) {i j : Nat} (hi : i < P.k) (hj : j < P.k) : VG.Proof.MlKem.AArch64.Kem.PO P (aOff P i j) :=
  have := ij_lt hi hj; ⟨by lom, by lom⟩
theorem po_y (hP : P.Wf) {j : Nat} (hj : j < P.k) : VG.Proof.MlKem.AArch64.Kem.PO P (yOff P j) := ⟨by lom, by lom⟩
theorem po_TP (hP : P.Wf) : VG.Proof.MlKem.AArch64.Kem.PO P (TP P) := ⟨by lom, by lom⟩
theorem po_PP (hP : P.Wf) : VG.Proof.MlKem.AArch64.Kem.PO P (PP P) := ⟨by lom, by lom⟩
theorem po_EP (hP : P.Wf) : VG.Proof.MlKem.AArch64.Kem.PO P (EP P) := ⟨by lom, by lom⟩
theorem po_TH (hP : P.Wf) : VG.Proof.MlKem.AArch64.Kem.PO P (TH P) := ⟨by lom, by lom⟩

/-- A polynomial buffer of `scratch` that `K-PKE.Encrypt` writes. -/
theorem far_w {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {kE eo kC co : Nat} (A : VG.Proof.MlKem.AArch64.Kem.EncArgs P L kE eo kC co) {nY nU : Nat}
    (hnY : nY ≤ P.k) (hnU : nU ≤ P.k) {off : Nat} (h1 : YH P + 1024 * nY ≤ off) (h2 : off + 1024 ≤ CB P) :
    VG.Proof.MlKem.AArch64.Kem.Far P L s₀ kC co nY nU (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc off 1024) :=
  have := hp.wf
  VG.Proof.MlKem.AArch64.Kem.far_s hp A hnY hnU (by lom) (by lom)

theorem far_ns {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {kE eo kC co : Nat} (A : VG.Proof.MlKem.AArch64.Kem.EncArgs P L kE eo kC co) {nY nU : Nat}
    (hnY : nY ≤ P.k) (hnU : nU ≤ P.k) : VG.Proof.MlKem.AArch64.Kem.Far P L s₀ kC co nY nU (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc NS 1024) :=
  have := hp.wf
  VG.Proof.MlKem.AArch64.Kem.far_s hp A hnY hnU (by lom) (by lom)

theorem far_pcW {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {kE eo kC co : Nat} (A : VG.Proof.MlKem.AArch64.Kem.EncArgs P L kE eo kC co) {nY nU : Nat}
    (hnY : nY ≤ P.k) (hnU : nU ≤ P.k) {off : Nat} (h1 : YH P + 1024 * nY ≤ off) (h2 : off + 1024 ≤ CB P) :
    ∀ r ∈ VG.Proof.MlKem.AArch64.Kem.pcW L s₀ off, VG.Proof.MlKem.AArch64.Kem.Far P L s₀ kC co nY nU r := by
  have := hp.wf
  intro r hr
  rcases mem6 hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact VG.Proof.MlKem.AArch64.Kem.far_s hp A hnY hnU (by lom) (by lom)
  · exact VG.Proof.MlKem.AArch64.Kem.far_s hp A hnY hnU (by lom) (by lom)
  · exact VG.Proof.MlKem.AArch64.Kem.far_below hp A hnY hnU
  · exact VG.Proof.MlKem.AArch64.Kem.far_s hp A hnY hnU (by lom) ⟨.inr (by decide), .inr (by decide), .inl (by decide), .inl (by lom),
      by lom, .inr (.inl ⟨rfl, rfl⟩)⟩
  · exact VG.Proof.MlKem.AArch64.Kem.far_s hp A hnY hnU (by lom) (by lom)
  · exact VG.Proof.MlKem.AArch64.Kem.far_w hp A hnY hnU h1 h2

theorem far_mul {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {kE eo kC co : Nat} (A : VG.Proof.MlKem.AArch64.Kem.EncArgs P L kE eo kC co) {nY nU : Nat}
    (hnY : nY ≤ P.k) (hnU : nU ≤ P.k) {off : Nat} (h1 : YH P + 1024 * nY ≤ off) (h2 : off + 1024 ≤ CB P) :
    ∀ r ∈ [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc off 1024, R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc NS 1024], VG.Proof.MlKem.AArch64.Kem.Far P L s₀ kC co nY nU r := by
  intro r hr
  rcases mem2' hr with rfl | rfl
  · exact VG.Proof.MlKem.AArch64.Kem.far_w hp A hnY hnU h1 h2
  · exact VG.Proof.MlKem.AArch64.Kem.far_ns hp A hnY hnU

theorem far_one {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {kE eo kC co : Nat} (A : VG.Proof.MlKem.AArch64.Kem.EncArgs P L kE eo kC co) {nY nU : Nat}
    (hnY : nY ≤ P.k) (hnU : nU ≤ P.k) {off : Nat} (h1 : YH P + 1024 * nY ≤ off) (h2 : off + 1024 ≤ CB P) :
    ∀ r ∈ [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc off 1024], VG.Proof.MlKem.AArch64.Kem.Far P L s₀ kC co nY nU r := fun r hr => by
  rw [List.mem_singleton.mp hr]; exact VG.Proof.MlKem.AArch64.Kem.far_w hp A hnY hnU h1 h2

/-- Two polynomial buffers of `scratch` apart. -/
theorem papart {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {o₁ o₂ : Nat} (h₁ : VG.Proof.MlKem.AArch64.Kem.PO P o₁) (h₂ : VG.Proof.MlKem.AArch64.Kem.PO P o₂)
    (h : o₁ + 1024 ≤ o₂ ∨ o₂ + 1024 ≤ o₁) : (polyRegion (VG.Proof.MlKem.AArch64.Kem.sA L s₀ o₁)).Disjoint (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc o₂ 1024) :=
  VG.Proof.MlKem.AArch64.Kem.sdisj hp h₁.le h₂.le h

/-- A polynomial buffer of `scratch` past the NTT's working space is apart from it. -/
theorem pns {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {o : Nat} (h : VG.Proof.MlKem.AArch64.Kem.PO P o) :
    (polyRegion (VG.Proof.MlKem.AArch64.Kem.sA L s₀ o)).Disjoint (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc NS 1024) := h.ns hp

/-! ## `ŷ` -/

theorem y_step {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {kE eo kC co : Nat} (A : VG.Proof.MlKem.AArch64.Kem.EncArgs P L kE eo kC co) {mE mB : Mem}
    {v : BitVec 64} {rv mv : List Byte} {j : Nat} (hj : j < P.k) {s : State}
    (h : VG.Proof.MlKem.AArch64.Kem.EInv P L s₀ kC co mE mB v rv mv j 0 s) :
    WP isa (P.encYAtWith keccak.callee j) s (VG.Proof.MlKem.AArch64.Kem.EInv P L s₀ kC co mE mB v rv mv (j + 1) 0) := by
  have hw := hp.wf
  have hpo := VG.Proof.MlKem.AArch64.Kem.po_y hw hj
  have h1 : YH P + 1024 * j ≤ yOff P j := by simp only [yOff]; omega
  have h2 : yOff P j + 1024 ≤ CB P := by lom
  refine WP.seq (WP.mono (VG.Proof.MlKem.AArch64.Kem.prfCbd_ok hp (N := j) (off := yOff P j) (by lom) hpo h.kb h.r)
    fun s₁ ⟨kb₁, f₁, p₁, x₁⟩ => ?_)
  have e₁ := h.frame hp kb₁ x₁ f₁ (VG.Proof.MlKem.AArch64.Kem.far_pcW hp A (by omega) (by omega) h1 h2)
  refine WP.mono (VG.Proof.MlKem.AArch64.Kem.ntt_ok hp hpo kb₁ p₁.1) fun s₂ ⟨kb₂, f₂, p₂, x₂⟩ => ?_
  have e₂ := e₁.frame hp kb₂ x₂ f₂ (VG.Proof.MlKem.AArch64.Kem.far_mul hp A (by omega) (by omega) h1 h2)
  rw [p₁.2] at p₂
  refine ⟨e₂.kb, e₂.x24, e₂.r, e₂.m, e₂.a, fun j' hj' => ?_, fun i hi => absurd hi (Nat.not_lt_zero _), e₂.fr⟩
  rcases (by omega : j' < j ∨ j' = j) with hj' | rfl
  · have hy := VG.Proof.MlKem.AArch64.Kem.po_y hw (j := j') (by omega)
    refine polyIs_frame f₂ (fun r hr => by
      rcases mem2' hr with rfl | rfl
      · exact VG.Proof.MlKem.AArch64.Kem.papart hp hy hpo (by simp only [yOff]; omega)
      · exact VG.Proof.MlKem.AArch64.Kem.pns hp hy) (polyIs_frame f₁ (fun r hr => ?_) (h.y j' hj'))
    -- `ŷ[j']` is apart from what `prfCbdWith keccak.callee` writes
    rcases mem6 hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp hy.le (by lom) (.inr (by lom))
    · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp hy.le (by lom) (.inr (by lom))
    · exact VG.Proof.MlKem.AArch64.Kem.below_R hp hp.scb (hp.fs hy.le)
    · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp hy.le (by lom) (.inr (by lom))
    · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp hy.le (by lom) (.inr (by lom))
    · exact VG.Proof.MlKem.AArch64.Kem.papart hp hy hpo (by simp only [yOff]; omega)
  · exact p₂

/-! ## `u` and `v` -/

/-- Bytes of the ciphertext past those written so far. -/
theorem far_ct {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {kE eo kC co : Nat} (A : VG.Proof.MlKem.AArch64.Kem.EncArgs P L kE eo kC co) {nU o l : Nat}
    (h : co + 32 * P.du * nU ≤ o) (f : o + l ≤ co + P.ctLen) :
    VG.Proof.MlKem.AArch64.Kem.Far P L s₀ kC co P.k nU (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) (L.slot kC) o l) := by
  have hw := hp.wf
  have hb := hp.lt A.hkC
  have fC := A.fC
  have f' : o + l ≤ L.len (L.slot kC) := by omega
  have hs : ∀ {o' l' : Nat}, o' + l' ≤ CB P → L.slot kC ≠ L.sc ∨ o' + l' ≤ o ∨ o + l ≤ o' := fun h' => by
    rcases A.sC with hC | hC
    · exact .inl hC
    · exact .inr (.inl (by subst hC; omega))
  have g : ∀ {o' l' : Nat}, o' + l' ≤ CB P → (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) L.sc o' l').Disjoint (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) (L.slot kC) o l) :=
    fun h' => hp.args.rdisj hp.scb hb (hp.fs (by lom)) f' (.inr (.inl hp.scw)) (by
      rcases hs h' with e | e
      · exact .inl (Ne.symm e)
      · exact .inr e)
  exact ⟨g (by lom), g (by lom), g (by lom), g (by lom),
    hp.args.rdisj hb hb (by omega) f' (.inl rfl) (.inr (.inl h)), ⟨_, by simp, R.sub2 (by omega) f⟩⟩

/-- `Â[j, i] ŷ[j]` into `h` (`TP` or `PP`). -/
theorem uprod_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {kE eo kC co : Nat} (A : VG.Proof.MlKem.AArch64.Kem.EncArgs P L kE eo kC co) {mE mB : Mem}
    {v : BitVec 64} {rv mv : List Byte} {i j h : Nat} (hi : i < P.k) (hj : j < P.k) (hh : h = TP P ∨ h = PP P)
    {s : State} (e : VG.Proof.MlKem.AArch64.Kem.EInv P L s₀ kC co mE mB v rv mv P.k i s) :
    WP isa (mulAt h (aOff P j i) (yOff P j)) s fun s' => VG.Proof.MlKem.AArch64.Kem.EInv P L s₀ kC co mE mB v rv mv P.k i s' ∧
      (∀ a, h = PP P → PolyIs s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ (TP P)) a → PolyIs s'.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ (TP P)) a) ∧
      PolyIs s'.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ h) (multiplyNTTs (VG.Proof.MlKem.AArch64.Kem.aM P L s₀ mB j i) (encY rv j)) := by
  have hw := hp.wf
  have hji := ij_lt hj hi
  have a₁ := e.a j hj i hi
  have y₁ := e.y j hj
  have ph : VG.Proof.MlKem.AArch64.Kem.PO P h := by rcases hh with rfl | rfl; exacts [VG.Proof.MlKem.AArch64.Kem.po_TP hw, VG.Proof.MlKem.AArch64.Kem.po_PP hw]
  refine WP.mono (VG.Proof.MlKem.AArch64.Kem.mul_ok hp ph (VG.Proof.MlKem.AArch64.Kem.po_a hw hj hi) (VG.Proof.MlKem.AArch64.Kem.po_y hw hj) (.inr (by rcases hh with rfl | rfl <;> lom))
    (.inr (by rcases hh with rfl | rfl <;> lom)) e.kb a₁.1 y₁.1) fun s₂ ⟨kb₂, f₂, t₂, x₂⟩ => ?_
  rw [a₁.2, y₁.2] at t₂
  refine ⟨e.frame hp kb₂ x₂ f₂ (VG.Proof.MlKem.AArch64.Kem.far_mul hp A (Nat.le_refl _) (Nat.le_of_lt hi) (by rcases hh with rfl | rfl <;> lom)
    (by rcases hh with rfl | rfl <;> lom)), fun a ep ta => ?_, t₂⟩
  subst ep
  exact polyIs_frame f₂ (fun r hr => by
    rcases mem2' hr with rfl | rfl
    · exact VG.Proof.MlKem.AArch64.Kem.papart hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw) (VG.Proof.MlKem.AArch64.Kem.po_PP hw) (.inl (by lom))
    · exact VG.Proof.MlKem.AArch64.Kem.pns hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw)) ta

/-- `TP ← TP + PP`. -/
theorem acc_TP {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {kE eo kC co : Nat} (A : VG.Proof.MlKem.AArch64.Kem.EncArgs P L kE eo kC co) {mE mB : Mem}
    {v : BitVec 64} {rv mv : List Byte} {nU : Nat} (hnU : nU ≤ P.k) {s : State} {a b : VG.Spec.MlKem.Poly}
    (e : VG.Proof.MlKem.AArch64.Kem.EInv P L s₀ kC co mE mB v rv mv P.k nU s) (ht : PolyIs s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ (TP P)) a)
    (hq : PolyIs s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ (PP P)) b) :
    WP isa (addAt (TP P) (PP P)) s fun s' => VG.Proof.MlKem.AArch64.Kem.EInv P L s₀ kC co mE mB v rv mv P.k nU s' ∧
      PolyIs s'.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ (TP P)) (add a b) := by
  have hw := hp.wf
  refine WP.mono (VG.Proof.MlKem.AArch64.Kem.add_ok hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw) (VG.Proof.MlKem.AArch64.Kem.po_PP hw) (.inl (by lom)) e.kb ht.1 hq.1) fun s₃ ⟨kb₃, f₃, t₃, x₃⟩ => ?_
  rw [ht.2, hq.2] at t₃
  exact ⟨e.frame hp kb₃ x₃ f₃ (VG.Proof.MlKem.AArch64.Kem.far_one hp A (Nat.le_refl _) hnU (by lom) (by lom)), t₃⟩

theorem u_step {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) (hc : VG.Proof.MlKem.AArch64.Kem.Calls P) {kE eo kC co : Nat} (A : VG.Proof.MlKem.AArch64.Kem.EncArgs P L kE eo kC co)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {i : Nat} (hi : i < P.k) {s : State}
    (h : VG.Proof.MlKem.AArch64.Kem.EInv P L s₀ kC co mE mB v rv mv P.k i s) :
    WP isa (P.encUAtWith keccak.callee (slotReg kC) co i) s (VG.Proof.MlKem.AArch64.Kem.EInv P L s₀ kC co mE mB v rv mv P.k (i + 1)) := by
  have hw := hp.wf
  have k1 := hw.facts.1
  have hn : i ≤ P.k := Nat.le_of_lt hi
  refine WPs.seqs (by simp) (WPs.append (WPs.mono (WPs.dot (tp := TP P) (pp := PP P)
      (term := fun j h => [mulAt h (aOff P j i) (yOff P j)])
      (E := VG.Proof.MlKem.AArch64.Kem.EInv P L s₀ kC co mE mB v rv mv P.k i)
      (T := fun s a => PolyIs s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ (TP P)) a) (Q := fun s a => PolyIs s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ (PP P)) a)
      (v := fun j => multiplyNTTs (VG.Proof.MlKem.AArch64.Kem.aM P L s₀ mB j i) (encY rv j)) (N := P.k)
      (fun s e => WPs.single (WP.mono (VG.Proof.MlKem.AArch64.Kem.uprod_ok hp A hi k1 (.inl rfl) e) fun _ ⟨e', _, t'⟩ => ⟨e', t'⟩))
      (fun j _ hj s a e t => WPs.single (WP.mono (VG.Proof.MlKem.AArch64.Kem.uprod_ok hp A hi hj (.inr rfl) e)
        fun _ ⟨e', ft, q'⟩ => ⟨e', ft a rfl t, q'⟩))
      (fun s a b e t q => VG.Proof.MlKem.AArch64.Kem.acc_TP hp A hn e t q) k1 (Nat.le_refl _) h) ?_))
  intro s₁ ⟨e₁, t₁⟩
  refine WPs.cons (WP.mono (VG.Proof.MlKem.AArch64.Kem.nttInv_ok hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw) e₁.kb t₁.1) fun s₂ ⟨kb₂, f₂, t₂, x₂⟩ => ?_)
  have e₂ := e₁.frame hp kb₂ x₂ f₂ (VG.Proof.MlKem.AArch64.Kem.far_mul hp A (Nat.le_refl _) hn (by lom) (by lom))
  rw [t₁.2] at t₂
  refine WPs.cons (WP.mono (VG.Proof.MlKem.AArch64.Kem.prfCbd_ok hp (N := P.k + i) (by lom) (VG.Proof.MlKem.AArch64.Kem.po_EP hw) e₂.kb e₂.r)
    fun s₃ ⟨kb₃, f₃, p₃, x₃⟩ => ?_)
  have e₃ := e₂.frame hp kb₃ x₃ f₃ (VG.Proof.MlKem.AArch64.Kem.far_pcW hp A (Nat.le_refl _) hn (by lom) (by lom))
  have t₃ := polyIs_frame f₃ (fun r hr => by
    rcases mem6 hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw).le (by lom) (by lom)
    · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw).le (by lom) (by lom)
    · exact VG.Proof.MlKem.AArch64.Kem.below_R hp hp.scb (hp.fs (VG.Proof.MlKem.AArch64.Kem.po_TP hw).le)
    · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw).le (by lom) (by lom)
    · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw).le (by lom) (by lom)
    · exact VG.Proof.MlKem.AArch64.Kem.papart hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw) (VG.Proof.MlKem.AArch64.Kem.po_EP hw) (by lom)) t₂
  refine WPs.cons (WP.mono (VG.Proof.MlKem.AArch64.Kem.add_ok hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw) (VG.Proof.MlKem.AArch64.Kem.po_EP hw) (.inr (by lom)) e₃.kb t₃.1 p₃.1)
    fun s₄ ⟨kb₄, f₄, t₄, x₄⟩ => ?_)
  have e₄ := e₃.frame hp kb₄ x₄ f₄ (VG.Proof.MlKem.AArch64.Kem.far_one hp A (Nat.le_refl _) hn (by lom) (by lom))
  rw [t₃.2, p₃.2] at t₄
  have fC := A.fC
  have hu := VG.Proof.MlKem.AArch64.Kem.du_le hi
  refine WPs.single (WP.mono (VG.Proof.MlKem.AArch64.Kem.ceL_ok hp hc (off := TP P) (d := P.du) (k := kC) (o := co + 32 * P.du * i)
    (VG.Proof.MlKem.AArch64.Kem.po_TP hw) (.inl rfl) A.hkC A.wC (by lom) (by
      rcases A.sC with hC | hC
      · exact .inl hC
      · exact .inr ⟨by subst hC; lom, .inr (by subst hC; lom)⟩)
    e₄.kb t₄.1) fun s₅ ⟨kb₅, f₅, b₅, x₅⟩ => ?_)
  have e₅ := e₄.frame hp kb₅ x₅ f₅ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact VG.Proof.MlKem.AArch64.Kem.far_ct hp A (Nat.le_refl _) (by lom)
  refine ⟨e₅.kb, e₅.x24, e₅.r, e₅.m, e₅.a, e₅.y, fun i' hi' => ?_, e₅.fr⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact e₅.u i' hi'
  · rw [b₅, t₄.2]; rfl

/-- `t̂[j] ŷ[j]` into `h` (`TP` or `PP`), with `t̂[j]` decoded into `TH`. -/
theorem vprod_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) {kE eo kC co : Nat} (A : VG.Proof.MlKem.AArch64.Kem.EncArgs P L kE eo kC co)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → VG.Spec.MlKem.Poly}
    (hT : ∀ j < P.k, decode12 (bytesAt s₀.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ (L.slot kE) + BitVec.ofNat 64 (eo + 384 * j)) 384) = T j)
    {j h : Nat} (hj : j < P.k) (hh : h = TP P ∨ h = PP P) {s : State}
    (e : VG.Proof.MlKem.AArch64.Kem.EInv P L s₀ kC co mE mB v rv mv P.k P.k s) :
    WPs [dec12At (slotReg kE) (eo + 384 * j) (TH P), mulAt h (TH P) (yOff P j)] s fun s' =>
      VG.Proof.MlKem.AArch64.Kem.EInv P L s₀ kC co mE mB v rv mv P.k P.k s' ∧
      (∀ a, h = PP P → PolyIs s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ (TP P)) a → PolyIs s'.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ (TP P)) a) ∧
      PolyIs s'.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ h) (multiplyNTTs (T j) (encY rv j)) := by
  have hw := hp.wf
  have fE := A.fE
  have hs : L.slot kE ≠ L.sc := by have := A.rE; have := hp.scw; omega
  have hjE := mul_succ_le (a := 384) hj
  refine WPs.cons (WP.mono (VG.Proof.MlKem.AArch64.Kem.dec12_ok hp (k := kE) (o := eo + 384 * j) A.hkE (by omega) (VG.Proof.MlKem.AArch64.Kem.po_TH hw) (.inl hs) e.kb)
    fun s₁ ⟨kb₁, f₁, d₁, x₁⟩ => ?_)
  have e₁ := e.frame hp kb₁ x₁ f₁ (VG.Proof.MlKem.AArch64.Kem.far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  rw [e.kb.ro_bytes A.rE (by omega), hT j hj] at d₁
  have y₁ := e₁.y j hj
  have ph : VG.Proof.MlKem.AArch64.Kem.PO P h := by rcases hh with rfl | rfl; exacts [VG.Proof.MlKem.AArch64.Kem.po_TP hw, VG.Proof.MlKem.AArch64.Kem.po_PP hw]
  refine WPs.single (WP.mono (VG.Proof.MlKem.AArch64.Kem.mul_ok hp ph (VG.Proof.MlKem.AArch64.Kem.po_TH hw) (VG.Proof.MlKem.AArch64.Kem.po_y hw hj) (.inl (by rcases hh with rfl | rfl <;> lom))
    (.inr (by rcases hh with rfl | rfl <;> lom)) e₁.kb d₁.1 y₁.1) fun s₂ ⟨kb₂, f₂, t₂, x₂⟩ => ?_)
  rw [d₁.2, y₁.2] at t₂
  refine ⟨e₁.frame hp kb₂ x₂ f₂ (VG.Proof.MlKem.AArch64.Kem.far_mul hp A (Nat.le_refl _) (Nat.le_refl _)
    (by rcases hh with rfl | rfl <;> lom) (by rcases hh with rfl | rfl <;> lom)), fun a ep ta => ?_, t₂⟩
  subst ep
  refine polyIs_frame f₂ (fun r hr => by
    rcases mem2' hr with rfl | rfl
    · exact VG.Proof.MlKem.AArch64.Kem.papart hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw) (VG.Proof.MlKem.AArch64.Kem.po_PP hw) (.inl (by lom))
    · exact VG.Proof.MlKem.AArch64.Kem.pns hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw)) (polyIs_frame f₁ (fun r hr => ?_) ta)
  rw [List.mem_singleton.mp hr]; exact VG.Proof.MlKem.AArch64.Kem.papart hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw) (VG.Proof.MlKem.AArch64.Kem.po_TH hw) (.inl (by lom))

/-- `v`. -/
abbrev vPoly (P : KemLay) (T : Nat → VG.Spec.MlKem.Poly) (rv mv : List Byte) : VG.Spec.MlKem.Poly :=
  add (add (nttInv (KPke.dotK T (encY rv) P.k)) (cbd rv (2 * P.k))) (decodeDecompress 1 mv)

theorem v_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) (hc : VG.Proof.MlKem.AArch64.Kem.Calls P) {kE eo kC co : Nat} (A : VG.Proof.MlKem.AArch64.Kem.EncArgs P L kE eo kC co)
    {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → VG.Spec.MlKem.Poly}
    (hT : ∀ j < P.k, decode12 (bytesAt s₀.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ (L.slot kE) + BitVec.ofNat 64 (eo + 384 * j)) 384) = T j)
    {s : State} (h : VG.Proof.MlKem.AArch64.Kem.EInv P L s₀ kC co mE mB v rv mv P.k P.k s) :
    WP isa (P.encVAtWith keccak.callee (slotReg kE) eo .x28 MB (slotReg kC) co) s fun s' =>
      VG.Proof.MlKem.AArch64.Kem.EInv P L s₀ kC co mE mB v rv mv P.k P.k s' ∧
      bytesAt s'.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ (L.slot kC) + BitVec.ofNat 64 (co + 32 * P.du * P.k)) (32 * P.dv) =
        compressEncode P.dv (VG.Proof.MlKem.AArch64.Kem.vPoly P T rv mv) := by
  have hw := hp.wf
  have k1 := hw.facts.1
  refine WPs.seqs (by simp) (WPs.append (WPs.mono (WPs.dot (tp := TP P) (pp := PP P)
      (term := fun j h => [dec12At (slotReg kE) (eo + 384 * j) (TH P), mulAt h (TH P) (yOff P j)])
      (E := VG.Proof.MlKem.AArch64.Kem.EInv P L s₀ kC co mE mB v rv mv P.k P.k)
      (T := fun s a => PolyIs s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ (TP P)) a) (Q := fun s a => PolyIs s.mem (VG.Proof.MlKem.AArch64.Kem.sA L s₀ (PP P)) a)
      (v := fun j => multiplyNTTs (T j) (encY rv j)) (N := P.k)
      (fun s e => WPs.mono (VG.Proof.MlKem.AArch64.Kem.vprod_ok hp A hT k1 (.inl rfl) e) fun _ ⟨e', _, t'⟩ => ⟨e', t'⟩)
      (fun j _ hj s a e t => WPs.mono (VG.Proof.MlKem.AArch64.Kem.vprod_ok hp A hT hj (.inr rfl) e)
        fun _ ⟨e', ft, q'⟩ => ⟨e', ft a rfl t, q'⟩)
      (fun s a b e t q => VG.Proof.MlKem.AArch64.Kem.acc_TP hp A (Nat.le_refl _) e t q) k1 (Nat.le_refl _) h) ?_))
  intro s₀' ⟨e₀, t₀⟩
  refine WPs.cons (WP.mono (VG.Proof.MlKem.AArch64.Kem.nttInv_ok hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw) e₀.kb t₀.1) fun s₁ ⟨kb₁, f₁, t₁, x₁⟩ => ?_)
  have e₁ := e₀.frame hp kb₁ x₁ f₁ (VG.Proof.MlKem.AArch64.Kem.far_mul hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  rw [t₀.2] at t₁
  refine WPs.cons (WP.mono (VG.Proof.MlKem.AArch64.Kem.prfCbd_ok hp (N := 2 * P.k) (by lom) (VG.Proof.MlKem.AArch64.Kem.po_EP hw) e₁.kb e₁.r)
    fun s₂ ⟨kb₂, f₂, p₂, x₂⟩ => ?_)
  have e₂ := e₁.frame hp kb₂ x₂ f₂ (VG.Proof.MlKem.AArch64.Kem.far_pcW hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  have fTP : ∀ r ∈ VG.Proof.MlKem.AArch64.Kem.pcW L s₀ (EP P), (polyRegion (VG.Proof.MlKem.AArch64.Kem.sA L s₀ (TP P))).Disjoint r := fun r hr => by
    rcases mem6 hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw).le (by lom) (by lom)
    · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw).le (by lom) (by lom)
    · exact VG.Proof.MlKem.AArch64.Kem.below_R hp hp.scb (hp.fs (VG.Proof.MlKem.AArch64.Kem.po_TP hw).le)
    · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw).le (by lom) (by lom)
    · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw).le (by lom) (by lom)
    · exact VG.Proof.MlKem.AArch64.Kem.papart hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw) (VG.Proof.MlKem.AArch64.Kem.po_EP hw) (by lom)
  have t₂ := polyIs_frame f₂ fTP t₁
  refine WPs.cons (WP.mono (VG.Proof.MlKem.AArch64.Kem.add_ok hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw) (VG.Proof.MlKem.AArch64.Kem.po_EP hw) (.inr (by lom)) e₂.kb t₂.1 p₂.1)
    fun s₃ ⟨kb₃, f₃, t₃, x₃⟩ => ?_)
  have e₃ := e₂.frame hp kb₃ x₃ f₃ (VG.Proof.MlKem.AArch64.Kem.far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  rw [t₂.2, p₂.2] at t₃
  refine WPs.cons (WP.mono (VG.Proof.MlKem.AArch64.Kem.dd_ok hp (k := 3) (o := MB) (d := 1) (off := EP P) (by decide)
    (hp.fs (by lom)) (by decide) (VG.Proof.MlKem.AArch64.Kem.po_EP hw) (.inr (.inl (by lom))) e₃.kb)
    fun s₄ ⟨kb₄, f₄, p₄, x₄⟩ => ?_)
  have e₄ := e₃.frame hp kb₄ x₄ f₄ (VG.Proof.MlKem.AArch64.Kem.far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  have t₄ := polyIs_frame f₄ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact VG.Proof.MlKem.AArch64.Kem.papart hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw) (VG.Proof.MlKem.AArch64.Kem.po_EP hw) (by lom)) t₃
  have hm : bytesAt s₃.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ (L.slot 3) + BitVec.ofNat 64 MB) (32 * 1) = mv := e₃.m
  rw [hm] at p₄
  refine WPs.cons (WP.mono (VG.Proof.MlKem.AArch64.Kem.add_ok hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw) (VG.Proof.MlKem.AArch64.Kem.po_EP hw) (.inr (by lom)) e₄.kb t₄.1 p₄.1)
    fun s₅ ⟨kb₅, f₅, t₅, x₅⟩ => ?_)
  have e₅ := e₄.frame hp kb₅ x₅ f₅ (VG.Proof.MlKem.AArch64.Kem.far_one hp A (Nat.le_refl _) (Nat.le_refl _) (by lom) (by lom))
  rw [t₄.2, p₄.2] at t₅
  have fC := A.fC
  have hmk := Nat.mul_assoc 32 P.du P.k
  refine WPs.single (WP.mono (VG.Proof.MlKem.AArch64.Kem.ceL_ok hp hc (off := TP P) (d := P.dv) (k := kC) (o := co + 32 * P.du * P.k)
    (VG.Proof.MlKem.AArch64.Kem.po_TP hw) (.inr rfl) A.hkC A.wC (by lom) (by
      rcases A.sC with hC | hC
      · exact .inl hC
      · exact .inr ⟨by subst hC; lom, .inr (by subst hC; lom)⟩)
    e₅.kb t₅.1) fun s₆ ⟨kb₆, f₆, b₆, x₆⟩ => ?_)
  refine ⟨e₅.frame hp kb₆ x₆ f₆ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact VG.Proof.MlKem.AArch64.Kem.far_ct hp A (Nat.le_refl _) (by lom), ?_⟩
  rw [b₆, t₅.2]

/-- `ŷ`, `u` and `v`. -/
theorem encrypt_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P L s₀) (hc : VG.Proof.MlKem.AArch64.Kem.Calls P) {kE eo kC co : Nat}
    (A : VG.Proof.MlKem.AArch64.Kem.EncArgs P L kE eo kC co) {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {T : Nat → VG.Spec.MlKem.Poly}
    (hT : ∀ j < P.k, decode12 (bytesAt s₀.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ (L.slot kE) + BitVec.ofNat 64 (eo + 384 * j)) 384) = T j)
    {s : State} (h : VG.Proof.MlKem.AArch64.Kem.EInv P L s₀ kC co mE mB v rv mv 0 0 s) :
    WP isa (P.encryptCWith keccak.callee (slotReg kE) eo .x28 MB (slotReg kC) co) s fun s' =>
      VG.Proof.MlKem.AArch64.Kem.EInv P L s₀ kC co mE mB v rv mv P.k P.k s' ∧
      bytesAt s'.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ (L.slot kC) + BitVec.ofNat 64 (co + 32 * P.du * P.k)) (32 * P.dv) =
        compressEncode P.dv (VG.Proof.MlKem.AArch64.Kem.vPoly P T rv mv) := by
  refine WPs.seqs (by simp) (WPs.append (WPs.append (WPs.mono (WPs.range
    (I := fun j => VG.Proof.MlKem.AArch64.Kem.EInv P L s₀ kC co mE mB v rv mv j 0) (fun j hj _ h => VG.Proof.MlKem.AArch64.Kem.y_step hp A hj h) h) fun s₁ h₁ =>
    WPs.mono (WPs.range (I := VG.Proof.MlKem.AArch64.Kem.EInv P L s₀ kC co mE mB v rv mv P.k) (fun i hi _ h => VG.Proof.MlKem.AArch64.Kem.u_step hp hc A hi h) h₁)
      fun s₂ h₂ => WPs.single (VG.Proof.MlKem.AArch64.Kem.v_ok hp hc A hT h₂))))

/-- The ciphertext's bytes. -/
theorem ct_at {m : Mem} {p : Addr} {U : Nat → List Byte} {V : List Byte}
    (hu : ∀ i < P.k, bytesAt m (p + BitVec.ofNat 64 (32 * P.du * i)) (32 * P.du) = U i)
    (hv : bytesAt m (p + BitVec.ofNat 64 (32 * P.du * P.k)) (32 * P.dv) = V) :
    bytesAt m p P.ctLen = KPke.catK U P.k ++ V := by
  have cat : ∀ n, n ≤ P.k → bytesAt m p (32 * P.du * n) = KPke.catK U n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [Nat.mul_succ, bytesAt_add, ih (by omega), hu n (by omega)]
      exact (KPke.foldK_succ (op := fun a b => a ++ b) (fun x => List.nil_append x) _ n).symm
  rw [show P.ctLen = 32 * P.du * P.k + 32 * P.dv by simp only [KemLay.ctLen]; rw [Nat.mul_add, Nat.mul_assoc],
    bytesAt_add, cat P.k (Nat.le_refl _), hv]

end VG.Proof.MlKem.AArch64.Kem

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.DecapsA`. -/
section

/-!
# ML-KEM on AArch64: `decaps`, the first phase

The prologue, `m' = K-PKE.Decrypt(dk_PKE, c)` (`m_ok`: `û'` by a loop over
`i < k`, and the sum of products by `WPs.dot`), `G(m' ‖ h)` and `ρ` (`a_ok`).
-/

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.MlKem.AArch64 (KemLay)

/-- AArch64 contract for `decaps(dk = x0, ct = x1, key = x2, scratch = x3) ->
w0` of the parameter set `P`. -/
def decapsAArch64 (P : KemLay) : Contract AArch64.isa where
  pre s :=
    let dk : Region := ⟨s.gpr .x0, P.dkLen⟩
    let ct : Region := ⟨s.gpr .x1, P.ctLen⟩
    let key : Region := ⟨s.gpr .x2, 32⟩
    let scratch : Region := ⟨s.gpr .x3, P.scl⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [dk, ct] ∧ s.wr = [key, scratch] ∧ dk.Disjoint key ∧ dk.Disjoint scratch ∧ ct.Disjoint key ∧
    ct.Disjoint scratch ∧ key.Disjoint scratch ∧ 16 ≤ s.sp.toNat ∧ stack.Disjoint dk ∧ stack.Disjoint ct ∧
    stack.Disjoint key ∧ stack.Disjoint scratch
  post s s' :=
    Outcome (fun iters => decapsInternal P.params iters (bytesAt s.mem (s.gpr .x0) P.dkLen)
        (bytesAt s.mem (s.gpr .x1) P.ctLen)) ((s'.gpr .x0).setWidth 32) (bytesAt s'.mem (s.gpr .x2) 32)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp ∧
      leakRho (dkRho P.params (bytesAt s₁.mem (s₁.gpr .x0) P.dkLen)) =
        leakRho (dkRho P.params (bytesAt s₂.mem (s₂.gpr .x0) P.dkLen))

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.Decaps

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

/-- 0 `dk`, 1 `ct` (read); 2 `key`, 3 `scratch` (written), kept in `x25`–`x28`. -/
def deL (P : KemLay) : VG.Proof.MlKem.AArch64.Kem.Layout where
  nb := 4
  nrd := 2
  len b := [P.dkLen, P.ctLen, 32, P.scl].getD b 0
  slot k := k

/-- Arithmetic on the offsets and the buffers of `deL`. -/
macro "dek" : tactic => `(tactic| (
  simp -failIfUnchanged only [deL, List.getD_cons_zero, List.getD_cons_succ, Layout.sc]
  first | decide | kom))

theorem pre_of (hP : P.Wf) {s₀ : State} (h : (VG.Proof.MlKem.decapsAArch64 P).pre s₀) : VG.Proof.MlKem.AArch64.Kem.Pre P (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀ := by
  obtain ⟨rd, wr, d02, d03, d12, d13, d23, sp16, k0, k1, k2, k3⟩ := h
  refine ⟨by rw [rd]; rfl, by rw [wr]; rfl, ⟨fun b hb c hc hbc hw => ?_, fun b hb => ?_, fun b hb => ?_⟩, sp16,
    fun k hk => hk, by dek, rfl, hP⟩
  · have e : ∀ {x y : Region}, x.Disjoint y → y.Disjoint x := fun h => h.symm
    simp only [VG.Proof.MlKem.AArch64.Decaps.deL] at hb hc hw
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hbc | exact absurd hw (by decide) | assumption | exact e ‹_›
  · simp only [VG.Proof.MlKem.AArch64.Decaps.deL] at hb
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
      simp only [VG.Proof.MlKem.AArch64.Decaps.deL, List.getD_cons_zero, List.getD_cons_succ] <;> lom
  · simp only [VG.Proof.MlKem.AArch64.Decaps.deL] at hb
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> assumption

/-- `dk`. -/
abbrev dkD (P : KemLay) (s₀ : State) : List Byte := bytesAt s₀.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ 0) P.dkLen
/-- `c`. -/
abbrev cD (P : KemLay) (s₀ : State) : List Byte := bytesAt s₀.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ 1) P.ctLen
/-- `m'`. -/
abbrev mD (P : KemLay) (s₀ : State) : List Byte := KPke.decM P.params (VG.Proof.MlKem.AArch64.Decaps.dkD P s₀) (VG.Proof.MlKem.AArch64.Decaps.cD P s₀)
/-- `(K', r') = G(m' ‖ h)`. -/
abbrev gD (P : KemLay) (s₀ : State) : List Byte × List Byte := G (VG.Proof.MlKem.AArch64.Decaps.mD P s₀ ++ KPke.dkH P.params (VG.Proof.MlKem.AArch64.Decaps.dkD P s₀))
/-- `ρ`. -/
abbrev rhoD (P : KemLay) (s₀ : State) : List Byte := dkRho P.params (VG.Proof.MlKem.AArch64.Decaps.dkD P s₀)

/-- Bytes `[o, o + n)` of `dk` or `c`, as they were. -/
theorem slice_eq {s₀ s : State} (h : VG.Proof.MlKem.AArch64.Kem.KB P (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀ s) {b o n : Nat} (hb : b < 2) (f : o + n ≤ (VG.Proof.MlKem.AArch64.Decaps.deL P).len b) :
    bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ ((VG.Proof.MlKem.AArch64.Decaps.deL P).slot b) + BitVec.ofNat 64 o) n =
      ((bytesAt s₀.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ b) ((VG.Proof.MlKem.AArch64.Decaps.deL P).len b)).drop o).take n := by
  rw [show (VG.Proof.MlKem.AArch64.Decaps.deL P).slot b = b from rfl, h.ro_bytes hb f, bytesAt_slice _ _ f]

/-! ## `m'` -/

/-- After `û'[i]` for `i < n`. -/
structure DInv (P : KemLay) (s₀ : State) (n : Nat) (s : State) : Prop where
  kb : VG.Proof.MlKem.AArch64.Kem.KB P (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀ s
  x24 : s.gpr .x24 = 1
  u : ∀ i < n, PolyIs s.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀ (yOff P i)) (ntt (KPke.dcU P.params (VG.Proof.MlKem.AArch64.Decaps.cD P s₀) i))

theorem DInv.frame {s₀ : State} {n : Nat} {s s' : State} (h : VG.Proof.MlKem.AArch64.Decaps.DInv P s₀ n s) (hk : VG.Proof.MlKem.AArch64.Kem.KB P (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀ s')
    (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region} (hf : Frame W s.mem s'.mem)
    (hW : ∀ r ∈ W, (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) (VG.Proof.MlKem.AArch64.Decaps.deL P).sc (YH P) (1024 * n)).Disjoint r) : VG.Proof.MlKem.AArch64.Decaps.DInv P s₀ n s' :=
  ⟨hk, by rw [hx, h.x24], fun i hi => polyIs_frame hf (fun r hr => (hW r hr).sub_left
    (R.sub2 (by simp only [yOff]; omega) (by simp only [yOff]; omega))) (h.u i hi)⟩

/-- A buffer of `scratch` past `û'`. -/
theorem dfar {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀) {n o l : Nat} (hn : n ≤ P.k) (f : o + l ≤ SV P + 48)
    (h : o + l ≤ YH P ∨ YH P + 1024 * n ≤ o) :
    (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) (VG.Proof.MlKem.AArch64.Decaps.deL P).sc (YH P) (1024 * n)).Disjoint (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) (VG.Proof.MlKem.AArch64.Decaps.deL P).sc o l) :=
  VG.Proof.MlKem.AArch64.Kem.sdisj hp (by kom) f (by omega)

theorem u_step {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀) (hc : VG.Proof.MlKem.AArch64.Kem.Calls P) {i : Nat} (hi : i < P.k) {s : State}
    (h : VG.Proof.MlKem.AArch64.Decaps.DInv P s₀ i s) : WP isa (P.deU i) s (VG.Proof.MlKem.AArch64.Decaps.DInv P s₀ (i + 1)) := by
  have hw := hp.wf
  have hpo := VG.Proof.MlKem.AArch64.Kem.po_y hw hi
  have hu := VG.Proof.MlKem.AArch64.Kem.du_le hi
  have fu : 32 * P.du * i + 32 * P.du ≤ (VG.Proof.MlKem.AArch64.Decaps.deL P).len 1 := by dek
  refine WP.seq (WP.mono (VG.Proof.MlKem.AArch64.Kem.ddL_ok hp hc (k := 1) (o := 32 * P.du * i) (d := P.du) (off := yOff P i) (by decide)
    fu (.inl rfl) hpo (.inl (by dek)) h.kb)
    fun s₁ ⟨kb₁, f₁, p₁, x₁⟩ => ?_)
  have e₁ := h.frame kb₁ x₁ f₁ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact VG.Proof.MlKem.AArch64.Decaps.dfar hp (by omega) hpo.le (.inr (by simp only [yOff]; omega))
  rw [VG.Proof.MlKem.AArch64.Decaps.slice_eq h.kb (b := 1) (by decide) fu] at p₁
  refine WP.mono (VG.Proof.MlKem.AArch64.Kem.ntt_ok hp hpo kb₁ p₁.1) fun s₂ ⟨kb₂, f₂, p₂, x₂⟩ => ?_
  have e₂ := e₁.frame kb₂ x₂ f₂ fun r hr => by
    rcases mem2' hr with rfl | rfl
    · exact VG.Proof.MlKem.AArch64.Decaps.dfar hp (by omega) hpo.le (.inr (by simp only [yOff]; omega))
    · exact VG.Proof.MlKem.AArch64.Decaps.dfar hp (by omega) (by kom) (.inl (by kom))
  rw [p₁.2] at p₂
  refine ⟨e₂.kb, e₂.x24, fun i' hi' => ?_⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact e₂.u i' hi'
  · refine (congrArg (fun x => PolyIs s₂.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀ (yOff P i')) (ntt x)) ?_).mp p₂
    simp only [KPke.dcU, VG.Proof.MlKem.AArch64.Decaps.cD, VG.Proof.MlKem.AArch64.Decaps.deL, List.getD_cons_zero, List.getD_cons_succ, KemLay.params]

/-- `ŝ[j] = ByteDecode₁₂(dk[384j : 384j + 384])`. -/
theorem dcS_eq (s₀ : State) {j : Nat} (hj : j < P.k) :
    ((bytesAt s₀.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ 0) ((VG.Proof.MlKem.AArch64.Decaps.deL P).len 0)).drop (384 * j)).take 384 =
      ((KPke.dkPke P.params (VG.Proof.MlKem.AArch64.Decaps.dkD P s₀)).drop (384 * j)).take 384 := by
  rw [KPke.dkPke, slice_take _ (show 384 * j + 384 ≤ 384 * P.params.k from mul_succ_le hj)]
  rfl

/-- `ŝ[j] û'[j]` into `h` (`TP` or `PP`), with `ŝ[j]` decoded into `TH`. -/
theorem dprod_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀) {j h : Nat} (hj : j < P.k) (hh : h = TP P ∨ h = PP P)
    {s : State} (e : VG.Proof.MlKem.AArch64.Decaps.DInv P s₀ P.k s) :
    WPs [dec12At .x25 (384 * j) (TH P), mulAt h (TH P) (yOff P j)] s fun s' =>
      VG.Proof.MlKem.AArch64.Decaps.DInv P s₀ P.k s' ∧
      (∀ a, h = PP P → PolyIs s.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀ (TP P)) a → PolyIs s'.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀ (TP P)) a) ∧
      PolyIs s'.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀ h)
        (multiplyNTTs (dcS (KPke.dkPke P.params (VG.Proof.MlKem.AArch64.Decaps.dkD P s₀)) j) (ntt (KPke.dcU P.params (VG.Proof.MlKem.AArch64.Decaps.cD P s₀) j))) := by
  have hw := hp.wf
  have hjE := mul_succ_le (a := 384) hj
  have fw : ∀ {o : Nat}, YH P + 1024 * P.k ≤ o → o + 1024 ≤ SV P + 48 →
      ∀ r ∈ [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) (VG.Proof.MlKem.AArch64.Decaps.deL P).sc o 1024], (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) (VG.Proof.MlKem.AArch64.Decaps.deL P).sc (YH P) (1024 * P.k)).Disjoint r :=
    fun h1 h2 r hr => by rw [List.mem_singleton.mp hr]; exact VG.Proof.MlKem.AArch64.Decaps.dfar hp (Nat.le_refl _) h2 (.inr h1)
  have fm : ∀ {o : Nat}, YH P + 1024 * P.k ≤ o → o + 1024 ≤ SV P + 48 →
      ∀ r ∈ [R (VG.Proof.MlKem.AArch64.Kem.kA s₀) (VG.Proof.MlKem.AArch64.Decaps.deL P).sc o 1024, R (VG.Proof.MlKem.AArch64.Kem.kA s₀) (VG.Proof.MlKem.AArch64.Decaps.deL P).sc NS 1024],
        (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) (VG.Proof.MlKem.AArch64.Decaps.deL P).sc (YH P) (1024 * P.k)).Disjoint r := fun h1 h2 r hr => by
    rcases mem2' hr with rfl | rfl
    · exact VG.Proof.MlKem.AArch64.Decaps.dfar hp (Nat.le_refl _) h2 (.inr h1)
    · exact VG.Proof.MlKem.AArch64.Decaps.dfar hp (Nat.le_refl _) (by kom) (.inl (by kom))
  have f0 : 384 * j + 384 ≤ (VG.Proof.MlKem.AArch64.Decaps.deL P).len 0 := by dek
  refine WPs.cons (WP.mono (VG.Proof.MlKem.AArch64.Kem.dec12_ok hp (k := 0) (o := 384 * j) (by decide) f0 (VG.Proof.MlKem.AArch64.Kem.po_TH hw) (.inl (by dek))
    e.kb) fun s₁ ⟨kb₁, f₁, d₁, x₁⟩ => ?_)
  have e₁ := e.frame kb₁ x₁ f₁ (fw (by kom) (by kom))
  rw [VG.Proof.MlKem.AArch64.Decaps.slice_eq e.kb (b := 0) (by decide) f0, VG.Proof.MlKem.AArch64.Decaps.dcS_eq s₀ hj] at d₁
  have y₁ := e₁.u j hj
  have ph : VG.Proof.MlKem.AArch64.Kem.PO P h := by rcases hh with rfl | rfl; exacts [VG.Proof.MlKem.AArch64.Kem.po_TP hw, VG.Proof.MlKem.AArch64.Kem.po_PP hw]
  refine WPs.single (WP.mono (VG.Proof.MlKem.AArch64.Kem.mul_ok hp ph (VG.Proof.MlKem.AArch64.Kem.po_TH hw) (VG.Proof.MlKem.AArch64.Kem.po_y hw hj) (.inl (by rcases hh with rfl | rfl <;> kom))
    (.inr (by rcases hh with rfl | rfl <;> kom)) e₁.kb d₁.1 y₁.1) fun s₂ ⟨kb₂, f₂, t₂, x₂⟩ => ?_)
  rw [d₁.2, y₁.2] at t₂
  refine ⟨e₁.frame kb₂ x₂ f₂ (fm (by rcases hh with rfl | rfl <;> kom) (by rcases hh with rfl | rfl <;> kom)),
    fun a ep ta => ?_, t₂⟩
  subst ep
  refine polyIs_frame f₂ (fun r hr => by
    rcases mem2' hr with rfl | rfl
    · exact VG.Proof.MlKem.AArch64.Kem.papart hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw) (VG.Proof.MlKem.AArch64.Kem.po_PP hw) (.inl (by kom))
    · exact VG.Proof.MlKem.AArch64.Kem.pns hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw)) (polyIs_frame f₁ (fun r hr => ?_) ta)
  rw [List.mem_singleton.mp hr]; exact VG.Proof.MlKem.AArch64.Kem.papart hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw) (VG.Proof.MlKem.AArch64.Kem.po_TH hw) (.inl (by kom))

/-- `m'`, into `MB`. -/
theorem m_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀) (hc : VG.Proof.MlKem.AArch64.Kem.Calls P) {s : State} (h : VG.Proof.MlKem.AArch64.Decaps.DInv P s₀ 0 s) :
    WP isa P.deM s fun s' => VG.Proof.MlKem.AArch64.Kem.KB P (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀ s' ∧ s'.gpr .x24 = 1 ∧
      bytesAt s'.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀ MB) 32 = VG.Proof.MlKem.AArch64.Decaps.mD P s₀ := by
  have hw := hp.wf
  have k1 := hw.facts.1
  refine WPs.seqs (by simp) (WPs.append (WPs.append (WPs.mono (WPs.range (I := VG.Proof.MlKem.AArch64.Decaps.DInv P s₀)
    (fun i hi _ h => VG.Proof.MlKem.AArch64.Decaps.u_step hp hc hi h) h) fun s₃ h₃ => WPs.mono (WPs.dot (tp := TP P) (pp := PP P)
      (term := fun j h => [dec12At .x25 (384 * j) (TH P), mulAt h (TH P) (yOff P j)])
      (E := VG.Proof.MlKem.AArch64.Decaps.DInv P s₀ P.k)
      (T := fun s a => PolyIs s.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀ (TP P)) a)
      (Q := fun s a => PolyIs s.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀ (PP P)) a)
      (v := fun j => multiplyNTTs (dcS (KPke.dkPke P.params (VG.Proof.MlKem.AArch64.Decaps.dkD P s₀)) j) (ntt (KPke.dcU P.params (VG.Proof.MlKem.AArch64.Decaps.cD P s₀) j)))
      (N := P.k)
      (fun s e => WPs.mono (VG.Proof.MlKem.AArch64.Decaps.dprod_ok hp k1 (.inl rfl) e) fun _ ⟨e', _, t'⟩ => ⟨e', t'⟩)
      (fun j _ hj s a e t => WPs.mono (VG.Proof.MlKem.AArch64.Decaps.dprod_ok hp hj (.inr rfl) e) fun _ ⟨e', ft, q'⟩ => ⟨e', ft a rfl t, q'⟩)
      (fun s a b e t q => WP.mono (VG.Proof.MlKem.AArch64.Kem.add_ok hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw) (VG.Proof.MlKem.AArch64.Kem.po_PP hw) (.inl (by kom)) e.kb t.1 q.1)
        fun s' ⟨kb', f', t', x'⟩ => ⟨e.frame kb' x' f' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact VG.Proof.MlKem.AArch64.Decaps.dfar hp (Nat.le_refl _) (by kom) (.inr (by kom)),
          by rw [t.2, q.2] at t'; exact t'⟩) k1 (Nat.le_refl _) h₃) ?_)))
  intro s₄ ⟨h₄, t₄⟩
  refine WPs.cons (WP.mono (VG.Proof.MlKem.AArch64.Kem.nttInv_ok hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw) h₄.kb t₄.1) fun s₅ ⟨kb₅, f₅, t₅, x₅⟩ => ?_)
  rw [t₄.2] at t₅
  have fv : 32 * P.du * P.k + 32 * P.dv ≤ (VG.Proof.MlKem.AArch64.Decaps.deL P).len 1 := by
    simp only [VG.Proof.MlKem.AArch64.Decaps.deL, List.getD_cons_zero, List.getD_cons_succ, KemLay.ctLen]
    rw [Nat.mul_add, Nat.mul_assoc]
  refine WPs.cons (WP.mono (VG.Proof.MlKem.AArch64.Kem.ddL_ok hp hc (k := 1) (o := 32 * P.du * P.k) (d := P.dv) (off := EP P) (by decide)
    fv (.inr rfl) (VG.Proof.MlKem.AArch64.Kem.po_EP hw) (.inl (by dek)) kb₅) fun s₆ ⟨kb₆, f₆, p₆, x₆⟩ => ?_)
  rw [VG.Proof.MlKem.AArch64.Decaps.slice_eq kb₅ (b := 1) (by decide) fv] at p₆
  have t₆ := polyIs_frame f₆ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact VG.Proof.MlKem.AArch64.Kem.papart hp (VG.Proof.MlKem.AArch64.Kem.po_TP hw) (VG.Proof.MlKem.AArch64.Kem.po_EP hw) (.inr (by kom))) t₅
  refine WPs.cons (WP.mono (VG.Proof.MlKem.AArch64.Kem.sub_ok hp (VG.Proof.MlKem.AArch64.Kem.po_EP hw) (VG.Proof.MlKem.AArch64.Kem.po_TP hw) (.inl (by kom)) kb₆ p₆.1 t₆.1)
    fun s₇ ⟨kb₇, f₇, p₇, x₇⟩ => ?_)
  rw [p₆.2, t₆.2] at p₇
  refine WPs.single (WP.mono (VG.Proof.MlKem.AArch64.Kem.ce_ok hp (off := EP P) (d := 1) (k := 3) (o := MB) (VG.Proof.MlKem.AArch64.Kem.po_EP hw) (by decide)
    (by decide) (by dek) (by dek) (.inr ⟨by kom, .inl (by kom)⟩) kb₇ p₇.1) fun s₈ ⟨kb₈, f₈, b₈, x₈⟩ => ?_)
  refine ⟨kb₈, by rw [x₈, x₇, x₆, x₅, h₄.x24], ?_⟩
  rw [show VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀ MB = VG.Proof.MlKem.AArch64.Kem.kA s₀ ((VG.Proof.MlKem.AArch64.Decaps.deL P).slot 3) + BitVec.ofNat 64 MB from rfl, b₈, p₇.2, VG.Proof.MlKem.AArch64.Decaps.mD, KPke.decM,
    KPke.kpkeDecrypt_eq]
  rfl

/-! ## `G(m' ‖ h)` and `ρ` -/

/-- After the first phase. -/
structure AfterA (P : KemLay) (s₀ s : State) : Prop where
  kb : VG.Proof.MlKem.AArch64.Kem.KB P (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀ s
  x24 : s.gpr .x24 = 1
  m : bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀ MB) 32 = VG.Proof.MlKem.AArch64.Decaps.mD P s₀
  kp : bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀ KP) 32 = (VG.Proof.MlKem.AArch64.Decaps.gD P s₀).1
  r : bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀ RB) 32 = (VG.Proof.MlKem.AArch64.Decaps.gD P s₀).2
  rho : bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀ SB) 32 = VG.Proof.MlKem.AArch64.Decaps.rhoD P s₀

theorem a_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀) (hc : VG.Proof.MlKem.AArch64.Kem.Calls P) :
    WP isa (P.deAWith keccak.callee) s₀ (VG.Proof.MlKem.AArch64.Decaps.AfterA P s₀) := by
  have hw := hp.wf
  refine WP.seq (WP.mono (VG.Proof.MlKem.AArch64.Kem.prologue_ok hp) fun s₁ h₁ => WP.seq (WP.mono (VG.Proof.MlKem.AArch64.Decaps.m_ok hp hc ⟨h₁.kb, h₁.x24,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s₂ ⟨kb₂, x₂, m₂⟩ => ?_))
  -- `G(m' ‖ h)`
  refine WP.seq (WP.mono (hashWith_ok keccak (VG.Proof.MlKem.AArch64.Kem.hsetup hp kb₂ (by decide : 72 ∈ Spec.Sha3.rates)) (sfx := 6) (by decide)
    (ins := [⟨.x28, MB, 32⟩, ⟨.x25, 768 * P.k + 32, 32⟩]) (outs := [⟨.x28, KP, 32⟩, ⟨.x28, RB, 32⟩]) (by simp)
    (fun p hp' => by
      rcases mem2' hp' with rfl | rfl
      · exact VG.Proof.MlKem.AArch64.Kem.pieceOk (k := 3) hp kb₂ (by decide) (by dek) (.inr (by decide)) (by decide) (by dek)
      · exact VG.Proof.MlKem.AArch64.Kem.pieceOk (k := 0) hp kb₂ (by decide) (by dek) (.inl (by dek)) (by decide) (by dek))
    (fun p hp' => by
      rcases mem2' hp' with rfl | rfl
      · exact VG.Proof.MlKem.AArch64.Kem.pieceOk (k := 3) hp kb₂ (by decide) (by dek) (.inr (by decide)) (by decide) (by dek)
      · exact VG.Proof.MlKem.AArch64.Kem.pieceOk (k := 3) hp kb₂ (by decide) (by dek) (.inr (by decide)) (by decide) (by dek))
    (by
      refine List.pairwise_pair.mpr ?_
      simp only [preg, VG.Proof.MlKem.AArch64.Kem.e28 kb₂]
      exact VG.Proof.MlKem.AArch64.Kem.sdisj hp (by kom) (by kom) (by decide)))
    fun s₃ ⟨k₃, o₃⟩ => ?_)
  have kb₃ := kb₂.hash hp k₃ fun p hp' => by
    rcases mem2' hp' with rfl | rfl
    · exact ⟨3, KP, 32, rfl, by decide, by dek, by dek, .inr (.inr (by kom))⟩
    · exact ⟨3, RB, 32, rfl, by decide, by dek, by dek, .inr (.inr (by kom))⟩
  have msg : (List.map (pbytes s₂) [⟨.x28, MB, 32⟩, ⟨.x25, 768 * P.k + 32, 32⟩]).flatten =
      VG.Proof.MlKem.AArch64.Decaps.mD P s₀ ++ KPke.dkH P.params (VG.Proof.MlKem.AArch64.Decaps.dkD P s₀) := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      VG.Proof.MlKem.AArch64.Kem.e28 kb₂, kb₂.x25]
    rw [m₂, VG.Proof.MlKem.AArch64.Decaps.slice_eq kb₂ (b := 0) (by decide) (by dek)]
    rfl
  obtain ⟨o₁, o₂, -⟩ := o₃
  rw [msg] at o₁ o₂
  have hG := G_eq (VG.Proof.MlKem.AArch64.Decaps.mD P s₀ ++ KPke.dkH P.params (VG.Proof.MlKem.AArch64.Decaps.dkD P s₀))
  have kp₃ : bytesAt s₃.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀ KP) 32 = (VG.Proof.MlKem.AArch64.Decaps.gD P s₀).1 := by
    rw [← VG.Proof.MlKem.AArch64.Kem.e28 kb₂, o₁]; show _ = (G (VG.Proof.MlKem.AArch64.Decaps.mD P s₀ ++ KPke.dkH P.params (VG.Proof.MlKem.AArch64.Decaps.dkD P s₀))).1; rw [hG]; rfl
  have r₃ : bytesAt s₃.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀ RB) 32 = (VG.Proof.MlKem.AArch64.Decaps.gD P s₀).2 := by
    rw [← VG.Proof.MlKem.AArch64.Kem.e28 kb₂, o₂]; show _ = (G (VG.Proof.MlKem.AArch64.Decaps.mD P s₀ ++ KPke.dkH P.params (VG.Proof.MlKem.AArch64.Decaps.dkD P s₀))).2; rw [hG]; rfl
  have k₃' := k₃
  simp only [VG.Proof.MlKem.AArch64.STr, VG.Proof.MlKem.AArch64.WKr, preg, List.map_cons, List.map_nil,
    kb₂.x28, kb₂.sp] at k₃'
  have m₃ : bytesAt s₃.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀ MB) 32 = VG.Proof.MlKem.AArch64.Decaps.mD P s₀ := by
    rw [bytesAt_frame k₃'.frame (fun r hr => by
      rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
      · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp (by kom) (by kom) (by decide)
      · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp (by kom) (by kom) (by decide)
      · exact VG.Proof.MlKem.AArch64.Kem.below_R hp hp.scb (hp.fs (by kom))
      · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp (by kom) (by kom) (by decide)
      · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp (by kom) (by kom) (by decide)) (by decide)]
    exact m₂
  -- `ρ`
  refine WP.mono (KeyGen.copy_ok (S := VG.Proof.MlKem.AArch64.Kem.kA s₀ 0) (D := VG.Proof.MlKem.AArch64.Kem.kA s₀ 3) (so := 768 * P.k) (dO := SB) (by decide)
    (by decide) (by kom) (by decide) (hp.args.rdisj (by dek) (by dek) (by dek) (hp.fs (by kom)) (by dek)
      (by dek)) kb₃.x25 kb₃.x28 (VG.Proof.MlKem.AArch64.Kem.cov_r hp kb₃ (b := 0) (by dek) (by dek)) (VG.Proof.MlKem.AArch64.Kem.cov_s hp kb₃ (by kom)))
    fun s₄ ⟨k₄, f₄, b₄⟩ => ?_
  have kb₄ := kb₃.frame k₄ f₄ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact VG.Proof.MlKem.AArch64.Kem.safe_scr hp (by kom)
  have far₄ : ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ SB ∨ SB + 32 ≤ o) →
      bytesAt s₄.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀ o) l = bytesAt s₃.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀ o) l := fun f h => by
    refine bytesAt_frame f₄ (fun r hr => ?_) (by kom)
    rw [List.mem_singleton.mp hr]
    exact VG.Proof.MlKem.AArch64.Kem.sdisj hp f (by kom) h
  refine ⟨kb₄, by rw [k₄.get .x24, k₃.cs _ (by decide) (by decide), x₂],
    by rw [far₄ (o := MB) (l := 32) (by kom) (by decide)]; exact m₃,
    by rw [far₄ (o := KP) (l := 32) (by kom) (by decide)]; exact kp₃,
    by rw [far₄ (o := RB) (l := 32) (by kom) (by decide)]; exact r₃, ?_⟩
  rw [show VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Decaps.deL P) s₀ SB = VG.Proof.MlKem.AArch64.Kem.kA s₀ 3 + BitVec.ofNat 64 SB from rfl, b₄,
    show VG.Proof.MlKem.AArch64.Kem.kA s₀ 0 = VG.Proof.MlKem.AArch64.Kem.kA s₀ ((VG.Proof.MlKem.AArch64.Decaps.deL P).slot 0) from rfl, VG.Proof.MlKem.AArch64.Decaps.slice_eq kb₃ (b := 0) (by decide) (by dek)]
  rfl

end VG.Proof.MlKem.AArch64.Decaps

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.Encaps`. -/
section

/-!
# ML-KEM on AArch64: `vg_mlkem768_encaps` and `vg_mlkem1024_encaps`

Correctness is the prologue, `m`, `H(ek)`, `G(m ‖ H(ek))` and `ρ` (`a_ok`),
the matrix (`matrix_ok`), then `ŷ`, `u` and `v` (`encrypt_ok`) and the
epilogue (`c_ok`).

Constant time up to `ρ`, relating two runs from states that agree on the
pointers and on `ρ`: the first and last phases by the taint analysis, the
matrix by `matrix_rct`.

The proof is stated once for a well-formed parameter set, with the taint
analyses of its code (`EnTaints`) decided on each; the end of this file is
ML-KEM-768's instance (and `Proof/MlKem1024/AArch64/Encaps.lean` ML-KEM-1024's).
-/

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.MlKem.AArch64 (KemLay)

/-- AArch64 contract for `encaps(ek = x0, m = x1, key = x2, ct = x3,
scratch = x4) -> w0` of the parameter set `P`. -/
def encapsAArch64 (P : KemLay) : Contract AArch64.isa where
  pre s :=
    let ek : Region := ⟨s.gpr .x0, P.ekLen⟩
    let msg : Region := ⟨s.gpr .x1, 32⟩
    let key : Region := ⟨s.gpr .x2, 32⟩
    let ct : Region := ⟨s.gpr .x3, P.ctLen⟩
    let scratch : Region := ⟨s.gpr .x4, P.scl⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [ek, msg] ∧ s.wr = [key, ct, scratch] ∧ ek.Disjoint key ∧ ek.Disjoint ct ∧
    ek.Disjoint scratch ∧ msg.Disjoint key ∧ msg.Disjoint ct ∧ msg.Disjoint scratch ∧ key.Disjoint ct ∧
    key.Disjoint scratch ∧ ct.Disjoint scratch ∧ 16 ≤ s.sp.toNat ∧ stack.Disjoint ek ∧ stack.Disjoint msg ∧
    stack.Disjoint key ∧ stack.Disjoint ct ∧ stack.Disjoint scratch
  post s s' :=
    Outcome (fun iters => encapsInternal P.params iters (bytesAt s.mem (s.gpr .x0) P.ekLen)
        (bytesAt s.mem (s.gpr .x1) 32)) ((s'.gpr .x0).setWidth 32)
      (bytesAt s'.mem (s.gpr .x2) 32, bytesAt s'.mem (s.gpr .x3) P.ctLen)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp ∧
      leakRho (ekRho P.params (bytesAt s₁.mem (s₁.gpr .x0) P.ekLen)) =
        leakRho (ekRho P.params (bytesAt s₂.mem (s₂.gpr .x0) P.ekLen))

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.Encaps

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

/-- 0 `ek`, 1 `m` (read); 2 `key`, 3 `ct`, 4 `scratch` (written); `ek`, `key`,
`ct` and `scratch` kept in `x25`–`x28`. -/
def enL (P : KemLay) : VG.Proof.MlKem.AArch64.Kem.Layout where
  nb := 5
  nrd := 2
  len b := [P.ekLen, 32, 32, P.ctLen, P.scl].getD b 0
  slot k := [0, 2, 3, 4].getD k 4

/-- Arithmetic on the offsets and the buffers of `enL`. -/
macro "enk" : tactic => `(tactic| (
  simp -failIfUnchanged only [enL, List.getD_cons_zero, List.getD_cons_succ, Layout.sc]
  first | decide | kom))

theorem pre_of (hP : P.Wf) {s₀ : State} (h : (VG.Proof.MlKem.encapsAArch64 P).pre s₀) : VG.Proof.MlKem.AArch64.Kem.Pre P (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀ := by
  obtain ⟨rd, wr, d02, d03, d04, d12, d13, d14, d23, d24, d34, sp16, k0, k1, k2, k3, k4⟩ := h
  refine ⟨by rw [rd]; rfl, by rw [wr]; rfl, ⟨fun b hb c hc hbc hw => ?_, fun b hb => ?_, fun b hb => ?_⟩, sp16,
    by enk, by enk, rfl, hP⟩
  · have e : ∀ {x y : Region}, x.Disjoint y → y.Disjoint x := fun h => h.symm
    simp only [VG.Proof.MlKem.AArch64.Encaps.enL] at hb hc hw
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4) with rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hbc | exact absurd hw (by decide) | assumption | exact e ‹_›
  · simp only [VG.Proof.MlKem.AArch64.Encaps.enL] at hb
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4) with rfl | rfl | rfl | rfl | rfl <;>
      simp only [VG.Proof.MlKem.AArch64.Encaps.enL, List.getD_cons_zero, List.getD_cons_succ] <;> lom
  · simp only [VG.Proof.MlKem.AArch64.Encaps.enL] at hb
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4) with rfl | rfl | rfl | rfl | rfl <;> assumption

/-- `ek`. -/
abbrev ekE (P : KemLay) (s₀ : State) : List Byte := bytesAt s₀.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ 0) P.ekLen
/-- `m`. -/
abbrev mE (s₀ : State) : List Byte := bytesAt s₀.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ 1) 32
/-- `(K, r) = G(m ‖ H(ek))`. -/
abbrev gE (P : KemLay) (s₀ : State) : List Byte × List Byte := G (VG.Proof.MlKem.AArch64.Encaps.mE s₀ ++ H (VG.Proof.MlKem.AArch64.Encaps.ekE P s₀))
/-- `ρ`. -/
abbrev rhoE (P : KemLay) (s₀ : State) : List Byte := ekRho P.params (VG.Proof.MlKem.AArch64.Encaps.ekE P s₀)

theorem sha3Suffix_eq : Spec.Sha3.sha3Suffix = BitVec.ofNat 8 6 := rfl

/-- After the first phase. -/
structure AfterA (P : KemLay) (s₀ s : State) : Prop where
  kb : VG.Proof.MlKem.AArch64.Kem.KB P (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀ s
  x24 : s.gpr .x24 = 1
  key : bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ 2) 32 = (VG.Proof.MlKem.AArch64.Encaps.gE P s₀).1
  r : bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀ RB) 32 = (VG.Proof.MlKem.AArch64.Encaps.gE P s₀).2
  m : bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀ MB) 32 = VG.Proof.MlKem.AArch64.Encaps.mE s₀
  rho : bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀ SB) 32 = VG.Proof.MlKem.AArch64.Encaps.rhoE P s₀

theorem a_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀) : WP isa (P.enAWith keccak.callee) s₀ (VG.Proof.MlKem.AArch64.Encaps.AfterA P s₀) := by
  have hw := hp.wf
  -- the prologue and `m`
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.AArch64.Kem.prologue_ok hp) fun s₁ h₁ => ?_
  refine WP.mono (KeyGen.copy_ok (S := VG.Proof.MlKem.AArch64.Kem.kA s₀ 1) (D := VG.Proof.MlKem.AArch64.Kem.kA s₀ 4) (so := 0) (dO := MB) (by decide) (by decide)
    (by decide) (by decide) (hp.args.rdisj (by enk) (by enk) (by enk) (hp.fs (by lom)) (by enk)
      (by decide)) (by rw [h₁.keep.get .x1 (by decide)]; rfl) h₁.kb.x28
    (VG.Proof.MlKem.AArch64.Kem.cov_r hp h₁.kb (b := 1) (by enk) (by enk)) (VG.Proof.MlKem.AArch64.Kem.cov_s hp h₁.kb (by lom)))
    fun s₂ ⟨k₂, f₂, b₂⟩ => ?_
  have kb₂ := h₁.kb.frame k₂ f₂ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact VG.Proof.MlKem.AArch64.Kem.safe_scr hp (by enk)
  have m₂ : bytesAt s₂.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀ MB) 32 = VG.Proof.MlKem.AArch64.Encaps.mE s₀ := by
    rw [show VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀ MB = VG.Proof.MlKem.AArch64.Kem.kA s₀ 4 + BitVec.ofNat 64 MB from rfl, b₂,
      h₁.kb.ro_bytes (b := 1) (by enk) (by enk), ptr_zero]
  have x24₂ : s₂.gpr .x24 = 1 := by rw [k₂.get .x24, h₁.x24]
  -- `H(ek)`
  refine WP.seq (WP.mono (hashWith_ok keccak (VG.Proof.MlKem.AArch64.Kem.hsetup hp kb₂ (by decide : 136 ∈ Spec.Sha3.rates)) (sfx := 6) (by decide)
    (ins := [⟨.x25, 0, P.ekLen⟩]) (outs := [⟨.x28, HB, 32⟩]) (by simp)
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact VG.Proof.MlKem.AArch64.Kem.pieceOk (k := 0) hp kb₂ (by decide) (by enk) (.inl (by enk)) (by enk) (by enk))
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact VG.Proof.MlKem.AArch64.Kem.pieceOk (k := 3) hp kb₂ (by decide) (by enk) (.inr (by decide)) (by decide) (by enk))
    (List.pairwise_singleton _ _)) fun s₃ ⟨k₃, o₃⟩ => ?_)
  have kb₃ := kb₂.hash hp k₃ fun p hp' => by
    rw [List.mem_singleton.mp hp']
    exact ⟨3, HB, 32, rfl, by decide, by enk, by enk, .inr (.inr (by enk))⟩
  have hek : bytesAt s₂.mem (s₂.gpr .x25 + BitVec.ofNat 64 0) P.ekLen = VG.Proof.MlKem.AArch64.Encaps.ekE P s₀ := by
    rw [kb₂.x25, ptr_zero]
    exact kb₂.ro (b := 0) (by enk)
  have h₃ : bytesAt s₃.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀ HB) 32 = H (VG.Proof.MlKem.AArch64.Encaps.ekE P s₀) := by
    obtain ⟨o, -⟩ := o₃
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      VG.Proof.MlKem.AArch64.Kem.e28 kb₂] at o
    rw [hek] at o
    rw [o, H_eq]; rfl
  have k₃' := k₃
  simp only [VG.Proof.MlKem.AArch64.STr, VG.Proof.MlKem.AArch64.WKr, preg, List.map_cons, List.map_nil,
    kb₂.x28, kb₂.sp] at k₃'
  have m₃ : bytesAt s₃.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀ MB) 32 = VG.Proof.MlKem.AArch64.Encaps.mE s₀ := by
    rw [bytesAt_frame k₃'.frame (fun r hr => by
      rcases mem4 hr with rfl | rfl | rfl | rfl
      · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp (by enk) (by enk) (by decide)
      · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp (by enk) (by enk) (by decide)
      · exact VG.Proof.MlKem.AArch64.Kem.below_R hp hp.scb (by enk)
      · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp (by enk) (by enk) (by decide)) (by decide)]
    exact m₂
  -- `G(m ‖ H(ek))`
  refine WP.seq (WP.mono (hashWith_ok keccak (VG.Proof.MlKem.AArch64.Kem.hsetup hp kb₃ (by decide : 72 ∈ Spec.Sha3.rates)) (sfx := 6) (by decide)
    (ins := [⟨.x28, MB, 32⟩, ⟨.x28, HB, 32⟩]) (outs := [⟨.x26, 0, 32⟩, ⟨.x28, RB, 32⟩]) (by simp)
    (fun p hp' => by
      rcases mem2' hp' with rfl | rfl
      · exact VG.Proof.MlKem.AArch64.Kem.pieceOk (k := 3) hp kb₃ (by decide) (by enk) (.inr (by decide)) (by decide) (by enk)
      · exact VG.Proof.MlKem.AArch64.Kem.pieceOk (k := 3) hp kb₃ (by decide) (by enk) (.inr (by decide)) (by decide) (by enk))
    (fun p hp' => by
      rcases mem2' hp' with rfl | rfl
      · exact VG.Proof.MlKem.AArch64.Kem.pieceOk (k := 1) hp kb₃ (by decide) (by enk) (.inl (by enk)) (by decide) (by enk)
      · exact VG.Proof.MlKem.AArch64.Kem.pieceOk (k := 3) hp kb₃ (by decide) (by enk) (.inr (by decide)) (by decide) (by enk))
    (by
      refine List.pairwise_pair.mpr ?_
      simp only [preg, kb₃.x26, VG.Proof.MlKem.AArch64.Kem.e28 kb₃]
      exact hp.args.rdisj (by enk) (by enk) (by enk) (by enk) (by enk) (by enk)))
    fun s₄ ⟨k₄, o₄⟩ => ?_)
  have kb₄ := kb₃.hash hp k₄ fun p hp' => by
    rcases mem2' hp' with rfl | rfl
    · exact ⟨1, 0, 32, rfl, by decide, by enk, by enk, .inl (by enk)⟩
    · exact ⟨3, RB, 32, rfl, by decide, by enk, by enk, .inr (.inr (by enk))⟩
  have msg : (List.map (pbytes s₃) [⟨.x28, MB, 32⟩, ⟨.x28, HB, 32⟩]).flatten = VG.Proof.MlKem.AArch64.Encaps.mE s₀ ++ H (VG.Proof.MlKem.AArch64.Encaps.ekE P s₀) := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, pbytes,
      VG.Proof.MlKem.AArch64.Kem.e28 kb₃]
    rw [m₃, h₃]
  obtain ⟨o₁, o₂, -⟩ := o₄
  rw [msg] at o₁ o₂
  have hG := G_eq (VG.Proof.MlKem.AArch64.Encaps.mE s₀ ++ H (VG.Proof.MlKem.AArch64.Encaps.ekE P s₀))
  have key₄ : bytesAt s₄.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ 2) 32 = (VG.Proof.MlKem.AArch64.Encaps.gE P s₀).1 := by
    have e : VG.Proof.MlKem.AArch64.Kem.kA s₀ 2 = s₃.gpr .x26 + BitVec.ofNat 64 0 := by rw [kb₃.x26, ptr_zero]; rfl
    rw [e, o₁]; show _ = (G (VG.Proof.MlKem.AArch64.Encaps.mE s₀ ++ H (VG.Proof.MlKem.AArch64.Encaps.ekE P s₀))).1; rw [hG]; rfl
  have r₄ : bytesAt s₄.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀ RB) 32 = (VG.Proof.MlKem.AArch64.Encaps.gE P s₀).2 := by
    rw [← VG.Proof.MlKem.AArch64.Kem.e28 kb₃, o₂]; show _ = (G (VG.Proof.MlKem.AArch64.Encaps.mE s₀ ++ H (VG.Proof.MlKem.AArch64.Encaps.ekE P s₀))).2; rw [hG]; rfl
  have k₄' := k₄
  simp only [VG.Proof.MlKem.AArch64.STr, VG.Proof.MlKem.AArch64.WKr, preg, List.map_cons, List.map_nil,
    kb₃.x28, kb₃.x26, kb₃.sp] at k₄'
  have m₄ : bytesAt s₄.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀ MB) 32 = VG.Proof.MlKem.AArch64.Encaps.mE s₀ := by
    rw [bytesAt_frame k₄'.frame (fun r hr => by
      rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
      · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp (by enk) (by enk) (by decide)
      · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp (by enk) (by enk) (by decide)
      · exact VG.Proof.MlKem.AArch64.Kem.below_R hp hp.scb (by enk)
      · exact hp.args.rdisj (by enk) (by enk) (by enk) (by enk) (by enk) (by enk)
      · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp (by enk) (by enk) (by decide)) (by decide)]
    exact m₃
  -- `ρ`
  refine WP.mono (KeyGen.copy_ok (S := VG.Proof.MlKem.AArch64.Kem.kA s₀ 0) (D := VG.Proof.MlKem.AArch64.Kem.kA s₀ 4) (so := 384 * P.k) (dO := SB) (by decide)
    (by decide) (by lom) (by decide) (hp.args.rdisj (by enk) (by enk) (by enk)
      (hp.fs (by lom)) (by enk) (by enk)) kb₄.x25 kb₄.x28 (VG.Proof.MlKem.AArch64.Kem.cov_r hp kb₄ (b := 0) (by enk)
      (by enk)) (VG.Proof.MlKem.AArch64.Kem.cov_s hp kb₄ (by lom)))
    fun s₅ ⟨k₅, f₅, b₅⟩ => ?_
  have kb₅ := kb₄.frame k₅ f₅ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact VG.Proof.MlKem.AArch64.Kem.safe_scr hp (by enk)
  have far₅ : ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ SB ∨ SB + 32 ≤ o) →
      bytesAt s₅.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀ o) l = bytesAt s₄.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀ o) l := fun f h => by
    refine bytesAt_frame f₅ (fun r hr => ?_) (by lom)
    rw [List.mem_singleton.mp hr]
    exact VG.Proof.MlKem.AArch64.Kem.sdisj hp f (by lom) h
  refine ⟨kb₅, by rw [k₅.get .x24, k₄.cs _ (by decide) (by decide), k₃.cs _ (by decide) (by decide), x24₂], ?_,
    by rw [far₅ (o := RB) (l := 32) (by lom) (by decide)]; exact r₄,
    by rw [far₅ (o := MB) (l := 32) (by lom) (by decide)]; exact m₄, ?_⟩
  · rw [bytesAt_frame f₅ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (hp.args.disj 2 (by enk) 4 (by enk) (by decide) (by enk)).sub_right
        (R.sub (hp.fs (by lom)))) (by decide)]
    exact key₄
  · rw [show VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀ SB = VG.Proof.MlKem.AArch64.Kem.kA s₀ 4 + BitVec.ofNat 64 SB from rfl, b₅,
      kb₄.ro_bytes (b := 0) (by enk) (by enk),
      ← bytesAt_slice _ _ (show 384 * P.k + 32 ≤ P.ekLen from Nat.le_refl _)]
    rfl

/-! ## `ŷ`, `u`, `v` and the epilogue -/

/-- What the function leaves. -/
structure Done (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (s : State) : Prop where
  abi : abiPreserved s₀ s
  x0 : s.gpr .x0 = v
  key : bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ 2) 32 = (VG.Proof.MlKem.AArch64.Encaps.gE P s₀).1
  ct : bytesAt s.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ 3) P.ctLen = KPke.ct P.params (VG.Proof.MlKem.AArch64.Kem.aM P (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀ mB) (VG.Proof.MlKem.AArch64.Encaps.ekE P s₀) (VG.Proof.MlKem.AArch64.Encaps.mE s₀) (VG.Proof.MlKem.AArch64.Encaps.gE P s₀).2

theorem encArgs : VG.Proof.MlKem.AArch64.Kem.EncArgs P (VG.Proof.MlKem.AArch64.Encaps.enL P) 0 0 2 0 :=
  ⟨by decide, by enk, by simp [VG.Proof.MlKem.AArch64.Encaps.enL], by decide, by enk, by simp [VG.Proof.MlKem.AArch64.Encaps.enL], .inl (by enk)⟩

theorem ekT_eq (s₀ : State) : ∀ j < P.k,
    decode12 (bytesAt s₀.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ ((VG.Proof.MlKem.AArch64.Encaps.enL P).slot 0) + BitVec.ofNat 64 (0 + 384 * j)) 384) = ekT (VG.Proof.MlKem.AArch64.Encaps.ekE P s₀) j :=
  fun j hj => by
    rw [ekT, bytesAt_slice _ _ (show 384 * j + 384 ≤ P.ekLen by
      have := mul_succ_le (a := 384) hj; simp only [KemLay.ekLen]; omega),
      Nat.zero_add]
    rfl

/-- The key is apart from what the rest writes. -/
theorem key_far {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀) {r : Region}
    (h : r ∈ VG.Proof.MlKem.AArch64.Kem.bW P (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀ ∨ r ∈ VG.Proof.MlKem.AArch64.Kem.encW P (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀ 2 0) : Region.Disjoint ⟨VG.Proof.MlKem.AArch64.Kem.kA s₀ 2, 32⟩ r := by
  have hw := hp.wf
  have hs : ∀ {b o l : Nat}, b < 5 → b ≠ 2 → 2 ≤ b → o + l ≤ (VG.Proof.MlKem.AArch64.Encaps.enL P).len b →
      Region.Disjoint ⟨VG.Proof.MlKem.AArch64.Kem.kA s₀ 2, 32⟩ (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) b o l) := fun hb hb2 hw f =>
    (hp.args.disj 2 (by enk) _ hb (Ne.symm hb2) (.inl (by enk))).sub_right (R.sub f)
  have hb : Region.Disjoint ⟨VG.Proof.MlKem.AArch64.Kem.kA s₀ 2, 32⟩ (below s₀.sp 16) := by
    rw [below16]; exact (hp.args.stk 2 (by enk)).symm
  rcases h with h | h
  · rcases mem4 h with rfl | rfl | rfl | rfl
    · exact hs (b := 4) (by decide) (by decide) (by decide) (hp.fs (by lom))
    · exact hs (b := 4) (by decide) (by decide) (by decide) (hp.fs (by lom))
    · exact hs (b := 4) (by decide) (by decide) (by decide) (hp.fs (by lom))
    · exact hb
  · rcases mem5 h with rfl | rfl | rfl | rfl | rfl
    · exact hs (b := 4) (by decide) (by decide) (by decide) (hp.fs (by lom))
    · exact hs (b := 4) (by decide) (by decide) (by decide) (hp.fs (by lom))
    · exact hs (b := 4) (by decide) (by decide) (by decide) (hp.fs (by lom))
    · exact hb
    · exact hs (b := 3) (by decide) (by decide) (by decide) (by simp [VG.Proof.MlKem.AArch64.Encaps.enL])

theorem c_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Kem.Pre P (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀) (hc : VG.Proof.MlKem.AArch64.Kem.Calls P) {uA sB : State} (hA : VG.Proof.MlKem.AArch64.Encaps.AfterA P s₀ uA)
    (hB : VG.Proof.MlKem.AArch64.Kem.BInv P (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀ uA.mem (VG.Proof.MlKem.AArch64.Encaps.rhoE P s₀) (P.k * P.k) sB) :
    WP isa (P.enCWith keccak.callee) sB (VG.Proof.MlKem.AArch64.Encaps.Done P s₀ sB.mem (sB.gpr .x24)) := by
  have hw := hp.wf
  have fbw : ∀ {o l : Nat}, o + l ≤ SV P + 48 → (o + l ≤ SB + 32 ∨ SB + 34 ≤ o) → (o + l ≤ AH) →
      (o + l ≤ SS ∨ SS + 2048 ≤ o) → ∀ r ∈ VG.Proof.MlKem.AArch64.Kem.bW P (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀, (R (VG.Proof.MlKem.AArch64.Kem.kA s₀) (VG.Proof.MlKem.AArch64.Encaps.enL P).sc o l).Disjoint r :=
    fun f h1 h2 h3 r hr => by
      rcases mem4 hr with rfl | rfl | rfl | rfl
      · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp f (by lom) h1
      · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp f (by lom) (.inl h2)
      · exact VG.Proof.MlKem.AArch64.Kem.sdisj hp f (by lom) h3
      · exact VG.Proof.MlKem.AArch64.Kem.below_R hp hp.scb (hp.fs f)
  have r : bytesAt sB.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀ RB) 32 = (VG.Proof.MlKem.AArch64.Encaps.gE P s₀).2 := by
    rw [bytesAt_frame hB.fr (fbw (o := RB) (l := 32) (by lom) (by decide) (by decide) (by decide))
      (by decide)]
    exact hA.r
  have m : bytesAt sB.mem (VG.Proof.MlKem.AArch64.Kem.sA (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀ MB) 32 = VG.Proof.MlKem.AArch64.Encaps.mE s₀ := by
    rw [bytesAt_frame hB.fr (fbw (o := MB) (l := 32) (by lom) (by decide) (by decide) (by decide))
      (by decide)]
    exact hA.m
  have key : bytesAt sB.mem (VG.Proof.MlKem.AArch64.Kem.kA s₀ 2) 32 = (VG.Proof.MlKem.AArch64.Encaps.gE P s₀).1 := by
    rw [bytesAt_frame hB.fr (fun r hr => VG.Proof.MlKem.AArch64.Encaps.key_far hp (.inl hr)) (by decide)]; exact hA.key
  have e0 : VG.Proof.MlKem.AArch64.Kem.EInv P (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀ 2 0 sB.mem sB.mem (sB.gpr .x24) (VG.Proof.MlKem.AArch64.Encaps.gE P s₀).2 (VG.Proof.MlKem.AArch64.Encaps.mE s₀) 0 0 sB :=
    ⟨hB.kb, rfl, r, m, fun i hi j hj => ⟨hB.reduced hi hj, rfl⟩, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩
  refine WP.seq (WP.mono (VG.Proof.MlKem.AArch64.Kem.encrypt_ok hp hc VG.Proof.MlKem.AArch64.Encaps.encArgs (T := ekT (VG.Proof.MlKem.AArch64.Encaps.ekE P s₀)) (VG.Proof.MlKem.AArch64.Encaps.ekT_eq s₀) e0) fun s₁ ⟨e₁, v₁⟩ => ?_)
  refine WP.mono (VG.Proof.MlKem.AArch64.Kem.epilogue_ok hp e₁.kb) fun s' ⟨abi, x0, hm⟩ => ⟨abi, by rw [x0, e₁.x24], ?_, ?_⟩
  · rw [hm, bytesAt_frame e₁.fr (fun r hr => VG.Proof.MlKem.AArch64.Encaps.key_far hp (.inr hr)) (by decide)]; exact key
  · rw [hm]
    exact VG.Proof.MlKem.AArch64.Kem.ct_at (U := fun i => compressEncode P.du (KPke.encU P.params (VG.Proof.MlKem.AArch64.Kem.aM P (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀ sB.mem) (VG.Proof.MlKem.AArch64.Encaps.gE P s₀).2 i))
      (fun i hi => by have := e₁.u i hi; rwa [Nat.zero_add] at this) (by rwa [Nat.zero_add] at v₁)

/-! ## Correctness -/

theorem post_of {s₀ sB s' : State} {mA : Mem} (hB : VG.Proof.MlKem.AArch64.Kem.BInv P (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀ mA (VG.Proof.MlKem.AArch64.Encaps.rhoE P s₀) (P.k * P.k) sB)
    (hD : VG.Proof.MlKem.AArch64.Encaps.Done P s₀ sB.mem (sB.gpr .x24) s') : (VG.Proof.MlKem.encapsAArch64 P).post s₀ s' := by
  show Outcome (fun iters => encapsInternal P.params iters (bytesAt s₀.mem (s₀.gpr .x0) P.ekLen)
    (bytesAt s₀.mem (s₀.gpr .x1) 32)) ((s'.gpr .x0).setWidth 32)
    (bytesAt s'.mem (s₀.gpr .x2) 32, bytesAt s'.mem (s₀.gpr .x3) P.ctLen)
  have key : bytesAt s'.mem (s₀.gpr .x2) 32 = (VG.Proof.MlKem.AArch64.Encaps.gE P s₀).1 := hD.key
  have ct : bytesAt s'.mem (s₀.gpr .x3) P.ctLen =
      KPke.ct P.params (VG.Proof.MlKem.AArch64.Kem.aM P (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀ sB.mem) (VG.Proof.MlKem.AArch64.Encaps.ekE P s₀) (VG.Proof.MlKem.AArch64.Encaps.mE s₀) (VG.Proof.MlKem.AArch64.Encaps.gE P s₀).2 := hD.ct
  rw [key, ct, hD.x0]
  rcases hB.outcome with ⟨h1, hs⟩ | ⟨h0, i, hi, j, hj, hn⟩
  · rw [h1]
    refine .inl ⟨rfl, 280, ?_⟩
    show encapsInternal P.params 280 (VG.Proof.MlKem.AArch64.Encaps.ekE P s₀) (VG.Proof.MlKem.AArch64.Encaps.mE s₀) = _
    rw [KPke.encapsInternal_eq, KPke.kpkeEncrypt_some (p := P.params) ⟨rfl, rfl⟩ (a := VG.Proof.MlKem.AArch64.Kem.aM P (VG.Proof.MlKem.AArch64.Encaps.enL P) s₀ sB.mem)
      fun i hi j hj => hs i hi j hj]
    rfl
  · rw [h0]
    refine .inr ⟨rfl, ?_⟩
    show encapsInternal P.params 280 (VG.Proof.MlKem.AArch64.Encaps.ekE P s₀) (VG.Proof.MlKem.AArch64.Encaps.mE s₀) = none
    rw [KPke.encapsInternal_eq, KPke.kpkeEncrypt_none (p := P.params) hi hj hn]
    rfl

theorem correct (hP : P.Wf) (hc : VG.Proof.MlKem.AArch64.Kem.Calls P) {s₀ : State} (hs : (VG.Proof.MlKem.encapsAArch64 P).pre s₀) :
    WP isa (P.encapsWith keccak.callee) s₀ fun s' => abiPreserved s₀ s' ∧ (VG.Proof.MlKem.encapsAArch64 P).post s₀ s' := by
  have hp := VG.Proof.MlKem.AArch64.Encaps.pre_of hP hs
  exact WP.seq (WP.mono (VG.Proof.MlKem.AArch64.Encaps.a_ok hp) fun _ hA => WP.seq (WP.mono
    (VG.Proof.MlKem.AArch64.Kem.matrix_ok hp (BInv.zero hA.kb hA.x24 hA.rho)) fun _ hB =>
    WP.mono (VG.Proof.MlKem.AArch64.Encaps.c_ok hp hc hA hB) fun _ hD => ⟨hD.abi, VG.Proof.MlKem.AArch64.Encaps.post_of hB hD⟩))

/-! ## Constant time -/

/-- The taint analyses of `P`'s code, decided for each parameter set: the
code before and after the matrix (with the Keccak functions `keccak`), and
the arguments of each `sample_ntt`. -/
structure EnTaints (P : KemLay) (keccak : VG.Proof.Sha3.AArch64.Permutation) : Prop where
  a : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (P.enAWith keccak.callee) h).isSome = true
  c : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (P.enCWith keccak.callee) h).isSome = true
  setup : VG.Proof.MlKem.AArch64.Kem.SetupTaint P

/-- Two runs from states the contract relates. -/
abbrev Pub3 (P : KemLay) (σ₁ σ₂ : State) : Prop :=
  (VG.Proof.MlKem.encapsAArch64 P).pre σ₁ ∧ (VG.Proof.MlKem.encapsAArch64 P).pre σ₂ ∧ (VG.Proof.MlKem.encapsAArch64 P).pub σ₁ σ₂

theorem Pub3.two (hP : P.Wf) {σ₁ σ₂ : State} (h : VG.Proof.MlKem.AArch64.Encaps.Pub3 P σ₁ σ₂) : VG.Proof.MlKem.AArch64.Kem.Two P (VG.Proof.MlKem.AArch64.Encaps.enL P) σ₁ σ₂ :=
  ⟨VG.Proof.MlKem.AArch64.Encaps.pre_of hP h.1, VG.Proof.MlKem.AArch64.Encaps.pre_of hP h.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

theorem Pub3.rho {σ₁ σ₂ : State} (h : VG.Proof.MlKem.AArch64.Encaps.Pub3 P σ₁ σ₂) : VG.Proof.MlKem.AArch64.Encaps.rhoE P σ₁ = VG.Proof.MlKem.AArch64.Encaps.rhoE P σ₂ :=
  map_toNat_inj h.2.2.2.2.2.2.2.2

theorem b_rct (hP : P.Wf) (ht : VG.Proof.MlKem.AArch64.Encaps.EnTaints P keccak) :
    RelCT isa (fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, VG.Proof.MlKem.AArch64.Encaps.Pub3 P σ₁ σ₂ ∧ VG.Proof.MlKem.AArch64.Encaps.AfterA P σ₁ s₁ ∧ VG.Proof.MlKem.AArch64.Encaps.AfterA P σ₂ s₂)
      (P.kemMatrixWith keccak.callee)
    fun s₁ s₂ => ∃ σ₁ σ₂ m₁ m₂, VG.Proof.MlKem.AArch64.Encaps.Pub3 P σ₁ σ₂ ∧ VG.Proof.MlKem.AArch64.Kem.BInv P (VG.Proof.MlKem.AArch64.Encaps.enL P) σ₁ m₁ (VG.Proof.MlKem.AArch64.Encaps.rhoE P σ₁) (P.k * P.k) s₁ ∧
      VG.Proof.MlKem.AArch64.Kem.BInv P (VG.Proof.MlKem.AArch64.Encaps.enL P) σ₂ m₂ (VG.Proof.MlKem.AArch64.Encaps.rhoE P σ₁) (P.k * P.k) s₂ := by
  refine RelCT.mono (RelCT.exists_ (P := fun (x : State × State × Mem × Mem) s₁ s₂ =>
      VG.Proof.MlKem.AArch64.Encaps.Pub3 P x.1 x.2.1 ∧ VG.Proof.MlKem.AArch64.Kem.BInv P (VG.Proof.MlKem.AArch64.Encaps.enL P) x.1 x.2.2.1 (VG.Proof.MlKem.AArch64.Encaps.rhoE P x.1) 0 s₁ ∧
        VG.Proof.MlKem.AArch64.Kem.BInv P (VG.Proof.MlKem.AArch64.Encaps.enL P) x.2.1 x.2.2.2 (VG.Proof.MlKem.AArch64.Encaps.rhoE P x.1) 0 s₂)
      fun x => ?_)
    (fun s₁ s₂ ⟨_, σ₁, σ₂, hpub, a₁, a₂⟩ => ⟨(σ₁, σ₂, s₁.mem, s₂.mem), hpub, BInv.zero a₁.kb a₁.x24 a₁.rho,
      BInv.zero a₂.kb a₂.x24 (by rw [a₂.rho, hpub.rho])⟩) fun _ _ h => h
  by_cases hpub : VG.Proof.MlKem.AArch64.Encaps.Pub3 P x.1 x.2.1
  · exact RelCT.mono (VG.Proof.MlKem.AArch64.Kem.matrix_rct ht.setup (hpub.two hP)) (fun _ _ h => h.2)
      fun _ _ h => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2, hpub, h⟩
  · exact RelCT.of_false fun _ _ h => hpub h.1

theorem c_rct (hP : P.Wf) (ht : VG.Proof.MlKem.AArch64.Encaps.EnTaints P keccak) :
    RelCT isa (fun s₁ s₂ => ∃ σ₁ σ₂ m₁ m₂, VG.Proof.MlKem.AArch64.Encaps.Pub3 P σ₁ σ₂ ∧ VG.Proof.MlKem.AArch64.Kem.BInv P (VG.Proof.MlKem.AArch64.Encaps.enL P) σ₁ m₁ (VG.Proof.MlKem.AArch64.Encaps.rhoE P σ₁) (P.k * P.k) s₁ ∧
      VG.Proof.MlKem.AArch64.Kem.BInv P (VG.Proof.MlKem.AArch64.Encaps.enL P) σ₂ m₂ (VG.Proof.MlKem.AArch64.Encaps.rhoE P σ₁) (P.k * P.k) s₂) (P.enCWith keccak.callee) fun _ _ => True :=
  VectorTaint.relCT (Taint.ofRegs [.x25, .x26, .x27, .x28])
    (fun s₁ s₂ ⟨σ₁, σ₂, m₁, m₂, hpub, b₁, b₂⟩ =>
    agree_of (by rw [b₁.kb.sp, b₂.kb.sp, (hpub.two hP).sp]) fun r hr => by
      rcases mem4 hr with rfl | rfl | rfl | rfl
      · rw [b₁.kb.x25, b₂.kb.x25]; exact hpub.2.2.1
      · rw [b₁.kb.x26, b₂.kb.x26]; exact hpub.2.2.2.2.1
      · rw [b₁.kb.x27, b₂.kb.x27]; exact hpub.2.2.2.2.2.1
      · rw [b₁.kb.x28, b₂.kb.x28]; exact hpub.2.2.2.2.2.2.1) ht.c.choose_spec

theorem ct (hP : P.Wf) (ht : VG.Proof.MlKem.AArch64.Encaps.EnTaints P keccak) :
    ConstantTime isa (VG.Proof.MlKem.encapsAArch64 P).pre (VG.Proof.MlKem.encapsAArch64 P).pub (P.encapsWith keccak.callee) :=
  RelCT.constantTime (Q := fun _ _ => True) (RelCT.seq
    ((VectorTaint.relCT (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) (fun _ _ h =>
      agree_of h.2.2.2.2.2.2.2.1 (by
        obtain ⟨-, -, e0, e1, e2, e3, e4, -, -⟩ := h
        simp [e0, e1, e2, e3, e4])) ht.a.choose_spec).wpDep (F := fun σ s => VG.Proof.MlKem.AArch64.Encaps.AfterA P σ s)
      fun _ _ h => ⟨VG.Proof.MlKem.AArch64.Encaps.a_ok (VG.Proof.MlKem.AArch64.Encaps.pre_of hP h.1), VG.Proof.MlKem.AArch64.Encaps.a_ok (VG.Proof.MlKem.AArch64.Encaps.pre_of hP h.2.1)⟩)
    (RelCT.seq (VG.Proof.MlKem.AArch64.Encaps.b_rct hP ht) (VG.Proof.MlKem.AArch64.Encaps.c_rct hP ht)))

theorem encaps_correct (hP : P.Wf) (hc : VG.Proof.MlKem.AArch64.Kem.Calls P) {s : State} (hs : (VG.Proof.MlKem.encapsAArch64 P).pre s) :
    ∃ t s', Exec isa (P.encapsWith keccak.callee) s t s' ∧ abiPreserved s s' ∧ (VG.Proof.MlKem.encapsAArch64 P).post s s' :=
  VG.Proof.MlKem.AArch64.Encaps.correct hP hc hs

/-! ## ML-KEM-768 -/

theorem calls768 : VG.Proof.MlKem.AArch64.Kem.Calls lay768 :=
  ⟨fun h0 h1 h2 h3 hd => compressEncode_call h0 h1 h2 h3 (by rcases hd with rfl | rfl <;> decide),
    fun h0 h1 h2 h3 hd => decodeDecompress_call h0 h1 h2 h3 (by rcases hd with rfl | rfl <;> decide)⟩

theorem setupTaint768 : VG.Proof.MlKem.AArch64.Kem.SetupTaint lay768 := by
  intro i hi j hj
  change i < 3 at hi
  change j < 3 at hj
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;>
  exact ⟨_, by taint_decide⟩

theorem taints768 : VG.Proof.MlKem.AArch64.Encaps.EnTaints lay768 keccak := ⟨keccak.mlkemEnATaint, keccak.mlkemEnCTaint, VG.Proof.MlKem.AArch64.Encaps.setupTaint768⟩

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | .x4 => 0x10000 | _ => 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, 1184⟩, ⟨0x2000, 32⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 1088⟩, ⟨0x10000, 32768⟩]

theorem encaps_correctWith (s : State) (hs : (VG.Proof.MlKem.encapsAArch64 lay768).pre s) :
    ∃ t s', Exec isa (encapsWith keccak.callee) s t s' ∧ abiPreserved s s' ∧ (VG.Proof.MlKem.encapsAArch64 lay768).post s s' :=
  VG.Proof.MlKem.AArch64.Encaps.encaps_correct KeyGen.wf768 VG.Proof.MlKem.AArch64.Encaps.calls768 hs

theorem encaps_verifiedWith :
    Verified AArch64.target (encapsWith keccak.callee) (Spec.MlKem.encapsContract AArch64.abi 16) :=
  Verified.of_correct (VG.Proof.MlKem.AArch64.Encaps.encaps_correctWith (keccak := keccak)) (VG.Proof.MlKem.AArch64.Encaps.ct KeyGen.wf768 VG.Proof.MlKem.AArch64.Encaps.taints768) (by
    mlkem_implies [Spec.MlKem.encapsContract, Spec.MlKem.encapsSig, VG.Proof.MlKem.encapsAArch64, lay768, KemLay.params,
      Spec.MlKem.mlKem768, KemLay.ekLen, KemLay.ctLen, AArch64.abi, AArch64.argRegs] [sat] using VG.Proof.MlKem.AArch64.Encaps.sat)

theorem encaps_verified :
    Verified AArch64.target encaps (Spec.MlKem.encapsContract AArch64.abi 16) :=
  VG.Proof.MlKem.AArch64.Encaps.encaps_verifiedWith (keccak := .scalar)

end VG.Proof.MlKem.AArch64.Encaps

end
