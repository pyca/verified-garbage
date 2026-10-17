module

public import VerifiedGarbage.Proof.Rsa.Arm.RvKM
public import VerifiedGarbage.Proof.Rsa.Arm.RvTaint2
public import VerifiedGarbage.Proof.Rsa.Arm.PrivSetupCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `vg_rsa_recover_primes` on ARMv7: tools for the stages

`VP.ctx`: a piece the taint analysis checks with the registers of the
working space's context public; `VP.stack`: a piece of loads and stores
relative to the stack. `KS.of_outZ`: memory past the working space changed
(frame word 0). `KR`: a stage but for `r8`, which steps of Montgomery
multiplication's working space keep (`KR.keep`, with `keepM`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

namespace VP
variable {F G : State → State → Prop}

/-- A piece the taint analysis checks with `r7`–`r9` public, at stages of
the working space's context. -/
theorem ctx {P : RP} {c : Prog isa} {v N : Nat}
    (cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs ctxRegs) c hc).isSome = true)
    (hws : ∀ σ s, F σ s → Ws s P.B P.Z v N) (wp : ∀ σ s, F σ s → WP isa c s (G σ)) : VP F c G :=
  VP.taint _ cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
    have w₁ := hws _ _ h₁; have w₂ := hws _ _ h₂
    simp only [ctxRegs, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · rw [w₁.r7, w₂.r7]
    · rw [w₁.r8, w₂.r8]
    · rw [w₁.r9, w₂.r9]) wp

/-- Loads, stores and arithmetic relative to the stack pointer. -/
theorem stack {code : List Instr} (keep : code.all (fun i => decide (dstOf i ≠ some .r12)) = true)
    (leak : code.all VG.Proof.Rsa.Arm.stackInstruction = true)
    (sp : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → s₁.sp = s₂.sp)
    (wp : ∀ σ s, F σ s → WP isa (.block (.addSp .r12 0 :: code)) s (G σ)) :
    VP F (.block (.addSp .r12 0 :: code)) G :=
  of_ct (fun _ _ => (VG.Proof.Rsa.Arm.setupChecked_ct code keep leak).mono
    (fun _ _ h => sp _ _ _ _ h.1 h.2) fun _ _ _ => trivial) wp

end VP

section
variable {P : RP} {σ s t : State} {A : Nat → Nat} {live : List Nat} {AW : Nat → Nat} {liveW : List Nat}
  {V : Nat → Nat} {ls : List Nat}

/-- A step that writes nothing in the working space. -/
theorem outZ_of_frame0 (hb : Bs P σ s) (f : Frame [P.r0F] s.mem t.mem) :
    Outs (State.addr P.B) [(P.Z, 2 ^ 64)] s.mem t.mem := by
  intro x hx
  have h := hx _ (List.mem_singleton_self _)
  have hz : ofs (State.addr P.B) x < P.Z := by
    have := (x - State.addr P.B).isLt; simp only [ofs] at h ⊢; omega
  refine f x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  have sF := hb.pre.sF
  refine sF x (by simp only [Region.Contains]; simp only [ofs] at hz; omega) ?_
  simp only [Region.Contains] at hc ⊢; omega

theorem KS.of_outZ (h : KS P σ A live AW liveW V ls s) (o : Outs (State.addr P.B) [(P.Z, 2 ^ 64)] s.mem t.mem)
    (hb : Bs P σ t) (r8 : t.gpr .r8 = P.B) : KS P σ A live AW liveW V ls t := by
  have sz := h.sizes
  have hz := hdr_Z sz
  have hZ := Z_64 sz
  have sl : ∀ d, d + 4 ≤ hdr → slot t.mem P.B d = slot s.mem P.B d := fun d hd => by
    have := Outs.val32 (k := 1) (d := d) o (fun r hr => by simp at hr; subst hr; left; omega) (by omega)
    simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  refine ⟨hb, r8, (BitVec.eq_of_toNat_eq (sl 16 (by decide))).trans h.cnt, fun j hj => ?_, fun j hj => ?_,
    fun d hd => (sl d (h.ls_ok d hd).1).trans (h.sl d hd), h.live_lt, h.liveW_lt, h.ls_ok⟩
  · have := fitZ_w sz (h.live_lt j hj)
    have : S P.w = 4 * (P.w + 2) := rfl
    rw [← h.arrs j hj]
    exact Outs.val32 o (fun r hr => by simp at hr; subst hr; left; omega) (by omega)
  · have := fitZ_W sz (h.liveW_lt j hj)
    have : S P.W = 4 * (P.W + 2) := rfl
    rw [← h.arrsW j hj]
    exact Outs.val32 o (fun r hr => by simp at hr; subst hr; left; omega) (by omega)

/-- A stage but for `r8`. -/
def KR (P : RP) (σ : State) (A : Nat → Nat) (live : List Nat) (AW : Nat → Nat) (liveW : List Nat)
    (V : Nat → Nat) (ls : List Nat) (s : State) : Prop :=
  ∃ u, KS P σ A live AW liveW V ls u ∧ u.mem = s.mem ∧ u.sp = s.sp ∧ u.rd = s.rd ∧ u.wr = s.wr

theorem KS.toR (h : KS P σ A live AW liveW V ls s) : KR P σ A live AW liveW V ls s :=
  ⟨s, h, rfl, rfl, rfl, rfl⟩

theorem KR.bs (h : KR P σ A live AW liveW V ls s) : Bs P σ s := by
  obtain ⟨u, hu, m, sp, rd, wr⟩ := h
  exact ⟨hu.bs.pre, sp ▸ hu.bs.sp, rd ▸ hu.bs.rd, wr ▸ hu.bs.wr, m ▸ hu.bs.frame⟩

theorem KR.toKS (h : KR P σ A live AW liveW V ls s) (r8 : s.gpr .r8 = P.B) : KS P σ A live AW liveW V ls s := by
  have hb := h.bs
  obtain ⟨u, hu, m, sp, rd, wr⟩ := h
  exact ⟨hb, r8, m ▸ hu.cnt, m ▸ hu.arrs, m ▸ hu.arrsW, m ▸ hu.sl, hu.live_lt, hu.liveW_lt, hu.ls_ok⟩

theorem KR.of_rest (h : KR P σ A live AW liveW V ls s) (m : t.mem = s.mem) (sp : t.sp = s.sp)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) : KR P σ A live AW liveW V ls t := by
  obtain ⟨u, hu, m', sp', rd', wr'⟩ := h
  exact ⟨u, hu, m'.trans m.symm, sp'.trans sp.symm, rd'.trans rd.symm, wr'.trans wr.symm⟩

/-- A step that writes the arrays `js` (with `w` words) and no header word. -/
theorem KR.keep {js : List Nat} (h : KR P σ A live AW liveW V ls s) (k : Keep P.B P.w js [] s.mem t.mem)
    (hjs : ∀ j ∈ js, j < nArr) (hl : ∀ j ∈ live, ∀ i ∈ js, i ≠ j) (hlW : ∀ j ∈ liveW, ∀ i ∈ js, i / 2 ≠ j)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : KR P σ A live AW liveW V ls t := by
  obtain ⟨u, hu, m, sp', rd', wr'⟩ := h
  let u' : State := { t with gpr := u.gpr }
  have k' : Keep P.B P.w js [] u.mem u'.mem := m ▸ k
  have sz := hu.sizes
  have hds : ∀ d ∈ ([] : List Nat), SlotOk d := by simp
  refine ⟨u', hu.core k' (fun j hj => fitZ_w sz (hjs j hj)) hds hu.r8 (sp.trans sp'.symm) (rd.trans rd'.symm)
    (wr.trans wr'.symm) (hu.arrs_w k' hl hds) hu.live_lt (hu.arrsW_w k' hlW hds) hu.liveW_lt
    (hu.sl_keep k' (by simp)) hu.ls_ok, rfl, rfl, rfl, rfl⟩

/-- The key arrays Montgomery multiplication's working space overlays. -/
abbrev mArrs : List Nat := [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- Memory that changed only within Montgomery multiplication's working space. -/
theorem keepM (sz : Sizes P) (hf : P.B.toNat + P.Z ≤ 2 ^ 32) {m m' : Mem} (f : Frame [P.rM] m m') :
    Keep P.B P.w mArrs [] m m' := by
  have hZ := Z_64 sz
  have endM := sz.endM
  have hdrM := sz.hdrM
  have fitM := Nat.le_trans (arr_mono (w := P.w) (show mBase + 8 ≤ nArr by decide)) sz.fits
  have hM : State.addr P.M0 = State.addr P.B + BitVec.ofNat 64 P.oM := M0_addr sz hf
  intro x hx
  refine f x fun r hr hc => ?_
  simp only [List.mem_singleton] at hr
  subst hr
  simp only [Region.Contains] at hc
  rw [hM] at hc
  have hin := (Offset.lt_iff x (State.addr P.B) (d := P.oM) (n := 8 * P.lenM)
    (by rw [endM]; exact Nat.le_trans fitM hZ)).mp hc
  -- The array the byte lies in.
  simp only [ofs] at hx
  have hS : 0 < S P.w := by simp only [S]; omega
  have e28 : arr P.w (mBase + 8) = hdr + 28 * S P.w := rfl
  have e16 : arr P.w 16 = hdr + 16 * S P.w := rfl
  generalize (x - State.addr P.B).toNat = o at hin hx
  have a16 : hdr + 16 * S P.w ≤ o := by rw [← e16]; exact Nat.le_trans hdrM hin.1
  have a28 : o < hdr + 28 * S P.w := by rw [← e28, ← endM]; exact hin.2
  clear hc hin e16 e28 endM hdrM fitM hM f hZ
  generalize hs : S P.w = S' at hS a16 a28
  have e := Nat.div_add_mod (o - hdr) S'
  have hm := Nat.mod_lt (o - hdr) hS
  have hj1 : 16 ≤ (o - hdr) / S' := (Nat.le_div_iff_mul_le hS).mpr (by clear hx; omega)
  have hj2 : (o - hdr) / S' < 28 := (Nat.div_lt_iff_lt_mul hS).mpr (by clear hx; omega)
  have hq : (o - hdr) / S' ∈ mArrs := by
    clear hx
    simp only [mArrs, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have := hx (arr P.w ((o - hdr) / S'), S P.w) (by
    simp only [ranges, List.map_nil, List.append_nil]; exact List.mem_map.mpr ⟨_, hq, rfl⟩)
  clear hx hq
  simp only [arr, hs] at this
  generalize (o - hdr) / S' = q at this e hj1 hj2
  have : S' * q = q * S' := Nat.mul_comm _ _
  omega

/-- Memory that changed only within the given ranges of Montgomery
multiplication's working space. -/
theorem frameM_of_outs {rs : List (Nat × Nat)} {m m' : Mem}
    (o : Outs (State.addr P.M0) rs m m') (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ 8 * P.lenM) : Frame [P.rM] m m' := by
  intro x hx
  have hc := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hc
  refine o x fun r hr => .inr ?_
  have := hrs r hr
  simp only [ofs]; omega

end

end VG.Proof.Rsa.Arm.Recover
