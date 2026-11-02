module
public import VerifiedGarbage.Proof.Rsa.Arm.KeyArrs
public import VerifiedGarbage.Proof.Rsa.Arm.RvBase

import VerifiedGarbage.Proof.Rsa.Arm.RvViews
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # `vg_rsa_recover_primes` on ARMv7: a stage in the key working space

`KS P σ A live AW liveW V ls s`: `Bs`, `r8` the base of the working space,
`w` in the division's header, the arrays `live` read with `w` words holding
`A`, those `liveW` read with `W` words holding `AW`, and the header words
`ls` holding `V`. A step that writes some arrays and header words keeps the
others (`KS.core`, with `arrs_w`, `arrsW_w`, `arrs_W`, `arrsW_W` and
`sl_keep`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

/-- The header words of the stages: apart from `w` (byte 16). -/
abbrev SlotOk (d : Nat) : Prop := d + 4 ≤ hdr ∧ (d + 4 ≤ 16 ∨ 20 ≤ d) ∧ d % 4 = 0

structure KS (P : RP) (σ : State) (A : Nat → Nat) (live : List Nat) (AW : Nat → Nat) (liveW : List Nat)
    (V : Nat → Nat) (ls : List Nat) (s : State) : Prop where
  bs : Bs P σ s
  r8 : s.gpr .r8 = P.B
  cnt : s.mem.readW (off (State.addr P.B) 16) 32 = BitVec.ofNat 32 P.w
  arrs : Arrs s.mem P.B P.w A live
  arrsW : Arrs s.mem P.B P.W AW liveW
  sl : ∀ d ∈ ls, slot s.mem P.B d = V d
  live_lt : ∀ j ∈ live, j < nArr
  liveW_lt : ∀ j ∈ liveW, j < 22
  ls_ok : ∀ d ∈ ls, SlotOk d

theorem KS.sizes {P : RP} {σ : State} {A : Nat → Nat} {live : List Nat} {AW : Nat → Nat} {liveW : List Nat}
    {V : Nat → Nat} {ls : List Nat} {s : State} (h : KS P σ A live AW liveW V ls s) : Sizes P :=
  h.bs.pre.sizes

theorem arrW_end (P : RP) : arr P.W 22 = arr P.w nArr := by rw [RP.W, arr_W]; rfl

theorem fitZ_w {P : RP} (sz : Sizes P) {j : Nat} (hj : j < nArr) : arr P.w j + S P.w ≤ P.Z :=
  Nat.le_trans (arr_end hj) sz.fits

theorem fitZ_W {P : RP} (sz : Sizes P) {j : Nat} (hj : j < 22) : arr P.W j + S P.W ≤ P.Z := by
  have f : arr P.W 22 ≤ P.Z := by rw [arrW_end P]; exact sz.fits
  exact Nat.le_trans (arr_end hj) f

theorem Z_64 {P : RP} (sz : Sizes P) : P.Z ≤ 2 ^ 64 :=
  Nat.le_trans sz.zle (Nat.pow_le_pow_right (by decide) (by decide))

theorem fit_w {P : RP} (sz : Sizes P) {j : Nat} (hj : j < nArr) : arr P.w j + S P.w ≤ 2 ^ 64 :=
  Nat.le_trans (fitZ_w sz hj) (Z_64 sz)

theorem fit_W {P : RP} (sz : Sizes P) {j : Nat} (hj : j < 22) : arr P.W j + S P.W ≤ 2 ^ 64 :=
  Nat.le_trans (fitZ_W sz hj) (Z_64 sz)

theorem hdr_Z {P : RP} (sz : Sizes P) : hdr ≤ P.Z :=
  Nat.le_trans (Nat.le_add_right _ _) sz.fits

section
variable {P : RP} {σ s t : State} {A : Nat → Nat} {live : List Nat} {AW : Nat → Nat} {liveW : List Nat}
  {V : Nat → Nat} {ls : List Nat}

/-- Fewer arrays and header words, with values as other functions give them. -/
theorem KS.mono (h : KS P σ A live AW liveW V ls s) {A' : Nat → Nat} {live' : List Nat} {AW' : Nat → Nat}
    {liveW' : List Nat} {V' : Nat → Nat} {ls' : List Nat}
    (hl : ∀ j ∈ live', j ∈ live ∧ A j = A' j) (hlW : ∀ j ∈ liveW', j ∈ liveW ∧ AW j = AW' j)
    (hls : ∀ d ∈ ls', d ∈ ls ∧ V d = V' d) : KS P σ A' live' AW' liveW' V' ls' s :=
  ⟨h.bs, h.r8, h.cnt, fun j hj => (h.arrs j (hl j hj).1).trans (hl j hj).2,
    fun j hj => (h.arrsW j (hlW j hj).1).trans (hlW j hj).2, fun d hd => (h.sl d (hls d hd).1).trans (hls d hd).2,
    fun j hj => h.live_lt j (hl j hj).1, fun j hj => h.liveW_lt j (hlW j hj).1, fun d hd => h.ls_ok d (hls d hd).1⟩

/-- A step that changes registers but `r8`, and no memory. -/
theorem KS.of_rest (h : KS P σ A live AW liveW V ls s) {rs : List Reg} (r : Rest rs s t) (m : t.mem = s.mem)
    (h8 : .r8 ∉ rs) : KS P σ A live AW liveW V ls t :=
  ⟨h.bs.of_rest r m, by rw [r.gpr _ h8, h.r8], m ▸ h.cnt, m ▸ h.arrs, m ▸ h.arrsW, m ▸ h.sl, h.live_lt,
    h.liveW_lt, h.ls_ok⟩

/-- A step with `w` words that writes the arrays `js` and the header words `ds`. -/
theorem KS.core {js ds : List Nat} {v : Nat} (h : KS P σ A live AW liveW V ls s)
    (k : Keep P.B v js ds s.mem t.mem) (hjs : ∀ j ∈ js, arr v j + S v ≤ P.Z) (hds : ∀ d ∈ ds, SlotOk d)
    (r8 : t.gpr .r8 = P.B) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    {A' : Nat → Nat} {live' : List Nat} {AW' : Nat → Nat} {liveW' : List Nat} {V' : Nat → Nat}
    {ls' : List Nat} (ha : Arrs t.mem P.B P.w A' live') (hl : ∀ j ∈ live', j < nArr)
    (haW : Arrs t.mem P.B P.W AW' liveW') (hlW : ∀ j ∈ liveW', j < 22)
    (hsl : ∀ d ∈ ls', slot t.mem P.B d = V' d) (hls : ∀ d ∈ ls', SlotOk d) :
    KS P σ A' live' AW' liveW' V' ls' t := by
  have sz := h.sizes
  refine ⟨h.bs.of_frame (k.frameS hjs (fun d hd => (hds d hd).1) (hdr_Z sz)) sp rd wr, r8, ?_, ha, haW,
    hsl, hl, hlW, hls⟩
  refine (BitVec.eq_of_toNat_eq ?_).trans h.cnt
  exact k.slot (e := 16) (by decide) fun d hd => by have := (hds d hd).2.1; omega

/-- The arrays read with `w` that a step with `w` words does not write. -/
theorem KS.arrs_w {js ds : List Nat} (h : KS P σ A live AW liveW V ls s) (k : Keep P.B P.w js ds s.mem t.mem)
    (hl : ∀ j ∈ live, ∀ i ∈ js, i ≠ j) (hds : ∀ d ∈ ds, SlotOk d) : Arrs t.mem P.B P.w A live :=
  h.arrs.keepOf k hl (fun d hd => (hds d hd).1) fun j hj => fit_w h.sizes (h.live_lt j hj)

/-- The arrays read with `W` that a step with `w` words does not write. -/
theorem KS.arrsW_w {js ds : List Nat} (h : KS P σ A live AW liveW V ls s) (k : Keep P.B P.w js ds s.mem t.mem)
    (hl : ∀ j ∈ liveW, ∀ i ∈ js, i / 2 ≠ j) (hds : ∀ d ∈ ds, SlotOk d) : Arrs t.mem P.B P.W AW liveW :=
  h.arrsW.keepOf k.toW (fun j hj i hi => by
      simp only [List.mem_map] at hi
      obtain ⟨i', hi', rfl⟩ := hi
      exact hl j hj i' hi') (fun d hd => (hds d hd).1) fun j hj => fit_W h.sizes (h.liveW_lt j hj)

/-- The arrays read with `w` that a step with `W` words does not write. -/
theorem KS.arrs_W {js ds : List Nat} (h : KS P σ A live AW liveW V ls s) (k : Keep P.B P.W js ds s.mem t.mem)
    (hl : ∀ j ∈ live, ∀ i ∈ js, j / 2 ≠ i) (hds : ∀ d ∈ ds, SlotOk d) : Arrs t.mem P.B P.w A live :=
  h.arrs.keepOf k.ofW (fun j hj i hi => by
      simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hi
      obtain ⟨i', hi', e⟩ := hi
      have := hl j hj i' hi'
      rcases e with rfl | rfl <;> omega) (fun d hd => (hds d hd).1) fun j hj => fit_w h.sizes (h.live_lt j hj)

/-- The arrays read with `W` that a step with `W` words does not write. -/
theorem KS.arrsW_W {js ds : List Nat} (h : KS P σ A live AW liveW V ls s) (k : Keep P.B P.W js ds s.mem t.mem)
    (hl : ∀ j ∈ liveW, ∀ i ∈ js, i ≠ j) (hds : ∀ d ∈ ds, SlotOk d) : Arrs t.mem P.B P.W AW liveW :=
  h.arrsW.keepOf k hl (fun d hd => (hds d hd).1) fun j hj => fit_W h.sizes (h.liveW_lt j hj)

/-- The header words a step does not write. -/
theorem KS.sl_keep {js ds : List Nat} {v : Nat} (h : KS P σ A live AW liveW V ls s)
    (k : Keep P.B v js ds s.mem t.mem) (hl : ∀ d ∈ ls, ∀ e ∈ ds, d + 4 ≤ e ∨ e + 4 ≤ d) :
    ∀ d ∈ ls, slot t.mem P.B d = V d := fun d hd => by
  rw [k.slot (h.ls_ok d hd).1 (fun e he => hl d hd e he), h.sl d hd]

end

end VG.Proof.Rsa.Arm.Recover
