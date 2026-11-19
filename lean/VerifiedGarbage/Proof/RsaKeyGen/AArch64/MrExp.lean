module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrWin
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrBit
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSelW
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.CrtExp
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.AArch64.CrtTab

/-! ### `RsaKeyGen.AArch64.MrTab`, which the modules that import this one used -/

section

/-!
# A candidate on AArch64: Miller–Rabin's table

`tabBuild_ok`: from `b R mod c` in `aXm`, the table `T_j = b^j R mod c`
(`TabOK`), entry `j` the array `aT0 + j`, and `y := 1`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Proof.Rsa (slot_lt)
open VG.Impl.Bignum.Public (aN aAcc aTmp aXm aY sCnt)

/-- What the table changes. -/
def tabRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aT0, 128 * (w + 2)), (slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2)),
    (8 * kV, 8), (8 * kBits, 8)]

/-- `tabRanges`'s ranges, in the header and in the arrays. -/
theorem tabRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w [(208, 8), (240, 8)]
    [(11, 16), (2, 1), (3, 1), (6, 1)] (tabRanges w) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false,
    tabRanges, Public.sCnt, Public.aAcc, Public.aTmp, Public.aY, aAcc, aTmp, aY, aT0, kT0, sFn, sCnt, kV, kBits, kT2] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr ⟨(11, 16), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(2, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(3, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(6, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inl (by decide)
  · exact .inl (by decide)

theorem tabRanges_mut (w : Nat) : ∀ r ∈ tabRanges w, KMut r := by unfold tabRanges; w_mut

theorem tabRanges_hdr (w : Nat) {i : Nat} (hi : i = kV ∨ i = kBits) : (8 * i, 8) ∈ tabRanges w := by
  rcases hi with rfl | rfl <;> simp [tabRanges]

theorem tab_end (w : Nat) : slot w aT0 + 128 * (w + 2) = slot w aE := by
  unfold slot aT0 aE; omega_arith

/-- An entry is within the table. -/
theorem ent_in_tab (w : Nat) {e : Nat} (he : e < 16) :
    slot w aT0 ≤ slot w (aT0 + e) ∧ slot w (aT0 + e) + 8 * (w + 2) ≤ slot w aT0 + 128 * (w + 2) := by
  rw [tab_end]
  exact ⟨VG.Proof.Bignum.slot_mono w (by omega_arith), slot_lt (by unfold aT0 aE; omega_arith)⟩

/-- `MrCtx` survives changes within the table's ranges. -/
theorem MrCtx.of_tab {s t : State} {B : Addr} {Z w c bm : Nat} {rs : List (Nat × Nat)}
    (hc : MrCtx s B Z w c bm) (hf : Frm B rs s.mem t.mem) (hs : ∀ r ∈ rs, r ∈ tabRanges w)
    {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : MrCtx t B Z w c bm :=
  hc.of_frm (hf.mono hs) (tabRanges_mut w) k hr (by unfold tabRanges; w_disj) (by unfold tabRanges; w_disj)
    (by unfold tabRanges; w_disj) (by unfold tabRanges; w_disj) (by unfold tabRanges; w_disj)

/-- A store to a header slot keeps any array within the scratch space. -/
theorem hdrStore_wv' (m : Mem) (B : Addr) {w i j : Nat} (v : BitVec 64) (hi : i < 32)
    (hn : slot w j + 8 * w ≤ 2 ^ 64) :
    wv (m.writeW (off B (8 * i)) v) B (slot w j) w = wv m B (slot w j) w :=
  (writeW_outside m B v (by omega_arith)).wv (by have := hdr_lt_slot w j hi; omega_arith) hn

theorem powMod_succ' (b e c : Nat) :
    Spec.Rsa.powMod b (e + 1) c = Spec.Rsa.powMod b e c * Spec.Rsa.powMod b 1 c % c := by
  rw [VG.Proof.Bignum.powMod_eq, VG.Proof.Bignum.powMod_eq, VG.Proof.Bignum.powMod_eq, ← Nat.mul_mod, Nat.pow_succ,
    Nat.pow_one]

/-- `toEnt a`: `[a]` into the entry `e` whose base is in `kV`. -/
theorem toEnt_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    {a e : Nat} (ha : a < aT0) (he : e < 16) (hV : word s.mem B (8 * kV) = off B (slot w (aT0 + e))) :
    WP isa (seqs (toEnt a)) s fun t =>
      wv t.mem B (slot w (aT0 + e)) w = wv s.mem B (slot w a) w ∧
      Outside B (slot w (aT0 + e)) (8 * w) s.mem t.mem ∧ Keep [.x3, .x11, .x12, .x14, .x16, .x17] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  obtain hT := tab_fits hEZ he
  obtain hsep : slot w a + 8 * (w + 2) ≤ slot w (aT0 + e) := slot_lt (by omega_arith)
  obtain hA : slot w a + 8 * (w + 2) ≤ Z := by omega_arith
  simp only [toEnt, seqs]
  rw [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_))
  rw [WP.block_append_iff]
  refine WP.mono (base_ok a .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun s₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  obtain k12 := k₁.trans k₂
  refine WP.mono (WP.keep [.x17] (Q := fun t => t.gpr .x17 = off B (slot w (aT0 + e)) ∧ t.mem = s₂.mem) (by
    brun [(k12.gpr .x0 (by decide)).trans h.x0, hdr_enc (show kV < 32 by decide),
      (h.scr.congr k12.wr).ld (d := 8 * kV) (by simp only [kV, kT0, sCnt, sFn]; omega_arith),
      (by rw [m₂, m₁]; exact hV : word s₂.mem B (8 * kV) = off B (slot w (aT0 + e)))])
    (by decide) (by decide) (by decide +kernel)) fun s₃ ⟨⟨h17, m₃⟩, k₃⟩ => ?_
  obtain k13 := k12.trans k₃
  obtain hs₃ := h.scr.congr k13.wr
  refine WP.mono (copyWords_ok ((k₃.gpr .x16 (by decide)).trans h16) h17
    ((k₂.trans k₃ |>.gpr .x12 (by decide)).trans h12) (by have := h.w1; omega_arith) (by have := h.w2; omega_arith) (by omega_arith)
    (fun i hi => hs₃.ld (by omega_arith)) (fun i hi => hs₃.st (by omega_arith))
    (fun i hi b hb => by rw [ofs_off B (by omega_arith)]; omega_arith)) fun t ⟨hv, _, o', _, _, k₄⟩ => ?_
  rw [m₃, m₂, m₁] at hv o'
  exact ⟨hv, o', (k13.trans k₄).mono (by decide)⟩

/-- `nextEnt`: `kV` up a stride. -/
theorem nextEnt_ok {s : State} {B : Addr} {Z w X : Nat} (h : Ws s B Z w) (hV : word s.mem B (8 * kV) = off B X) :
    WP isa (.block nextEnt) s fun t =>
      t.mem = s.mem.writeW (off B (8 * kV)) (off B (X + 8 * (w + 2))) ∧ Keep [.x3, .x4] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  refine WP.keep [.x3, .x4] ?_ (by decide) (by decide) (by decide +kernel)
  brun [nextEnt, h.x0, hdr_enc (show kV < 32 by decide), hdr_enc (show sStride < 32 by decide),
    h.scr.ld (d := 8 * kV) (by simp only [kV, kT0, sCnt, sFn]; omega_arith),
    h.scr.ld (d := 8 * sStride) (by simp only [sStride, sFn]; omega_arith),
    h.scr.st (d := 8 * kV) (by simp only [kV, kT0, sCnt, sFn]; omega_arith), hV, h.hS, off_add]

/-- After `i` entries of the table's loop, from `s₀`: entries `0` to `i + 1`,
`y = T_(i+1)`, the entry `i + 2` in `kV`, `14 − i` in `kBits`. -/
structure TabI (B : Addr) (Z w : Nat) (c bm b : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  ctx : MrCtx s B Z w c bm
  ent : ∀ e < i + 2, wv s.mem B (slot w (aT0 + e)) w = Spec.Rsa.powMod b e c * 2 ^ (64 * w) % c
  y : wv s.mem B (slot w aY) w = Spec.Rsa.powMod b (i + 1) c * 2 ^ (64 * w) % c
  xm : wv s.mem B (slot w aXm) w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c
  v : word s.mem B (8 * kV) = off B (slot w (aT0 + (i + 2)))
  bits : word s.mem B (8 * kBits) = BitVec.ofNat 64 (14 - i)
  frm : Frm B (tabRanges w) s₀.mem s.mem
  keep : Keep mmRegs s₀ s

/-- The end of a loop step: the next entry, and `x3 := kBits := kBits − 1`. -/
theorem tabNext_ok {s : State} {B : Addr} {Z w X n : Nat} (h : Ws s B Z w) (hV : word s.mem B (8 * kV) = off B X)
    (hnb : word s.mem B (8 * kBits) = BitVec.ofNat 64 n) (hn1 : 1 ≤ n) (hn' : n < 2 ^ 64) :
    WP isa (.block (nextEnt ++ [ldh .x3 kBits, .subImm .x .x3 .x3 1, sth .x3 kBits])) s fun t =>
      (t.mem = (s.mem.writeW (off B (8 * kV)) (off B (X + 8 * (w + 2)))).writeW (off B (8 * kBits))
        (BitVec.ofNat 64 (n - 1)) ∧ t.gpr .x3 = BitVec.ofNat 64 (n - 1)) ∧ Keep [.x3, .x4] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  refine WP.keep [.x3, .x4] ?_ (by decide) (by decide) (by decide +kernel)
  brun [nextEnt, h.x0, hdr_enc (show kV < 32 by decide), hdr_enc (show sStride < 32 by decide),
    hdr_enc (show kBits < 32 by decide),
    h.scr.ld (d := 8 * kV) (by simp only [kV, kT0, sCnt, sFn]; omega_arith),
    h.scr.ld (d := 8 * sStride) (by simp only [sStride, sFn]; omega_arith),
    h.scr.ld (d := 8 * kBits) (by simp only [kBits, kT2, sFn]; omega_arith),
    h.scr.st (d := 8 * kV) (by simp only [kV, kT0, sCnt, sFn]; omega_arith),
    h.scr.st (d := 8 * kBits) (by simp only [kBits, kT2, sFn]; omega_arith), hV, h.hS, off_add,
    fun X => (hdrStore_hdr s.mem B X (show kV < 32 by decide) (show kBits < 32 by decide) (by decide)).trans hnb,
    ofNat64_pred hn1 hn']

/-- One entry of the table. -/
theorem tabStep_ok (M : Mont) {B : Addr} {Z w c bm b : Nat} {s₀ s : State} (hw128 : w ≤ 128)
    (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hodd : c % 2 = 1) (hc1 : 1 < c) {i : Nat} (hi : i < 14)
    (hI : TabI B Z w c bm b s₀ i s) :
    WP isa (seqs (([M.mm aY aY aXm] : List (Prog isa)) ++ toEnt aY ++
      ([.block (nextEnt ++ ([ldh .x3 kBits, .subImm .x .x3 .x3 1, sth .x3 kBits] : List Instr))] :
        List (Prog isa)))) s fun t =>
      TabI B Z w c bm b s₀ (i + 1) t ∧ ((t.gpr .x3).toNat ≠ 0 ↔ i + 1 ≠ 14) := by
  have hn := hI.ctx.ws.scr.nowrap
  have hw2 := hI.ctx.ws.w1
  obtain hw' : w < 2 ^ 31 := by omega_arith
  have hZ8 := hI.ctx.good.2
  obtain hR : Nat.Coprime (2 ^ (64 * w)) c := VG.Proof.Bignum.coprime_pow2 hodd _
  obtain hc0 : 0 < c := by omega_arith
  obtain hYl : slot w aY + 8 * (w + 2) ≤ slot w aT0 := slot_lt (show aY < aT0 by decide)
  obtain hXl : slot w aXm + 8 * (w + 2) ≤ slot w aT0 := slot_lt (show aXm < aT0 by decide)
  obtain hAl : slot w aAcc + 8 * (w + 2) ≤ slot w aT0 := slot_lt (show aAcc < aT0 by decide)
  obtain hTl : slot w aTmp + 8 * (w + 2) ≤ slot w aT0 := slot_lt (show aTmp < aT0 by decide)
  obtain hTE := VG.Proof.Bignum.slot_mono w (show aT0 ≤ aE by decide)
  rw [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [toEnt]) ?_
  simp only [seqs]
  -- `y := y T_1`.
  have hg := hI.ctx.good
  refine WP.mono (M.mm_ok hg.1 hg.2 hw2 hw' (o := aY) (a := aY) (b := aXm) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hI.ctx.inv
    (by rw [hI.xm, hI.ctx.n]; exact Nat.mod_lt _ hc0)) fun s₁ ⟨_, hlt₁, hy₁, ha₁, k₁⟩ => ?_
  rw [hI.ctx.n] at hlt₁ hy₁
  rw [hI.y, hI.xm] at hy₁
  obtain hY₁ : wv s₁.mem B (slot w aY) w = Spec.Rsa.powMod b (i + 2) c * 2 ^ (64 * w) % c := by
    rw [mont_val hR hlt₁ hy₁ rfl rfl, ← powMod_succ']
  obtain hf₁ : Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2))] s.mem s₁.mem :=
    Frm.of_arrays ha₁ (by simp)
  obtain hc₁ : MrCtx s₁ B Z w c bm := hI.ctx.of_tab hf₁ (by simp [tabRanges]) k₁ (by decide)
  obtain hlo : ∀ e < 16, wv s₁.mem B (slot w (aT0 + e)) w = wv s.mem B (slot w (aT0 + e)) w := fun e he => by
    have := ent_in_tab w he
    have := tab_fits hEZ he
    exact hf₁.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> right <;> simp only <;> omega_arith) (by omega_arith)
  obtain hV₁ : word s₁.mem B (8 * kV) = off B (slot w (aT0 + (i + 2))) := by
    rw [hf₁.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [kV, kT0, sCnt, sFn]; omega_arith)]; exact hI.v
  obtain hB₁ : word s₁.mem B (8 * kBits) = BitVec.ofNat 64 (14 - i) := by
    rw [hf₁.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [kBits, kT2, sFn]; omega_arith)]; exact hI.bits
  -- The entry.
  refine wp_seqs_append (by simp [toEnt]) (by simp) ?_
  refine WP.mono (toEnt_ok hc₁.ws hEZ (a := aY) (e := i + 2) (by decide) (by omega_arith) hV₁)
    fun s₂ ⟨hv₂, ho₂, k₂⟩ => ?_
  obtain hE := ent_in_tab w (e := i + 2) (by omega_arith)
  obtain hf₂ : Frm B [(slot w aT0, 128 * (w + 2))] s₁.mem s₂.mem :=
    Frm.of_outside (ho₂.mono (o' := slot w aT0) (n' := 128 * (w + 2)) hE.1 (by omega_arith)) (by simp)
  obtain hc₂ : MrCtx s₂ B Z w c bm := hc₁.of_tab hf₂ (by simp [tabRanges]) k₂ (by decide)
  obtain hV₂ : word s₂.mem B (8 * kV) = off B (slot w (aT0 + (i + 2))) := by
    rw [hf₂.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [kV, kT0, sCnt, sFn]; omega_arith)]; exact hV₁
  obtain hB₂ : word s₂.mem B (8 * kBits) = BitVec.ofNat 64 (14 - i) := by
    rw [hf₂.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [kBits, kT2, sFn]; omega_arith)]; exact hB₁
  -- `kV` and `kBits`.
  simp only [seqs]
  refine WP.mono (tabNext_ok hc₂.ws hV₂ hB₂ (by omega_arith) (by omega_arith)) fun t ⟨⟨hm, h3⟩, k⟩ => ⟨?_, ?_⟩
  · have hft : Frm B (tabRanges w) s₂.mem t.mem := by
      rw [hm]
      exact (Frm.of_outside (writeW_outside _ B _ (d := 8 * kV) (by decide))
        (tabRanges_hdr w (Or.inl rfl))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kBits)
          (by decide)) (tabRanges_hdr w (Or.inr rfl)))
    obtain hf1t : Frm B (tabRanges w) s.mem t.mem :=
      ((hf₁.mono (by simp [tabRanges])).trans (hf₂.mono (by simp [tabRanges]))).trans hft
    have hnw : B.toNat + Z ≤ 2 ^ 64 := hn
    -- The arrays through the header writes.
    obtain hwv : ∀ j < 28, wv t.mem B (slot w j) w = wv s₂.mem B (slot w j) w := fun j hj => by
      have := VG.Proof.Bignum.slot_mono w (show j ≤ aE by unfold aE; omega_arith)
      rw [hm, hdrStore_wv' _ _ _ (by decide) (by omega_arith), hdrStore_wv' _ _ _ (by decide) (by omega_arith)]
    -- What the copy keeps: the arrays other than entry `i + 2`.
    obtain hcp : ∀ j < 28, j ≠ aT0 + (i + 2) → wv s₂.mem B (slot w j) w = wv s₁.mem B (slot w j) w := fun j hj hne => by
      have := VG.Proof.Bignum.slot_mono w (show j ≤ aE by unfold aE; omega_arith)
      rcases slot_sep (w := w) hne with h | h
      · exact ho₂.wv (Or.inl (by omega_arith)) (by omega_arith)
      · exact ho₂.wv (Or.inr (by omega_arith)) (by omega_arith)
    refine ⟨hI.ctx.of_tab hf1t (fun _ h => h) ((k₁.trans k₂).trans k) (by decide), fun e he => ?_, ?_, ?_, ?_, ?_,
      hI.frm.trans hf1t, (((hI.keep.trans k₁).trans k₂).trans k).mono (by decide)⟩
    · rw [hwv (aT0 + e) (by unfold aT0; omega_arith)]
      by_cases hei : e = i + 2
      · subst hei; rw [hv₂, hY₁]
      · rw [hcp (aT0 + e) (by unfold aT0; omega_arith) (by omega_arith), hlo e (by omega_arith)]
        exact hI.ent e (by omega_arith)
    · rw [hwv aY (by decide), hcp aY (by decide) (by unfold aY aT0; omega_arith), hY₁]
    · rw [hwv aXm (by decide), hcp aXm (by decide) (by unfold aXm aT0; omega_arith),
        hf₁.wv_eq (d := slot w aXm) (k := w) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (by omega_arith)]
      exact hI.xm
    · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self, slot_succ,
        show aT0 + (i + 2) + 1 = aT0 + (i + 1 + 2) by omega_arith]
    · rw [hm, word_writeW_self, show 14 - i - 1 = 14 - (i + 1) by omega_arith]
  · rw [h3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith

/-- The table's start. -/
def tabHead : List (Prog isa) :=
  [.block (ws ++ base aT0 .x3 ++ [sth .x3 kV, movi .x3 14, sth .x3 kBits])] ++ (toEnt aR1 ++
    (([.block nextEnt] : List (Prog isa)) ++ (toEnt aXm ++ ([.block nextEnt, copyA aY aXm] : List (Prog isa)))))

theorem tabBuild_eq (mul : Nat → Nat → Nat → Prog isa) : tabBuild mul =
    tabHead ++ (([.loop (seqs (([mul aY aY aXm] : List (Prog isa)) ++ toEnt aY ++
      ([.block (nextEnt ++ ([ldh .x3 kBits, .subImm .x .x3 .x3 1, sth .x3 kBits] : List Instr))] :
        List (Prog isa)))) (.nonzero .x .x3)] : List (Prog isa)) ++ ([copyA aY aR1] : List (Prog isa))) := by
  simp only [tabBuild, tabHead, List.append_assoc, List.cons_append, List.nil_append]

/-- The table's first block: `kV := ` entry 0, `kBits := 14`. -/
theorem tabStart_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block (ws ++ base aT0 .x3 ++ [sth .x3 kV, movi .x3 14, sth .x3 kBits])) s fun t =>
      t.mem = (s.mem.writeW (off B (8 * kV)) (off B (slot w aT0))).writeW (off B (8 * kBits)) (BitVec.ofNat 64 14) ∧
      Keep [.x3, .x11, .x12] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨_, h11, m₁, _⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aT0 .x3 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun s₂ ⟨⟨h3, m₂, _⟩, k₂⟩ => ?_
  obtain k12 := k₁.trans k₂
  obtain hs₂ := h.scr.congr k12.wr
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = (s₂.mem.writeW (off B (8 * kV)) (off B (slot w aT0))).writeW
      (off B (8 * kBits)) (BitVec.ofNat 64 14)) (by
    brun [(k12.gpr .x0 (by decide)).trans h.x0, hdr_enc (show kV < 32 by decide), hdr_enc (show kBits < 32 by decide),
      hs₂.st (d := 8 * kV) (by simp only [kV, kT0, sCnt, sFn]; omega_arith),
      hs₂.st (d := 8 * kBits) (by simp only [kBits, kT2, sFn]; omega_arith), h3]
    rfl)
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ⟨by rw [hm, m₂, m₁], (k12.trans k).mono (by decide)⟩

/-- The table's start: `TabI` at the start of its loop. -/
theorem tabHead_ok {s : State} {B : Addr} {Z w c bm b : Nat} (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hc : MrCtx s B Z w c bm) (hc1 : 1 < c)
    (hX : wv s.mem B (slot w aXm) w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c) :
    WP isa (seqs tabHead) s fun t => TabI B Z w c bm b t 0 t ∧ Frm B (tabRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.ws.scr.nowrap
  have hw2 := hc.ws.w1
  have hZ8 := hc.good.2
  obtain hTE := VG.Proof.Bignum.slot_mono w (show aT0 ≤ aE by decide)
  obtain hYl : slot w aY + 8 * (w + 2) ≤ slot w aT0 := slot_lt (show aY < aT0 by decide)
  obtain hXl : slot w aXm + 8 * (w + 2) ≤ slot w aT0 := slot_lt (show aXm < aT0 by decide)
  obtain hRl : slot w aR1 + 8 * (w + 2) ≤ slot w aT0 := slot_lt (show aR1 < aT0 by decide)
  obtain e0 := ent_in_tab w (e := 0) (by decide)
  obtain e1 := ent_in_tab w (e := 1) (by decide)
  obtain hnw : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_arith
  unfold tabHead
  refine wp_seqs_append (by simp) (by simp [toEnt]) ?_
  simp only [seqs]
  refine WP.mono (tabStart_ok hc.ws) fun s₁ ⟨hm₁, k₁⟩ => ?_
  obtain hf₁ : Frm B (tabRanges w) s.mem s₁.mem := by
    rw [hm₁]
    exact (Frm.of_outside (writeW_outside _ B _ (d := 8 * kV) (by decide))
      (tabRanges_hdr w (Or.inl rfl))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kBits)
        (by decide)) (tabRanges_hdr w (Or.inr rfl)))
  obtain hc₁ := hc.of_tab hf₁ (fun _ h => h) k₁ (by decide)
  obtain hV₁ : word s₁.mem B (8 * kV) = off B (slot w (aT0 + 0)) := by
    rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]; rfl
  -- `T_0 := R mod c`.
  refine wp_seqs_append (by simp [toEnt]) (by simp) ?_
  refine WP.mono (toEnt_ok hc₁.ws hEZ (a := aR1) (e := 0) (by decide) (by decide) hV₁) fun s₂ ⟨hv₂, ho₂, k₂⟩ => ?_
  obtain hf₂ : Frm B [(slot w aT0, 128 * (w + 2))] s₁.mem s₂.mem :=
    Frm.of_outside (ho₂.mono (o' := slot w aT0) (n' := 128 * (w + 2)) e0.1 (by omega_arith)) (by simp)
  obtain hc₂ := hc₁.of_tab hf₂ (by simp [tabRanges]) k₂ (by decide)
  obtain hV₂ : word s₂.mem B (8 * kV) = off B (slot w aT0) := by
    rw [hf₂.word_eq (d := 8 * kV) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by decide)]; exact hV₁
  -- The next entry.
  refine wp_seqs_append (by simp) (by simp [toEnt]) ?_
  simp only [seqs]
  refine WP.mono (nextEnt_ok hc₂.ws hV₂) fun s₃ ⟨hm₃, k₃⟩ => ?_
  obtain hf₃ : Frm B [(8 * kV, 8)] s₂.mem s₃.mem := by
    rw [hm₃]; exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kV) (by decide)) (by simp)
  obtain hc₃ := hc₂.of_tab hf₃ (by simp [tabRanges]) k₃ (by decide)
  obtain hV₃ : word s₃.mem B (8 * kV) = off B (slot w (aT0 + 1)) := by
    rw [hm₃, word_writeW_self, slot_succ]
  -- `T_1 := b R mod c`.
  refine wp_seqs_append (by simp [toEnt]) (by simp) ?_
  refine WP.mono (toEnt_ok hc₃.ws hEZ (a := aXm) (e := 1) (by decide) (by decide) hV₃) fun s₄ ⟨hv₄, ho₄, k₄⟩ => ?_
  obtain hf₄ : Frm B [(slot w aT0, 128 * (w + 2))] s₃.mem s₄.mem :=
    Frm.of_outside (ho₄.mono (o' := slot w aT0) (n' := 128 * (w + 2)) e1.1 (by omega_arith)) (by simp)
  obtain hc₄ := hc₃.of_tab hf₄ (by simp [tabRanges]) k₄ (by decide)
  obtain hV₄ : word s₄.mem B (8 * kV) = off B (slot w (aT0 + 1)) := by
    rw [hf₄.word_eq (d := 8 * kV) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by decide)]; exact hV₃
  simp only [seqs]
  refine WP.seq (WP.mono (nextEnt_ok hc₄.ws hV₄) fun s₅ ⟨hm₅, k₅⟩ => ?_)
  obtain hf₅ : Frm B [(8 * kV, 8)] s₄.mem s₅.mem := by
    rw [hm₅]; exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kV) (by decide)) (by simp)
  obtain hc₅ := hc₄.of_tab hf₅ (by simp [tabRanges]) k₅ (by decide)
  -- `y := T_1`.
  refine WP.mono (copyA_ok hc₅.ws (o := aY) (a := aXm) (by decide) (by decide) (by decide))
    fun t ⟨hv, ho, _, _, k⟩ => ?_
  obtain hft : Frm B [(slot w aY, 8 * (w + 2))] s₅.mem t.mem :=
    Frm.of_outside (ho.mono (o' := slot w aY) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_arith)) (by simp)
  obtain hf : Frm B (tabRanges w) s.mem t.mem :=
    hf₁.trans ((((hf₂.mono (by simp [tabRanges])).trans (hf₃.mono (by simp [tabRanges]))).trans
      ((hf₄.mono (by simp [tabRanges])).trans (hf₅.mono (by simp [tabRanges])))).trans (hft.mono (by simp [tabRanges])))
  obtain k15 := (((k₁.trans k₂).trans k₃).trans k₄).trans k₅
  -- The values.
  obtain hX₄ : wv s₃.mem B (slot w aXm) w = wv s.mem B (slot w aXm) w := by
    rw [hf₃.wv_eq (by w_disj) (by omega_arith), hf₂.wv_eq (by w_disj) (by omega_arith),
      hf₁.wv_eq (by unfold tabRanges; w_disj) (by omega_arith)]
  obtain hte := tab_end w
  obtain h01 := slot_lt (w := w) (show aT0 + 0 < aT0 + 1 by decide)
  obtain hT0 : wv s₄.mem B (slot w (aT0 + 0)) w = wv s₂.mem B (slot w (aT0 + 0)) w := by
    rw [ho₄.wv (Or.inl (by omega_arith)) (by omega_arith), hf₃.wv_eq (by w_disj) (by omega_arith)]
  have hR1 : wv s₁.mem B (slot w aR1) w = 2 ^ (64 * w) % c := hc₁.r1
  -- Through the last copy and the last `kV` store.
  obtain hY5 : ∀ j, j < 28 → j ≠ aY → wv t.mem B (slot w j) w = wv s₄.mem B (slot w j) w := fun j hj hne => by
    have := VG.Proof.Bignum.slot_mono w (show j ≤ aE by unfold aE; omega_arith)
    rw [hft.wv_eq (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rcases slot_sep (w := w) hne with h | h
      · exact Or.inl (by simp only; omega_arith)
      · exact Or.inr (by simp only; omega_arith)) (by omega_arith),
      hf₅.wv_eq (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (by omega_arith)]
  obtain hY5w : ∀ i, i = kV ∨ i = kBits → word t.mem B (8 * i) = word s₅.mem B (8 * i) := fun i hi => by
    refine hft.word_eq ?_ (by rcases hi with rfl | rfl <;> decide)
    rcases hi with rfl | rfl <;> w_disj
  refine ⟨⟨hc₅.of_tab hft (by simp [tabRanges]) k (by decide), fun e he => ?_, ?_, ?_, ?_, ?_, Frm.refl _ _ _,
    Keep.refl _ _⟩, hf, (k15.trans k).mono (by decide)⟩
  · rcases (by omega_arith : e = 0 ∨ e = 1) with rfl | rfl
    · rw [hY5 _ (by decide) (by decide), hT0, hv₂, hR1, powMod_zero' hc1, Nat.one_mul]
    · rw [hY5 _ (by decide) (by decide), hv₄, hX₄, hX]
  · rw [hv, hf₅.wv_eq (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (by omega_arith), ho₄.wv (Or.inl (by omega_arith)) (by omega_arith), hX₄, hX]
  · rw [hY5 _ (by decide) (by decide), ho₄.wv (Or.inl (by omega_arith)) (by omega_arith), hX₄, hX]
  · rw [hY5w kV (Or.inl rfl), hm₅, word_writeW_self, slot_succ]
  · rw [hY5w kBits (Or.inr rfl), hm₅, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hf₄.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by decide), hm₃, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hf₂.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by decide), hm₁, word_writeW_self]

/-- The table, from `b R mod c` in `aXm`: `TabOK`, and `y := 1`. -/
theorem tabBuild_ok (M : Mont) {s : State} {B : Addr} {Z w c bm b : Nat} (hw128 : w ≤ 128)
    (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hc : MrCtx s B Z w c bm) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hX : wv s.mem B (slot w aXm) w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c) :
    WP isa (seqs (tabBuild M.mm)) s fun t =>
      MrCtx t B Z w c bm ∧ TabOK t.mem B w c b ∧ wv t.mem B (slot w aY) w = 2 ^ (64 * w) % c ∧
      Frm B (tabRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.ws.scr.nowrap
  obtain hYl : slot w aY + 8 * (w + 2) ≤ slot w aT0 := slot_lt (show aY < aT0 by decide)
  obtain hTE := VG.Proof.Bignum.slot_mono w (show aT0 ≤ aE by decide)
  rw [tabBuild_eq]
  refine wp_seqs_append (by simp [tabHead, toEnt]) (by simp) ?_
  refine WP.mono (tabHead_ok hEZ hc hc1 hX) fun s₄ ⟨hI0, hf₄, k₄⟩ => ?_
  refine wp_seqs_append (by simp) (by simp) ?_
  simp only [seqs]
  refine WP.mono (count_loop (cr := .x3) (n := 14) (by decide) (TabI B Z w c bm b s₄)
    (fun i hi t hI => tabStep_ok M hw128 hEZ hodd hc1 hi hI) hI0) fun s₅ hI => ?_
  -- `y := 1`.
  refine WP.mono (copyA_ok hI.ctx.ws (o := aY) (a := aR1) (by decide) (by decide) (by decide))
    fun t ⟨hv, ho, _, _, k⟩ => ?_
  obtain hft : Frm B [(slot w aY, 8 * (w + 2))] s₅.mem t.mem :=
    Frm.of_outside (ho.mono (o' := slot w aY) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_arith)) (by simp)
  obtain hf : Frm B (tabRanges w) s.mem t.mem := (hf₄.trans hI.frm).trans (hft.mono (by simp [tabRanges]))
  refine ⟨hI.ctx.of_tab hft (by simp [tabRanges]) k (by decide), fun j hj => ?_, by rw [hv, hI.ctx.r1], hf,
    ((k₄.trans hI.keep).trans k).mono (by decide)⟩
  have := ent_in_tab w hj
  rw [ho.wv (Or.inr (by omega_arith)) (by have := tab_fits hEZ hj; omega_arith)]
  exact hI.ent j (by omega_arith)

end VG.Proof.RsaKeyGen.AArch64

end

end

/-! ### `RsaKeyGen.AArch64.MrLoop`, which this module and modules that import it used -/

section

/-!
# A candidate on AArch64: Miller–Rabin's exponentiation loops

`WinInv`: after `t` windows of word `k − 1` of `E` (the words from the top),
`y R mod c` and the flag after the `16 (w − k) + t` windows from the top
(`wRun`), the word shifted left by `4 t` in `kV`. `mrWins_ok`: the inner
loop over the word's 16 windows; `mrWord_ok`: one word.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Impl.Bignum.Public (aN aAcc aTmp aXm aY sCnt)

/-- What the exponentiation changes. -/
def expRanges (w : Nat) : List (Nat × Nat) := winRanges w ++ [(8 * kWords, 8)]

/-- `expRanges`'s ranges, in the header and in the arrays. -/
theorem expRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w [(8, 8), (184, 8), (208, 8), (240, 8), (232, 8)]
    [(2, 1), (3, 1), (6, 1), (5, 1)] (expRanges w) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append,
    expRanges, winRanges, Public.sCnt, Public.aAcc, Public.aTmp, Public.aXm, Public.aY, aAcc, aTmp, aXm, aY, kT0, sFn, sCnt, kG, kV, kWords, kBits, kFlag, kPlen, kT1, kT2] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr ⟨(2, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(3, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(6, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(5, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inl (by decide)

theorem expRanges_low (w : Nat) : ∀ r ∈ expRanges w, r.1 + r.2 ≤ slot w aT0 := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact winRanges_low w r hr
  · simp only [List.mem_singleton] at hr; subst hr
    simp only [slot, hdrBytes, aT0, kWords, kT1, sFn]; omega_using []

theorem expRanges_mut (w : Nat) : ∀ r ∈ expRanges w, KMut r := by
  unfold expRanges winRanges; simp only [List.cons_append, List.nil_append]; w_mut

theorem sqRanges_sub (w : Nat) : ∀ r ∈ sqRanges w, r ∈ expRanges w := fun r hr =>
  List.mem_append_left _ (sqRanges_win w r hr)

theorem winRanges_sub (w : Nat) : ∀ r ∈ winRanges w, r ∈ expRanges w := fun _ hr => List.mem_append_left _ hr

theorem expRanges_hdr (w : Nat) {i : Nat} (hi : i = kWords ∨ i = kV ∨ i = kBits ∨ i = kFlag) :
    (8 * i, 8) ∈ expRanges w := by
  rcases hi with rfl | rfl | rfl | rfl <;> simp [expRanges, winRanges]

/-- `MrCtx` survives changes within the exponentiation's ranges. -/
theorem MrCtx.of_exp {s t : State} {B : Addr} {Z w c bm : Nat} {rs : List (Nat × Nat)}
    (hc : MrCtx s B Z w c bm) (hf : Frm B rs s.mem t.mem) (hs : ∀ r ∈ rs, r ∈ expRanges w)
    {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : MrCtx t B Z w c bm :=
  hc.of_frm (hf.mono hs) (expRanges_mut w) k hr
    (by simp only [expRanges, winRanges, List.cons_append, List.nil_append]; w_disj)
    (by simp only [expRanges, winRanges, List.cons_append, List.nil_append]; w_disj)
    (by simp only [expRanges, winRanges, List.cons_append, List.nil_append]; w_disj)
    (by simp only [expRanges, winRanges, List.cons_append, List.nil_append]; w_disj)
    (by simp only [expRanges, winRanges, List.cons_append, List.nil_append]; w_disj)

/-- After `t` windows of word `k − 1`, `W`, of `E`. -/
structure WinInv (B : Addr) (Z w : Nat) (c bm b k : Nat) (W : BitVec 64) (s₀ : State) (t : Nat)
    (s : State) : Prop where
  ctx : MrCtx s B Z w c bm
  tab : TabOK s.mem B w c b
  y : wv s.mem B (slot w aY) w = (wRun c b (mrE c) (16 * w) (16 * (w - k) + t)).1 * 2 ^ (64 * w) % c
  flag : word s.mem B (8 * kFlag) = mask (wRun c b (mrE c) (16 * w) (16 * (w - k) + t)).2
  v : word s.mem B (8 * kV) = W <<< (4 * t)
  bits : word s.mem B (8 * kBits) = BitVec.ofNat 64 (16 - t)
  words : word s.mem B (8 * kWords) = BitVec.ofNat 64 (k - 1)
  frm : Frm B (expRanges w) s₀.mem s.mem
  keep : Keep mmRegs s₀ s

/-- One window of word `k − 1`. -/
theorem mrWinStepW_ok {win : List (Prog isa)} (hwin : WinOK win) {B : Addr} {Z w c bm b k : Nat} {W : BitVec 64} {s₀ s : State}
    (hw128 : w ≤ 128) (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hodd : c % 2 = 1) (hc1 : 1 < c) (hk : 1 ≤ k)
    (hkw : k ≤ w) (hW : W.toNat = mrE c / 2 ^ (64 * (k - 1)) % 2 ^ 64) {j : Nat} (hj : j < 16)
    (hI : WinInv B Z w c bm b k W s₀ j s) :
    WP isa (seqs win) s fun t =>
      WinInv B Z w c bm b k W s₀ (j + 1) t ∧ ((t.gpr .x3).toNat ≠ 0 ↔ j + 1 ≠ 16) := by
  have hdig := win_digit hW hj
  refine WP.mono (hwin hw128 hEZ hI.ctx hI.tab hodd hc1 hI.y hI.flag hI.v hI.bits (by omega_arith)
    (by omega_arith)) fun t ⟨hct, htt, hyt, hft, hvt, hbt, h3, hfr, kt⟩ => ⟨?_, ?_⟩
  · have e : wRun c b (mrE c) (16 * w) (16 * (w - k) + (j + 1)) =
        wWin c b ((W <<< (4 * j)) >>> 60).toNat
          ((wRun c b (mrE c) (16 * w) (16 * (w - k) + j)).1, (wRun c b (mrE c) (16 * w) (16 * (w - k) + j)).2) := by
      rw [show 16 * (w - k) + (j + 1) = (16 * (w - k) + j) + 1 by omega_arith, wRun, hdig,
        show 16 * w - 1 - (16 * (w - k) + j) = 16 * (k - 1) + (15 - j) by omega_arith]
    refine ⟨hct, htt, by rw [e]; exact hyt, by rw [e]; exact hft, by rw [hvt, shl4_succ], ?_, ?_,
      hI.frm.trans (hfr.mono (winRanges_sub w)), (hI.keep.trans kt).mono (by decide)⟩
    · rw [hbt, show 16 - j - 1 = 16 - (j + 1) by omega_arith]
    · rw [hfr.word_eq (d := 8 * kWords) (by unfold winRanges; w_disj) (by decide)]
      exact hI.words
  · rw [h3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith

/-- The inner loop: the 16 windows of word `k − 1`. -/
theorem mrWinsW_ok {win : List (Prog isa)} (hwin : WinOK win) {B : Addr} {Z w c bm b k : Nat} {W : BitVec 64} {s₀ s : State}
    (hw128 : w ≤ 128) (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hodd : c % 2 = 1) (hc1 : 1 < c) (hk : 1 ≤ k)
    (hkw : k ≤ w) (hW : W.toNat = mrE c / 2 ^ (64 * (k - 1)) % 2 ^ 64) (h0 : WinInv B Z w c bm b k W s₀ 0 s) :
    WP isa (.loop (seqs win) (.nonzero .x .x3)) s (WinInv B Z w c bm b k W s₀ 16) :=
  count_loop (cr := .x3) (n := 16) (by decide) (WinInv B Z w c bm b k W s₀)
    (fun _ hj _ hI => mrWinStepW_ok hwin hw128 hEZ hodd hc1 hk hkw hW hj hI) h0

/-- One window of word `k − 1`, with the masked selection. -/
theorem mrWinStep_ok (M : Mont) {B : Addr} {Z w c bm b k : Nat} {W : BitVec 64} {s₀ s : State}
    (hw128 : w ≤ 128) (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hodd : c % 2 = 1) (hc1 : 1 < c) (hk : 1 ≤ k)
    (hkw : k ≤ w) (hW : W.toNat = mrE c / 2 ^ (64 * (k - 1)) % 2 ^ 64) {j : Nat} (hj : j < 16)
    (hI : WinInv B Z w c bm b k W s₀ j s) :
    WP isa (seqs (mrWin M.mm)) s fun t =>
      WinInv B Z w c bm b k W s₀ (j + 1) t ∧ ((t.gpr .x3).toNat ≠ 0 ↔ j + 1 ≠ 16) :=
  mrWinStepW_ok (mrWin_winOK M) hw128 hEZ hodd hc1 hk hkw hW hj hI

/-- The inner loop, with the masked selection. -/
theorem mrWins_ok (M : Mont) {B : Addr} {Z w c bm b k : Nat} {W : BitVec 64} {s₀ s : State}
    (hw128 : w ≤ 128) (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hodd : c % 2 = 1) (hc1 : 1 < c) (hk : 1 ≤ k)
    (hkw : k ≤ w) (hW : W.toNat = mrE c / 2 ^ (64 * (k - 1)) % 2 ^ 64) (h0 : WinInv B Z w c bm b k W s₀ 0 s) :
    WP isa (.loop (seqs (mrWin M.mm)) (.nonzero .x .x3)) s (WinInv B Z w c bm b k W s₀ 16) :=
  mrWinsW_ok (mrWin_winOK M) hw128 hEZ hodd hc1 hk hkw hW h0

/-- After `j` of the `w` words. -/
structure WordInv (B : Addr) (Z w : Nat) (c bm b : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  ctx : MrCtx s B Z w c bm
  tab : TabOK s.mem B w c b
  y : wv s.mem B (slot w aY) w = (wRun c b (mrE c) (16 * w) (16 * j)).1 * 2 ^ (64 * w) % c
  flag : word s.mem B (8 * kFlag) = mask (wRun c b (mrE c) (16 * w) (16 * j)).2
  words : word s.mem B (8 * kWords) = BitVec.ofNat 64 (w - j)
  frm : Frm B (expRanges w) s₀.mem s.mem
  keep : Keep mmRegs s₀ s

/-- The word `w − 1 − j` of `E`, as `WinInv` reads it. -/
abbrev wordE (m : Mem) (B : Addr) (w j : Nat) : BitVec 64 := word m B (slot w aE + 8 * (w - j - 1))

/-- The start of a word, after `ws` and `aE`'s base. -/
def wordHead : List Instr :=
  [ldh .x3 kWords, .subImm .x .x3 .x3 1, sth .x3 kWords, .lsl .x .x5 .x3 3, .add .x .x4 .x16 .x5, ld .x5 .x4,
    sth .x5 kV, movi .x6 16, sth .x6 kBits]

/-- The start of word `w − 1 − j`: `kWords := w − 1 − j`, the word into
`kV`, 16 into `kBits`. -/
theorem wordStart_ok {B : Addr} {Z w c bm b : Nat} {s₀ s : State} (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    {j : Nat} (hj : j < w) (hI : WordInv B Z w c bm b s₀ j s) :
    WP isa (.block (ws ++ base aE .x16 ++ wordHead)) s
      fun s₁ => WinInv B Z w c bm b (w - j) (wordE s.mem B w j) s₀ 0 s₁ := by
  have h := hI.ctx.ws
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  have hw2 := h.w2
  have hZ8 := hI.ctx.good.2
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aE .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun s₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.wr
  have hl : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off B (8 * i)) 8 := fun i hi => hs₂.ld (by omega_arith)
  have hst : ∀ i < 32, InRegions s₂.wr (off B (8 * i)) 8 := fun i hi => hs₂.st (by omega_arith)
  have hWd : word s₂.mem B (8 * kWords) = BitVec.ofNat 64 (w - j) := by rw [m₂, m₁]; exact hI.words
  have hEw : ∀ X, word (s₂.mem.writeW (off B (8 * kWords)) X) B (slot w aE + 8 * (w - j - 1)) = wordE s.mem B w j :=
    fun X => by
      rw [(writeW_outside _ B _ (d := 8 * kWords) (by decide)).word
        (Or.inr (by have := hdr_lt_slot w aE (show kWords < 32 by decide); omega_arith)) (by omega_arith), m₂, m₁]
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x6] (Q := fun t => t.mem = ((s₂.mem.writeW (off B (8 * kWords))
      (BitVec.ofNat 64 (w - j - 1))).writeW (off B (8 * kV)) (wordE s.mem B w j)).writeW (off B (8 * kBits))
      (BitVec.ofNat 64 16)) (by
    brun [wordHead, (k12.gpr .x0 (by decide)).trans h.x0, hdr_enc (show kWords < 32 by decide),
      hdr_enc (show kV < 32 by decide), hdr_enc (show kBits < 32 by decide), hl kWords (by decide),
      hst kWords (by decide), hst kV (by decide), hst kBits (by decide), hWd, h16,
      ofNat64_pred (show 1 ≤ w - j by omega_arith) (by omega_arith),
      ofNat_shl3 (show w - j - 1 < 2 ^ 60 by omega_arith), off_add,
      hs₂.ld (d := slot w aE + 8 * (w - j - 1)) (by omega_arith), hEw]
    rfl)
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
  have hf : Frm B (expRanges w) s.mem t.mem := by
    rw [hm, m₂, m₁]
    exact ((Frm.of_outside (writeW_outside _ B _ (d := 8 * kWords) (by decide))
      (expRanges_hdr w (Or.inl rfl))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kV)
        (by decide)) (expRanges_hdr w (Or.inr (Or.inl rfl))))).trans
      (Frm.of_outside (writeW_outside _ B _ (d := 8 * kBits) (by decide))
        (expRanges_hdr w (Or.inr (Or.inr (Or.inl rfl)))))
  have hnw : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_arith
  refine ⟨hI.ctx.of_exp hf (fun _ h => h) (k12.trans k) (by decide),
    hI.tab.of_low hf (expRanges_low w) hEZ hn, ?_, ?_, ?_, ?_, ?_, hI.frm.trans hf,
    (hI.keep.trans (k12.trans k)).mono (by decide)⟩
  · rw [hm, hdrStore_wv _ _ _ (by decide) (by decide) hnw, hdrStore_wv _ _ _ (by decide) (by decide) hnw,
      hdrStore_wv _ _ _ (by decide) (by decide) hnw, m₂, m₁, hI.y, show 16 * (w - (w - j)) + 0 = 16 * j by omega_arith]
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), m₂, m₁, hI.flag,
      show 16 * (w - (w - j)) + 0 = 16 * j by omega_arith]
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self, Nat.mul_zero,
      BitVec.shiftLeft_zero]
  · rw [hm, word_writeW_self]
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      word_writeW_self]

/-- The end of word `w − 1 − j`: `x3 := kWords`. -/
theorem wordEnd_ok {B : Addr} {Z w c bm b : Nat} {W : BitVec 64} {s₀ s : State} {j : Nat} (hj : j < w)
    (hB : WinInv B Z w c bm b (w - j) W s₀ 16 s) :
    WP isa (.block [ldh .x3 kWords]) s fun t =>
      WordInv B Z w c bm b s₀ (j + 1) t ∧ ((t.gpr .x3).toNat ≠ 0 ↔ j + 1 ≠ w) := by
  have h := hB.ctx.ws
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hw2 := h.w2
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 (w - j - 1) ∧ t.mem = s.mem) (by
    brun [h.x0, hdr_enc (show kWords < 32 by decide), h.scr.ld (d := 8 * kWords) (by simp only [kWords, kT1, sFn]; omega_using [h256]),
      hB.words]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h3, hm⟩, k⟩ => ⟨?_, ?_⟩
  · have e : 16 * (w - (w - j)) + 16 = 16 * (j + 1) := by omega_arith
    refine ⟨hB.ctx.of_exp (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide),
      by rw [hm]; exact hB.tab, ?_, ?_, ?_, by rw [hm]; exact hB.frm, (hB.keep.trans k).mono (by decide)⟩
    · rw [hm, hB.y, e]
    · rw [hm, hB.flag, e]
    · rw [hm, hB.words, show w - j - 1 = w - (j + 1) by omega_arith]
  · rw [h3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith

/-- One word of the exponentiation. -/
theorem mrWordW_ok {win : List (Prog isa)} (hwin : WinOK win) {B : Addr} {Z w c bm b : Nat} {s₀ s : State} (hw128 : w ≤ 128)
    (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hE : ECtx s.mem B w c) (hodd : c % 2 = 1) (hc1 : 1 < c) {j : Nat}
    (hj : j < w) (hI : WordInv B Z w c bm b s₀ j s) :
    WP isa (seqs [.block (ws ++ base aE .x16 ++ wordHead), .loop (seqs win) (.nonzero .x .x3),
      .block [ldh .x3 kWords]]) s fun t =>
      WordInv B Z w c bm b s₀ (j + 1) t ∧ ((t.gpr .x3).toNat ≠ 0 ↔ j + 1 ≠ w) := by
  have hW : (wordE s.mem B w j).toNat = mrE c / 2 ^ (64 * (w - j - 1)) % 2 ^ 64 := by
    rw [← hE.e]; exact word_of_wv s.mem B (slot w aE) w (by omega_arith)
  simp only [seqs]
  refine WP.seq (WP.mono (wordStart_ok hEZ hj hI) fun s₁ hB0 => ?_)
  exact WP.seq (WP.mono (mrWinsW_ok hwin hw128 hEZ hodd hc1 (by omega_arith) (by omega_arith)
    hW hB0) fun s₂ hB => wordEnd_ok hj hB)

/-- One word of the exponentiation, with the masked selection. -/
theorem mrWord_ok (M : Mont) {B : Addr} {Z w c bm b : Nat} {s₀ s : State} (hw128 : w ≤ 128)
    (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hE : ECtx s.mem B w c) (hodd : c % 2 = 1) (hc1 : 1 < c) {j : Nat}
    (hj : j < w) (hI : WordInv B Z w c bm b s₀ j s) :
    WP isa (seqs [.block (ws ++ base aE .x16 ++ wordHead), .loop (seqs (mrWin M.mm)) (.nonzero .x .x3),
      .block [ldh .x3 kWords]]) s fun t =>
      WordInv B Z w c bm b s₀ (j + 1) t ∧ ((t.gpr .x3).toNat ≠ 0 ↔ j + 1 ≠ w) :=
  mrWordW_ok (mrWin_winOK M) hw128 hEZ hE hodd hc1 hj hI

end VG.Proof.RsaKeyGen.AArch64

end

end

/-!
# A candidate on AArch64: Miller–Rabin's exponentiation

`mrExpLoop_ok`: from `y = 1` and the table of the witness `b`, the windows
of `E` from the top, then the three squarings of `wEnd`: the flag is
`wEnd`'s.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen
open VG.Proof.MlKem.AArch64 (Keep count_loop)
open VG.Impl.Bignum.Public (aN aAcc aTmp aXm aY sCnt)

theorem setWidth_zero_mask : BitVec.setWidth 64 (0#16) = mask false := rfl

/-- The start of the exponentiation: `kWords := w`, the flag clear. -/
theorem expStart_ok {B : Addr} {Z w c bm b : Nat} {s : State} (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hc : MrCtx s B Z w c bm) (hT : TabOK s.mem B w c b) (hY : wv s.mem B (slot w aY) w = 2 ^ (64 * w) % c) :
    WP isa (.block [ldh .x3 sW, sth .x3 kWords, movi .x3 0, sth .x3 kFlag]) s (WordInv B Z w c bm b s 0) := by
  have h := hc.ws
  have hZ8 := hc.good.2
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => h.scr.ld (by omega_arith)
  have hs : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8 := fun i hi => h.scr.st (by omega_arith)
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = (s.mem.writeW (off B (8 * kWords))
      (BitVec.ofNat 64 w)).writeW (off B (8 * kFlag)) (mask false)) (by
    brun [h.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show kWords < 32 by decide),
      hdr_enc (show kFlag < 32 by decide), hl sW (by decide), hs kWords (by decide), hs kFlag (by decide), h.hw,
      setWidth_zero_mask]) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨hm₁, k₁⟩ => ?_
  have hf₁ : Frm B (expRanges w) s.mem s₁.mem := by
    rw [hm₁]
    exact (Frm.of_outside (writeW_outside _ B _ (d := 8 * kWords) (by decide))
      (expRanges_hdr w (Or.inl rfl))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kFlag)
        (by decide)) (expRanges_hdr w (Or.inr (Or.inr (Or.inr rfl)))))
  have hnw : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_arith
  refine ⟨hc.of_exp hf₁ (fun _ h => h) k₁ (by decide), hT.of_low hf₁ (expRanges_low w) hEZ hn, ?_, ?_, ?_, hf₁,
    k₁.mono (by decide)⟩
  · rw [hm₁, hdrStore_wv _ _ _ (by decide) (by decide) hnw, hdrStore_wv _ _ _ (by decide) (by decide) hnw,
      hY, Nat.mul_zero]
    simp only [wRun, Nat.one_mul]
  · rw [hm₁, word_writeW_self, Nat.mul_zero]; rfl
  · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self, Nat.sub_zero]

/-- `mrLast j` as a squaring of `wEnd`. -/
theorem mrLast_wsq (M : Mont) {s : State} {B : Addr} {Z w c bm : Nat} {st : Nat × Bool} (hw128 : w ≤ 128)
    (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hc : MrCtx s B Z w c bm) (hE : ECtx s.mem B w c) (hodd : c % 2 = 1)
    (hc1 : 1 < c) (hY : wv s.mem B (slot w aY) w = st.1 * 2 ^ (64 * w) % c)
    (hP : word s.mem B (8 * kFlag) = mask st.2) {j : Nat} (hj : 1 ≤ j ∧ j ≤ 3) :
    WP isa (seqs (mrLast M.mm j)) s fun t =>
      MrCtx t B Z w c bm ∧ ECtx t.mem B w c ∧
      wv t.mem B (slot w aY) w = (wSq c (decide (j < mrSig c)) st).1 * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kFlag) = mask (wSq c (decide (j < mrSig c)) st).2 ∧
      Frm B (sqRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.ws.scr.nowrap
  refine WP.mono (mrLast_ok M hw128 hEZ hc hE hodd hc1 hY hP hj) fun t ⟨hct, hyt, hft, hfr, kt⟩ =>
    ⟨hct, hE.of_low hfr (fun r hr => winRanges_low w r (sqRanges_win w r hr)) hEZ hn,
      hyt, by rw [hft, Bool.and_comm]; rfl, hfr, kt⟩

theorem mrExpLoopW_eq (win : List (Prog isa)) (mul : Nat → Nat → Nat → Prog isa) : mrExpLoopW win mul =
    ([.block [ldh .x3 sW, sth .x3 kWords, movi .x3 0, sth .x3 kFlag],
      .loop (seqs [.block (ws ++ base aE .x16 ++ wordHead), .loop (seqs win) (.nonzero .x .x3),
        .block [ldh .x3 kWords]]) (.nonzero .x .x3)] : List (Prog isa)) ++
    (mrLast mul 1 ++ (mrLast mul 2 ++ mrLast mul 3)) := by
  simp only [mrExpLoopW, wordHead, List.append_assoc]

theorem mrExpLoop_eq (mul : Nat → Nat → Nat → Prog isa) : mrExpLoop mul =
    ([.block [ldh .x3 sW, sth .x3 kWords, movi .x3 0, sth .x3 kFlag],
      .loop (seqs [.block (ws ++ base aE .x16 ++ wordHead), .loop (seqs (mrWin mul)) (.nonzero .x .x3),
        .block [ldh .x3 kWords]]) (.nonzero .x .x3)] : List (Prog isa)) ++
    (mrLast mul 1 ++ (mrLast mul 2 ++ mrLast mul 3)) := mrExpLoopW_eq (mrWin mul) mul

/-- The exponentiation: from `y = 1` (`R mod c` in `aY`) and the table, the
flag of `wEnd` over the windows of `E`. -/
theorem mrExpLoopW_ok {win : List (Prog isa)} (M : Mont) (hwin : WinOK win) {B : Addr} {Z w c bm b : Nat} {s : State} (hw128 : w ≤ 128)
    (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hc : MrCtx s B Z w c bm) (hT : TabOK s.mem B w c b)
    (hE : ECtx s.mem B w c) (hodd : c % 2 = 1) (hc1 : 1 < c) (hY : wv s.mem B (slot w aY) w = 2 ^ (64 * w) % c) :
    WP isa (seqs (mrExpLoopW win M.mm)) s fun t => MrCtx t B Z w c bm ∧ ECtx t.mem B w c ∧
      word t.mem B (8 * kFlag) = mask (wEnd c (wRun c b (mrE c) (16 * w) (16 * w))).2 ∧
      Frm B (expRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.ws.scr.nowrap
  have hw2 := hc.ws.w1
  rw [mrExpLoopW_eq]
  refine wp_seqs_append (by simp) (by simp [mrLast]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (expStart_ok hEZ hc hT hY) fun s₁ hI0 => ?_)
  refine WP.mono (count_loop (cr := .x3) (n := w) (by omega_arith) (WordInv B Z w c bm b s)
    (fun j hj t hI => mrWordW_ok hwin hw128 hEZ (hE.of_low hI.frm (expRanges_low w) hEZ hn) hodd hc1 hj hI) hI0)
    fun s₂ hI => ?_
  have hE₂ : ECtx s₂.mem B w c := hE.of_low hI.frm (expRanges_low w) hEZ hn
  generalize hst : wRun c b (mrE c) (16 * w) (16 * w) = st
  have hY₂ : wv s₂.mem B (slot w aY) w = st.1 * 2 ^ (64 * w) % c := by rw [← hst]; exact hI.y
  have hP₂ : word s₂.mem B (8 * kFlag) = mask st.2 := by rw [← hst]; exact hI.flag
  refine wp_seqs_append (by simp [mrLast]) (by simp [mrLast]) (WP.mono (mrLast_wsq M hw128 hEZ hI.ctx hE₂ hodd hc1
    hY₂ hP₂ (j := 1) (by decide)) fun s₃ ⟨hc₃, hE₃, hY₃, hP₃, hf₃, k₃⟩ => ?_)
  refine wp_seqs_append (by simp [mrLast]) (by simp [mrLast]) (WP.mono (mrLast_wsq M hw128 hEZ hc₃ hE₃ hodd hc1
    hY₃ hP₃ (j := 2) (by decide)) fun s₄ ⟨hc₄, hE₄, hY₄, hP₄, hf₄, k₄⟩ => ?_)
  refine WP.mono (mrLast_wsq M hw128 hEZ hc₄ hE₄ hodd hc1 hY₄ hP₄ (j := 3) (by decide))
    fun t ⟨hct, hEt, _, hPt, hft, kt⟩ => ⟨hct, hEt, hPt, ?_, ?_⟩
  · exact ((hI.frm.trans (hf₃.mono (sqRanges_sub w))).trans (hf₄.mono (sqRanges_sub w))).trans
      (hft.mono (sqRanges_sub w))
  · exact (((hI.keep.trans k₃).trans k₄).trans kt).mono (by decide)

/-- The exponentiation: from `y = 1` (`R mod c` in `aY`) and the table, the
flag of `wEnd` over the windows of `E`. -/
theorem mrExpLoop_ok (M : Mont) {B : Addr} {Z w c bm b : Nat} {s : State} (hw128 : w ≤ 128)
    (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hc : MrCtx s B Z w c bm) (hT : TabOK s.mem B w c b)
    (hE : ECtx s.mem B w c) (hodd : c % 2 = 1) (hc1 : 1 < c) (hY : wv s.mem B (slot w aY) w = 2 ^ (64 * w) % c) :
    WP isa (seqs (mrExpLoop M.mm)) s fun t => MrCtx t B Z w c bm ∧ ECtx t.mem B w c ∧
      word t.mem B (8 * kFlag) = mask (wEnd c (wRun c b (mrE c) (16 * w) (16 * w))).2 ∧
      Frm B (expRanges w) s.mem t.mem ∧ Keep mmRegs s t :=
  mrExpLoopW_ok M (mrWin_winOK M) hw128 hEZ hc hT hE hodd hc1 hY

end VG.Proof.RsaKeyGen.AArch64
