module

import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWin
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.RsaKeyGen.Gcd

/-! ### `RsaKeyGen.X86_64.MrTab`, which the modules that import this one used -/

section

/-!
# A candidate on x86-64: Miller–Rabin's table

`tabBuild_ok`: from `b R mod c` in `aXm`, the table `T_j = b^j R mod c`
(`TabOK`) and `y := 1`: `T_1` and `y` from `aXm`, `T_0` from `R mod c`,
then `y := y T_1` into each entry from 2 to 15 (`TabStep`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 VG.Proof.RsaKeyGen

/-- What the table changes. -/
def tabRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w 8, tabBytes w), (slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2)),
    (8 * kV, 8), (8 * kBits, 8)]

/-- `tabRanges`'s ranges, in the header and in the arrays. -/
theorem tabRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w [(208, 8), (224, 8)]
    [(8, 16), (2, 1), (3, 1), (6, 1)] (tabRanges w) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false,
    tabRanges, Public.aAcc, Public.aTmp, Public.aY, aAcc, aTmp, aY, VG.Proof.Bignum.tabBytes, kT0, sFn, kV, kBits, kT2] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr ⟨(8, 16), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(2, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(3, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(6, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inl (by decide)
  · exact .inl (by decide)

theorem powMod_succ' (b e c : Nat) :
    Spec.Rsa.powMod b (e + 1) c = Spec.Rsa.powMod b e c * Spec.Rsa.powMod b 1 c % c := by
  rw [VG.Proof.Bignum.powMod_eq, VG.Proof.Bignum.powMod_eq, VG.Proof.Bignum.powMod_eq, ← Nat.mul_mod, Nat.pow_succ,
    Nat.pow_one]

theorem tab_end (w : Nat) : slot w 8 + tabBytes w = slot w aE := by
  rw [show aE = 8 + 16 from rfl, slot_add_mul]; rfl

theorem tabRanges_lt (w : Nat) : ∀ r ∈ tabRanges w, r.1 + r.2 ≤ slot w aE := by
  obtain h0 := tab_end w
  obtain h8 := slot_mono w (show 8 ≤ aE by decide)
  obtain h1 := slot_le (w := w) (show aAcc < 8 by decide)
  obtain h2 := slot_le (w := w) (show aTmp < 8 by decide)
  obtain h3 := slot_le (w := w) (show aY < 8 by decide)
  obtain h4 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  simp only [tabRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [kV, kT0, kBits, kT2, sFn] at * <;> omega_arith

/-- `MrCtx` with a new witness in `aB`, after changes to the table and the
working arrays. -/
theorem MrCtx.of_tab {s t : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm bm' : Nat}
    (hc : MrCtx s B Z w mi c bm) (hd : MrDims B Z w) (hf : Frm B (tabRanges w) s.mem t.mem) (hs : Scr t B Z)
    (hdi : t.gpr .rdi = B) (hb : wv t.mem B (slot w aB) w = bm') : MrCtx t B Z w mi c bm' := by
  have hn := hc.good.scr.nowrap
  have hx := hd.x
  obtain hE1 := slot_mono w (show aE ≤ aR1 by decide)
  obtain h1 := slot_succ w aR1
  obtain hRm := slot_mono w (show aE ≤ aRm1 by decide)
  obtain hN := slot_le (w := w) (show aN < 8 by decide)
  obtain h8R := slot_mono w (show 8 ≤ aRm1 by decide)
  obtain h1R := slot_mono w (show aR1 ≤ aRm1 by decide)
  obtain hdN : ∀ r ∈ tabRanges w, slot w aN + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aN := by
    simp only [tabRanges]; rng_disj
  obtain hlt := tabRanges_lt w
  refine ⟨⟨hs, hdi, Hdr.of_frm hc.good.hdr hf (by simp only [tabRanges]; rng_le)⟩, ?_, ?_, hb, ?_, ?_⟩
  · rw [hf.word_eq (d := slot w aN) (fun r hr => by have := hdN r hr; have := hd.w4; omega_arith) (by omega_arith)]; exact hc.inv
  · rw [hf.wv_eq hdN (by omega_arith)]; exact hc.n
  · rw [hf.wv_eq (d := slot w aR1) (fun r hr => Or.inr (by have := hlt r hr; omega_arith)) (by omega_arith)]
    exact hc.r1
  · rw [hf.wv_eq (d := slot w aRm1) (fun r hr => Or.inr (by have := hlt r hr; omega_arith)) (by omega_arith)]
    exact hc.rm1

/-- After `i` entries of the table's loop, from `s₀`: entries `0` to `i + 1`,
`y = T_(i+1)`, the entry `i + 2` in `kV`, `14 − i` in `kBits`. -/
structure TabI (B : Addr) (Z w : Nat) (mi : BitVec 64) (c bm b : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  ctx : MrCtx s B Z w mi c bm
  ent : ∀ e < i + 2, wv s.mem B (slot w (8 + e)) w = Spec.Rsa.powMod b e c * 2 ^ (64 * w) % c
  y : wv s.mem B (slot w aY) w = Spec.Rsa.powMod b (i + 1) c * 2 ^ (64 * w) % c
  xm : wv s.mem B (slot w aXm) w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c
  v : word s.mem B (8 * kV) = off B (slot w (8 + (i + 2)))
  bits : word s.mem B (8 * kBits) = BitVec.ofNat 64 (14 - i)
  frm : Frm B (tabRanges w) s₀.mem s.mem
  keep : Keep mmRegs s₀ s

theorem tabStep_eq (mul : Nat → Nat → Nat → Prog isa) : seqs [mul aY aY aXm,
    .block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aY))), .mov .rbx (.mem (hdr kV))], copyWords,
    .block [.mov .rax (.mem (hdr kV)), .mov .rdx (.mem (hdr sW)), .alu .add .rdx (.imm 2), .alu .add .rdx (.reg .rdx),
      .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rax (.reg .rdx), .store (hdr kV) .rax,
      .mov .rax (.mem (hdr kBits)), .alu .sub .rax (.imm 1), .store (hdr kBits) .rax]] =
    .seq (mul aY aY aXm) (.seq (.block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aY))),
      .mov .rbx (.mem (hdr kV))]) (.seq copyWords (.block [.mov .rax (.mem (hdr kV)), .mov .rdx (.mem (hdr sW)),
      .alu .add .rdx (.imm 2), .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx),
      .alu .add .rax (.reg .rdx), .store (hdr kV) .rax, .mov .rax (.mem (hdr kBits)), .alu .sub .rax (.imm 1),
      .store (hdr kBits) .rax]))) := rfl

theorem tabRanges_hdr (w : Nat) {i : Nat} (hi : i = kV ∨ i = kBits) : (8 * i, 8) ∈ tabRanges w := by
  rcases hi with rfl | rfl <;> simp [tabRanges]

theorem ent_in_tab (w : Nat) {e : Nat} (he : e < 16) :
    slot w 8 ≤ slot w (8 + e) ∧ slot w (8 + e) + 8 * (w + 2) ≤ slot w 8 + tabBytes w :=
  ⟨slot_mono w (by omega_arith), ent_le w he⟩

/-- One entry of the table. -/
theorem tabStep_ok (M : Mont) {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm b : Nat} {s₀ s : State}
    (hd : MrDims B Z w) (hodd : c % 2 = 1) (hc1 : 1 < c) {i : Nat} (hi : i < 14)
    (hI : TabI B Z w mi c bm b s₀ i s) :
    WP isa (seqs [M.mm aY aY aXm,
      .block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aY))), .mov .rbx (.mem (hdr kV))], copyWords,
      .block [.mov .rax (.mem (hdr kV)), .mov .rdx (.mem (hdr sW)), .alu .add .rdx (.imm 2), .alu .add .rdx (.reg .rdx),
        .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rax (.reg .rdx), .store (hdr kV) .rax,
        .mov .rax (.mem (hdr kBits)), .alu .sub .rax (.imm 1), .store (hdr kBits) .rax]]) s fun t =>
      t.zf = some (decide (i + 1 = 14)) ∧ TabI B Z w mi c bm b s₀ (i + 1) t := by
  have hg := hI.ctx.good
  have hZ := hd.z
  have hx := hd.x
  have hw4 := hd.w4
  obtain hw' : w < 2 ^ 31 := by have := hd.w128; omega_arith
  have hn := hg.scr.nowrap
  obtain hR : Nat.Coprime (2 ^ (64 * w)) c := VG.Proof.Bignum.coprime_pow2 hodd _
  obtain hc0 : 0 < c := by omega_arith
  obtain hTZ : slot w 8 + tabBytes w ≤ Z := by
    rw [tab_end]; have := slot_mono w (show aE + 1 ≤ aRm1 by decide); rw [slot_succ] at this; omega_arith
  obtain hT8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  obtain hY8 := slot_le (w := w) (show aY < 8 by decide)
  obtain hX8 := slot_le (w := w) (show aXm < 8 by decide)
  rw [tabStep_eq]
  -- `y := y T_1`.
  refine WP.seq (WP.mono (M.mm_ok hg hZ (by omega_arith) hw' (o := aY) (a := aY) (b := aXm) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hI.ctx.inv
    (by rw [hI.xm, hI.ctx.n]; exact Nat.mod_lt _ hc0)) fun s₁ ⟨hg₁, hlt₁, hy₁, ha₁, k₁⟩ => ?_)
  rw [hI.ctx.n] at hlt₁ hy₁
  rw [hI.y, hI.xm] at hy₁
  obtain hY₁ : wv s₁.mem B (slot w aY) w = Spec.Rsa.powMod b (i + 2) c * 2 ^ (64 * w) % c := by
    rw [mont_val hR hlt₁ hy₁ rfl rfl, ← powMod_succ']
  obtain hf₁ : Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2))] s.mem s₁.mem :=
    Frm.of_arrays ha₁ (by simp)
  obtain hc₁ : MrCtx s₁ B Z w mi c bm := hI.ctx.of_frm hd hf₁ hg₁.scr hg₁.rdi (VG.Proof.RsaKeyGen.HdrShapeC.geD rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
  obtain hlo : ∀ e < 16, ∀ m m' : Mem, Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)),
      (slot w aY, 8 * (w + 2))] m m' → wv m' B (slot w (8 + e)) w = wv m B (slot w (8 + e)) w := fun e he m m' hf => by
    have := ent_in_tab w he
    exact hf.wv_eq (fun r hr => by
      obtain h1 := slot_le (w := w) (show aAcc < 8 by decide)
      obtain h2 := slot_le (w := w) (show aTmp < 8 by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> right <;> simp only <;> omega_arith) (by omega_arith)
  -- The entry's base and `y`.
  obtain hl : ∀ (t : State), Scr t B Z → ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun t hs i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  obtain hst : ∀ (t : State), Scr t B Z → ∀ i < 32, InRegions t.wr (off B (8 * i)) 8 := fun t hs i hi =>
    hs.st (by have := hdr_lt_slot w 8 hi; omega_arith)
  obtain hV₁ : word s₁.mem B (8 * kV) = off B (slot w (8 + (i + 2))) := by
    rw [hf₁.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by unfold kV kT0 sFn; omega_arith)]; exact hI.v
  refine WP.seq (WP.mono (WP.keep [.r12, .rsi, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rsi = off B (slot w aY) ∧ t.gpr .rbx = off B (slot w (8 + (i + 2))) ∧ t.mem = s₁.mem) (by
    xrun [State.ea, hdr, hg₁.rdi, hdrOff, hl s₁ hg₁.scr sW (by decide), hl s₁ hg₁.scr (sArr aY) (by decide),
      hl s₁ hg₁.scr kV (by decide), hg₁.hdr.hw, hg₁.hdr.harr aY (by decide), hV₁]) rfl)
    fun s₂ ⟨⟨h12, hsi, hbx, hm₂⟩, k₂⟩ => ?_)
  obtain hE := ent_in_tab w (e := i + 2) (by omega_arith)
  refine WP.seq (WP.mono (copyB_ok (hg₁.scr.congr k₂.2.2) hsi hbx h12 (by omega_arith) hw' (by omega_arith)
    (by omega_arith) (Or.inr (by omega_arith))) fun s₃ ⟨hv₃, ho₃, k₃⟩ => ?_)
  rw [hm₂] at hv₃ ho₃
  obtain hf₃ : Frm B [(slot w 8, tabBytes w)] s₁.mem s₃.mem :=
    Frm.of_outside (ho₃.mono (o' := slot w 8) (n' := tabBytes w) hE.1 (by omega_arith)) (by simp)
  obtain hg₃ : Good s₃ B Z w mi := ⟨(hg₁.scr.congr k₂.2.2).congr k₃.2.2,
    (k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans hg₁.rdi), Hdr.of_frm hg₁.hdr hf₃ (by simp; omega_arith)⟩
  -- `kV` and `kBits`.
  obtain hV₃ : word s₃.mem B (8 * kV) = off B (slot w (8 + (i + 2))) := by
    rw [ho₃.word (Or.inl (by have := hdr_lt_slot w (8 + (i + 2)) (show kV < 32 by decide); omega_arith))
      (by unfold kV kT0 sFn; omega_arith), hV₁]
  obtain hB₃ : word s₃.mem B (8 * kBits) = BitVec.ofNat 64 (14 - i) := by
    rw [ho₃.word (Or.inl (by have := hdr_lt_slot w (8 + (i + 2)) (show kBits < 32 by decide); omega_arith))
      (by unfold kBits kT2 sFn; omega_arith), hf₁.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by unfold kBits kT2 sFn; omega_arith)]
    exact hI.bits
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.mem = (s₃.mem.writeW (off B (8 * kV))
      (off B (slot w (8 + (i + 2)) + 8 * (w + 2)))).writeW (off B (8 * kBits)) (BitVec.ofNat 64 (14 - i - 1)) ∧
      t.zf = some (decide (14 - i - 1 = 0))) (by
    xrun [State.ea, hdr, hg₃.rdi, hdrOff, hl s₃ hg₃.scr kV (by decide), hl s₃ hg₃.scr sW (by decide),
      hl s₃ hg₃.scr kBits (by decide), hst s₃ hg₃.scr kV (by decide), hst s₃ hg₃.scr kBits (by decide), hV₃,
      hg₃.hdr.hw, entStep,
      fun X => (hdrStore_hdr s₃.mem B X (show kV < 32 by decide) (show kBits < 32 by decide) (by decide)).trans hB₃,
      ofNat64_pred (show 1 ≤ 14 - i by omega_arith) (by omega_arith),
      ofNat64_beq_zero (show 14 - i - 1 < 2 ^ 64 by omega_arith)]) rfl) fun t ⟨⟨hm, hz⟩, k⟩ => ⟨?_, ?_⟩
  · rw [hz]; exact congrArg some (decide_eq_decide.mpr (by omega_arith))
  obtain hft : Frm B (tabRanges w) s₃.mem t.mem := by
    rw [hm]
    exact (Frm.of_outside (writeW_outside _ B _ (d := 8 * kV) (by unfold kV kT0 sFn; omega_arith))
      (tabRanges_hdr w (Or.inl rfl))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kBits)
        (by unfold kBits kT2 sFn; omega_arith)) (tabRanges_hdr w (Or.inr rfl)))
  obtain hf1t : Frm B (tabRanges w) s.mem t.mem :=
    ((hf₁.mono (by simp [tabRanges])).trans (hf₃.mono (by simp [tabRanges]))).trans hft
  obtain hgt : Good t B Z w mi := ⟨hg₃.scr.congr k.2.2, (k.gpr (by decide)).trans hg₃.rdi,
    Hdr.of_frm hg₃.hdr hft (by simp only [tabRanges]; rng_le)⟩
  -- The arrays through the header writes.
  obtain hwv : ∀ j ≤ 24, wv t.mem B (slot w j) w = wv s₃.mem B (slot w j) w := fun j hj => by
    have := slot_lt24 w hj
    obtain h1 := hdr_lt_slot w j (show kV < 32 by decide)
    obtain h2 := hdr_lt_slot w j (show kBits < 32 by decide)
    rw [hm, (writeW_outside _ B _ (d := 8 * kBits) (by unfold kBits kT2 sFn; omega_arith)).wv (Or.inr h2)
      (by omega_arith), (writeW_outside _ B _ (d := 8 * kV) (by unfold kV kT0 sFn; omega_arith)).wv (Or.inr h1)
      (by omega_arith)]
  -- What the copy keeps: the arrays other than entry `i + 2`.
  obtain hcp : ∀ j ≤ 24, j ≠ 8 + (i + 2) → wv s₃.mem B (slot w j) w = wv s₁.mem B (slot w j) w := fun j hj hne => by
    have := slot_lt24 w hj
    rcases slot_sep (w := w) hne with h | h
    · exact ho₃.wv (Or.inl (by omega_arith)) (by omega_arith)
    · exact ho₃.wv (Or.inr (by omega_arith)) (by omega_arith)
  obtain hBt : wv t.mem B (slot w aB) w = wv s.mem B (slot w aB) w := by
    rw [hwv aB (by decide), hcp aB (by decide) (by show 9 ≠ 8 + (i + 2); omega_arith)]
    exact hlo 1 (by decide) s.mem s₁.mem hf₁
  refine ⟨hI.ctx.of_tab hd hf1t hgt.scr hgt.rdi (hBt.trans hI.ctx.b), fun e he => ?_, ?_, ?_, ?_, ?_,
    hI.frm.trans hf1t, (((hI.keep.trans k₁).trans k₂).trans (k₃.trans k)).mono (by decide)⟩
  · rw [hwv (8 + e) (by omega_arith)]
    by_cases hei : e = i + 2
    · subst hei; rw [hv₃, hY₁]
    · rw [hcp (8 + e) (by omega_arith) (by omega_arith), hlo e (by omega_arith) s.mem s₁.mem hf₁]
      exact hI.ent e (by omega_arith)
  · rw [hwv aY (by decide), hcp aY (by decide) (by unfold aY; omega_arith), hY₁]
  · rw [hwv aXm (by decide), hcp aXm (by decide) (by unfold aXm; omega_arith),
      hf₁.wv_eq (d := slot w aXm) (k := w) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (by omega_arith)]
    exact hI.xm
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self, ← slot_succ,
      show 8 + (i + 2) + 1 = 8 + (i + 1 + 2) by omega_arith]
  · rw [hm, word_writeW_self, show 14 - i - 1 = 14 - (i + 1) by omega_arith]

/-- The bases of the table's start, and the entry pointer and the count. -/
theorem tabBases_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi) (hd : MrDims B Z w) :
    WP isa (.block (([.mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aXm))), .mov .r10 (.mem (hdr (sArr aY)))] :
      List Instr) ++ extBase aB .r9 ++ extBase aR1 .r11 ++ extBase aT0 .r13 ++ extBase (aT0 + 2) .rcx ++
      ([.store (hdr kV) .rcx, .mov32 .rax (.imm 14), .store (hdr kBits) .rax] : List Instr))) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r8 = off B (slot w aXm) ∧ t.gpr .r10 = off B (slot w aY) ∧
      t.gpr .r9 = off B (slot w aB) ∧ t.gpr .r11 = off B (slot w aR1) ∧ t.gpr .r13 = off B (slot w aT0) ∧
      t.mem = (s.mem.writeW (off B (8 * kV)) (off B (slot w (8 + (0 + 2))))).writeW (off B (8 * kBits))
        (BitVec.ofNat 64 (14 - 0)) ∧ Keep [.rax, .rcx, .r8, .r9, .r10, .r11, .r12, .r13] s t := by
  have hn := hg.scr.nowrap
  have hZ := hd.z
  obtain hw' : w < 2 ^ 31 := by have := hd.w128; omega_arith
  obtain hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r12, .r8, .r10] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r8 = off B (slot w aXm) ∧ t.gpr .r10 = off B (slot w aY) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aXm) (by decide), hl (sArr aY) (by decide),
      hg.hdr.hw, hg.hdr.harr aXm (by decide), hg.hdr.harr aY (by decide)]) rfl) fun s₁ ⟨⟨h12, h8, h10, hm₁⟩, k₁⟩ => ?_
  obtain hg₁ : Good s₁ B Z w mi := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, by rw [hm₁]; exact hg.hdr⟩
  refine WP.mono (extBase_ok hg₁ hZ hw' (j := aB) (by decide) (r := .r9) (by decide) rfl rfl) fun s₂ ⟨h9, hm₂, k₂⟩ => ?_
  obtain hg₂ : Good s₂ B Z w mi := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi, by rw [hm₂]; exact hg₁.hdr⟩
  refine WP.mono (extBase_ok hg₂ hZ hw' (j := aR1) (by decide) (r := .r11) (by decide) rfl rfl)
    fun s₃ ⟨h11, hm₃, k₃⟩ => ?_
  obtain hg₃ : Good s₃ B Z w mi := ⟨hg₂.scr.congr k₃.2.2, (k₃.gpr (by decide)).trans hg₂.rdi, by rw [hm₃]; exact hg₂.hdr⟩
  refine WP.mono (extBase_ok hg₃ hZ hw' (j := aT0) (by decide) (r := .r13) (by decide) rfl rfl)
    fun s₄ ⟨h13, hm₄, k₄⟩ => ?_
  obtain hg₄ : Good s₄ B Z w mi := ⟨hg₃.scr.congr k₄.2.2, (k₄.gpr (by decide)).trans hg₃.rdi, by rw [hm₄]; exact hg₃.hdr⟩
  refine WP.mono (extBase_ok hg₄ hZ hw' (j := aT0 + 2) (by decide) (r := .rcx) (by decide) rfl rfl)
    fun s₅ ⟨hcx, hm₅, k₅⟩ => ?_
  obtain hst : ∀ i < 32, InRegions s₅.wr (off B (8 * i)) 8 := fun i hi => by
    rw [k₅.2.2, k₄.2.2, k₃.2.2, k₂.2.2, k₁.2.2]; exact hg.scr.st (by have := hdr_lt_slot w 8 hi; omega_arith)
  obtain hdi₅ : s₅.gpr .rdi = B := (k₅.gpr (by decide)).trans hg₄.rdi
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = (s.mem.writeW (off B (8 * kV))
      (off B (slot w (8 + (0 + 2))))).writeW (off B (8 * kBits)) (BitVec.ofNat 64 (14 - 0))) (by
    xrun [State.ea, hdr, hdi₅, hdrOff, hst kV (by decide), hst kBits (by decide), hcx, hm₅, hm₄, hm₃, hm₂, hm₁]
    rfl) rfl) fun t ⟨hm, k⟩ => ?_
  obtain kA := (((k₁.trans k₂).trans k₃).trans k₄).trans k₅
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hm, (kA.trans k).mono (by decide)⟩
  · rw [k.gpr (by decide), k₅.gpr (by decide), k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide)]; exact h12
  · rw [k.gpr (by decide), k₅.gpr (by decide), k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide)]; exact h8
  · rw [k.gpr (by decide), k₅.gpr (by decide), k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide)]; exact h10
  · rw [k.gpr (by decide), k₅.gpr (by decide), k₄.gpr (by decide), k₃.gpr (by decide)]; exact h9
  · rw [k.gpr (by decide), k₅.gpr (by decide), k₄.gpr (by decide)]; exact h11
  · rw [k.gpr (by decide), k₅.gpr (by decide)]; exact h13

/-- `[d] := [a]` for bases already in `rsi` and `rbx`. -/
theorem copyRegs_ok {s : State} {B : Addr} {Z w eS eD : Nat} {rS rD : Reg} (hs : Scr s B Z) (hS : s.gpr rS = off B eS)
    (hD : s.gpr rD = off B eD) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hSZ : eS + 8 * w ≤ Z) (hDZ : eD + 8 * w ≤ Z) (hsep : eD + 8 * w ≤ eS ∨ eS + 8 * w ≤ eD)
    (hne : rD ≠ .rsi := by decide) :
    WP isa (seqs [.block [.mov .rsi (.reg rS), .mov .rbx (.reg rD)], copyWords]) s fun t =>
      wv t.mem B eD w = wv s.mem B eS w ∧ Outside B eD (8 * w) s.mem t.mem ∧ Keep [.rax, .rbx, .rsi, .r14] s t := by
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rsi, .rbx] (Q := fun t => t.gpr .rsi = off B eS ∧ t.gpr .rbx = off B eD ∧
      t.mem = s.mem) (by xrun [hS, hD, hne]) rfl) fun s₁ ⟨⟨hsi, hbx, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (copyB_ok (hs.congr k₁.2.2) hsi hbx ((k₁.gpr (by decide)).trans h12) hw hw' hSZ hDZ hsep)
    fun t ⟨hv, ho, k⟩ => ⟨by rw [hv, hm₁], by rw [← hm₁]; exact ho, (k₁.trans k).mono (by decide)⟩

/-- The table's start: `TabI` at the start of its loop. -/
theorem tabHead_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm b : Nat}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm) (hc1 : 1 < c)
    (hX : wv s.mem B (slot w aXm) w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c) :
    WP isa (seqs tabHead) s fun t =>
      TabI B Z w mi c (Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c) b t 0 t ∧ Frm B (tabRanges w) s.mem t.mem ∧
      Keep mmRegs s t := by
  have hg := hc.good
  have hZ := hd.z
  have hx := hd.x
  have hw4 := hd.w4
  obtain hw' : w < 2 ^ 31 := by have := hd.w128; omega_arith
  have hn := hg.scr.nowrap
  obtain hY8 := slot_le (w := w) (show aY < 8 by decide)
  obtain hX8 := slot_le (w := w) (show aXm < 8 by decide)
  obtain hB := ent_in_tab w (e := 1) (by decide)
  obtain hR1 := slot_mono w (show aR1 + 1 ≤ aRm1 by decide)
  obtain hR1s := slot_succ w aR1
  obtain hER := slot_mono w (show aE ≤ aR1 by decide)
  obtain hte := tab_end w
  obtain hBs : slot w aB = slot w 8 + 8 * (w + 2) := slot_succ w 8
  have hT0s : slot w aT0 = slot w 8 := rfl
  obtain htb : tabBytes w = 128 * (w + 2) := by unfold tabBytes; omega_arith
  unfold tabHead
  simp only [seqs]
  refine WP.seq (WP.mono (tabBases_ok hg hd) fun s₁ ⟨h12, h8, h10, h9, h11, h13, hm₁, k₁⟩ => ?_)
  obtain hf₁ : Frm B (tabRanges w) s.mem s₁.mem := by
    rw [hm₁]
    exact (Frm.of_outside (writeW_outside _ B _ (d := 8 * kV) (by unfold kV kT0 sFn; omega_arith))
      (tabRanges_hdr w (Or.inl rfl))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kBits)
        (by unfold kBits kT2 sFn; omega_arith)) (tabRanges_hdr w (Or.inr rfl)))
  obtain hs₁ := hg.scr.congr k₁.2.2
  obtain hwv1 : ∀ j ≤ 26, wv s₁.mem B (slot w j) w = wv s.mem B (slot w j) w := fun j hj => by
    have := slot_lt27 w (show j ≤ 27 by omega_arith)
    obtain h1 := hdr_lt_slot w j (show kV < 32 by decide)
    obtain h2 := hdr_lt_slot w j (show kBits < 32 by decide)
    rw [hm₁, (writeW_outside _ B _ (d := 8 * kBits) (by unfold kBits kT2 sFn; omega_arith)).wv (Or.inr h2)
      (by omega_arith), (writeW_outside _ B _ (d := 8 * kV) (by unfold kV kT0 sFn; omega_arith)).wv (Or.inr h1)
      (by omega_arith)]
  -- `T_1 := b R mod c`.
  refine WP.seq (WP.mono (copyRegs_ok hs₁ h8 h9 h12 (by omega_arith) hw' (by omega_arith) (by omega_arith)
    (Or.inr (by omega_arith))) fun s₂ ⟨hv₂, ho₂, k₂⟩ => ?_)
  obtain hs₂ := hs₁.congr k₂.2.2
  -- `y := T_1`.
  refine WP.seq (WP.mono (copyRegs_ok hs₂ ((k₂.gpr (by decide)).trans h8) ((k₂.gpr (by decide)).trans h10)
    ((k₂.gpr (by decide)).trans h12) (by omega_arith) hw' (by omega_arith) (by omega_arith)
    (by rcases slot_sep (w := w) (show aY ≠ aXm by decide) with h | h
        exacts [Or.inl (by omega_arith), Or.inr (by omega_arith)])) fun s₃ ⟨hv₃, ho₃, k₃⟩ => ?_)
  obtain hs₃ := hs₂.congr k₃.2.2
  -- `T_0 := R mod c`.
  refine WP.mono (copyRegs_ok hs₃ ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h11))
    ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h13)) ((k₃.gpr (by decide)).trans
    ((k₂.gpr (by decide)).trans h12)) (by omega_arith) hw' (by omega_arith) (by omega_arith) (Or.inl (by omega_arith)))
    fun t ⟨hv, ho, k⟩ => ?_
  obtain hf : Frm B (tabRanges w) s.mem t.mem := by
    refine hf₁.trans (((Frm.of_outside (ho₂.mono (o' := slot w 8) (n' := tabBytes w) hB.1 (by omega_arith))
      (by simp [tabRanges])).trans (Frm.of_outside (ho₃.mono (o' := slot w aY) (n' := 8 * (w + 2)) (Nat.le_refl _)
        (by omega_arith)) (by simp [tabRanges]))).trans (Frm.of_outside (ho.mono (o' := slot w 8) (n' := tabBytes w)
          (by omega_arith) (by omega_arith)) (by simp [tabRanges])))
  obtain hgt : Good t B Z w mi := ⟨hs₃.congr k.2.2, (k.gpr (by decide)).trans ((k₃.gpr (by decide)).trans
    ((k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi))), Hdr.of_frm hg.hdr hf (by simp only [tabRanges]; rng_le)⟩
  obtain hXt : wv t.mem B (slot w aXm) w = wv s.mem B (slot w aXm) w := by
    rw [ho.wv (Or.inl (by omega_arith)) (by omega_arith),
      ho₃.wv (by rcases slot_sep (w := w) (show aY ≠ aXm by decide) with h | h
                 exacts [Or.inr (by omega_arith), Or.inl (by omega_arith)]) (by omega_arith),
      ho₂.wv (Or.inl (by omega_arith)) (by omega_arith), hwv1 aXm (by decide)]
  obtain hBt : wv t.mem B (slot w aB) w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c := by
    rw [ho.wv (Or.inr (by omega_arith)) (by omega_arith), ho₃.wv (Or.inr (by omega_arith)) (by omega_arith), hv₂,
      hwv1 aXm (by decide), hX]
  refine ⟨⟨hc.of_tab hd hf hgt.scr hgt.rdi hBt, fun e he => ?_, ?_, ?_, ?_, ?_, Frm.refl _ _ _, Keep.refl _ _⟩, hf,
    ((k₁.trans k₂).trans (k₃.trans k)).mono (by decide)⟩
  · rcases (by omega_arith : e = 0 ∨ e = 1) with rfl | rfl
    · rw [show 8 + 0 = aT0 from rfl, hv, ho₃.wv (Or.inr (by omega_arith)) (by omega_arith),
        ho₂.wv (Or.inr (by omega_arith)) (by omega_arith), hwv1 aR1 (by decide), hc.r1, powMod_zero' hc1, Nat.one_mul]
    · exact hBt
  · rw [ho.wv (Or.inl (by omega_arith)) (by omega_arith), hv₃, ho₂.wv (Or.inl (by omega_arith)) (by omega_arith),
      hwv1 aXm (by decide), hX]
  · rw [hXt, hX]
  all_goals
    obtain a1 := hdr_lt_slot w aT0 (show kV < 32 by decide)
    obtain a2 := hdr_lt_slot w aY (show kV < 32 by decide)
    obtain a3 := hdr_lt_slot w aB (show kV < 32 by decide)
    obtain b1 := hdr_lt_slot w aT0 (show kBits < 32 by decide)
    obtain b2 := hdr_lt_slot w aY (show kBits < 32 by decide)
    obtain b3 := hdr_lt_slot w aB (show kBits < 32 by decide)
  · rw [ho.word (Or.inl a1) (by unfold kV kT0 sFn; omega_arith), ho₃.word (Or.inl a2) (by unfold kV kT0 sFn; omega_arith),
      ho₂.word (Or.inl a3) (by unfold kV kT0 sFn; omega_arith), hm₁,
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [ho.word (Or.inl b1) (by unfold kBits kT2 sFn; omega_arith),
      ho₃.word (Or.inl b2) (by unfold kBits kT2 sFn; omega_arith),
      ho₂.word (Or.inl b3) (by unfold kBits kT2 sFn; omega_arith), hm₁, word_writeW_self]

theorem tabBuild_eq (mul : Nat → Nat → Nat → Prog isa) : tabBuild mul =
    ([seqs tabHead] : List (Prog isa)) ++ (([.loop (seqs [mul aY aY aXm,
      .block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aY))), .mov .rbx (.mem (hdr kV))], copyWords,
      .block [.mov .rax (.mem (hdr kV)), .mov .rdx (.mem (hdr sW)), .alu .add .rdx (.imm 2),
        .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rdx (.reg .rdx), .alu .add .rax (.reg .rdx),
        .store (hdr kV) .rax, .mov .rax (.mem (hdr kBits)), .alu .sub .rax (.imm 1), .store (hdr kBits) .rax]]) .ne] : List (Prog isa)) ++
    ([.block (([.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aY)))] : List Instr) ++ extBase aR1 .rsi),
      copyWords] : List (Prog isa))) := rfl

/-- The table, from `b R mod c` in `aXm`: `TabOK`, and `y := 1`. -/
theorem tabBuild_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm b : Nat}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hX : wv s.mem B (slot w aXm) w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c) :
    WP isa (seqs (tabBuild M.mm)) s fun t =>
      MrCtx t B Z w mi c (Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c) ∧ TabOK t.mem B w c b ∧
      wv t.mem B (slot w aY) w = 2 ^ (64 * w) % c ∧ Frm B (tabRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hZ := hd.z
  have hx := hd.x
  obtain hw' : w < 2 ^ 31 := by have := hd.w128; omega_arith
  have hn := hc.good.scr.nowrap
  obtain hY8 := slot_le (w := w) (show aY < 8 by decide)
  obtain hR1 := slot_mono w (show aR1 + 1 ≤ aRm1 by decide)
  obtain hR1s := slot_succ w aR1
  obtain hER := slot_mono w (show aE ≤ aR1 by decide)
  obtain hte := tab_end w
  obtain hBs : slot w aB = slot w 8 + 8 * (w + 2) := slot_succ w 8
  obtain htb : tabBytes w = 128 * (w + 2) := by unfold tabBytes; omega_arith
  rw [tabBuild_eq]
  refine wp_seqs_append (by simp) (by simp) ?_
  simp only [seqs]
  refine WP.mono (tabHead_ok hd hc hc1 hX) fun s₄ ⟨hI0, hf₄, k₄⟩ => ?_
  refine wp_seqs_append (by simp) (by simp) ?_
  simp only [seqs]
  refine WP.mono (wp_upto (a := 0) (N := 14) (by decide) (TabI B Z w mi c _ b s₄)
    (fun i _ hi t hI => tabStep_ok M hd hodd hc1 hi hI) (fun t h => h) hI0) fun s₅ hI => ?_
  -- `y := 1`.
  refine WP.mono (copyFromExt_ok hI.ctx.good hZ (by have := hd.w4; omega_arith) hw' (a := aY) (d := aR1) (by decide)
    (by decide) (by omega_arith)) fun t ⟨hv, ho, k⟩ => ?_
  obtain hft : Frm B (tabRanges w) s₅.mem t.mem :=
    Frm.of_outside (ho.mono (o' := slot w aY) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_arith)) (by simp [tabRanges])
  obtain hf : Frm B (tabRanges w) s.mem t.mem := (hf₄.trans hI.frm).trans hft
  obtain hgt : Good t B Z w mi := ⟨hI.ctx.good.scr.congr k.2.2, (k.gpr (by decide)).trans hI.ctx.good.rdi,
    Hdr.of_frm hc.good.hdr hf (by simp only [tabRanges]; rng_le)⟩
  refine ⟨hc.of_tab hd hf hgt.scr hgt.rdi ?_, fun j hj => ?_, by rw [hv, hI.ctx.r1], hf,
    ((k₄.trans hI.keep).trans k).mono (by decide)⟩
  · rw [ho.wv (Or.inr (by omega_arith)) (by omega_arith)]; exact hI.ctx.b
  · have := ent_in_tab w hj
    rw [ho.wv (Or.inr (by omega_arith)) (by omega_arith)]
    exact hI.ent j (by omega_arith)

end VG.Proof.RsaKeyGen.X86_64

end

end

/-! ### `RsaKeyGen.X86_64.MrLoop`, which this module and modules that import it used -/

section

/-!
# A candidate on x86-64: Miller–Rabin's exponentiation loops

`WinInv`: after `t` windows of word `k − 1` of `E` (the words from the top),
`y R mod c` and the flag after the `16 (w − k) + t` windows from the top
(`wRun`), the word shifted left by `4 t` in `kV`. `mrWins_ok`: the inner
loop over the word's 16 windows; `mrWord_ok`: one word.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 VG.Proof.RsaKeyGen

/-- What the exponentiation changes. -/
def expRanges (w : Nat) : List (Nat × Nat) := winRanges w ++ [(8 * kWords, 8)]

/-- `expRanges`'s ranges, in the header and in the arrays. -/
theorem expRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w [(248, 8), (176, 8), (208, 8), (224, 8), (216, 8)]
    [(2, 1), (3, 1), (6, 1), (5, 1)] (expRanges w) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append,
    expRanges, winRanges, Public.aAcc, Public.aTmp, Public.aXm, Public.aY, aAcc, aTmp, aXm, aY, kT0, sFn, kG, kV, kWords, kBits, kFlag, kPlen, kT1, kT2] at hr
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

theorem expRanges_low (w : Nat) : ∀ r ∈ expRanges w, r.1 + r.2 ≤ slot w 8 := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact winRanges_low w r hr
  · simp only [List.mem_singleton] at hr; subst hr
    exact hdr_lt_slot w 8 (show kWords < 32 by decide)

theorem sqRanges_sub (w : Nat) : ∀ r ∈ sqRanges w, r ∈ expRanges w := by
  simp only [sqRanges, expRanges, winRanges, List.mem_cons, List.not_mem_nil, or_false, List.mem_append]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp

theorem winRanges_sub (w : Nat) : ∀ r ∈ winRanges w, r ∈ expRanges w := fun _ hr => List.mem_append_left _ hr

/-- After `t` windows of word `k − 1`, `W`, of `E`. -/
structure WinInv (B : Addr) (Z w : Nat) (mi : BitVec 64) (c bm b k : Nat) (W : BitVec 64) (s₀ : State) (t : Nat)
    (s : State) : Prop where
  ctx : MrCtx s B Z w mi c bm
  tab : TabOK s.mem B w c b
  y : wv s.mem B (slot w aY) w = (wRun c b (mrE c) (16 * w) (16 * (w - k) + t)).1 * 2 ^ (64 * w) % c
  flag : word s.mem B (8 * kFlag) = mask (wRun c b (mrE c) (16 * w) (16 * (w - k) + t)).2
  v : word s.mem B (8 * kV) = W <<< (4 * t)
  bits : word s.mem B (8 * kBits) = BitVec.ofNat 64 (16 - t)
  words : word s.mem B (8 * kWords) = BitVec.ofNat 64 (k - 1)
  frm : Frm B (expRanges w) s₀.mem s.mem
  keep : Keep mmRegs s₀ s

/-- One window of word `k − 1`. -/
theorem mrWinStep_ok (M : Mont) {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm b k : Nat} {W : BitVec 64}
    {s₀ s : State} (hd : MrDims B Z w) (hodd : c % 2 = 1) (hc1 : 1 < c) (hk : 1 ≤ k) (hkw : k ≤ w)
    (hW : W.toNat = mrE c / 2 ^ (64 * (k - 1)) % 2 ^ 64) {j : Nat} (hj : j < 16)
    (hI : WinInv B Z w mi c bm b k W s₀ j s) :
    WP isa (seqs (mrWin M.mm)) s fun t =>
      t.zf = some (decide (j + 1 = 16)) ∧ WinInv B Z w mi c bm b k W s₀ (j + 1) t := by
  have hdig := win_digit hW hj
  refine WP.mono (mrWin_ok M hd hI.ctx hI.tab hodd hc1 hI.y hI.flag hI.v hI.bits (by omega_arith) (by omega_arith))
    fun t ⟨hct, htt, hyt, hft, hvt, hbt, hz, hfr, kt⟩ =>
      ⟨by rw [hz, decide_eq_decide.mpr (show 16 - j - 1 = 0 ↔ j + 1 = 16 by omega_arith)], ?_⟩
  have e : wRun c b (mrE c) (16 * w) (16 * (w - k) + (j + 1)) =
      wWin c b ((W <<< (4 * j)) >>> 60).toNat
        ((wRun c b (mrE c) (16 * w) (16 * (w - k) + j)).1, (wRun c b (mrE c) (16 * w) (16 * (w - k) + j)).2) := by
    rw [show 16 * (w - k) + (j + 1) = (16 * (w - k) + j) + 1 by omega_arith, wRun, hdig,
      show 16 * w - 1 - (16 * (w - k) + j) = 16 * (k - 1) + (15 - j) by omega_arith]
  refine ⟨hct, htt, by rw [e]; exact hyt, by rw [e]; exact hft, by rw [hvt, shl4_succ], ?_, ?_,
    hI.frm.trans (hfr.mono (winRanges_sub w)), (hI.keep.trans kt).mono (by decide)⟩
  · rw [hbt, show 16 - j - 1 = 16 - (j + 1) by omega_arith]
  · rw [hfr.word_eq (d := 8 * kWords) (by simp only [winRanges]; rng_disj) (by unfold kWords kT1 sFn; omega_arith)]
    exact hI.words

/-- The inner loop: the 16 windows of word `k − 1`. -/
theorem mrWins_ok (M : Mont) {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm b k : Nat} {W : BitVec 64}
    {s₀ s : State} (hd : MrDims B Z w) (hodd : c % 2 = 1) (hc1 : 1 < c) (hk : 1 ≤ k) (hkw : k ≤ w)
    (hW : W.toNat = mrE c / 2 ^ (64 * (k - 1)) % 2 ^ 64) (h0 : WinInv B Z w mi c bm b k W s₀ 0 s) :
    WP isa (.loop (seqs (mrWin M.mm)) .ne) s (WinInv B Z w mi c bm b k W s₀ 16) :=
  wp_upto (a := 0) (N := 16) (by decide) (WinInv B Z w mi c bm b k W s₀)
    (fun j _ hj s hI => mrWinStep_ok M hd hodd hc1 hk hkw hW hj hI) (fun _ h => h) h0

/-- After `j` of the `w` words. -/
structure WordInv (B : Addr) (Z w : Nat) (mi : BitVec 64) (c bm b : Nat) (s₀ : State) (j : Nat) (s : State) :
    Prop where
  ctx : MrCtx s B Z w mi c bm
  tab : TabOK s.mem B w c b
  y : wv s.mem B (slot w aY) w = (wRun c b (mrE c) (16 * w) (16 * j)).1 * 2 ^ (64 * w) % c
  flag : word s.mem B (8 * kFlag) = mask (wRun c b (mrE c) (16 * w) (16 * j)).2
  words : word s.mem B (8 * kWords) = BitVec.ofNat 64 (w - j)
  frm : Frm B (expRanges w) s₀.mem s.mem
  keep : Keep mmRegs s₀ s

theorem expRanges_hdr (w : Nat) {i : Nat} (hi : i = kWords ∨ i = kV ∨ i = kBits ∨ i = kFlag) :
    (8 * i, 8) ∈ expRanges w := by
  rcases hi with rfl | rfl | rfl | rfl <;> simp [expRanges, winRanges]

/-- `MrCtx` survives changes within the exponentiation's ranges. -/
theorem MrCtx.of_exp {s t : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm : Nat}
    (hc : MrCtx s B Z w mi c bm) (hd : MrDims B Z w) (hf : Frm B (expRanges w) s.mem t.mem) (hs : Scr t B Z)
    (hdi : t.gpr .rdi = B) : MrCtx t B Z w mi c bm :=
  hc.of_frm hd hf hs hdi (by simp only [expRanges, winRanges, List.cons_append, List.nil_append]; rng_disj)
    (by simp only [expRanges, winRanges, List.cons_append, List.nil_append]; rng_disj)
    (by simp only [expRanges, winRanges, List.cons_append, List.nil_append]; rng_disj)
    (by simp only [expRanges, winRanges, List.cons_append, List.nil_append]; rng_disj)
    (by simp only [expRanges, winRanges, List.cons_append, List.nil_append]; rng_disj)

/-- The word `w − 1 − j` of `E`, as `WinInv` reads it. -/
abbrev wordE (m : Mem) (B : Addr) (w j : Nat) : BitVec 64 := word m B (slot w aE + 8 * (w - j - 1))

/-- The start of word `w − 1 − j`: `kWords := w − 1 − j`, the word into
`kV`, 16 into `kBits`. -/
theorem wordStart_ok {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm b : Nat} {s₀ s : State}
    (hd : MrDims B Z w) {j : Nat} (hj : j < w) (hI : WordInv B Z w mi c bm b s₀ j s) :
    WP isa (.block (([.mov .rax (.mem (hdr kWords)), .alu .sub .rax (.imm 1), .store (hdr kWords) .rax] :
        List Instr) ++ extBase aE .rdx ++ ([.mov .rax (.mem (hdr kWords)), .mov .rcx (.mem (ix .rdx .rax)),
        .store (hdr kV) .rcx, .mov32 .rcx (.imm 16), .store (hdr kBits) .rcx] : List Instr))) s
      fun s₁ => WinInv B Z w mi c bm b (w - j) (wordE s.mem B w j) s₀ 0 s₁ := by
  have hg := hI.ctx.good
  have hZ := hd.z
  have hXZ := hd.x
  have hw4 := hd.w4
  have hw' : w < 2 ^ 31 := by have := hd.w128; omega_arith
  have hn := hg.scr.nowrap
  have hl : ∀ (t : State), Scr t B Z → ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun t hs i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  have hst : ∀ (t : State), Scr t B Z → ∀ i < 32, InRegions t.wr (off B (8 * i)) 8 := fun t hs i hi =>
    hs.st (by have := hdr_lt_slot w 8 hi; omega_arith)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off B (8 * kWords))
      (BitVec.ofNat 64 (w - j - 1))) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl s hg.scr kWords (by decide), hst s hg.scr kWords (by decide), hI.words,
      ofNat64_pred (show 1 ≤ w - j by omega_arith) (by omega_arith)]) rfl) fun s₁ ⟨hm₁, k₁⟩ => ?_
  have hg₁ : Good s₁ B Z w mi := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi,
    by rw [hm₁]; exact hg.hdr.store (by decide) (by decide) _⟩
  refine WP.mono (extBase_ok hg₁ hZ hw' (j := aE) (by decide) (r := .rdx) (by decide) rfl rfl)
    fun s₂ ⟨hdx, hm₂, k₂⟩ => ?_
  have hg₂ : Good s₂ B Z w mi := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi, by rw [hm₂]; exact hg₁.hdr⟩
  have hWd : word s₂.mem B (8 * kWords) = BitVec.ofNat 64 (w - j - 1) := by rw [hm₂, hm₁, word_writeW_self]
  have hEw : word s₂.mem B (slot w aE + 8 * (w - j - 1)) = wordE s.mem B w j := by
    rw [hm₂, hm₁, (writeW_outside _ B _ (d := 8 * kWords) (by unfold kWords kT1 sFn; omega_arith)).word
      (Or.inr (by have := hdr_lt_slot w aE (show kWords < 32 by decide); omega_arith)) (by
        have := slot_lt24 w (show aE ≤ 24 by decide); omega_arith)]
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.mem = (s₂.mem.writeW (off B (8 * kV))
      (wordE s.mem B w j)).writeW (off B (8 * kBits)) (BitVec.ofNat 64 16)) (by
    xrun [State.ea, hdr, ix, hg₂.rdi, hdrOff, hl s₂ hg₂.scr kWords (by decide), hst s₂ hg₂.scr kV (by decide),
      hst s₂ hg₂.scr kBits (by decide), hWd, hdx, addr0 rfl rfl,
      hg₂.scr.ld (d := slot w aE + 8 * (w - j - 1)) (by have := aE_fits hd; omega_arith), hEw]
    rfl) rfl) fun t ⟨hm, k⟩ => ?_
  have hf : Frm B (expRanges w) s.mem t.mem := by
    rw [hm, hm₂, hm₁]
    exact ((Frm.of_outside (writeW_outside _ B _ (d := 8 * kWords) (by unfold kWords kT1 sFn; omega_arith))
      (expRanges_hdr w (Or.inl rfl))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kV)
        (by unfold kV kT0 sFn; omega_arith)) (expRanges_hdr w (Or.inr (Or.inl rfl))))).trans
      (Frm.of_outside (writeW_outside _ B _ (d := 8 * kBits) (by unfold kBits kT2 sFn; omega_arith))
        (expRanges_hdr w (Or.inr (Or.inr (Or.inl rfl)))))
  have hst' := hg₂.scr.congr k.2.2
  have hdi : t.gpr .rdi = B := (k.gpr (by decide)).trans hg₂.rdi
  refine ⟨hI.ctx.of_exp hd hf hst' hdi, hI.tab.of_low hf (expRanges_low w) hw', ?_, ?_, ?_, ?_, ?_,
    hI.frm.trans hf, ((hI.keep.trans k₁).trans (k₂.trans k)).mono (by decide)⟩
  · rw [hm, hdrStore_wv _ _ _ (by decide) (by decide) (by omega_arith), hdrStore_wv _ _ _ (by decide) (by decide) (by omega_arith),
      hm₂, hm₁, hdrStore_wv _ _ _ (by decide) (by decide) (by omega_arith), hI.y,
      show 16 * (w - (w - j)) + 0 = 16 * j by omega_arith]
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hm₂, hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hI.flag,
      show 16 * (w - (w - j)) + 0 = 16 * j by omega_arith]
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self, Nat.mul_zero,
      BitVec.shiftLeft_zero]
  · rw [hm, word_writeW_self]
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      hWd]

/-- The end of word `w − 1 − j`: ZF set after the last. -/
theorem wordEnd_ok {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm b : Nat} {W : BitVec 64} {s₀ s : State}
    (hd : MrDims B Z w) {j : Nat} (hj : j < w) (hB : WinInv B Z w mi c bm b (w - j) W s₀ 16 s) :
    WP isa (.block [.mov .rax (.mem (hdr kWords)), .alu .test .rax (.reg .rax)]) s fun t =>
      t.zf = some (decide (j + 1 = w)) ∧ WordInv B Z w mi c bm b s₀ (j + 1) t := by
  have hg₂ := hB.ctx.good
  have hn := hg₂.scr.nowrap
  have hZ := hd.z
  have h64 := hd.w128
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * kWords)) 8 :=
    hg₂.scr.ld (by have := hdr_lt_slot w 8 (show kWords < 32 by decide); omega_arith)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (j + 1 = w)) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg₂.rdi, hdrOff, hl, hB.words, BitVec.and_self,
      ofNat64_beq_zero (show w - j - 1 < 2 ^ 64 by omega_arith)]
    exact decide_eq_decide.mpr (by omega_using [hj])) rfl) fun t ⟨⟨hz, hm⟩, k⟩ => ⟨hz, ?_⟩
  have e : 16 * (w - (w - j)) + 16 = 16 * (j + 1) := by omega_arith
  have hft : Frm B [] s.mem t.mem := by rw [hm]; exact Frm.refl _ _ _
  refine ⟨hB.ctx.of_frm hd hft (hg₂.scr.congr k.2.2) ((k.gpr (by decide)).trans hg₂.rdi) (by simp) (by simp) (by simp)
      (by simp) (by simp), by rw [hm]; exact hB.tab, ?_, ?_, ?_, by rw [hm]; exact hB.frm, (hB.keep.trans k).mono (by decide)⟩
  · rw [hm, hB.y, e]
  · rw [hm, hB.flag, e]
  · rw [hm, hB.words, show w - j - 1 = w - (j + 1) by omega_arith]

/-- One word of the exponentiation. -/
theorem mrWord_ok (M : Mont) {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm b : Nat} {s₀ s : State}
    (hd : MrDims B Z w) (hE : ECtx s.mem B w c) (hodd : c % 2 = 1) (hc1 : 1 < c) {j : Nat} (hj : j < w)
    (hI : WordInv B Z w mi c bm b s₀ j s) :
    WP isa (seqs [
      .block (([.mov .rax (.mem (hdr kWords)), .alu .sub .rax (.imm 1), .store (hdr kWords) .rax] : List Instr) ++
        extBase aE .rdx ++ ([.mov .rax (.mem (hdr kWords)), .mov .rcx (.mem (ix .rdx .rax)), .store (hdr kV) .rcx,
        .mov32 .rcx (.imm 16), .store (hdr kBits) .rcx] : List Instr)),
      .loop (seqs (mrWin M.mm)) .ne,
      .block [.mov .rax (.mem (hdr kWords)), .alu .test .rax (.reg .rax)]]) s fun t =>
      t.zf = some (decide (j + 1 = w)) ∧ WordInv B Z w mi c bm b s₀ (j + 1) t := by
  have hW : (wordE s.mem B w j).toNat = mrE c / 2 ^ (64 * (w - j - 1)) % 2 ^ 64 := by
    rw [← hE.e]; exact word_of_wv s.mem B (slot w aE) w (by omega_arith)
  simp only [seqs]
  refine WP.seq (WP.mono (wordStart_ok hd hj hI) fun s₁ hB0 => ?_)
  exact WP.seq (WP.mono (mrWins_ok M hd hodd hc1 (by omega_arith) (by omega_arith)
    hW hB0) fun s₂ hB => wordEnd_ok hd hj hB)

end VG.Proof.RsaKeyGen.X86_64

end

end

/-!
# A candidate on x86-64: Miller–Rabin's exponentiation

`mrExpLoop_ok`: from `y = 1` and the table, the windows of all the words of
`E` and the three squarings after them: the flag of `wEnd`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 VG.Proof.RsaKeyGen

/-- The start of the exponentiation: `kWords := w`, the flag clear. -/
theorem expStart_ok {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm b : Nat} {s : State}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm) (hT : TabOK s.mem B w c b)
    (hY : wv s.mem B (slot w aY) w = 2 ^ (64 * w) % c) :
    WP isa (.block [.mov .rax (.mem (hdr sW)), .store (hdr kWords) .rax, .mov32 .rax (.imm 0), .store (hdr kFlag) .rax])
      s (WordInv B Z w mi c bm b s 0) := by
  have hg := hc.good
  have hZ := hd.z
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  have hs : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8 := fun i hi =>
    hg.scr.st (by have := hdr_lt_slot w 8 hi; omega_arith)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = (s.mem.writeW (off B (8 * kWords))
      (BitVec.ofNat 64 w)).writeW (off B (8 * kFlag)) (mask false)) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hs kWords (by decide), hs kFlag (by decide), hg.hdr.hw]
    rfl) rfl) fun s₁ ⟨hm₁, k₁⟩ => ?_
  have hf₁ : Frm B (expRanges w) s.mem s₁.mem := by
    rw [hm₁]
    exact (Frm.of_outside (writeW_outside _ B _ (d := 8 * kWords) (by unfold kWords kT1 sFn; omega_arith))
      (expRanges_hdr w (Or.inl rfl))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kFlag)
        (by unfold kFlag kPlen sFn; omega_arith)) (expRanges_hdr w (Or.inr (Or.inr (Or.inr rfl)))))
  have hs₁ := hg.scr.congr k₁.2.2
  refine ⟨hc.of_exp hd hf₁ hs₁ ((k₁.gpr (by decide)).trans hg.rdi), hT.of_low hf₁ (expRanges_low w)
    (by have := hd.w128; omega_arith), ?_, ?_, ?_, hf₁, k₁.mono (by decide)⟩
  · rw [hm₁, hdrStore_wv _ _ _ (by decide) (by decide) (by omega_arith), hdrStore_wv _ _ _ (by decide) (by decide) (by omega_arith),
      hY, Nat.mul_zero]
    simp only [wRun, Nat.one_mul]
  · rw [hm₁, word_writeW_self, Nat.mul_zero]; rfl
  · rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self, Nat.sub_zero]

/-- `mrLast j` as a squaring of `wEnd`. -/
theorem mrLast_wsq (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm : Nat} {st : Nat × Bool}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm) (hE : ECtx s.mem B w c) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hY : wv s.mem B (slot w aY) w = st.1 * 2 ^ (64 * w) % c) (hP : word s.mem B (8 * kFlag) = mask st.2)
    {j : Nat} (hj : 1 ≤ j ∧ j ≤ 3) :
    WP isa (seqs (mrLast M.mm j)) s fun t =>
      MrCtx t B Z w mi c bm ∧ ECtx t.mem B w c ∧
      wv t.mem B (slot w aY) w = (wSq c (decide (j < mrSig c)) st).1 * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kFlag) = mask (wSq c (decide (j < mrSig c)) st).2 ∧
      Frm B (sqRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.good.scr.nowrap
  refine WP.mono (mrLast_ok M hd hc hE hodd hc1 hY hP hj) fun t ⟨hct, hyt, hft, hfr, kt⟩ =>
    ⟨hct, hE.of_low hfr (fun r hr => winRanges_low w r (by
      simp only [sqRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [winRanges, List.mem_cons, List.not_mem_nil, or_false]
      rcases hr with rfl | rfl | rfl | rfl <;> simp)) (by have := aE_fits hd; have := hd.z; omega_arith),
      hyt, by rw [hft, Bool.and_comm]; rfl, hfr, kt⟩

theorem mrExpLoop_eq (mul : Nat → Nat → Nat → Prog isa) : mrExpLoop mul =
    ([.block [.mov .rax (.mem (hdr sW)), .store (hdr kWords) .rax, .mov32 .rax (.imm 0), .store (hdr kFlag) .rax],
      .loop (seqs [
        .block (([.mov .rax (.mem (hdr kWords)), .alu .sub .rax (.imm 1), .store (hdr kWords) .rax] : List Instr) ++
          extBase aE .rdx ++ ([.mov .rax (.mem (hdr kWords)), .mov .rcx (.mem (ix .rdx .rax)), .store (hdr kV) .rcx,
          .mov32 .rcx (.imm 16), .store (hdr kBits) .rcx] : List Instr)),
        .loop (seqs (mrWin mul)) .ne,
        .block [.mov .rax (.mem (hdr kWords)), .alu .test .rax (.reg .rax)]]) .ne] : List (Prog isa)) ++
    (mrLast mul 1 ++ (mrLast mul 2 ++ mrLast mul 3)) := by
  simp only [mrExpLoop, List.append_assoc]

/-- The exponentiation: from `y = 1` (`R mod c` in `aY`) and the table, the
flag of `wEnd` over the windows of `E`. -/
theorem mrExpLoop_ok (M : Mont) {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm b : Nat} {s : State}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm) (hT : TabOK s.mem B w c b) (hE : ECtx s.mem B w c)
    (hodd : c % 2 = 1) (hc1 : 1 < c) (hY : wv s.mem B (slot w aY) w = 2 ^ (64 * w) % c) :
    WP isa (seqs (mrExpLoop M.mm)) s fun t => MrCtx t B Z w mi c bm ∧ ECtx t.mem B w c ∧
      word t.mem B (8 * kFlag) = mask (wEnd c (wRun c b (mrE c) (16 * w) (16 * w))).2 ∧
      Frm B (expRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hw4 := hd.w4
  have hn := hc.good.scr.nowrap
  have hEn : B.toNat + slot w aE + 8 * (w + 1) ≤ 2 ^ 64 := by have := aE_fits hd; have := hd.z; omega_arith
  rw [mrExpLoop_eq]
  refine wp_seqs_append (by simp) (by simp [mrLast]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (expStart_ok hd hc hT hY) fun s₁ hI0 => ?_)
  refine WP.mono (wp_upto (a := 0) (N := w) (by omega_arith) (WordInv B Z w mi c bm b s)
    (fun j _ hj t hI => mrWord_ok M hd (hE.of_low hI.frm (expRanges_low w) hEn) hodd hc1 hj hI)
    (fun t hI => hI) hI0) fun s₂ hI => ?_
  have hE₂ : ECtx s₂.mem B w c := hE.of_low hI.frm (expRanges_low w) hEn
  generalize hst : wRun c b (mrE c) (16 * w) (16 * w) = st
  have hY₂ : wv s₂.mem B (slot w aY) w = st.1 * 2 ^ (64 * w) % c := by rw [← hst]; exact hI.y
  have hP₂ : word s₂.mem B (8 * kFlag) = mask st.2 := by rw [← hst]; exact hI.flag
  refine wp_seqs_append (by simp [mrLast]) (by simp [mrLast]) (WP.mono (mrLast_wsq M hd hI.ctx hE₂ hodd hc1 hY₂ hP₂
    (j := 1) (by decide)) fun s₃ ⟨hc₃, hE₃, hY₃, hP₃, hf₃, k₃⟩ => ?_)
  refine wp_seqs_append (by simp [mrLast]) (by simp [mrLast]) (WP.mono (mrLast_wsq M hd hc₃ hE₃ hodd hc1 hY₃ hP₃
    (j := 2) (by decide)) fun s₄ ⟨hc₄, hE₄, hY₄, hP₄, hf₄, k₄⟩ => ?_)
  refine WP.mono (mrLast_wsq M hd hc₄ hE₄ hodd hc1 hY₄ hP₄ (j := 3) (by decide))
    fun t ⟨hct, hEt, _, hPt, hft, kt⟩ => ⟨hct, hEt, hPt, ?_, ?_⟩
  · exact ((hI.frm.trans (hf₃.mono (sqRanges_sub w))).trans (hf₄.mono (sqRanges_sub w))).trans
      (hft.mono (sqRanges_sub w))
  · exact (((hI.keep.trans k₃).trans k₄).trans kt).mono (by decide)

end VG.Proof.RsaKeyGen.X86_64
