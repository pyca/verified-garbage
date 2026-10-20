module
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSq

import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSelW
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSel
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.CrtExp
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.RsaKeyGen.Gcd

/-!
# A candidate on x86-64: one window of Miller–Rabin's exponentiation

`TabOK`: the table `T_j = b^j R mod c`. `mrWin_ok`: from `y R mod c` in
`aY`, the flag and the digit `d` at the top of `kV`, the window of
`Proof/RsaKeyGen/MrWindow.lean` (`wWin`), `kV` shifted left by 4 and `kBits`
decremented.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 VG.Proof.RsaKeyGen

/-- The table of the witness `b`: entry `j` (the array `8 + j`) is
`b^j R mod c`. -/
def TabOK (m : Mem) (B : Addr) (w c b : Nat) : Prop :=
  ∀ j < 16, wv m B (slot w (8 + j)) w = Spec.Rsa.powMod b j c * 2 ^ (64 * w) % c

theorem slot_lt24 (w : Nat) {j : Nat} (hj : j ≤ 24) : slot w j ≤ 256 + 192 * (w + 2) := by
  have := slot_mono w hj
  have e : slot w 24 = 256 + 192 * (w + 2) := by unfold slot hdrBytes; omega
  omega

theorem slot_lt27 (w : Nat) {j : Nat} (hj : j ≤ 27) : slot w j ≤ 256 + 216 * (w + 2) := by
  have := slot_mono w hj
  have e : slot w 27 = 256 + 216 * (w + 2) := by unfold slot hdrBytes; omega
  omega

/-- The table survives changes below it. -/
theorem TabOK.of_low {m m' : Mem} {B : Addr} {w c b : Nat} {rs : List (Nat × Nat)} (h : TabOK m B w c b)
    (hf : Frm B rs m m') (hl : ∀ r ∈ rs, r.1 + r.2 ≤ slot w 8) (hw : w < 2 ^ 31) : TabOK m' B w c b := fun j hj => by
  have := slot_mono w (show 8 ≤ 8 + j by omega)
  have := slot_lt24 w (show 8 + j + 1 ≤ 24 by omega)
  have := slot_succ w (8 + j)
  rw [hf.wv_eq (fun r hr => Or.inr (by have := hl r hr; omega)) (by omega)]
  exact h j hj

/-- `ECtx` survives changes below the table. -/
theorem ECtx.of_low {m m' : Mem} {B : Addr} {w c : Nat} {rs : List (Nat × Nat)} (h : ECtx m B w c)
    (hf : Frm B rs m m') (hl : ∀ r ∈ rs, r.1 + r.2 ≤ slot w 8) (hn : B.toNat + slot w aE + 8 * (w + 1) ≤ 2 ^ 64) :
    ECtx m' B w c :=
  h.of_frm hf (fun r hr => Or.inr (by have := hl r hr; have := slot_mono w (show 8 ≤ aE by decide); omega)) hn

/-- What a window changes. -/
def winRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2)), (slot w aXm, 8 * (w + 2)),
    (8 * kG, 8), (8 * kFlag, 8), (8 * kV, 8), (8 * kBits, 8)]

/-- `winRanges`'s ranges, in the header and in the arrays. -/
theorem winRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w [(248, 8), (176, 8), (208, 8), (224, 8)]
    [(2, 1), (3, 1), (6, 1), (5, 1)] (winRanges w) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false,
    winRanges, Public.aAcc, Public.aTmp, Public.aXm, Public.aY, aAcc, aTmp, aXm, aY, kT0, sFn, kG, kV, kBits, kFlag, kPlen, kT2] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

/-- What a window changes before its flag. -/
def midRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2)), (slot w aXm, 8 * (w + 2)),
    (8 * kG, 8)]

/-- `midRanges`'s ranges, in the header and in the arrays. -/
theorem midRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w [(248, 8)]
    [(2, 1), (3, 1), (6, 1), (5, 1)] (midRanges w) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false,
    midRanges, Public.aAcc, Public.aTmp, Public.aXm, Public.aY, aAcc, aTmp, aXm, aY, sFn, kG] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact .inr ⟨(2, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(3, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(6, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(5, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inl (by decide)

theorem midRanges_sub (w : Nat) : ∀ r ∈ midRanges w, r ∈ winRanges w := by
  simp only [midRanges, winRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;> simp

theorem winRanges_low (w : Nat) : ∀ r ∈ winRanges w, r.1 + r.2 ≤ slot w 8 := by
  have h1 := slot_le (w := w) (show aAcc < 8 by decide)
  have h2 := slot_le (w := w) (show aTmp < 8 by decide)
  have h3 := slot_le (w := w) (show aY < 8 by decide)
  have h4 := slot_le (w := w) (show aXm < 8 by decide)
  have h5 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  simp only [winRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [kG, kFlag, kPlen, kV, kT0, kBits, kT2, sFn] at * <;> omega

/-- `MrCtx` survives changes within a window's ranges. -/
theorem MrCtx.of_win {s t : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm : Nat}
    (hc : MrCtx s B Z w mi c bm) (hd : MrDims B Z w) (hf : Frm B (winRanges w) s.mem t.mem) (hs : Scr t B Z)
    (hdi : t.gpr .rdi = B) : MrCtx t B Z w mi c bm :=
  hc.of_frm hd hf hs hdi (by simp only [winRanges]; rng_disj) (by simp only [winRanges]; rng_disj)
    (by simp only [winRanges]; rng_disj) (by simp only [winRanges]; rng_disj) (by simp only [winRanges]; rng_disj)

theorem mrSq_wsq (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm : Nat} {st : Nat × Bool}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hY : wv s.mem B (slot w aY) w = st.1 * 2 ^ (64 * w) % c) (hP : word s.mem B (8 * kFlag) = mask st.2) :
    WP isa (seqs (mrSq M.mm)) s fun t =>
      MrCtx t B Z w mi c bm ∧ wv t.mem B (slot w aY) w = (wSq c true st).1 * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kFlag) = mask (wSq c true st).2 ∧ Frm B (sqRanges w) s.mem t.mem ∧ Keep mmRegs s t :=
  mrSq_ok M hd hc hodd hc1 hY hP

/-- Four squarings. -/
theorem sq4_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm : Nat} {st : Nat × Bool}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hY : wv s.mem B (slot w aY) w = st.1 * 2 ^ (64 * w) % c) (hP : word s.mem B (8 * kFlag) = mask st.2) :
    WP isa (seqs (mrSq M.mm ++ (mrSq M.mm ++ (mrSq M.mm ++ mrSq M.mm)))) s fun t =>
      MrCtx t B Z w mi c bm ∧
      wv t.mem B (slot w aY) w = (wSq c true (wSq c true (wSq c true (wSq c true st)))).1 * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kFlag) = mask (wSq c true (wSq c true (wSq c true (wSq c true st)))).2 ∧
      Frm B (sqRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  refine wp_seqs_append (by simp [mrSq]) (by simp [mrSq]) (WP.mono (mrSq_wsq M hd hc hodd hc1 hY hP)
    fun s₁ ⟨hc₁, hY₁, hP₁, hf₁, k₁⟩ => ?_)
  refine wp_seqs_append (by simp [mrSq]) (by simp [mrSq]) (WP.mono (mrSq_wsq M hd hc₁ hodd hc1 hY₁ hP₁)
    fun s₂ ⟨hc₂, hY₂, hP₂, hf₂, k₂⟩ => ?_)
  refine wp_seqs_append (by simp [mrSq]) (by simp [mrSq]) (WP.mono (mrSq_wsq M hd hc₂ hodd hc1 hY₂ hP₂)
    fun s₃ ⟨hc₃, hY₃, hP₃, hf₃, k₃⟩ => ?_)
  exact WP.mono (mrSq_wsq M hd hc₃ hodd hc1 hY₃ hP₃) fun t ⟨hct, hYt, hPt, hft, kt⟩ =>
    ⟨hct, hYt, hPt, ((hf₁.trans hf₂).trans hf₃).trans hft, (((k₁.trans k₂).trans k₃).trans kt).mono (by decide)⟩

/-- The window's flag. -/
theorem win_flag (P e1 em z : Bool) :
    mask P &&& mask z ||| (mask e1 ||| mask em) &&& (mask z ^^^ BitVec.signExtend 64 (BitVec.ofInt 32 (-1))) =
      mask (if z then P else e1 || em) := by
  cases P <;> cases e1 <;> cases em <;> cases z <;> decide

theorem top_nibble (V : BitVec 64) : (V >>> 60).toNat < 16 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := V.isLt
  omega

theorem mrWin_eq (mul : Nat → Nat → Nat → Prog isa) : mrWin mul =
    mrSq mul ++ (mrSq mul ++ (mrSq mul ++ mrSq mul)) ++
      (([.block [.mov .rax (.mem (hdr kV)), .shift .shr .rax 60, .store (hdr kG) .rax]] : List (Prog isa)) ++
        (mrSel ++ ([mul aY aY aXm] ++ (eqMask aRm1 ++
          (([.block [.store (hdr kG) .rbp]] : List (Prog isa)) ++ (eqMask aR1 ++
            ([.block [.mov .rax (.mem (hdr kV)), .shift .shr .rax 60, .alu .cmp .rax (.imm 1),
              .alu .sbb .r15 (.reg .r15), .mov .rdx (.mem (hdr kG)), .alu .or .rbp (.reg .rdx),
              .mov .rax (.mem (hdr kFlag)), .alu .and .rax (.reg .r15), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1))),
              .alu .and .rbp (.reg .r15), .alu .or .rax (.reg .rbp), .store (hdr kFlag) .rax,
              .mov .rax (.mem (hdr kV)), .shift .shl .rax 4, .store (hdr kV) .rax,
              .mov .rax (.mem (hdr kBits)), .alu .sub .rax (.imm 1), .store (hdr kBits) .rax]] :
              List (Prog isa)))))))) := by
  simp only [mrWin, List.append_assoc]

/-- One window. -/
theorem mrWin_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm b y : Nat} {P : Bool}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm) (hT : TabOK s.mem B w c b) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hY : wv s.mem B (slot w aY) w = y * 2 ^ (64 * w) % c) (hP : word s.mem B (8 * kFlag) = mask P)
    {V : BitVec 64} {n : Nat} (hV : word s.mem B (8 * kV) = V)
    (hnb : word s.mem B (8 * kBits) = BitVec.ofNat 64 n) (hn1 : 1 ≤ n) (hn' : n < 2 ^ 64) :
    WP isa (seqs (mrWin M.mm)) s fun t =>
      MrCtx t B Z w mi c bm ∧ TabOK t.mem B w c b ∧
      wv t.mem B (slot w aY) w = (wWin c b (V >>> 60).toNat (y, P)).1 * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kFlag) = mask (wWin c b (V >>> 60).toNat (y, P)).2 ∧
      word t.mem B (8 * kV) = V <<< 4 ∧ word t.mem B (8 * kBits) = BitVec.ofNat 64 (n - 1) ∧
      t.zf = some (decide (n - 1 = 0)) ∧ Frm B (winRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hg := hc.good
  have hZ := hd.z
  have hXZ := hd.x
  have hw := hd.w4
  have hw' : w < 2 ^ 30 := by have := hd.w128; omega_arith
  have hn := hg.scr.nowrap
  have hR : Nat.Coprime (2 ^ (64 * w)) c := VG.Proof.Bignum.coprime_pow2 hodd _
  have hc0 : 0 < c := by omega_arith
  have hTZ : slot w 8 + tabBytes w ≤ Z := by
    have := slot_mono w (show 24 ≤ aRm1 by decide); unfold tabBytes slot at *; omega_arith
  generalize hd' : (V >>> 60).toNat = d
  have hd16 : d < 16 := hd' ▸ top_nibble V
  rw [mrWin_eq]
  -- The four squarings.
  refine wp_seqs_append (by simp [mrSq]) (by simp) (WP.mono (sq4_ok M hd hc hodd hc1 (st := (y, P)) hY hP)
    fun s₁ ⟨hc₁, hY₁, hP₁, hf₁, k₁⟩ => ?_)
  generalize hs4 : wSq c true (wSq c true (wSq c true (wSq c true (y, P)))) = s4 at hY₁ hP₁
  have hg₁ := hc₁.good
  have hlo₁ : ∀ i, i = kV ∨ i = kBits → word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    rcases hi with rfl | rfl
    · exact hf₁.word_eq (by simp only [sqRanges]; rng_disj) (by unfold kV kT0 sFn; omega_arith)
    · exact hf₁.word_eq (by simp only [sqRanges]; rng_disj) (by unfold kBits kT2 sFn; omega_arith)
  have hT₁ : TabOK s₁.mem B w c b := hT.of_low hf₁ (fun r hr => winRanges_low w r (by
    simp only [sqRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [winRanges, List.mem_cons, List.not_mem_nil, or_false]
    rcases hr with rfl | rfl | rfl | rfl <;> simp)) (by omega_arith)
  -- The digit into `kG`.
  have hl : ∀ (t : State), Scr t B Z → ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun t hs i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  have hst : ∀ (t : State), Scr t B Z → ∀ i < 32, InRegions t.wr (off B (8 * i)) 8 := fun t hs i hi =>
    hs.st (by have := hdr_lt_slot w 8 hi; omega_arith)
  refine wp_seqs_append (by simp) (by simp [mrSel]) ?_
  simp only [seqs]
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s₁.mem.writeW (off B (8 * kG)) (BitVec.ofNat 64 d)) (by
    xrun [State.ea, hdr, hg₁.rdi, hdrOff, hl s₁ hg₁.scr kV (by decide), hst s₁ hg₁.scr kG (by decide),
      hlo₁ kV (Or.inl rfl), hV]
    rw [← hd', BitVec.ofNat_toNat, BitVec.setWidth_eq]) rfl) fun s₂ ⟨hm₂, k₂⟩ => ?_
  have hf₂ : Frm B [(8 * kG, 8)] s₁.mem s₂.mem := by
    rw [hm₂]; exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kG) (by unfold kG sFn; omega_arith)) (by simp)
  have hg₂ : Good s₂ B Z w mi := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi,
    Hdr.of_frm hg₁.hdr hf₂ (VG.Proof.RsaKeyGen.HdrShapeC.geD rfl rfl)⟩
  -- `T_d` into `aXm`.
  refine wp_seqs_append (by simp [mrSel]) (by simp) ?_
  refine WP.mono (mrSel_ok hg₂ hTZ (by omega_arith) hw' hd16 (by rw [hm₂, word_writeW_self])) fun s₃ ⟨hv₃, ho₃, k₃⟩ => ?_
  have hf₃ : Frm B [(slot w aXm, 8 * (w + 2))] s₂.mem s₃.mem := Frm.of_outside ho₃ (by simp)
  have hg₃ : Good s₃ B Z w mi := ⟨hg₂.scr.congr k₃.2.2, (k₃.gpr (by decide)).trans hg₂.rdi,
    Hdr.of_frm hg₂.hdr hf₃ (VG.Proof.RsaKeyGen.HdrShapeC.geD rfl rfl)⟩
  have hf13 : Frm B (midRanges w) s₁.mem s₃.mem := (hf₂.mono (by simp [midRanges])).trans (hf₃.mono (by simp [midRanges]))
  have hc₃ : MrCtx s₃ B Z w mi c bm := hc₁.of_win hd (hf13.mono (midRanges_sub w)) hg₃.scr hg₃.rdi
  have hT₂ : TabOK s₂.mem B w c b := hT₁.of_low hf₂ (VG.Proof.RsaKeyGen.SlotShapeC.leD rfl rfl) (by omega_arith)
  have hX₃ : wv s₃.mem B (slot w aXm) w = Spec.Rsa.powMod b d c * 2 ^ (64 * w) % c := by rw [hv₃]; exact hT₂ d hd16
  have hY₃ : wv s₃.mem B (slot w aY) w = s4.1 * 2 ^ (64 * w) % c := by
    have := slot_le (w := w) (show aY < 8 by decide)
    rw [hf₃.wv_eq (d := slot w aY) (k := w) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (by omega_arith),
      hf₂.wv_eq (d := slot w aY) (k := w) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (by omega_arith)]; exact hY₁
  -- `y := y T_d`.
  refine wp_seqs_append (by simp) (by simp [eqMask]) ?_
  refine WP.mono (M.mm_ok hg₃ hZ (by omega_arith) (by omega_arith) (o := aY) (a := aY) (b := aXm) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hc₃.inv
    (by rw [hX₃, hc₃.n]; exact Nat.mod_lt _ hc0)) fun s₄ ⟨hg₄, hlt₄, hy₄, ha₄, k₄⟩ => ?_
  rw [hc₃.n] at hlt₄ hy₄
  rw [hY₃, hX₃] at hy₄
  have hY₄ : wv s₄.mem B (slot w aY) w = s4.1 * Spec.Rsa.powMod b d c % c * 2 ^ (64 * w) % c :=
    mont_val hR hlt₄ hy₄ rfl rfl
  have hf₄ : Frm B (midRanges w) s₃.mem s₄.mem := Frm.of_arrays ha₄ (by simp [midRanges])
  have hc₄ : MrCtx s₄ B Z w mi c bm := hc₃.of_win hd (hf₄.mono (midRanges_sub w)) hg₄.scr hg₄.rdi
  have hlt2 : s4.1 * Spec.Rsa.powMod b d c % c < c := Nat.mod_lt _ hc0
  -- `y = c − 1` into `kG`, `y = 1` into `rbp`.
  refine wp_seqs_append (by simp [eqMask]) (by simp) ?_
  refine WP.mono (eqMask_ok hg₄ hZ (by omega_arith) (by omega_arith) (j := aRm1) (by decide) hXZ)
    fun s₅ ⟨hbp₅, hm₅, k₅⟩ => ?_
  have em1 : decide (s4.1 * Spec.Rsa.powMod b d c % c * 2 ^ (64 * w) % c = c - 2 ^ (64 * w) % c) =
      decide (s4.1 * Spec.Rsa.powMod b d c % c = c - 1) := decide_eq_decide.mpr (mont_eq_m1 hR hc1 hlt2)
  rw [hY₄, hc₄.rm1, em1] at hbp₅
  have hdi₅ : s₅.gpr .rdi = B := (k₅.gpr (by decide)).trans hg₄.rdi
  have hs₅ := hg₄.scr.congr k₅.2.2
  refine wp_seqs_append (by simp) (by simp [eqMask]) ?_
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s₅.mem.writeW (off B (8 * kG)) (s₅.gpr .rbp)) (by
    xrun [State.ea, hdr, hdi₅, hdrOff, hst s₅ hs₅ kG (by decide)]) rfl) fun s₆ ⟨hm₆, k₆⟩ => ?_
  have hg₆ : Good s₆ B Z w mi := ⟨hs₅.congr k₆.2.2, (k₆.gpr (by decide)).trans hdi₅,
    by rw [hm₆, hm₅]; exact hg₄.hdr.store (by decide) (by decide) _⟩
  have hY₆ : wv s₆.mem B (slot w aY) w = wv s₄.mem B (slot w aY) w := by
    rw [hm₆, hdrStore_wv _ _ _ (by decide) (by decide) (by omega_arith), hm₅]
  have hR1₆ : wv s₆.mem B (slot w aR1) w = wv s₄.mem B (slot w aR1) w := by
    rw [hm₆, (writeW_outside _ B _ (d := 8 * kG) (by unfold kG sFn; omega_arith)).wv
      (Or.inr (by unfold slot kG sFn aR1 hdrBytes; omega_arith)) (by unfold slot aR1 aRm1 at *; omega_arith), hm₅]
  refine wp_seqs_append (by simp [eqMask]) (by simp) ?_
  refine WP.mono (eqMask_ok hg₆ hZ (by omega_arith) (by omega_arith) (j := aR1) (by decide)
    (by unfold slot aR1 aRm1 at *; omega_arith)) fun s₇ ⟨hbp₇, hm₇, k₇⟩ => ?_
  have e1 : decide (s4.1 * Spec.Rsa.powMod b d c % c * 2 ^ (64 * w) % c = 2 ^ (64 * w) % c) =
      decide (s4.1 * Spec.Rsa.powMod b d c % c = 1) := decide_eq_decide.mpr (mont_eq_one hR hc1 hlt2)
  rw [hY₆, hR1₆, hY₄, hc₄.r1, e1] at hbp₇
  have hg₇ : Good s₇ B Z w mi := ⟨hg₆.scr.congr k₇.2.2, (k₇.gpr (by decide)).trans hg₆.rdi, by rw [hm₇]; exact hg₆.hdr⟩
  -- The header words after `y := y T_d`.
  have hf17 : Frm B (midRanges w) s₁.mem s₇.mem := by
    refine (hf13.trans hf₄).trans ?_
    rw [hm₇, hm₆, hm₅]
    exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kG) (by unfold kG sFn; omega_arith)) (by simp [midRanges])
  have hh₇ : ∀ i, i = kV ∨ i = kBits ∨ i = kFlag → word s₇.mem B (8 * i) = word s₁.mem B (8 * i) := fun i hi => by
    have h32 : i < 32 := by rcases hi with rfl | rfl | rfl <;> decide
    refine hf17.word_eq ?_ (by omega_arith)
    simp only [midRanges]
    rcases hi with rfl | rfl | rfl <;> rng_disj
  have hG₇ : word s₇.mem B (8 * kG) = mask (decide (s4.1 * Spec.Rsa.powMod b d c % c = c - 1)) := by
    rw [hm₇, hm₆, word_writeW_self, ← hbp₅]
  -- The flag, `kV` and `kBits`.
  have hV₇ : word s₇.mem B (8 * kV) = V := by rw [hh₇ kV (Or.inl rfl), hlo₁ kV (Or.inl rfl)]; exact hV
  have hB₇ : word s₇.mem B (8 * kBits) = BitVec.ofNat 64 n := by
    rw [hh₇ kBits (Or.inr (Or.inl rfl)), hlo₁ kBits (Or.inr rfl)]; exact hnb
  have hP₇ : word s₇.mem B (8 * kFlag) = mask s4.2 := by rw [hh₇ kFlag (Or.inr (Or.inr rfl))]; exact hP₁
  have hz : decide ((V >>> 60).toNat < (1 : BitVec 64).toNat) = decide (d = 0) := by
    rw [hd', show (1 : BitVec 64).toNat = 1 from rfl]; exact decide_eq_decide.mpr (by omega)
  refine WP.mono (WP.keep [.rax, .rdx, .rbp, .r15] (Q := fun t => t.mem = ((s₇.mem.writeW (off B (8 * kFlag))
      (mask (if decide (d = 0) then s4.2 else decide (s4.1 * Spec.Rsa.powMod b d c % c = 1) ||
        decide (s4.1 * Spec.Rsa.powMod b d c % c = c - 1)))).writeW (off B (8 * kV)) (V <<< 4)).writeW
        (off B (8 * kBits)) (BitVec.ofNat 64 (n - 1)) ∧ t.zf = some (decide (n - 1 = 0))) (by
    xrun [State.ea, hdr, hg₇.rdi, hdrOff, hl s₇ hg₇.scr kV (by decide), hl s₇ hg₇.scr kG (by decide),
      hl s₇ hg₇.scr kFlag (by decide), hl s₇ hg₇.scr kBits (by decide), hst s₇ hg₇.scr kV (by decide),
      hst s₇ hg₇.scr kFlag (by decide), hst s₇ hg₇.scr kBits (by decide), hV₇, hG₇, hP₇, hbp₇,
      fun X => (hdrStore_hdr s₇.mem B X (show kFlag < 32 by decide) (show kV < 32 by decide) (by decide)).trans hV₇,
      fun X Y => (hdrStore_hdr _ B Y (show kV < 32 by decide) (show kBits < 32 by decide) (by decide)).trans
        ((hdrStore_hdr s₇.mem B X (show kFlag < 32 by decide) (show kBits < 32 by decide) (by decide)).trans hB₇),
      ofNat64_pred hn1 hn', ofNat64_beq_zero (show n - 1 < 2 ^ 64 by omega_arith), hz, mask_def', win_flag]
    done) rfl) fun t ⟨⟨hm, hzf⟩, k⟩ => ?_
  have hft : Frm B (winRanges w) s₁.mem t.mem := by
    refine (hf17.mono (midRanges_sub w)).trans ?_
    rw [hm]
    refine ((Frm.of_outside (writeW_outside _ B _ (d := 8 * kFlag) (by unfold kFlag kPlen sFn; omega_arith))
      (by simp [winRanges])).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kV) (by unfold kV kT0 sFn; omega_arith))
      (by simp [winRanges]))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kBits)
        (by unfold kBits kT2 sFn; omega_arith)) (by simp [winRanges]))
  have hgt : Good t B Z w mi := ⟨hg₇.scr.congr k.2.2, (k.gpr (by decide)).trans hg₇.rdi,
    Hdr.of_frm hg₁.hdr hft (by simp only [winRanges]; rng_disj)⟩
  have hw1 : (wWin c b d (y, P)).1 = s4.1 * Spec.Rsa.powMod b d c % c := by simp only [wWin, hs4]
  have hw2 : (wWin c b d (y, P)).2 = (if decide (d = 0) then s4.2 else
      decide (s4.1 * Spec.Rsa.powMod b d c % c = 1) || decide (s4.1 * Spec.Rsa.powMod b d c % c = c - 1)) := by
    simp only [wWin, hs4, decide_eq_true_eq]
  refine ⟨hc₁.of_win hd hft hgt.scr hgt.rdi, hT₁.of_low hft (winRanges_low w) (by omega_arith), ?_, ?_, ?_, ?_, hzf,
    (hf₁.mono fun r hr => by
      simp only [sqRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [winRanges, List.mem_cons, List.not_mem_nil, or_false]
      rcases hr with rfl | rfl | rfl | rfl <;> simp).trans hft,
    ((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans k |>.mono (by decide)⟩
  · rw [hm, hdrStore_wv _ _ _ (by decide) (by decide) (by omega_arith), hdrStore_wv _ _ _ (by decide) (by decide) (by omega_arith),
      hdrStore_wv _ _ _ (by decide) (by decide) (by omega_arith), hm₇, hY₆, hY₄, hw1]
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      word_writeW_self, hw2]
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hm, word_writeW_self]

end VG.Proof.RsaKeyGen.X86_64
