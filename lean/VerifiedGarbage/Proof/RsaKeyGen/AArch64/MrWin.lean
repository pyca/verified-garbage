module
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSq

import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSelW
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrBit
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.CrtExp
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# A candidate on AArch64: one window of Miller–Rabin's exponentiation

`TabOK`: the table `T_j = b^j R mod c`. `mrWin_ok`: from `y R mod c` in
`aY`, the flag and the digit `d` at the top of `kV`, the window of
`Proof/RsaKeyGen/MrWindow.lean` (`wWin`), `kV` shifted left by 4 and
`x3 := kBits := kBits − 1`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Rsa (slot_lt)
open VG.Impl.Bignum.Public (aN aAcc aTmp aXm aY sCnt)

/-- The table of the witness `b`: entry `j` (the array `aT0 + j`) is
`b^j R mod c`. -/
def TabOK (m : Mem) (B : Addr) (w c b : Nat) : Prop :=
  ∀ j < 16, wv m B (slot w (aT0 + j)) w = Spec.Rsa.powMod b j c * 2 ^ (64 * w) % c

/-- The table survives changes below it. -/
theorem TabOK.of_low {m m' : Mem} {B : Addr} {Z w c b : Nat} {rs : List (Nat × Nat)} (h : TabOK m B w c b)
    (hf : Frm B rs m m') (hl : ∀ r ∈ rs, r.1 + r.2 ≤ slot w aT0) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hn : B.toNat + Z ≤ 2 ^ 64) : TabOK m' B w c b := fun j hj => by
  have := VG.Proof.Bignum.slot_mono w (show aT0 ≤ aT0 + j by omega)
  have := tab_fits hEZ hj
  rw [hf.wv_eq (fun r hr => Or.inr (by have := hl r hr; omega)) (by omega)]
  exact h j hj

/-- `ECtx` survives changes below the table. -/
theorem ECtx.of_low {m m' : Mem} {B : Addr} {Z w c : Nat} {rs : List (Nat × Nat)} (h : ECtx m B w c)
    (hf : Frm B rs m m') (hl : ∀ r ∈ rs, r.1 + r.2 ≤ slot w aT0) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hn : B.toNat + Z ≤ 2 ^ 64) : ECtx m' B w c :=
  h.of_frm hf (fun r hr => Or.inr (by have := hl r hr; have := VG.Proof.Bignum.slot_mono w (show aT0 ≤ aE by decide); omega))
    (by omega)

/-- What a window changes. -/
def winRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2)), (slot w aXm, 8 * (w + 2)),
    (8 * kG, 8), (8 * kFlag, 8), (8 * kV, 8), (8 * kBits, 8)]

/-- `winRanges`'s ranges, in the header and in the arrays. -/
theorem winRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w [(8, 8), (184, 8), (208, 8), (240, 8)]
    [(2, 1), (3, 1), (6, 1), (5, 1)] (winRanges w) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false,
    winRanges, Public.sCnt, Public.aAcc, Public.aTmp, Public.aXm, Public.aY, aAcc, aTmp, aXm, aY, kT0, sFn, sCnt, kG, kV, kBits, kFlag, kPlen, kT2] at hr
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
theorem midRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w [(8, 8)]
    [(2, 1), (3, 1), (6, 1), (5, 1)] (midRanges w) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false,
    midRanges, Public.aAcc, Public.aTmp, Public.aXm, Public.aY, aAcc, aTmp, aXm, aY, kG] at hr
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

theorem winRanges_low (w : Nat) : ∀ r ∈ winRanges w, r.1 + r.2 ≤ slot w aT0 := by
  simp only [winRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [slot, hdrBytes, aT0, aAcc, aTmp, aY, aXm, kG, kFlag, kPlen, kV, kT0, sCnt, kBits, kT2, sFn] <;> omega

theorem winRanges_mut (w : Nat) : ∀ r ∈ winRanges w, KMut r := by unfold winRanges; w_mut

/-- `MrCtx` survives changes within a window's ranges. -/
theorem MrCtx.of_win {s t : State} {B : Addr} {Z w c bm : Nat} {rs : List (Nat × Nat)}
    (hc : MrCtx s B Z w c bm) (hf : Frm B rs s.mem t.mem) (hs : ∀ r ∈ rs, r ∈ winRanges w)
    {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : MrCtx t B Z w c bm :=
  hc.of_frm (hf.mono hs) (winRanges_mut w) k hr (by unfold winRanges; w_disj) (by unfold winRanges; w_disj)
    (by unfold winRanges; w_disj) (by unfold winRanges; w_disj) (by unfold winRanges; w_disj)

theorem sqRanges_win (w : Nat) : ∀ r ∈ sqRanges w, r ∈ winRanges w := by
  simp only [sqRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp [winRanges]

theorem mrSq_wsq (M : Mont) {s : State} {B : Addr} {Z w c bm : Nat} {st : Nat × Bool} (hw128 : w ≤ 128)
    (hc : MrCtx s B Z w c bm) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hY : wv s.mem B (slot w aY) w = st.1 * 2 ^ (64 * w) % c) (hP : word s.mem B (8 * kFlag) = mask st.2) :
    WP isa (seqs (mrSq M.mm)) s fun t =>
      MrCtx t B Z w c bm ∧ wv t.mem B (slot w aY) w = (wSq c true st).1 * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kFlag) = mask (wSq c true st).2 ∧ Frm B (sqRanges w) s.mem t.mem ∧ Keep mmRegs s t :=
  mrSq_ok M hw128 hc hodd hc1 hY hP

/-- Four squarings. -/
theorem sq4_ok (M : Mont) {s : State} {B : Addr} {Z w c bm : Nat} {st : Nat × Bool} (hw128 : w ≤ 128)
    (hc : MrCtx s B Z w c bm) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hY : wv s.mem B (slot w aY) w = st.1 * 2 ^ (64 * w) % c) (hP : word s.mem B (8 * kFlag) = mask st.2) :
    WP isa (seqs (mrSq M.mm ++ (mrSq M.mm ++ (mrSq M.mm ++ mrSq M.mm)))) s fun t =>
      MrCtx t B Z w c bm ∧
      wv t.mem B (slot w aY) w = (wSq c true (wSq c true (wSq c true (wSq c true st)))).1 * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kFlag) = mask (wSq c true (wSq c true (wSq c true (wSq c true st)))).2 ∧
      Frm B (sqRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  refine wp_seqs_append (by simp [mrSq]) (by simp [mrSq]) (WP.mono (mrSq_wsq M hw128 hc hodd hc1 hY hP)
    fun s₁ ⟨hc₁, hY₁, hP₁, hf₁, k₁⟩ => ?_)
  refine wp_seqs_append (by simp [mrSq]) (by simp [mrSq]) (WP.mono (mrSq_wsq M hw128 hc₁ hodd hc1 hY₁ hP₁)
    fun s₂ ⟨hc₂, hY₂, hP₂, hf₂, k₂⟩ => ?_)
  refine wp_seqs_append (by simp [mrSq]) (by simp [mrSq]) (WP.mono (mrSq_wsq M hw128 hc₂ hodd hc1 hY₂ hP₂)
    fun s₃ ⟨hc₃, hY₃, hP₃, hf₃, k₃⟩ => ?_)
  exact WP.mono (mrSq_wsq M hw128 hc₃ hodd hc1 hY₃ hP₃) fun t ⟨hct, hYt, hPt, hft, kt⟩ =>
    ⟨hct, hYt, hPt, ((hf₁.trans hf₂).trans hf₃).trans hft, (((k₁.trans k₂).trans k₃).trans kt).mono (by decide)⟩

/-- The window's flag. -/
theorem win_flag (P e1 em nz : Bool) :
    mask P &&& (mask nz ^^^ (BitVec.setWidth 64 0#16 - 1#64)) ||| (mask e1 ||| mask em) &&& mask nz =
      mask (if nz then e1 || em else P) := by
  cases P <;> cases e1 <;> cases em <;> cases nz <;> decide

theorem top_nibble (V : BitVec 64) : (V >>> 60).toNat < 16 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := V.isLt
  omega

theorem top_nibble_eq (V : BitVec 64) : V >>> 60 = BitVec.ofNat 64 (V >>> 60).toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The window's last block. -/
def winTail : List Instr :=
  [ldh .x3 kV, .lsr .x .x3 .x3 60, movi .x4 1, .subs .x .x3 .x3 .x4, movi .x7 0, .subImm .x .x8 .x7 1,
    .csel .x .x6 .x8 .x7, ldh .x5 kG, .logic .orr .x .x15 .x15 .x5, .logic .and .x .x15 .x15 .x6,
    .logic .eor .x .x6 .x6 .x8, ldh .x4 kFlag, .logic .and .x .x4 .x4 .x6, .logic .orr .x .x4 .x4 .x15,
    sth .x4 kFlag, ldh .x3 kV, .lsl .x .x3 .x3 4, sth .x3 kV, ldh .x3 kBits, .subImm .x .x3 .x3 1, sth .x3 kBits]

theorem mrWin_eq (mul : Nat → Nat → Nat → Prog isa) : mrWin mul =
    mrSq mul ++ (mrSq mul ++ (mrSq mul ++ mrSq mul)) ++
      (([.block [ldh .x3 kV, .lsr .x .x3 .x3 60, sth .x3 kG]] : List (Prog isa)) ++
        (mrSel ++ (([mul aY aY aXm] : List (Prog isa)) ++ (eqMask aRm1 ++
          (([.block [sth .x15 kG]] : List (Prog isa)) ++ (eqMask aR1 ++
            ([.block winTail] : List (Prog isa)))))))) := by
  simp only [mrWin, winTail, List.append_assoc]

/-- The flag, `kV` and `kBits`. -/
theorem winTail_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    {V : BitVec 64} {e1 em P : Bool} {n : Nat} (hV : word s.mem B (8 * kV) = V)
    (hG : word s.mem B (8 * kG) = mask em) (h15 : s.gpr .x15 = mask e1)
    (hP : word s.mem B (8 * kFlag) = mask P) (hnb : word s.mem B (8 * kBits) = BitVec.ofNat 64 n) (hn1 : 1 ≤ n)
    (hn' : n < 2 ^ 64) :
    WP isa (.block winTail) s fun t =>
      (t.mem = ((s.mem.writeW (off B (8 * kFlag)) (mask (if !decide (V >>> 60 = 0) then e1 || em else P))).writeW
        (off B (8 * kV)) (V <<< 4)).writeW (off B (8 * kBits)) (BitVec.ofNat 64 (n - 1)) ∧
        t.gpr .x3 = BitVec.ofNat 64 (n - 1)) ∧
      Keep [.x3, .x4, .x5, .x6, .x7, .x8, .x15] s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  have hst : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8 := fun i hi => hs.st (by omega)
  refine WP.keep [.x3, .x4, .x5, .x6, .x7, .x8, .x15] ?_ (by decide) (by decide) (by decide +kernel)
  brun [winTail, h.x0, hdr_enc (show kV < 32 by decide), hdr_enc (show kG < 32 by decide),
    hdr_enc (show kFlag < 32 by decide), hdr_enc (show kBits < 32 by decide), hl kV (by decide), hl kG (by decide),
    hl kFlag (by decide), hl kBits (by decide), hst kV (by decide), hst kFlag (by decide), hst kBits (by decide), hV,
    hG, hP, h15, subs_one_c, csel_mask_pos, win_flag,
    fun X => (hdrStore_hdr s.mem B X (show kFlag < 32 by decide) (show kV < 32 by decide) (by decide)).trans hV,
    fun X Y => (hdrStore_hdr _ B Y (show kV < 32 by decide) (show kBits < 32 by decide) (by decide)).trans
      ((hdrStore_hdr s.mem B X (show kFlag < 32 by decide) (show kBits < 32 by decide) (by decide)).trans hnb),
    ofNat64_pred hn1 hn']

/-- The digit into `kG`. -/
theorem winDigit_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {V : BitVec 64}
    (hV : word s.mem B (8 * kV) = V) :
    WP isa (.block [ldh .x3 kV, .lsr .x .x3 .x3 60, sth .x3 kG]) s fun t =>
      t.mem = s.mem.writeW (off B (8 * kG)) (BitVec.ofNat 64 (V >>> 60).toNat) ∧ Keep [.x3] s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  refine WP.keep [.x3] ?_ (by decide) (by decide) (by decide +kernel)
  rw [← top_nibble_eq]
  brun [h.x0, hdr_enc (show kV < 32 by decide), hdr_enc (show kG < 32 by decide),
    hs.ld (d := 8 * kV) (by simp only [kV, kT0, sCnt, sFn]; omega), hs.st (d := 8 * kG) (by simp only [kG]; omega), hV]

/-- One window. -/
theorem mrWin_ok (M : Mont) {s : State} {B : Addr} {Z w c bm b y : Nat} {P : Bool} (hw128 : w ≤ 128)
    (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hc : MrCtx s B Z w c bm) (hT : TabOK s.mem B w c b) (hodd : c % 2 = 1)
    (hc1 : 1 < c) (hY : wv s.mem B (slot w aY) w = y * 2 ^ (64 * w) % c) (hP : word s.mem B (8 * kFlag) = mask P)
    {V : BitVec 64} {n : Nat} (hV : word s.mem B (8 * kV) = V)
    (hnb : word s.mem B (8 * kBits) = BitVec.ofNat 64 n) (hn1 : 1 ≤ n) (hn' : n < 2 ^ 64) :
    WP isa (seqs (mrWin M.mm)) s fun t =>
      MrCtx t B Z w c bm ∧ TabOK t.mem B w c b ∧
      wv t.mem B (slot w aY) w = (wWin c b (V >>> 60).toNat (y, P)).1 * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kFlag) = mask (wWin c b (V >>> 60).toNat (y, P)).2 ∧
      word t.mem B (8 * kV) = V <<< 4 ∧ word t.mem B (8 * kBits) = BitVec.ofNat 64 (n - 1) ∧
      t.gpr .x3 = BitVec.ofNat 64 (n - 1) ∧ Frm B (winRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.ws.scr.nowrap
  have hZ := hc.ws.hZ
  have hw2 := hc.ws.w1
  have hw' : w < 2 ^ 31 := by omega_arith
  have hR : Nat.Coprime (2 ^ (64 * w)) c := VG.Proof.Bignum.coprime_pow2 hodd _
  have hc0 : 0 < c := by omega_arith
  have hZ8 := hc.good.2
  have hYl : slot w aY + 8 * (w + 2) ≤ slot w aT0 := slot_lt (show aY < aT0 by decide)
  have hXl : slot w aXm + 8 * (w + 2) ≤ slot w aT0 := slot_lt (show aXm < aT0 by decide)
  have hT0 : slot w aT0 ≤ Z := by have := VG.Proof.Bignum.slot_mono w (show aT0 ≤ aE by decide); omega_arith
  generalize hd' : (V >>> 60).toNat = d
  have hd16 : d < 16 := hd' ▸ top_nibble V
  rw [mrWin_eq]
  -- The four squarings.
  refine wp_seqs_append (by simp [mrSq]) (by simp) (WP.mono (sq4_ok M hw128 hc hodd hc1 (st := (y, P)) hY hP)
    fun s₁ ⟨hc₁, hY₁, hP₁, hf₁, k₁⟩ => ?_)
  generalize hs4 : wSq c true (wSq c true (wSq c true (wSq c true (y, P)))) = s4 at hY₁ hP₁
  have hf₁w := hf₁.mono (sqRanges_win w)
  have hlo₁ : ∀ i, i = kV ∨ i = kBits → word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    rcases hi with rfl | rfl
    · exact hf₁.word_eq (by unfold sqRanges; w_disj) (by simp only [kV, kT0, sCnt, sFn]; omega_arith)
    · exact hf₁.word_eq (by unfold sqRanges; w_disj) (by simp only [kBits, kT2, sFn]; omega_arith)
  have hT₁ : TabOK s₁.mem B w c b := hT.of_low hf₁w (winRanges_low w) hEZ hn
  -- The digit into `kG`.
  refine wp_seqs_append (by simp) (by simp [mrSel]) ?_
  simp only [seqs]
  refine WP.mono (winDigit_ok hc₁.ws (V := V) (by rw [hlo₁ kV (Or.inl rfl)]; exact hV)) fun s₂ ⟨hm₂, k₂⟩ => ?_
  rw [hd'] at hm₂
  have hf₂ : Frm B [(8 * kG, 8)] s₁.mem s₂.mem := by
    rw [hm₂]; exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kG) (by decide)) (by simp)
  have hc₂ := hc₁.of_win hf₂ (by simp [winRanges]) k₂ (by decide)
  -- `T_d` into `aXm`.
  refine wp_seqs_append (by simp [mrSel]) (by simp) ?_
  refine WP.mono (mrSel_ok hc₂.ws hEZ hd16 (by rw [hm₂, word_writeW_self])) fun s₃ ⟨hv₃, ho₃, hs₃, k₃⟩ => ?_
  have hf₃ : Frm B [(slot w aXm, 8 * (w + 2))] s₂.mem s₃.mem :=
    Frm.of_outside (ho₃.mono (o' := slot w aXm) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_arith)) (by simp)
  have hf13 : Frm B (midRanges w) s₁.mem s₃.mem :=
    (hf₂.mono (by simp [midRanges])).trans (hf₃.mono (by simp [midRanges]))
  have hc₃ : MrCtx s₃ B Z w c bm := hc₁.of_win hf13 (midRanges_sub w) (k₂.trans k₃) (by decide)
  have hT₂ : TabOK s₂.mem B w c b := hT₁.of_low (hf₂.mono (by simp [winRanges])) (winRanges_low w) hEZ hn
  have hX₃ : wv s₃.mem B (slot w aXm) w = Spec.Rsa.powMod b d c * 2 ^ (64 * w) % c := by rw [hv₃]; exact hT₂ d hd16
  have hY₃ : wv s₃.mem B (slot w aY) w = s4.1 * 2 ^ (64 * w) % c := by
    rw [hf₃.wv_eq (d := slot w aY) (k := w) (by w_disj) (by omega_arith),
      hf₂.wv_eq (d := slot w aY) (k := w) (by w_disj) (by omega_arith)]; exact hY₁
  -- `y := y T_d`.
  refine wp_seqs_append (by simp) (by simp [eqMask, eqA]) ?_
  have hg₃ := hc₃.good
  refine WP.mono (M.mm_ok hg₃.1 hg₃.2 hw2 hw' (o := aY) (a := aY) (b := aXm) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hc₃.inv
    (by rw [hX₃, hc₃.n]; exact Nat.mod_lt _ hc0)) fun s₄ ⟨_, hlt₄, hy₄, ha₄, k₄⟩ => ?_
  rw [hc₃.n] at hlt₄ hy₄
  rw [hY₃, hX₃] at hy₄
  have hY₄ : wv s₄.mem B (slot w aY) w = s4.1 * Spec.Rsa.powMod b d c % c * 2 ^ (64 * w) % c :=
    mont_val hR hlt₄ hy₄ rfl rfl
  have hf₄ : Frm B (midRanges w) s₃.mem s₄.mem := Frm.of_arrays ha₄ (by simp [midRanges])
  have hc₄ : MrCtx s₄ B Z w c bm := hc₃.of_win hf₄ (midRanges_sub w) k₄ (by decide)
  have hlt2 : s4.1 * Spec.Rsa.powMod b d c % c < c := Nat.mod_lt _ hc0
  -- `y = c − 1` into `kG`, `y = 1` into `x15`.
  refine wp_seqs_append (by simp [eqMask, eqA]) (by simp) ?_
  refine WP.mono (eqMask_ok hc₄.ws (j := aRm1) (by decide)) fun s₅ ⟨h15₅, hm₅, k₅⟩ => ?_
  rw [hY₄, hc₄.rm1, decide_eq_decide.mpr (mont_eq_m1 hR hc1 hlt2)] at h15₅
  refine wp_seqs_append (by simp) (by simp [eqMask, eqA]) ?_
  have h0₅ : s₅.gpr .x0 = B := (k₅.gpr .x0 (by decide)).trans hc₄.ws.x0
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s₅.mem.writeW (off B (8 * kG)) (s₅.gpr .x15)) (by
    brun [h0₅, hdr_enc (show kG < 32 by decide), (hc₄.ws.scr.congr k₅.wr).st (d := 8 * kG)
      (by have := hdr_lt_slot w 8 (show kG < 32 by decide); omega_arith)]) (by decide) (by decide) (by decide +kernel))
    fun s₆ ⟨hm₆, k₆⟩ => ?_
  rw [h15₅, hm₅] at hm₆
  have hf₆ : Frm B (midRanges w) s₄.mem s₆.mem := by
    rw [hm₆]; exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kG) (by decide)) (by simp [midRanges])
  have hc₆ := hc₄.of_win hf₆ (midRanges_sub w) (k₅.trans k₆) (by decide)
  have hY₆ : wv s₆.mem B (slot w aY) w = wv s₄.mem B (slot w aY) w := by
    rw [hm₆, hdrStore_wv _ _ _ (by decide) (by decide) (by omega_arith)]
  refine wp_seqs_append (by simp [eqMask, eqA]) (by simp) ?_
  refine WP.mono (eqMask_ok hc₆.ws (j := aR1) (by decide)) fun s₇ ⟨h15₇, hm₇, k₇⟩ => ?_
  rw [hY₆, hY₄, hc₆.r1, decide_eq_decide.mpr (mont_eq_one hR hc1 hlt2)] at h15₇
  have hf₇ : Frm B (midRanges w) s₆.mem s₇.mem := fun x _ => by rw [hm₇]
  have hc₇ := hc₆.of_win hf₇ (midRanges_sub w) k₇ (by decide)
  -- The header words after `y := y T_d`.
  have hf17 : Frm B (midRanges w) s₁.mem s₇.mem := ((hf13.trans hf₄).trans hf₆).trans hf₇
  have hh₇ : ∀ i, i = kV ∨ i = kBits ∨ i = kFlag → word s₇.mem B (8 * i) = word s₁.mem B (8 * i) := fun i hi => by
    have h32 : i < 32 := by rcases hi with rfl | rfl | rfl <;> decide
    refine hf17.word_eq ?_ (by omega_arith)
    unfold midRanges
    rcases hi with rfl | rfl | rfl <;> w_disj
  have hG₇ : word s₇.mem B (8 * kG) = mask (decide (s4.1 * Spec.Rsa.powMod b d c % c = c - 1)) := by
    rw [hm₇, hm₆, word_writeW_self]
  -- The flag, `kV` and `kBits`.
  have hV₇ : word s₇.mem B (8 * kV) = V := by rw [hh₇ kV (Or.inl rfl), hlo₁ kV (Or.inl rfl)]; exact hV
  have hB₇ : word s₇.mem B (8 * kBits) = BitVec.ofNat 64 n := by
    rw [hh₇ kBits (Or.inr (Or.inl rfl)), hlo₁ kBits (Or.inr rfl)]; exact hnb
  have hP₇ : word s₇.mem B (8 * kFlag) = mask s4.2 := by rw [hh₇ kFlag (Or.inr (Or.inr rfl))]; exact hP₁
  refine WP.mono (winTail_ok hc₇.ws hV₇ hG₇ h15₇ hP₇ hB₇ hn1 hn') fun t ht => ?_
  obtain ⟨⟨hm, h3⟩, k⟩ := ht
  have hft : Frm B (winRanges w) s₁.mem t.mem := by
    refine (hf17.mono (midRanges_sub w)).trans ?_
    rw [hm]
    refine ((Frm.of_outside (writeW_outside _ B _ (d := 8 * kFlag) (by decide))
      (by simp [winRanges])).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kV) (by decide))
      (by simp [winRanges]))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kBits) (by decide))
        (by simp [winRanges]))
  have hz : (!decide (V >>> 60 = 0)) = !decide (d = 0) := by
    rw [← hd']
    congr 1
  have hw1 : (wWin c b d (y, P)).1 = s4.1 * Spec.Rsa.powMod b d c % c := by simp only [wWin, hs4]
  have hw2 : (wWin c b d (y, P)).2 = (if !decide (d = 0) then
      decide (s4.1 * Spec.Rsa.powMod b d c % c = 1) || decide (s4.1 * Spec.Rsa.powMod b d c % c = c - 1)
      else s4.2) := by
    simp only [wWin, hs4]
    by_cases h0 : d = 0 <;> simp [h0]
  refine ⟨hc₁.of_win hft (fun _ h => h) (((((k₂.trans k₃).trans k₄).trans k₅).trans k₆).trans k₇ |>.trans k)
      (by decide), hT₁.of_low hft (winRanges_low w) hEZ hn, ?_, ?_, ?_, ?_, h3,
    hf₁w.trans hft, ((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans k |>.mono (by decide)⟩
  · rw [hm, hdrStore_wv _ _ _ (by decide) (by decide) (by omega_arith), hdrStore_wv _ _ _ (by decide) (by decide) (by omega_arith),
      hdrStore_wv _ _ _ (by decide) (by decide) (by omega_arith), hm₇, hY₆, hY₄, hw1]
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
      word_writeW_self, hw2, hz]
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hm, word_writeW_self]

end VG.Proof.RsaKeyGen.AArch64
