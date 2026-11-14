module

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Stages
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.TwoStages
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.QDiv
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Prod
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.WordLoops
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyReduce
import VerifiedGarbage.Proof.Rsa.X86_64.WordInit
import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Bignum.LongDivision
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on x86-64: the divisions

`divA` (`a = g x`, `m = ⌊a / n⌋`, `r = a mod n` and whether `m < n`) and
`divB` (`b - 1 = ⌊(n - r) / (m + 1)⌋` and whether the remainder is zero), by
`qDiv` once divisor and dividend are normalized.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.Rsa.RecoverDet

/-- What `divA` changes: `e`'s length, the mask, the count, `sC` and the wide
arrays from 6 on. -/
def DaP (w y : Nat) : Prop :=
  (160 ≤ y ∧ y < 168) ∨ (176 ≤ y ∧ y < 184) ∨ (200 ≤ y ∧ y < 208) ∨ (240 ≤ y ∧ y < 248) ∨
    (slot w 6 ≤ y ∧ y < slot w 16)

macro "da_omega" : tactic =>
  `(tactic| (simp only [DaP, DOk, Bignum.slot, hdrBytes, Impl.Bignum.X86_64.Public.sMask,
    Impl.Bignum.X86_64.Public.sElen, sFn, sC, sCt, qQ, qR, qT, qV, qA, qD]; omega_arith))

/-- `divA`'s first part (wide): `a = g x` into wide arrays 10 and 11. -/
theorem divA1_ok {s : State} {B : Addr} {Z w v : Nat} (h : Ws s B Z w) (hwv : w = 2 * v + 2) (hv1 : 1 ≤ v)
    {G X : Nat} (hG : wv s.mem B (slot w 6) w = G) (hGv : G < 2 ^ (64 * v)) (hX : wv s.mem B (slot w 2) w = X) :
    WP isa (seqs (([.block setEl, copyA 8 6, copyA 9 2] : List (Prog isa)) ++ Recover.prod)) s fun t =>
      wv t.mem B (slot w 10) w = X * G % 2 ^ (64 * w) ∧
      word t.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 (4 * w - 8) ∧ mw t.mem B = mw s.mem B ∧
      FrmP B (DaP w) s.mem t.mem ∧ Keep mmRegs s t ∧ Ws t B Z w := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hZ := h.hZ
  have hZ' : 256 + 16 * (8 * (w + 2)) ≤ Z := hZ
  have hw1 := h.w1
  have hw2 := h.w2
  have hw4 : (4 * w - 8 + 7) / 8 = v := by omega_arith
  simp only [List.cons_append, List.nil_append, seqs]
  refine WP.seq (WP.mono (setEl_ok h) fun t₁ ⟨m1, k1⟩ => ?_)
  have h₁ := h.congrW m1 (by da_omega) (by decide) k1 (by simp)
  have o1 : Outside B (8 * Impl.Bignum.X86_64.Public.sElen) 8 s.mem t₁.mem := by
    rw [m1]; exact writeW_outside _ _ _ (by da_omega)
  refine WP.seq (WP.mono (copyA_ok h₁ (o := 8) (a := 6) (by decide) (by decide) (by decide)) fun t₂ ⟨v2, o2, k2⟩ => ?_)
  have h₂ := h₁.congrO o2 (by da_omega) k2 (by simp)
  refine WP.seq (WP.mono (copyA_ok h₂ (o := 9) (a := 2) (by decide) (by decide) (by decide)) fun t₃ ⟨v3, o3, k3⟩ => ?_)
  have h₃ := h₂.congrO o3 (by da_omega) k3 (by simp)
  have G₃ : wv t₃.mem B (slot w 8) w = G := by
    rw [o3.wv (by da_omega) (by da_omega), v2, o1.wv (by da_omega) (by da_omega), hG]
  have X₃ : wv t₃.mem B (slot w 9) w = X := by
    rw [v3, o2.wv (by da_omega) (by da_omega), o1.wv (by da_omega) (by da_omega), hX]
  have el₃ : word t₃.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 (4 * w - 8) := by
    rw [o3.word (by da_omega) (by da_omega), o2.word (by da_omega) (by da_omega), m1, word_writeW_self]
  refine WP.mono (prod_ok h₃ el₃ (by omega_arith) (by omega_arith)
    (by rw [hw4]; show wv t₃.mem B (slot w 8) w < _; rw [G₃]; exact hGv)) fun t ⟨v4, o4, k4⟩ => ?_
  simp only [Recover.aE, Recover.aD, Recover.aM] at v4 o4
  rw [G₃, X₃] at v4
  have fr : ∀ {o n : Nat} {m m' : Mem}, Outside B o n m m' → (∀ y, o ≤ y → y < o + n → DaP w y) →
      FrmP B (DaP w) m m' := fun ho hP => FrmP.of_out ho hP
  refine ⟨by rw [← v4, show 2 * (w + 2) = w + (w + 4) by omega_arith]; exact wv_low_mod,
    by rw [o4.word (by da_omega) (by da_omega), el₃],
    by unfold mw; rw [o4.word (by da_omega) (by da_omega), o3.word (by da_omega) (by da_omega),
      o2.word (by da_omega) (by da_omega), o1.word (by da_omega) (by da_omega)],
    (((fr o1 fun y => by da_omega).trans (fr o2 fun y => by da_omega)).trans (fr o3 fun y => by da_omega)).trans
      (fr o4 fun y => by da_omega),
    (((k1.trans k2).trans k3).trans k4).mono (by simp [mmRegs]), h₃.congrO o4 (by da_omega) k4 (by simp)⟩

/-- A number below `2^(64 (k + 1))`: its word `k` is its top. -/
theorem word_top {m : Mem} {B : Addr} {d n k : Nat} (hk : k < n) (h : wv m B d n < 2 ^ (64 * (k + 1))) :
    (word m B (d + 8 * k)).toNat = wv m B d n / 2 ^ (64 * k) := by
  rw [wv_div_pow _ _ _ (Nat.le_of_lt hk)]
  have hlt : wv m B (d + 8 * k) (n - k) < 2 ^ (64 * 1) := by
    rw [← wv_div_pow _ _ _ (Nat.le_of_lt hk)]
    exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (by
      rw [← Nat.pow_add, show 64 * 1 + 64 * k = 64 * (k + 1) by omega_arith]; exact h)
  rw [← Key.wv_low (k := 1) (by omega_arith) hlt]
  simp [wv]

/-- `divA`'s second part (wide, `h = w / 2 - 2`): `z = sC`, the leading zeros of
`n`'s word `h - 1`; `[8] := n 2^z` and `[9] := a 2^z mod 2^(64 w)`. -/
theorem divA2_ok {s : State} {B : Addr} {Z w h : Nat} (hw : Ws s B Z w) (hwh : w = 2 * h + 4) (h8 : 8 ≤ h) {N A : Nat}
    (hN : wv s.mem B (slot w 0) w = N) (hA : wv s.mem B (slot w 10) w = A) :
    WP isa (seqs [.block (clzTop 0), zeroA 8, shlZ 0 8, zeroA 9, shlZ 10 9]) s fun t =>
      wv t.mem B (slot w 8) w = N * 2 ^ (63 - Nat.log2 (word s.mem B (slot w 0 + 8 * (h - 1))).toNat) %
        2 ^ (64 * w) ∧
      wv t.mem B (slot w 9) w = A * 2 ^ (63 - Nat.log2 (word s.mem B (slot w 0 + 8 * (h - 1))).toNat) %
        2 ^ (64 * w) ∧
      word t.mem B (8 * sC) = BitVec.ofNat 64 (63 - Nat.log2 (word s.mem B (slot w 0 + 8 * (h - 1))).toNat) ∧
      mw t.mem B = mw s.mem B ∧
      word t.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) ∧
      FrmP B (DaP w) s.mem t.mem ∧ Keep mmRegs s t ∧ Ws t B Z w := by
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  have hZ := hw.hZ
  have hZ' : 256 + 16 * (8 * (w + 2)) ≤ Z := hZ
  have hw2 := hw.w2
  generalize hz : 63 - Nat.log2 (word s.mem B (slot w 0 + 8 * (h - 1))).toNat = z
  have hz64 : z < 64 := by omega_arith
  simp only [seqs]
  refine WP.seq (WP.mono (clzTop_ok hw (j := 0) (by decide) (by omega_arith)) fun t₁ ⟨m1, k1⟩ => ?_)
  rw [show w / 2 - 2 - 1 = h - 1 by omega_arith, hz] at m1
  have h₁ := hw.congrW m1 (by da_omega) (by decide) k1 (by simp)
  have o1 : Outside B (8 * sC) 8 s.mem t₁.mem := by rw [m1]; exact writeW_outside _ _ _ (by da_omega)
  have c₁ : word t₁.mem B (8 * sC) = BitVec.ofNat 64 z := by rw [m1, word_writeW_self]
  refine WP.seq (WP.mono (zeroA_ok h₁ (j := 8) (by decide)) fun t₂ ⟨_, o2, k2⟩ => ?_)
  have h₂ := h₁.congrO o2 (by da_omega) k2 (by simp)
  refine WP.seq (WP.mono (shlClP_ok h₂ false (j := 0) (t := 8) (by simp) (by simp)
    (by simp only [shlN, Bool.false_eq_true, ↓reduceIte]; da_omega) hz64
    (sC_pre h256 (by rw [o2.word (by da_omega) (by da_omega), c₁]))) fun t₃ ⟨v3, o3, k3⟩ => ?_)
  simp only [shlN, Bool.false_eq_true, ↓reduceIte] at v3 o3
  have h₃ := h₂.congrO o3 (by da_omega) k3 (by simp)
  refine WP.seq (WP.mono (zeroA_ok h₃ (j := 9) (by decide)) fun t₄ ⟨_, o4, k4⟩ => ?_)
  have h₄ := h₃.congrO o4 (by da_omega) k4 (by simp)
  refine WP.mono (shlClP_ok h₄ false (j := 10) (t := 9) (by simp) (by simp)
    (by simp only [shlN, Bool.false_eq_true, ↓reduceIte]; da_omega) hz64
    (sC_pre h256 (by rw [o4.word (by da_omega) (by da_omega), o3.word (by da_omega) (by da_omega),
      o2.word (by da_omega) (by da_omega), c₁]))) fun t ⟨v5, o5, k5⟩ => ?_
  simp only [shlN, Bool.false_eq_true, ↓reduceIte] at v5 o5
  have fr : ∀ {o n : Nat} {m m' : Mem}, Outside B o n m m' → (∀ y, o ≤ y → y < o + n → DaP w y) →
      FrmP B (DaP w) m m' := fun ho hP => FrmP.of_out ho hP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ((((k1.trans k2).trans k3).trans k4).trans k5).mono (by simp [mmRegs]),
    h₄.congrO o5 (by da_omega) k5 (by simp)⟩
  · rw [o5.wv (by da_omega) (by da_omega), o4.wv (by da_omega) (by da_omega), v3,
      o2.wv (by da_omega) (by da_omega), o1.wv (by da_omega) (by da_omega), hN]
  · rw [v5, o4.wv (by da_omega) (by da_omega), o3.wv (by da_omega) (by da_omega),
      o2.wv (by da_omega) (by da_omega), o1.wv (by da_omega) (by da_omega), hA]
  · rw [o5.word (by da_omega) (by da_omega), o4.word (by da_omega) (by da_omega), o3.word (by da_omega) (by da_omega),
      o2.word (by da_omega) (by da_omega), c₁]
  · unfold mw
    rw [o5.word (by da_omega) (by da_omega), o4.word (by da_omega) (by da_omega), o3.word (by da_omega) (by da_omega),
      o2.word (by da_omega) (by da_omega), o1.word (by da_omega) (by da_omega)]
  · rw [o5.word (by da_omega) (by da_omega), o4.word (by da_omega) (by da_omega), o3.word (by da_omega) (by da_omega),
      o2.word (by da_omega) (by da_omega), o1.word (by da_omega) (by da_omega)]
  · exact (((((fr o1 fun y => by da_omega).trans (fr o2 fun y => by da_omega)).trans (fr o3 fun y => by da_omega)).trans
      (fr o4 fun y => by da_omega)).trans (fr o5 fun y => by da_omega))

/-- `divA`'s last part (wide): `qDiv 3` of the dividend `A₂ = [9]` (its low
`2 h + 2` words) by `M = [8]` (its low `h`), `[6] := (A₂ mod M) / 2^z`,
`[7] := A₂ / M` and the mask and'ed with `A₂ / M < n`. -/
theorem divA3_ok {s : State} {B : Addr} {Z w h : Nat} (hw : Ws s B Z w) (hwh : w = 2 * h + 4) (h8 : 8 ≤ h)
    {N z : Nat} {c : Bool} (hN : wv s.mem B (slot w 0) w = N) (hz : word s.mem B (8 * sC) = BitVec.ofNat 64 z)
    (hz64 : z < 64) (hm : mw s.mem B = mask c)
    (hd : 2 ^ 63 ≤ (word s.mem B (slot w qD + 8 * (h - 1))).toNat) :
    WP isa (seqs (qDiv 3 ++ [zeroA 6, shrZ 12 6, subA 14 11 0, .block andNz, copyA 7 11])) s fun t =>
      wv t.mem B (slot w 7) w = wv s.mem B (slot w 9) (2 * h + 2) / wv s.mem B (slot w 8) h ∧
      wv t.mem B (slot w 6) w = wv s.mem B (slot w 9) (2 * h + 2) % wv s.mem B (slot w 8) h / 2 ^ z ∧
      mw t.mem B = mask (c && decide (wv s.mem B (slot w 9) (2 * h + 2) / wv s.mem B (slot w 8) h < N)) ∧
      word t.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) ∧
      FrmP B (DaP w) s.mem t.mem ∧ Keep mmRegs s t ∧ Ws t B Z w := by
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  have hZ := hw.hZ
  have hZ' : 256 + 16 * (8 * (w + 2)) ≤ Z := hZ
  have hw2 := hw.w2
  have L : QLay w h 3 := ⟨hwh, h8, by decide, by decide⟩
  generalize hA2 : wv s.mem B (slot w 9) (2 * h + 2) = A2
  generalize hM : wv s.mem B (slot w 8) h = M
  have hMpos : 0 < M := by
    rw [← hM]
    have e := wv_add s.mem B (slot w 8) (h - 1) 1
    rw [show h - 1 + 1 = h by omega_arith] at e
    have e1 : wv s.mem B (slot w 8 + 8 * (h - 1)) 1 = (word s.mem B (slot w qD + 8 * (h - 1))).toNat := by
      simp [wv, qD]
    rw [e1] at e
    have : 0 < 2 ^ (64 * (h - 1)) * (word s.mem B (slot w qD + 8 * (h - 1))).toNat :=
      Nat.mul_pos (Nat.two_pow_pos _) (by omega_arith)
    omega_arith
  have hMlt : M < 2 ^ (64 * h) := hM ▸ wv_lt _ _ _ _
  refine wp_seqs_append (by simp [qDiv]) (by simp) (WP.mono (qDiv_ok hw L hd) fun t₁ ⟨r1, q1, h₁, f1, k1⟩ => ?_)
  simp only [qR, qQ, qA, qD] at r1 q1 f1
  rw [show 2 * h + 3 - 1 = 2 * h + 2 by omega_arith, hA2, hM] at r1 q1
  simp only [seqs]
  have fq : FrmP B (DaP w) s.mem t₁.mem := FrmP.of_frm f1 (by
    simp only [qDivRs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨fun y h1 h2 => ?_, fun y h1 h2 => ?_, fun y h1 h2 => ?_, fun y h1 h2 => ?_, fun y h1 h2 => ?_⟩ <;>
      simp only [Bignum.slot, hdrBytes, qQ, qR, qT, qV, sCt, sFn] at h1 h2 <;> da_omega)
  have qs : ∀ d, d + 8 ≤ 256 → d + 8 ≤ 200 ∨ 208 ≤ d → ∀ r ∈ qDivRs w, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d := by
    intro d hd hd'
    simp only [qDivRs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> da_omega
  have hA2lt : A2 < 2 ^ (64 * w) := by
    rw [← hA2]; exact Nat.lt_of_lt_of_le (wv_lt _ _ _ _) (Nat.pow_le_pow_right (by decide) (by omega_arith))
  have R1 : wv t₁.mem B (slot w 12) w = A2 % M := by
    rw [Key.wv_low (k := w) (n := w + 2) (by omega_arith) (by
      rw [r1]; exact Nat.lt_of_lt_of_le (Nat.lt_trans (Nat.mod_lt _ hMpos) hMlt)
        (Nat.pow_le_pow_right (by decide) (by omega_arith))), r1]
  have Q1 : wv t₁.mem B (slot w 11) w = A2 / M := by
    rw [Key.wv_low (k := w) (n := w + 2) (by omega_arith) (by
      rw [q1]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hA2lt), q1]
  have z12 : word t₁.mem B (slot w 12 + 8 * w) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [word_top (n := w + 2) (by omega_arith) (by
      rw [r1]; exact Nat.lt_of_lt_of_le (Nat.lt_trans (Nat.mod_lt _ hMpos) hMlt)
        (Nat.pow_le_pow_right (by decide) (by omega_arith))), r1,
      Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (Nat.lt_trans (Nat.mod_lt _ hMpos) hMlt)
        (Nat.pow_le_pow_right (by decide) (by omega_arith)))]
    rfl
  have N₁ : wv t₁.mem B (slot w 0) w = N := by rw [fq.wv_eq (fun y => by da_omega) (by da_omega), hN]
  have c₁ : word t₁.mem B (8 * sC) = BitVec.ofNat 64 z := by
    rw [f1.word_eq (qs _ (by da_omega) (by da_omega)) (by da_omega), hz]
  have m₁ : mw t₁.mem B = mask c := by
    unfold mw at hm ⊢; rw [f1.word_eq (qs _ (by da_omega) (by da_omega)) (by da_omega), hm]
  refine WP.seq (WP.mono (zeroA_ok h₁ (j := 6) (by decide)) fun t₂ ⟨_, o2, k2⟩ => ?_)
  have h₂ := h₁.congrO o2 (by da_omega) k2 (by simp)
  refine WP.seq (WP.mono (shrClP_ok h₂ (j := 12) (t := 6) (by decide) (by decide) (by decide) hz64
    (sC_pre h256 (by rw [o2.word (by da_omega) (by da_omega), c₁]))
    (by rw [o2.word (by da_omega) (by da_omega), z12])) fun t₃ ⟨v3, o3, k3⟩ => ?_)
  rw [o2.wv (by da_omega) (by da_omega), R1] at v3
  have h₃ := h₂.congrO o3 (by da_omega) k3 (by simp)
  refine WP.seq (WP.mono (subA_ok h₃ (t := 14) (a := 11) (b := 0) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t₄ ⟨hb4, _, o4, k4⟩ => ?_)
  rw [o3.wv (by da_omega) (by da_omega), o2.wv (by da_omega) (by da_omega), Q1,
    o3.wv (by da_omega) (by da_omega), o2.wv (by da_omega) (by da_omega), N₁] at hb4
  have h₄ := h₃.congrO o4 (by da_omega) k4 (by simp)
  have m₄ : mw t₄.mem B = mask c := by
    unfold mw at m₁ ⊢
    rw [o4.word (by da_omega) (by da_omega), o3.word (by da_omega) (by da_omega), o2.word (by da_omega) (by da_omega), m₁]
  refine WP.seq (WP.mono (andNz_ok h₄ m₄ hb4) fun t₅ ⟨m5, k5⟩ => ?_)
  have h₅ := h₄.congrW m5 (by da_omega) (by decide) k5 (by simp)
  have o5 : Outside B (8 * Impl.Bignum.X86_64.Public.sMask) 8 t₄.mem t₅.mem := by
    rw [m5]; exact writeW_outside _ _ _ (by da_omega)
  refine WP.mono (copyA_ok h₅ (o := 7) (a := 11) (by decide) (by decide) (by decide)) fun t ⟨v6, o6, k6⟩ => ?_
  have fr : ∀ {o n : Nat} {m m' : Mem}, Outside B o n m m' → (∀ y, o ≤ y → y < o + n → DaP w y) →
      FrmP B (DaP w) m m' := fun ho hP => FrmP.of_out ho hP
  refine ⟨?_, ?_, ?_, ?_, ?_, (((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).mono (by simp [mmRegs]),
    h₅.congrO o6 (by da_omega) k6 (by simp)⟩
  · rw [v6, o5.wv (by da_omega) (by da_omega), o4.wv (by da_omega) (by da_omega), o3.wv (by da_omega) (by da_omega),
      o2.wv (by da_omega) (by da_omega), Q1]
  · rw [o6.wv (by da_omega) (by da_omega), o5.wv (by da_omega) (by da_omega), o4.wv (by da_omega) (by da_omega), v3]
  · unfold mw
    rw [o6.word (by da_omega) (by da_omega), m5, word_writeW_self]
  · rw [o6.word (by da_omega) (by da_omega), o5.word (by da_omega) (by da_omega), o4.word (by da_omega) (by da_omega),
      o3.word (by da_omega) (by da_omega), o2.word (by da_omega) (by da_omega),
      f1.word_eq (qs _ (by da_omega) (by da_omega)) (by da_omega)]
  · exact fq.trans ((((((fr o2 fun y => by da_omega).trans (fr o3 fun y => by da_omega)).trans
      (fr o4 fun y => by da_omega)).trans (fr o5 fun y => by da_omega)).trans (fr o6 fun y => by da_omega)))

/-- `divA`'s first two parts (wide): what its division needs, the divisor's top
bit set and `sC` the shift, below 64. -/
theorem divA12_ok {s : State} {B : Addr} {Z w h : Nat} (hw : Ws s B Z w) (hwh : w = 2 * h + 4) (h8 : 8 ≤ h)
    {N G X : Nat} (hN : wv s.mem B (slot w 0) w = N) (hNlo : 2 ^ (64 * (h - 1)) ≤ N)
    (hNhi : N < 2 ^ (64 * h)) (hG : wv s.mem B (slot w 6) w = G) (hGv : G < 2 ^ (64 * (h + 1)))
    (hX : wv s.mem B (slot w 2) w = X) :
    WP isa (seqs (([.block setEl, copyA 8 6, copyA 9 2] : List (Prog isa)) ++ Recover.prod ++
      ([.block (clzTop 0), zeroA 8, shlZ 0 8, zeroA 9, shlZ 10 9] : List (Prog isa)))) s fun t =>
      2 ^ 63 ≤ (word t.mem B (slot w qD + 8 * (h - 1))).toNat ∧
      (∃ z, z < 64 ∧ word t.mem B (8 * sC) = BitVec.ofNat 64 z) ∧
      word t.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 (4 * w - 8) ∧ mw t.mem B = mw s.mem B ∧ FrmP B (DaP w) s.mem t.mem ∧ Keep mmRegs s t ∧ Ws t B Z w := by
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  have hZ := hw.hZ
  have hZ' : 256 + 16 * (8 * (w + 2)) ≤ Z := hZ
  refine wp_seqs_append (by simp) (by simp) (WP.mono (divA1_ok hw (v := h + 1) (by omega_arith) (by omega_arith) hG
    hGv hX) fun t₁ ⟨a1, el1, mm1, f1, k1, h₁⟩ => ?_)
  have N₁ : wv t₁.mem B (slot w 0) w = N := by rw [f1.wv_eq (fun y => by da_omega) (by da_omega), hN]
  refine WP.mono (divA2_ok h₁ hwh h8 N₁ a1) fun t₂ ⟨d2, _, z2, mm2, el2, f2, k2, h₂⟩ => ?_
  have top0 : (word t₁.mem B (slot w 0 + 8 * (h - 1))).toNat = N / 2 ^ (64 * (h - 1)) := by
    rw [word_top (n := w) (by omega_arith) (by rw [N₁, show h - 1 + 1 = h by omega_arith]; exact hNhi), N₁]
  rw [top0] at d2 z2
  have nb := LongDivision.norm_bounds (K := h - 1) hNlo (by
    rw [← Nat.pow_add, show 64 * (h - 1) + 64 = 64 * h by omega_arith]; exact hNhi)
  generalize hz : 63 - Nat.log2 (N / 2 ^ (64 * (h - 1))) = z at d2 z2 nb
  have hz64 : z < 64 := by omega_arith
  have hPh : 2 ^ (64 * (h - 1)) * 2 ^ 64 = 2 ^ (64 * h) := by rw [← Nat.pow_add]; congr 1; omega_arith
  have hNz : N * 2 ^ z < 2 ^ (64 * h) := hPh ▸ nb.2
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hNz (Nat.pow_le_pow_right (by decide) (by omega_arith)))] at d2
  refine ⟨?_, ⟨z, hz64, z2⟩, el2.trans el1, mm2.trans mm1, f1.trans f2, (k1.trans k2).mono (by simp [mmRegs]), h₂⟩
  rw [show qD = 8 from rfl, word_top (n := w) (by omega_arith) (by
    rw [d2, show h - 1 + 1 = h by omega_arith]; exact hNz), d2]
  exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by rw [Nat.mul_comm]; exact nb.1)

/-- `divA` (wide, `w = 2 h + 4`): `a = g x mod 2^(64 w)` for `g` (wide array 6,
below `2^(64 (h + 1))`) and `x` (wide array 2); the mask and'ed with whether
`m = ⌊a / n⌋ < n`; where the mask was set and `a < n 2^(64 (h + 1))`, `m` in
wide array 7 and `r = a mod n` in wide array 6. -/
theorem divA_ok {s : State} {B : Addr} {Z w h : Nat} (hw : Ws s B Z w) (hwh : w = 2 * h + 4) (h8 : 8 ≤ h)
    {N G X : Nat} {c : Bool} (hN : wv s.mem B (slot w 0) w = N) (hNlo : 2 ^ (64 * (h - 1)) ≤ N)
    (hNhi : N < 2 ^ (64 * h)) (hG : wv s.mem B (slot w 6) w = G) (hGv : G < 2 ^ (64 * (h + 1)))
    (hX : wv s.mem B (slot w 2) w = X) (hm : mw s.mem B = mask c)
    (hA : c = true → X * G % 2 ^ (64 * w) < N * 2 ^ (64 * (h + 1))) :
    WP isa (seqs divA) s fun t =>
      mw t.mem B = mask (c && decide (X * G % 2 ^ (64 * w) / N < N)) ∧
      (c = true → wv t.mem B (slot w 7) w = X * G % 2 ^ (64 * w) / N ∧
        wv t.mem B (slot w 6) w = X * G % 2 ^ (64 * w) % N) ∧
      word t.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 (4 * w - 8) ∧
      FrmP B (DaP w) s.mem t.mem ∧ Keep mmRegs s t ∧ Ws t B Z w := by
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  have hZ := hw.hZ
  have hZ' : 256 + 16 * (8 * (w + 2)) ≤ Z := hZ
  generalize hAd : X * G % 2 ^ (64 * w) = A at hA
  unfold divA
  rw [show [.block setEl, copyA 8 6, copyA 9 2] ++ Recover.prod ++ [.block (clzTop 0), zeroA 8, shlZ 0 8, zeroA 9,
      shlZ 10 9] ++ qDiv 3 ++ [zeroA 6, shrZ 12 6, subA 14 11 0, .block andNz, copyA 7 11] =
    ([.block setEl, copyA 8 6, copyA 9 2] ++ Recover.prod) ++ ([.block (clzTop 0), zeroA 8, shlZ 0 8, zeroA 9,
      shlZ 10 9] ++ (qDiv 3 ++ [zeroA 6, shrZ 12 6, subA 14 11 0, .block andNz, copyA 7 11])) by
    simp only [List.append_assoc]]
  refine wp_seqs_append (by simp) (by simp) (WP.mono (divA1_ok hw (v := h + 1) (by omega_arith) (by omega_arith) hG
    hGv hX) fun t₁ ⟨a1, el1, mm1, f1, k1, h₁⟩ => ?_)
  rw [hAd] at a1
  have N₁ : wv t₁.mem B (slot w 0) w = N := by rw [f1.wv_eq (fun y => by da_omega) (by da_omega), hN]
  have m₁ : mw t₁.mem B = mask c := by rw [mm1, hm]
  refine wp_seqs_append (by simp) (by simp [qDiv]) (WP.mono (divA2_ok h₁ hwh h8 N₁ a1)
    fun t₂ ⟨d2, a2, z2, mm2, el2, f2, k2, h₂⟩ => ?_)
  -- the normalization
  have hNw : N < 2 ^ (64 * w) := Nat.lt_of_lt_of_le hNhi (Nat.pow_le_pow_right (by decide) (by omega_arith))
  have top0 : (word t₁.mem B (slot w 0 + 8 * (h - 1))).toNat = N / 2 ^ (64 * (h - 1)) := by
    rw [word_top (n := w) (by omega_arith) (by rw [N₁, show h - 1 + 1 = h by omega_arith]; exact hNhi), N₁]
  rw [top0] at d2 a2 z2
  have nb := LongDivision.norm_bounds (K := h - 1) hNlo (by
    rw [← Nat.pow_add, show 64 * (h - 1) + 64 = 64 * h by omega_arith]; exact hNhi)
  generalize hz : 63 - Nat.log2 (N / 2 ^ (64 * (h - 1))) = z at d2 a2 z2 nb
  have hz64 : z < 64 := by omega_arith
  have hPh : 2 ^ (64 * (h - 1)) * 2 ^ 64 = 2 ^ (64 * h) := by rw [← Nat.pow_add]; congr 1; omega_arith
  have hNz : N * 2 ^ z < 2 ^ (64 * h) := hPh ▸ nb.2
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hNz (Nat.pow_le_pow_right (by decide) (by omega_arith)))] at d2
  have M₂ : wv t₂.mem B (slot w 8) h = N * 2 ^ z := by
    rw [Key.wv_low (k := h) (n := w) (by omega_arith) (by rw [d2]; exact hNz), d2]
  have top8 : 2 ^ 63 ≤ (word t₂.mem B (slot w qD + 8 * (h - 1))).toNat := by
    rw [show qD = 8 from rfl, word_top (n := w) (by omega_arith) (by
      rw [d2, show h - 1 + 1 = h by omega_arith]; exact hNz), d2]
    exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by rw [Nat.mul_comm]; exact nb.1)
  have N₂ : wv t₂.mem B (slot w 0) w = N := by rw [f2.wv_eq (fun y => by da_omega) (by da_omega), N₁]
  have m₂ : mw t₂.mem B = mask c := by rw [mm2, m₁]
  refine WP.mono (divA3_ok h₂ hwh h8 N₂ z2 hz64 m₂ top8) fun t ⟨q3, r3, m3, el3, f3, k3, h₃⟩ => ?_
  rw [M₂] at q3 r3 m3
  have A2e : wv t₂.mem B (slot w 9) (2 * h + 2) = A * 2 ^ z % 2 ^ (64 * w) % 2 ^ (64 * (2 * h + 2)) := by
    rw [← a2, wv_mod_low _ _ _ (show 2 * h + 2 ≤ w by omega_arith)]
  rw [A2e] at q3 r3 m3
  have hz0 := Nat.two_pow_pos z
  have exact : c = true → A * 2 ^ z % 2 ^ (64 * w) % 2 ^ (64 * (2 * h + 2)) = A * 2 ^ z := by
    intro hc
    have h1 : A * 2 ^ z < 2 ^ (64 * (2 * h + 2)) := by
      calc A * 2 ^ z < N * 2 ^ (64 * (h + 1)) * 2 ^ z := Nat.mul_lt_mul_of_pos_right (hA hc) hz0
        _ = N * 2 ^ z * 2 ^ (64 * (h + 1)) := by rw [Nat.mul_right_comm]
        _ ≤ 2 ^ (64 * h) * 2 ^ (64 * (h + 1)) := Nat.mul_le_mul_right _ (Nat.le_of_lt hNz)
        _ = 2 ^ (64 * (2 * h + 1)) := by rw [← Nat.pow_add]; congr 1; omega_arith
        _ ≤ 2 ^ (64 * (2 * h + 2)) := Nat.pow_le_pow_right (by decide) (by omega_arith)
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (by omega_arith))),
      Nat.mod_eq_of_lt h1]
  refine ⟨?_, fun hc => ?_, ?_, (f1.trans f2).trans f3, ((k1.trans k2).trans k3).mono (by simp [mmRegs]), h₃⟩
  · rw [m3]
    cases c
    · rfl
    · rw [exact rfl, Nat.mul_div_mul_right _ _ hz0]
  · rw [exact hc] at q3 r3
    rw [q3, r3, Nat.mul_div_mul_right _ _ hz0, Nat.mul_mod_mul_right, Nat.mul_div_cancel _ hz0]
    exact ⟨rfl, rfl⟩
  · rw [el3, el2, el1]

/-! ## `divB`'s normalization -/

/-- `testTop`'s setup: the base of the top `c` of `[j]`'s low `h` words, `rbp := 0`, `r12 := c`. -/
theorem testTopHd_ok {s : State} {B : Addr} {Z w h : Nat} (hw : Ws s B Z w) (hwh : w = 2 * h + 4) {j c : Nat}
    (hc : c ≤ h) (hc64 : c ≤ 64) :
    WP isa (.block (ws ++ base j .rbx ++ hOf ++ ([.alu .sub .r12 (.imm (BitVec.ofNat 32 c)), .shift .shl .r12 3,
      .alu .add .rbx (.reg .r12), .mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr))) s
      fun t => t.gpr .rbx = off B (slot w j + 8 * (h - c)) ∧ t.gpr .rbp = 0 ∧ t.gpr .r12 = BitVec.ofNat 64 c ∧
        t.mem = s.mem ∧ Keep [.r12, .r9, .rbx, .rbp] s t := by
  have hw2 := hw.w2
  rw [show ws ++ base j .rbx ++ hOf ++ ([.alu .sub .r12 (.imm (BitVec.ofNat 32 c)), .shift .shl .r12 3,
      .alu .add .rbx (.reg .r12), .mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) =
    ws ++ (base j .rbx ++ (hOf ++ ([.alu .sub .r12 (.imm (BitVec.ofNat 32 c)), .shift .shl .r12 3,
      .alu .add .rbx (.reg .r12), .mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr))) by
    simp only [List.append_assoc], WP.block_append_iff]
  refine WP.mono hw.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok j (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans hw.rdi) h9) fun s₂ ⟨hbx, m₂, k₂⟩ => ?_
  refine WP.mono (WP.keep [.r12, .rbx, .rbp] (Q := fun t => t.gpr .rbx = off B (slot w j + 8 * (h - c)) ∧
      t.gpr .rbp = 0 ∧ t.gpr .r12 = BitVec.ofNat 64 c ∧ t.mem = s₂.mem) (by
    simp only [hOf, List.cons_append, List.nil_append]
    have shv : (1 ≤ 3 ∧ 3 ≤ 63) = True := eq_true ⟨by decide, by decide⟩
    xrun [(k₂.gpr (by decide) : s₂.gpr .r12 = _), h12, hOf_ofNat (W := w) (by omega_arith) (by omega_arith),
      show w / 2 - 2 = h by omega_arith, sx_ofNat (show c < 2 ^ 31 by omega_arith), hbx, shv, setW32 (show c < 2 ^ 32 by omega_arith),
      ofNat_sub64 (show c ≤ h by omega_arith) (by omega_arith), ofNat_shl3 (show 8 * (h - c) < 2 ^ 64 by omega_arith),
      off_addN]
    done) rfl) fun t ⟨⟨a1, a2, a3, m₃⟩, k₃⟩ => ?_
  exact ⟨a1, a2, a3, by rw [m₃, m₂, m₁], ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- `testTop j c`: `sB2 := ` the mask of the top `c` of `[j]`'s low `h` words not all zero. -/
theorem testTop_ok {s : State} {B : Addr} {Z w h : Nat} (hw : Ws s B Z w) (hwh : w = 2 * h + 4) {j c : Nat}
    (hj : j < 16) (hc1 : 1 ≤ c) (hc : c ≤ h) (hc64 : c ≤ 64) :
    WP isa (seqs (testTop j c)) s fun t =>
      t.mem = s.mem.writeW (off B (8 * sB2)) (mask (!decide (wv s.mem B (slot w j + 8 * (h - c)) c = 0))) ∧
      Keep [.r12, .r9, .rbx, .rbp, .rax, .r14] s t := by
  have hn := hw.scr.nowrap
  have sj := hw.sl hj
  have hw2 := hw.w2
  simp only [testTop, seqs]
  refine WP.seq (WP.seq (WP.mono (testTopHd_ok hw hwh (j := j) hc hc64) fun s₁ ⟨hbx, hbp, h12, m₁, k₁⟩ => ?_))
  have hs := hw.scr.congr k₁.2.2
  have h₁ : Ws s₁ B Z w := hw.congrP (P := fun _ => False) (fun _ _ => by rw [m₁]) (fun _ f => f.elim) k₁ (by simp)
  refine WP.mono (or1_ok hs hbx h12 hc1 (by omega_arith) (by omega_arith)) fun s₂ ⟨hz, m₂, k₂⟩ => ?_
  refine WP.mono (keepOf_ok (h₁.congrP (P := fun _ => False) (fun _ _ => by rw [m₂]) (fun _ f => f.elim) k₂ (by simp))
    (z := wv s.mem B (slot w j + 8 * (h - c)) c = 0) (by rw [hz, hbp, m₁]; simp)) fun t ⟨m₃, k₃⟩ => ?_
  exact ⟨by rw [m₃, m₂, m₁], ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- `shlWords false`' block: `w - c` words of `[j]` to word `c` of `[t]`. -/
theorem shlWBN_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j c t : Nat} (hc : c ≤ 128)
    (hcw : c ≤ w) :
    WP isa (.block (wsW false ++ ([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ base j .rsi ++
      base t .rbx ++ ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr))) s fun u =>
      u.gpr .r12 = BitVec.ofNat 64 (w - c) ∧ u.gpr .rsi = off B (slot w j) ∧
        u.gpr .rbx = off B (slot w t + 8 * c) ∧ u.mem = s.mem ∧ Keep [.r12, .r9, .rsi, .rbx] s u := by
  have hw2 := h.w2
  unfold wsW
  simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (Q := fun u => u.gpr .r12 = BitVec.ofNat 64 w - BitVec.ofNat 64 c ∧
    u.mem = s₁.mem) (by xrun [h12, sx_ofNat (show c < 2 ^ 31 by omega_arith)]) rfl) fun s₃ ⟨⟨h12', m₃⟩, k₃⟩ => ?_
  have k13 := k₁.trans k₃
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (base2_ok j t (r₁ := .rsi) (r₂ := .rbx) (w := w) (by decide) (by decide) (by decide)
    ((k13.gpr (by decide)).trans h.rdi) ((k₃.gpr (by decide)).trans h9) (by decide))
    fun s₄ ⟨hsi, hbx, m₄, k₄⟩ => ?_
  refine WP.mono (WP.keep [.rbx] (Q := fun u => u.gpr .rbx = off B (slot w t + 8 * c) ∧ u.mem = s₄.mem)
    (by xrun [hbx, sx_ofNat (show 8 * c < 2 ^ 31 by omega_arith), off_addN]) rfl) fun u ⟨⟨hbx', m₅⟩, k₅⟩ => ?_
  refine ⟨?_, (k₅.gpr (by decide)).trans hsi, hbx', by rw [m₅, m₄, m₃, m₁],
    ((k13.trans k₄).trans k₅).mono (by simp)⟩
  rw [((k₄.trans k₅).gpr (by decide)), h12', ofNat_sub64 (by omega_arith) (by omega_arith)]

/-- `shlWords false j c t`: `[t] := [j] 2^(64 c)` modulo `2^(64 w)`. -/
theorem shlWordsN_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j c t : Nat}
    (hj : j < 16) (ht : t < 16) (hjt : j ≠ t) (hc : 1 ≤ c) (hcw : c + 1 ≤ w) (hc64 : c ≤ 128) :
    WP isa (seqs (shlWords false j c t)) s fun u =>
      wv u.mem B (slot w t) w = wv s.mem B (slot w j) w * 2 ^ (64 * c) % 2 ^ (64 * w) ∧
      Outside B (slot w t) (8 * (w + 2)) s.mem u.mem ∧ Keep [.r12, .r9, .r8, .rax, .r14, .rsi, .rbx] s u := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  have st := h.sl ht
  have pj := slot_far (w := w) hjt
  have hw2 := h.w2
  simp only [shlWords, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append, seqs]
  refine WP.seq (WP.mono (zeroA_ok h ht) fun s₁ ⟨z1, o1, k1⟩ => ?_)
  have h₁ := h.congrO o1 (slot_256 _ _) k1 (by simp)
  refine WP.seq (WP.mono (shlWBN_ok h₁ hc64 (by omega_arith) (j := j) (t := t)) fun s₃ ⟨h12, hsi, hbx, m₃, k₃⟩ => ?_)
  have hs₃ := h₁.scr.congr k₃.2.2
  refine WP.mono (copyWords_ok hsi hbx h12 (by omega_arith) (by omega_arith) (by omega_arith)
    (fun i hi => hs₃.ld (by omega_arith)) (fun i hi => hs₃.st (by omega_arith))
    (fun i hi b hb => by rw [ofs_off B (by omega_arith)]; omega_arith)) fun u ⟨v, _, o, k₄⟩ => ?_
  rw [m₃] at v o
  have lo : wv u.mem B (slot w t) c = 0 := by
    rw [o.wv (by omega_arith) (by omega_arith)]
    exact (wv_eq_zero_iff _ _ _ _).mpr fun q hq => (wv_eq_zero_iff _ _ _ _).mp z1 q (by omega_arith)
  have Jv : wv s₁.mem B (slot w j) (w - c) = wv s.mem B (slot w j) (w - c) := o1.wv (by omega_arith) (by omega_arith)
  refine ⟨?_, ?_, (((k1.trans k₃).trans k₄).mono (by simp))⟩
  · have sp := wv_add u.mem B (slot w t) c (w - c)
    rw [show c + (w - c) = w by omega_arith, lo, Nat.zero_add] at sp
    rw [sp, v, Jv, wv_mul_pow_mod _ _ _ (by omega_arith)]
  · intro x hx
    rw [o x (by omega_arith), o1 x hx]

/-- `[j] := keep ? [j] : [j] 2^(64 c) mod 2^(64 w)`, through `[3]`. -/
theorem selShlD_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j t c : Nat} (hj : j < 16) (ht : t < 16)
    (hj3 : j ≠ t) (hc : 1 ≤ c) (hcw : c + 1 ≤ w) (hc64 : c ≤ 128) {keep : Bool} (hk : word s.mem B (8 * sB2) = mask keep) :
    WP isa (seqs (shlWords false j c t ++ [selK false j t])) s fun u =>
      wv u.mem B (slot w j) w =
        (if keep then wv s.mem B (slot w j) w else wv s.mem B (slot w j) w * 2 ^ (64 * c) % 2 ^ (64 * w)) ∧
      Frm B [(slot w t, 8 * (w + 2)), (slot w j, 8 * w)] s.mem u.mem ∧ Keep mmRegs s u ∧ Ws u B Z w := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  have s3 := h.sl ht
  have pj := slot_far (w := w) hj3
  refine wp_seqs_append (by simp [shlWords]) (by simp) (WP.mono (shlWordsN_ok h (j := j) (t := t) hj ht
    hj3 hc hcw hc64) fun s₁ ⟨v1, o1, k1⟩ => ?_)
  have h₁ := h.congrO o1 (slot_256 _ _) k1 (by simp)
  simp only [seqs]
  refine WP.mono (selK_ok h₁ false (j := j) (t := t) (keep := keep) (by simp; omega_arith) (by simp; omega_arith) (by
    simp only [shlN, Bool.false_eq_true, ↓reduceIte]; omega_arith)
    (by rw [o1.word (by unfold sB2 sFn; have := slot_256 w t; omega_arith)
      (by unfold sB2 sFn; have := h.h256; omega_arith)]; exact hk))
    fun u ⟨v2, o2, k2⟩ => ?_
  simp only [shlN, Bool.false_eq_true, ↓reduceIte] at v2 o2
  have Jv : wv s₁.mem B (slot w j) w = wv s.mem B (slot w j) w := o1.wv (by omega_arith) (by omega_arith)
  refine ⟨by rw [v2, Jv, v1], frm2 o1 o2, (k1.trans k2).mono (by simp [mmRegs]),
    h₁.congrO o2 (slot_256 _ _) k2 (by simp)⟩

/-- What `normDN`'s stages change: arrays 2 to 5 and `sB2`. -/
def dnRs (w : Nat) : List (Nat × Nat) := [(slot w 2, 32 * (w + 2)), (8 * sB2, 8)]

theorem dnR_trans {B : Addr} {w : Nat} {a b c : State} (h₁ : Frm B (dnRs w) a.mem b.mem ∧ Keep mmRegs a b)
    (h₂ : Frm B (dnRs w) b.mem c.mem ∧ Keep mmRegs b c) : Frm B (dnRs w) a.mem c.mem ∧ Keep mmRegs a c :=
  ⟨h₁.1.trans h₂.1, (h₁.2.trans h₂.2).mono (by simp [mmRegs])⟩

/-- A stage's guard: `CF` of `h < c + 1`. -/
theorem stageDHd_ok {s : State} {B : Addr} {Z w h : Nat} (hw : Ws s B Z w) (hwh : w = 2 * h + 4) {c : Nat}
    (hc : c ≤ 64) :
    WP isa (.block (ws ++ hOf ++ ([.alu .cmp .r12 (.imm (BitVec.ofNat 32 (c + 1)))] : List Instr))) s fun t =>
      (t.cf = some (decide (h < c + 1)) ∧ t.mem = s.mem) ∧ Keep [.r12, .r9] s t := by
  have hw2 := hw.w2
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono hw.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.cf = some (decide (h < c + 1)) ∧ t.mem = s₁.mem) (by
    simp only [hOf, List.cons_append, List.nil_append]
    xrun [h12, hOf_ofNat (W := w) (by omega_arith) (by omega_arith), show w / 2 - 2 = h by omega_arith,
      sx_ofNat (show c + 1 < 2 ^ 31 by omega_arith)]
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show h < 2 ^ 64 by omega_arith),
      Nat.mod_eq_of_lt (show c + 1 < 2 ^ 64 by omega_arith)]) rfl)
    fun t ⟨⟨hcf, m₂⟩, k₂⟩ => ⟨⟨hcf, by rw [m₂, m₁]⟩, (k₁.trans k₂).mono (by simp)⟩

/-- A stage of `c` words of `D`'s leading zeros in its low `h` words: where
`c + 1 ≤ h` and its top `c` words are zero, `D` and `N` shift left by `64 c` bits. -/
theorem stageD_ok {s : State} {B : Addr} {Z w h : Nat} (hw : Ws s B Z w) (hwh : w = 2 * h + 4) {D N : Nat}
    (hD : wv s.mem B (slot w 2) w = D) (hN : wv s.mem B (slot w 5) w = N) {c : Nat} (hc : 1 ≤ c) (hc64 : c ≤ 64) :
    WP isa (stageD c) s fun t =>
      wv t.mem B (slot w 2) w =
        (if c + 1 ≤ h ∧ D / 2 ^ (64 * (h - c)) % 2 ^ (64 * c) = 0 then D * 2 ^ (64 * c) % 2 ^ (64 * w) else D) ∧
      wv t.mem B (slot w 5) w =
        (if c + 1 ≤ h ∧ D / 2 ^ (64 * (h - c)) % 2 ^ (64 * c) = 0 then N * 2 ^ (64 * c) % 2 ^ (64 * w) else N) ∧
      Frm B (dnRs w) s.mem t.mem ∧ Keep mmRegs s t ∧ Ws t B Z w := by
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  rw [slotE] at hZ
  have hw2 := hw.w2
  have sl2 := slotE w 2
  have sl3 := slotE w 3
  have sl5 := slotE w 5
  have hsb : 8 * sB2 = 216 := rfl
  unfold stageD
  refine WP.seq (WP.mono (stageDHd_ok hw hwh hc64) fun s₁ ⟨⟨hcf, m₁⟩, k₁⟩ => ?_)
  have h₁ : Ws s₁ B Z w := hw.congrP (P := fun _ => False) (fun _ _ => by rw [m₁]) (fun _ f => f.elim) k₁ (by simp)
  refine WP.ite (decide (h < c + 1)) (by simp only [eval, hcf]) (fun hb => ?_) (fun hb => ?_)
  · have hg : ¬ (c + 1 ≤ h) := by simp only [decide_eq_true_eq] at hb; omega_arith
    refine WP.block_nil_iff.mpr ⟨?_, ?_, ?_, k₁.mono (by simp [mmRegs]), h₁⟩
    · simp only [hg, false_and, ↓reduceIte]; rw [m₁, hD]
    · simp only [hg, false_and, ↓reduceIte]; rw [m₁, hN]
    · rw [m₁]; exact Frm.refl _ _ _
  · have hg : c + 1 ≤ h := by simp only [decide_eq_false_iff_not] at hb; omega_arith
    have hz : wv s₁.mem B (slot w 2 + 8 * (h - c)) c = D / 2 ^ (64 * (h - c)) % 2 ^ (64 * c) := by
      rw [m₁, ← hD, wv_div_pow _ _ _ (show h - c ≤ w by omega_arith),
        wv_mod_low _ _ _ (show c ≤ w - (h - c) by omega_arith)]
    show WP isa (seqs (testTop 2 c ++ ((shlWords false 2 c 3 ++ [selK false 2 3]) ++
      (shlWords false 5 c 3 ++ [selK false 5 3])))) s₁ _
    refine wp_seqs_append (by simp [testTop]) (by simp [shlWords]) (WP.mono (testTop_ok h₁ hwh (j := 2) (by decide)
      hc (by omega_arith) hc64) fun s₂ ⟨m₂, k₂⟩ => ?_)
    rw [hz] at m₂
    have h₂ := h₁.congrW m₂ (by unfold DOk; simp only [sB2, sFn]; omega_arith) (by decide) k₂ (by simp)
    have o₂ : Outside B (8 * sB2) 8 s₁.mem s₂.mem := by rw [m₂]; exact writeW_outside _ _ _ (by omega_arith)
    have hk₂ := (show word s₂.mem B (8 * sB2) = _ by rw [m₂, word_writeW_self])
    have D₂ : wv s₂.mem B (slot w 2) w = D := by rw [o₂.wv (by omega_arith) (by omega_arith), m₁, hD]
    have N₂ : wv s₂.mem B (slot w 5) w = N := by rw [o₂.wv (by omega_arith) (by omega_arith), m₁, hN]
    refine wp_seqs_append (by simp [shlWords]) (by simp [shlWords]) (WP.mono (selShlD_ok h₂ (j := 2) (t := 3) (by decide)
      (by decide) (by decide) hc (by omega_arith) (by omega_arith) hk₂) fun s₃ ⟨v3, f3, k3, h₃⟩ => ?_)
    rw [if_not_decide, D₂] at v3
    have hk₃ : word s₃.mem B (8 * sB2) = mask (!decide (D / 2 ^ (64 * (h - c)) % 2 ^ (64 * c) = 0)) := by
      rw [f3.word_eq (by tw_sep) (by omega_arith), hk₂]
    refine WP.mono (selShlD_ok h₃ (j := 5) (t := 3) (by decide) (by decide) (by decide) hc (by omega_arith) (by omega_arith) hk₃)
      fun t ⟨v4, f4, k4, ht⟩ => ?_
    rw [if_not_decide, f3.wv_eq (by tw_sep) (by omega_arith), N₂] at v4
    refine ⟨?_, ?_, ?_, (((k₁.trans k₂).trans k3).trans k4).mono (by simp [mmRegs]), ht⟩
    · rw [f4.wv_eq (by tw_sep) (by omega_arith), v3]; simp only [hg, true_and]
    · rw [v4]; simp only [hg, true_and]
    · rw [← m₁]
      refine ((Frm.of_outside o₂ (by simp [dnRs])).trans (WordDivide.cover f3 ?_)).trans (WordDivide.cover f4 ?_) <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      · exact ⟨⟨(slot w 2, 32 * (w + 2)), by simp [dnRs], by omega_arith, by omega_arith⟩,
          ⟨(slot w 2, 32 * (w + 2)), by simp [dnRs], by omega_arith, by omega_arith⟩⟩
      · exact ⟨⟨(slot w 2, 32 * (w + 2)), by simp [dnRs], by omega_arith, by omega_arith⟩,
          ⟨(slot w 2, 32 * (w + 2)), by simp [dnRs], by omega_arith, by omega_arith⟩⟩

/-- The word stages of `D`'s leading zeros in turn (`h` words, modulo `2^(64 w)`). -/
def dnF (h w : Nat) (D N : Nat) : List Nat → Nat × Nat
  | [] => (D, N)
  | c :: cs => if c + 1 ≤ h ∧ D / 2 ^ (64 * (h - c)) % 2 ^ (64 * c) = 0
      then dnF h w (D * 2 ^ (64 * c) % 2 ^ (64 * w)) (N * 2 ^ (64 * c) % 2 ^ (64 * w)) cs
      else dnF h w D N cs

theorem dnStages_ok {B : Addr} {Z w h : Nat} (hwh : w = 2 * h + 4) : ∀ (cs : List Nat), (∀ c ∈ cs, 1 ≤ c ∧ c ≤ 64) →
    cs ≠ [] → ∀ {s : State} {D N : Nat}, Ws s B Z w → wv s.mem B (slot w 2) w = D → wv s.mem B (slot w 5) w = N →
    WP isa (seqs (cs.map stageD)) s fun t =>
      wv t.mem B (slot w 2) w = (dnF h w D N cs).1 ∧ wv t.mem B (slot w 5) w = (dnF h w D N cs).2 ∧
      Frm B (dnRs w) s.mem t.mem ∧ Keep mmRegs s t ∧ Ws t B Z w
  | [], _, h0, _, _, _, _, _, _ => absurd rfl h0
  | [c], hc, _, s, D, N, hw, hD, hN => by
    have hc' := hc c (by simp)
    simp only [List.map_cons, List.map_nil, seqs]
    refine WP.mono (stageD_ok hw hwh hD hN hc'.1 hc'.2) fun t ⟨v2, v5, f, k, ht⟩ => ⟨?_, ?_, f, k, ht⟩ <;>
    · by_cases hg : c + 1 ≤ h ∧ D / 2 ^ (64 * (h - c)) % 2 ^ (64 * c) = 0 <;>
        simp only [dnF, hg, ↓reduceIte] at v2 v5 ⊢ <;> first | exact v2 | exact v5
  | c :: c' :: cs, hc, _, s, D, N, hw, hD, hN => by
    have hc' := hc c (by simp)
    rw [List.map_cons, show seqs (stageD c :: (c' :: cs).map stageD) = .seq (stageD c) (seqs ((c' :: cs).map stageD))
      from rfl]
    refine WP.seq (WP.mono (stageD_ok hw hwh hD hN hc'.1 hc'.2) fun t ⟨v2, v5, f, k, ht⟩ => ?_)
    refine WP.mono (dnStages_ok hwh (c' :: cs) (fun x hx => hc x (by simp [hx])) (by simp) ht v2 v5)
      fun u ⟨u2, u5, f', k', hu⟩ => ⟨?_, ?_, (dnR_trans ⟨f, k⟩ ⟨f', k'⟩).1, (dnR_trans ⟨f, k⟩ ⟨f', k'⟩).2, hu⟩ <;>
    · by_cases hg : c + 1 ≤ h ∧ D / 2 ^ (64 * (h - c)) % 2 ^ (64 * c) = 0 <;>
        simp only [dnF, hg, ↓reduceIte] at v2 v5 u2 u5 ⊢ <;> first | exact u2 | exact u5

open VG.Proof.Bignum.ShiftStages in
/-- The word stages take `D`'s leading zero words `C = (64 h - 1 - log₂ D) / 64`
in its `h` words: `D 2^(64 C)` and `N 2^(64 C)`, exactly. -/
theorem dnF_greedy {h w D N : Nat} (hwh : w = 2 * h + 4) (hD1 : 1 ≤ D) (hDh : D < 2 ^ (64 * h))
    (hNh : N < 2 ^ (64 * h)) : ∀ (cs : List Nat), (∀ c ∈ cs, 1 ≤ c) → ∀ (a : Nat),
    a ≤ (64 * h - 1 - Nat.log2 D) / 64 →
    dnF h w (D * 2 ^ (64 * a)) (N * 2 ^ (64 * a)) cs =
      (D * 2 ^ (64 * greedy ((64 * h - 1 - Nat.log2 D) / 64) cs a),
        N * 2 ^ (64 * greedy ((64 * h - 1 - Nat.log2 D) / 64) cs a))
  | [], _, a, _ => rfl
  | c :: cs, hc, a, ha => by
    have hD0 : D ≠ 0 := by omega_arith
    have hlog : Nat.log2 D < 64 * h := (lt_pow_iff hD0 0 (64 * h)).mp (by simpa using hDh)
    generalize hC : (64 * h - 1 - Nat.log2 D) / 64 = C at ha ⊢
    have fits : ∀ k, D * 2 ^ (64 * k) < 2 ^ (64 * h) ↔ k ≤ C := fun k => by
      rw [lt_pow_iff hD0]; omega_arith
    have hc1 := (hc c (by simp))
    have hDa : D * 2 ^ (64 * a) < 2 ^ (64 * h) := (fits a).mpr ha
    have hP : 2 ^ (64 * h) ≤ 2 ^ (64 * w) := Nat.pow_le_pow_right (by decide) (by omega_arith)
    have key : (c + 1 ≤ h ∧ D * 2 ^ (64 * a) / 2 ^ (64 * (h - c)) % 2 ^ (64 * c) = 0) ↔ a + c ≤ C := by
      by_cases hch : c + 1 ≤ h
      · have hq : D * 2 ^ (64 * a) / 2 ^ (64 * (h - c)) < 2 ^ (64 * c) := by
          rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
            show 64 * c + 64 * (h - c) = 64 * h by omega_arith]; exact hDa
        rw [Nat.mod_eq_of_lt hq, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _), ← fits,
          show 64 * (a + c) = 64 * a + 64 * c by omega_arith, Nat.pow_add, ← Nat.mul_assoc]
        constructor
        · intro ⟨_, h2⟩
          calc D * 2 ^ (64 * a) * 2 ^ (64 * c) < 2 ^ (64 * (h - c)) * 2 ^ (64 * c) :=
                Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos _)
            _ = 2 ^ (64 * h) := by rw [← Nat.pow_add]; congr 1; omega_arith
        · intro h2
          refine ⟨hch, ?_⟩
          have : 2 ^ (64 * h) = 2 ^ (64 * (h - c)) * 2 ^ (64 * c) := by rw [← Nat.pow_add]; congr 1; omega_arith
          rw [this] at h2
          exact Nat.lt_of_mul_lt_mul_right h2
      · have : ¬ (a + c ≤ C) := by
          intro hl
          have := (fits (a + c)).mpr hl
          have hCh : C ≤ h - 1 := by rw [← hC]; omega_arith
          omega_arith
        simp only [hch, false_and, this]
    rw [dnF, greedy_cons]
    by_cases hl : a + c ≤ C
    · simp only [key.mpr hl, ↓reduceIte, hl]
      have hDc : D * 2 ^ (64 * a) * 2 ^ (64 * c) = D * 2 ^ (64 * (a + c)) := by
        rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega_arith
      have hNc : N * 2 ^ (64 * a) * 2 ^ (64 * c) = N * 2 ^ (64 * (a + c)) := by
        rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega_arith
      have hCh : a + c ≤ h - 1 := by rw [← hC] at hl; omega_arith
      have hNw : N * 2 ^ (64 * (a + c)) < 2 ^ (64 * w) := by
        calc N * 2 ^ (64 * (a + c)) < 2 ^ (64 * h) * 2 ^ (64 * (a + c)) :=
              Nat.mul_lt_mul_of_pos_right hNh (Nat.two_pow_pos _)
          _ = 2 ^ (64 * (h + (a + c))) := by rw [← Nat.pow_add]; congr 1; omega_arith
          _ ≤ 2 ^ (64 * w) := Nat.pow_le_pow_right (by decide) (by omega_arith)
      rw [hDc, hNc, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le ((fits _).mpr hl) hP), Nat.mod_eq_of_lt hNw]
      rw [← hC]
      exact hC ▸ dnF_greedy hwh hD1 hDh hNh cs (fun x hx => hc x (by simp [hx])) (a + c) (hC ▸ hl)
    · simp only [mt key.mp hl, ↓reduceIte, hl]
      rw [← hC]
      exact dnF_greedy hwh hD1 hDh hNh cs (fun x hx => hc x (by simp [hx])) a (hC ▸ ha)

/-- `normDN`'s last block: the divisor's word `h - 1` with its top bit set. -/
theorem forceTop_ok {s : State} {B : Addr} {Z w h : Nat} (hw : Ws s B Z w) (hwh : w = 2 * h + 4) (h1 : 1 ≤ h) :
    WP isa (.block (ws ++ base 8 .r10 ++ hOf ++ ([.mov .rax (.mem (ix .r10 .r12 (-8))),
      .movImm64 .rdx 9223372036854775808, .alu .or .rax (.reg .rdx), .store (ix .r10 .r12 (-8)) .rax] : List Instr))) s fun t =>
      t.mem = s.mem.writeW (off B (slot w 8 + 8 * (h - 1)))
        (word s.mem B (slot w 8 + 8 * (h - 1)) ||| BitVec.ofNat 64 9223372036854775808) ∧
      Keep [.r12, .r9, .r10, .rax, .rdx] s t := by
  have hn := hw.scr.nowrap
  have s8 := hw.sl (j := 8) (by decide)
  have hw2 := hw.w2
  rw [show ws ++ base 8 .r10 ++ hOf ++ ([.mov .rax (.mem (ix .r10 .r12 (-8))),
      .movImm64 .rdx 9223372036854775808, .alu .or .rax (.reg .rdx), .store (ix .r10 .r12 (-8)) .rax] : List Instr) =
    ws ++ (base 8 .r10 ++ (hOf ++ ([.mov .rax (.mem (ix .r10 .r12 (-8))),
      .movImm64 .rdx 9223372036854775808, .alu .or .rax (.reg .rdx), .store (ix .r10 .r12 (-8)) .rax] :
        List Instr))) by simp only [List.append_assoc], WP.block_append_iff]
  refine WP.mono hw.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok 8 (r := .r10) (by decide) ((k₁.gpr (by decide)).trans hw.rdi) h9) fun s₂ ⟨h10, m₂, k₂⟩ => ?_
  have hs₂ := hw.scr.congr (k₁.trans k₂).2.2
  refine WP.mono (WP.keep [.r12, .rax, .rdx] (Q := fun t => t.mem = s.mem.writeW (off B (slot w 8 + 8 * (h - 1)))
      (word s.mem B (slot w 8 + 8 * (h - 1)) ||| BitVec.ofNat 64 9223372036854775808)) (by
    simp only [hOf, List.cons_append, List.nil_append]
    xrun [(k₂.gpr (by decide) : s₂.gpr .r12 = _), h12, hOf_ofNat (W := w) (by omega_arith) (by omega_arith),
      show w / 2 - 2 = h by omega_arith, State.ea, ix, addrm8 h10 rfl (show 1 ≤ h by omega_arith),
      hs₂.ld (d := slot w 8 + 8 * (h - 1)) (by omega_arith), hs₂.st (d := slot w 8 + 8 * (h - 1)) (by omega_arith),
      m₂, m₁]
    rfl) rfl) fun t ⟨m₃, k₃⟩ => ⟨m₃, ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- What `divB` changes: the header's mask, counts and `sB2`/`sC`, and wide
arrays 2 to 5 and 8 to 15. -/
def DbP (w y : Nat) : Prop :=
  (176 ≤ y ∧ y < 184) ∨ (200 ≤ y ∧ y < 208) ∨ (216 ≤ y ∧ y < 224) ∨ (240 ≤ y ∧ y < 248) ∨
    (slot w 2 ≤ y ∧ y < slot w 6) ∨ (slot w 8 ≤ y ∧ y < slot w 16)

macro "db_omega" : tactic =>
  `(tactic| (simp only [DbP, DOk, Bignum.slot, hdrBytes, Impl.Bignum.X86_64.Public.sMask, sFn, sC, sCt, sB2,
    qQ, qR, qT, qV, qA, qD, dnRs]; omega_arith))

theorem pows6 : wordStages = VG.Proof.Bignum.ShiftStages.pows 6 := by decide

theorem top_or (x : BitVec 64) : 2 ^ 63 ≤ (x ||| BitVec.ofNat 64 9223372036854775808).toNat := by
  rw [BitVec.toNat_or, show (BitVec.ofNat 64 9223372036854775808).toNat = 2 ^ 63 from rfl]
  exact Nat.right_le_or

theorem or_top_eq {x : BitVec 64} (hx : 2 ^ 63 ≤ x.toNat) : x ||| BitVec.ofNat 64 9223372036854775808 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, show (BitVec.ofNat 64 9223372036854775808).toNat = 2 ^ 63 from rfl]
  have hl := x.isLt
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_two_pow]
  by_cases hi : 63 = i
  · subst hi
    have : x.toNat.testBit 63 = true := by
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
      have : x.toNat / 2 ^ 63 = 1 := by omega_arith
      rw [this]; rfl
    rw [this]; rfl
  · simp [hi]

/-- `normDN` (wide, `w = 2 h + 4`): the divisor `[8]`'s word `h - 1` has its top
bit set; for `1 ≤ D < 2^(64 h)` and `N < 2^(64 h)` (`[2]` and `[5]`), `[8]`'s
low `h` words are `D 2^s` and `[9]`'s low `2 h` words `N 2^s` for one `s`. -/
theorem normDN_ok {s : State} {B : Addr} {Z w h : Nat} (hw : Ws s B Z w) (hwh : w = 2 * h + 4) (h8 : 8 ≤ h)
    (h128 : h ≤ 128) {D N : Nat} (hD : wv s.mem B (slot w 2) w = D) (hN : wv s.mem B (slot w 5) w = N) :
    WP isa (seqs normDN) s fun t =>
      2 ^ 63 ≤ (word t.mem B (slot w qD + 8 * (h - 1))).toNat ∧
      (1 ≤ D → D < 2 ^ (64 * h) → N < 2 ^ (64 * h) → ∃ sh,
        wv t.mem B (slot w 8) h = D * 2 ^ sh ∧ wv t.mem B (slot w 9) (2 * h) = N * 2 ^ sh) ∧
      mw t.mem B = mw s.mem B ∧ FrmP B (DbP w) s.mem t.mem ∧ Keep mmRegs s t ∧ Ws t B Z w := by
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  have hZ := hw.hZ
  have hZ' : 256 + 16 * (8 * (w + 2)) ≤ Z := hZ
  have hw2 := hw.w2
  unfold normDN
  refine wp_seqs_append (by simp [wordStages]) (by simp) (WP.mono (dnStages_ok hwh wordStages
    (by decide) (by decide) hw hD hN) fun t₁ ⟨d1, n1, f1, k1, h₁⟩ => ?_)
  have fd1 : FrmP B (DbP w) s.mem t₁.mem := FrmP.of_frm f1 (by
    simp only [dnRs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨fun y h1 h2 => by simp only [Bignum.slot, hdrBytes] at h1 h2; db_omega,
      fun y h1 h2 => by simp only [sB2, sFn] at h1 h2; db_omega⟩)
  generalize hDN : dnF h w D N wordStages = DN at d1 n1
  simp only [seqs]
  refine WP.seq (WP.mono (clzTop_ok h₁ (j := 2) (by decide) (by omega_arith)) fun t₂ ⟨m2, k2⟩ => ?_)
  rw [show w / 2 - 2 - 1 = h - 1 by omega_arith] at m2
  generalize hz : 63 - Nat.log2 (word t₁.mem B (slot w 2 + 8 * (h - 1))).toNat = z at m2
  have hz64 : z < 64 := by omega_arith
  have h₂ := h₁.congrW m2 (by db_omega) (by decide) k2 (by simp)
  have o2 : Outside B (8 * sC) 8 t₁.mem t₂.mem := by rw [m2]; exact writeW_outside _ _ _ (by db_omega)
  have c₂ : word t₂.mem B (8 * sC) = BitVec.ofNat 64 z := by rw [m2, word_writeW_self]
  refine WP.seq (WP.mono (zeroA_ok h₂ (j := 8) (by decide)) fun t₃ ⟨_, o3, k3⟩ => ?_)
  have h₃ := h₂.congrO o3 (by db_omega) k3 (by simp)
  refine WP.seq (WP.mono (shlClP_ok h₃ false (j := 2) (t := 8) (by simp) (by simp)
    (by simp only [shlN, Bool.false_eq_true, ↓reduceIte]; db_omega) hz64
    (sC_pre h256 (by rw [o3.word (by db_omega) (by db_omega), c₂]))) fun t₄ ⟨v4, o4, k4⟩ => ?_)
  simp only [shlN, Bool.false_eq_true, ↓reduceIte] at v4 o4
  have h₄ := h₃.congrO o4 (by db_omega) k4 (by simp)
  refine WP.seq (WP.mono (zeroA_ok h₄ (j := 9) (by decide)) fun t₅ ⟨_, o5, k5⟩ => ?_)
  have h₅ := h₄.congrO o5 (by db_omega) k5 (by simp)
  refine WP.seq (WP.mono (shlClP_ok h₅ false (j := 5) (t := 9) (by simp) (by simp)
    (by simp only [shlN, Bool.false_eq_true, ↓reduceIte]; db_omega) hz64
    (sC_pre h256 (by rw [o5.word (by db_omega) (by db_omega), o4.word (by db_omega) (by db_omega),
      o3.word (by db_omega) (by db_omega), c₂]))) fun t₆ ⟨v6, o6, k6⟩ => ?_)
  simp only [shlN, Bool.false_eq_true, ↓reduceIte] at v6 o6
  have h₆ := h₅.congrO o6 (by db_omega) k6 (by simp)
  refine WP.mono (forceTop_ok h₆ hwh (by omega_arith)) fun t ⟨m7, k7⟩ => ?_
  have o7 : Outside B (slot w 8 + 8 * (h - 1)) 8 t₆.mem t.mem := by rw [m7]; exact writeW_outside _ _ _ (by db_omega)
  have D8 : wv t₆.mem B (slot w 8) w = DN.1 * 2 ^ z % 2 ^ (64 * w) := by
    rw [o6.wv (by db_omega) (by db_omega), o5.wv (by db_omega) (by db_omega), v4,
      o3.wv (by db_omega) (by db_omega), o2.wv (by db_omega) (by db_omega), d1]
  have N9 : wv t₆.mem B (slot w 9) w = DN.2 * 2 ^ z % 2 ^ (64 * w) := by
    rw [v6, o5.wv (by db_omega) (by db_omega), o4.wv (by db_omega) (by db_omega),
      o3.wv (by db_omega) (by db_omega), o2.wv (by db_omega) (by db_omega), n1]
  have top7 : word t.mem B (slot w 8 + 8 * (h - 1)) =
      word t₆.mem B (slot w 8 + 8 * (h - 1)) ||| BitVec.ofNat 64 9223372036854775808 := by
    rw [m7, word_writeW_self]
  have fr : ∀ {o n : Nat} {m m' : Mem}, Outside B o n m m' → (∀ y, o ≤ y → y < o + n → DbP w y) →
      FrmP B (DbP w) m m' := fun ho hP => FrmP.of_out ho hP
  refine ⟨?_, ?_, ?_, ?_, ((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).mono (by simp [mmRegs]),
    h₆.congrO o7 (by db_omega) k7 (by simp)⟩
  · rw [show qD = 8 from rfl, top7]; exact top_or _
  · intro hD1 hDh hNh
    have hDw : D < 2 ^ (64 * w) := Nat.lt_of_lt_of_le hDh (Nat.pow_le_pow_right (by decide) (by omega_arith))
    have hD0 : D ≠ 0 := by omega_arith
    have hlog : Nat.log2 D < 64 * h := (VG.Proof.Bignum.ShiftStages.lt_pow_iff hD0 0 (64 * h)).mp (by simpa using hDh)
    generalize hC : (64 * h - 1 - Nat.log2 D) / 64 = C
    have hCh : C ≤ h - 1 := by omega_arith
    have eDN : DN = (D * 2 ^ (64 * C), N * 2 ^ (64 * C)) := by
      rw [← hDN, pows6]
      have := dnF_greedy (N := N) hwh hD1 hDh hNh (VG.Proof.Bignum.ShiftStages.pows 6) (by decide) 0
        (Nat.zero_le _)
      simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one] at this
      rw [this, hC, VG.Proof.Bignum.ShiftStages.greedy_pows 6 C 0 (Nat.zero_le _) (by omega_arith)]
    have fits : ∀ k, D * 2 ^ (64 * k) < 2 ^ (64 * h) ↔ k ≤ C := fun k => by
      rw [VG.Proof.Bignum.ShiftStages.lt_pow_iff hD0, ← hC]; omega_arith
    have hD'hi : D * 2 ^ (64 * C) < 2 ^ (64 * (h - 1)) * 2 ^ 64 := by
      rw [← Nat.pow_add, show 64 * (h - 1) + 64 = 64 * h by omega_arith]; exact (fits C).mpr (Nat.le_refl _)
    have hD'lo : 2 ^ (64 * (h - 1)) ≤ D * 2 ^ (64 * C) := by
      have := mt (fits (C + 1)).mp (by omega_arith)
      rw [Nat.not_lt, show 64 * (C + 1) = 64 * C + 64 by omega_arith, Nat.pow_add, ← Nat.mul_assoc,
        show 2 ^ (64 * h) = 2 ^ (64 * (h - 1)) * 2 ^ 64 by rw [← Nat.pow_add]; congr 1; omega_arith] at this
      exact Nat.le_of_mul_le_mul_right this (Nat.two_pow_pos _)
    rw [eDN] at d1 D8 N9
    have hP : 2 ^ (64 * (h - 1)) * 2 ^ 64 = 2 ^ (64 * h) := by rw [← Nat.pow_add]; congr 1; omega_arith
    have top1 : (word t₁.mem B (slot w 2 + 8 * (h - 1))).toNat = D * 2 ^ (64 * C) / 2 ^ (64 * (h - 1)) := by
      rw [word_top (n := w) (by omega_arith) (by rw [d1, show h - 1 + 1 = h by omega_arith, ← hP]; exact hD'hi), d1]
    rw [top1] at hz
    have nb := LongDivision.norm_bounds hD'lo hD'hi
    rw [hz] at nb
    have hDz : D * 2 ^ (64 * C) * 2 ^ z < 2 ^ (64 * h) := hP ▸ nb.2
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hDz (Nat.pow_le_pow_right (by decide) (by omega_arith)))] at D8
    have hNz : N * 2 ^ (64 * C) * 2 ^ z < 2 ^ (64 * (2 * h)) := by
      calc N * 2 ^ (64 * C) * 2 ^ z < 2 ^ (64 * h) * 2 ^ (64 * C) * 2 ^ z :=
            Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right hNh (Nat.two_pow_pos _)) (Nat.two_pow_pos _)
        _ = 2 ^ (64 * h + 64 * C + z) := by rw [Nat.pow_add, Nat.pow_add]
        _ ≤ 2 ^ (64 * (2 * h)) := Nat.pow_le_pow_right (by decide) (by omega_arith)
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hNz (Nat.pow_le_pow_right (by decide) (by omega_arith)))] at N9
    have top6 : 2 ^ 63 ≤ (word t₆.mem B (slot w 8 + 8 * (h - 1))).toNat := by
      rw [word_top (n := w) (by omega_arith) (by rw [D8, show h - 1 + 1 = h by omega_arith]; exact hDz), D8]
      exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by rw [Nat.mul_comm]; exact nb.1)
    have same : wv t.mem B (slot w 8) w = wv t₆.mem B (slot w 8) w := by
      apply wv_congr
      intro i hi
      by_cases hi' : i = h - 1
      · subst hi'; rw [top7, or_top_eq top6]
      · exact o7.word (by omega_arith) (by db_omega)
    refine ⟨64 * C + z, ?_, ?_⟩
    · rw [Key.wv_low (k := h) (n := w) (by omega_arith) (by rw [same, D8]; exact hDz), same, D8, Nat.pow_add,
        Nat.mul_assoc]
    · rw [o7.wv (by db_omega) (by db_omega), Key.wv_low (k := 2 * h) (n := w) (by omega_arith) (by rw [N9]; exact hNz),
        N9, Nat.pow_add, Nat.mul_assoc]
  · unfold mw
    rw [o7.word (by db_omega) (by db_omega), o6.word (by db_omega) (by db_omega), o5.word (by db_omega) (by db_omega),
      o4.word (by db_omega) (by db_omega), o3.word (by db_omega) (by db_omega), o2.word (by db_omega) (by db_omega),
      f1.word_eq (by
        simp only [dnRs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨by db_omega, by db_omega⟩) (by db_omega)]
  · exact fd1.trans ((((((fr o2 fun y => by db_omega).trans (fr o3 fun y => by db_omega)).trans
      (fr o4 fun y => by db_omega)).trans (fr o5 fun y => by db_omega)).trans (fr o6 fun y => by db_omega)).trans
      (fr o7 fun y => by db_omega))

/-- `divB`'s first part (wide): `[5] := n - r` and `[2] := m + 1`. -/
theorem divB1_ok {s : State} {B : Addr} {Z w : Nat} (hw : Ws s B Z w) {N M R : Nat}
    (hN : wv s.mem B (slot w 0) w = N) (hone : wv s.mem B (slot w 1) w = 1) (hM : wv s.mem B (slot w 7) w = M)
    (hR : wv s.mem B (slot w 6) w = R) :
    WP isa (seqs [zeroA 5, subA 5 0 6, zeroA 2, addA 2 7 1]) s fun t =>
      (R ≤ N → wv t.mem B (slot w 5) w = N - R) ∧ wv t.mem B (slot w 2) w = (M + 1) % 2 ^ (64 * w) ∧
      mw t.mem B = mw s.mem B ∧ wv t.mem B (slot w 0) w = N ∧ wv t.mem B (slot w 1) w = 1 ∧
      FrmP B (DbP w) s.mem t.mem ∧ Keep mmRegs s t ∧ Ws t B Z w := by
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  have hZ' : 256 + 16 * (8 * (w + 2)) ≤ Z := hZ
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_ok hw (j := 5) (by decide)) fun t₁ ⟨_, o1, k1⟩ => ?_)
  have h₁ := hw.congrO o1 (by db_omega) k1 (by simp)
  refine WP.seq (WP.mono (subA_ok h₁ (t := 5) (a := 0) (b := 6) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t₂ ⟨_, e2, o2, k2⟩ => ?_)
  have h₂ := h₁.congrO o2 (by db_omega) k2 (by simp)
  rw [o1.wv (by db_omega) (by db_omega), o1.wv (by db_omega) (by db_omega), hN, hR] at e2
  refine WP.seq (WP.mono (zeroA_ok h₂ (j := 2) (by decide)) fun t₃ ⟨_, o3, k3⟩ => ?_)
  have h₃ := h₂.congrO o3 (by db_omega) k3 (by simp)
  refine WP.mono (addA_ok h₃ (o := 2) (a := 7) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t ⟨v4, o4, k4⟩ => ?_
  have fr : ∀ {o n : Nat} {m m' : Mem}, Outside B o n m m' → (∀ y, o ≤ y → y < o + n → DbP w y) →
      FrmP B (DbP w) m m' := fun ho hP => FrmP.of_out ho hP
  refine ⟨fun hle => ?_, ?_, ?_, ?_, ?_, (((fr o1 fun y => by db_omega).trans (fr o2 fun y => by db_omega)).trans
    (fr o3 fun y => by db_omega)).trans (fr o4 fun y => by db_omega),
    (((k1.trans k2).trans k3).trans k4).mono (by simp [mmRegs]), h₃.congrO o4 (by db_omega) k4 (by simp)⟩
  · rw [o4.wv (by db_omega) (by db_omega), o3.wv (by db_omega) (by db_omega)]
    have : decide (N < R) = false := by simp only [decide_eq_false_iff_not]; omega_arith
    rw [this] at e2
    simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at e2
    omega_arith
  · rw [v4]
    rw [o3.wv (by db_omega) (by db_omega), o2.wv (by db_omega) (by db_omega), o1.wv (by db_omega) (by db_omega), hM,
      o3.wv (by db_omega) (by db_omega), o2.wv (by db_omega) (by db_omega), o1.wv (by db_omega) (by db_omega), hone]
  · unfold mw
    rw [o4.word (by db_omega) (by db_omega), o3.word (by db_omega) (by db_omega), o2.word (by db_omega) (by db_omega),
      o1.word (by db_omega) (by db_omega)]
  · rw [o4.wv (by db_omega) (by db_omega), o3.wv (by db_omega) (by db_omega), o2.wv (by db_omega) (by db_omega),
      o1.wv (by db_omega) (by db_omega), hN]
  · rw [o4.wv (by db_omega) (by db_omega), o3.wv (by db_omega) (by db_omega), o2.wv (by db_omega) (by db_omega),
      o1.wv (by db_omega) (by db_omega), hone]

/-- `divB`'s last part (wide): `qDiv 1` of `A₂ = [9]` (its low `2 h` words) by
`M = [8]` (its low `h`); the mask and'ed with `A₂ mod M = 0`; `[4] := A₂ / M + 1`. -/
theorem divB3_ok {s : State} {B : Addr} {Z w h : Nat} (hw : Ws s B Z w) (hwh : w = 2 * h + 4) (h8 : 8 ≤ h)
    {c : Bool} (hone : wv s.mem B (slot w 1) w = 1) (hm : mw s.mem B = mask c)
    (hd : 2 ^ 63 ≤ (word s.mem B (slot w qD + 8 * (h - 1))).toNat) :
    WP isa (seqs (qDiv 1 ++ (([zeroA 3] : List (Prog isa)) ++ (eqA 12 3 ++
      ([.block CrtValues.andZero, zeroA 4, addA 4 11 1] : List (Prog isa)))))) s fun t =>
      wv t.mem B (slot w 4) w = (wv s.mem B (slot w 9) (2 * h) / wv s.mem B (slot w 8) h + 1) % 2 ^ (64 * w) ∧
      mw t.mem B = mask (c && decide (wv s.mem B (slot w 9) (2 * h) % wv s.mem B (slot w 8) h = 0)) ∧
      FrmP B (DbP w) s.mem t.mem ∧ Keep mmRegs s t ∧ Ws t B Z w := by
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  have hZ := hw.hZ
  have hZ' : 256 + 16 * (8 * (w + 2)) ≤ Z := hZ
  have hw2 := hw.w2
  have L : QLay w h 1 := ⟨hwh, h8, by decide, by decide⟩
  generalize hA2 : wv s.mem B (slot w 9) (2 * h) = A2
  generalize hM : wv s.mem B (slot w 8) h = M
  have hMpos : 0 < M := by
    rw [← hM]
    have e := wv_add s.mem B (slot w 8) (h - 1) 1
    rw [show h - 1 + 1 = h by omega_arith] at e
    have e1 : wv s.mem B (slot w 8 + 8 * (h - 1)) 1 = (word s.mem B (slot w qD + 8 * (h - 1))).toNat := by
      simp [wv, qD]
    rw [e1] at e
    have : 0 < 2 ^ (64 * (h - 1)) * (word s.mem B (slot w qD + 8 * (h - 1))).toNat :=
      Nat.mul_pos (Nat.two_pow_pos _) (by omega_arith)
    omega_arith
  have hMlt : M < 2 ^ (64 * h) := hM ▸ wv_lt _ _ _ _
  have hA2lt : A2 < 2 ^ (64 * w) := by
    rw [← hA2]; exact Nat.lt_of_lt_of_le (wv_lt _ _ _ _) (Nat.pow_le_pow_right (by decide) (by omega_arith))
  refine wp_seqs_append (by simp [qDiv]) (by simp) (WP.mono (qDiv_ok hw L hd) fun t₁ ⟨r1, q1, h₁, f1, k1⟩ => ?_)
  simp only [qR, qQ, qA, qD] at r1 q1 f1
  rw [show 2 * h + 1 - 1 = 2 * h by omega_arith, hA2, hM] at r1 q1
  have fq : FrmP B (DbP w) s.mem t₁.mem := FrmP.of_frm f1 (by
    simp only [qDivRs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨fun y h1 h2 => ?_, fun y h1 h2 => ?_, fun y h1 h2 => ?_, fun y h1 h2 => ?_, fun y h1 h2 => ?_⟩ <;>
      simp only [Bignum.slot, hdrBytes, qQ, qR, qT, qV, sCt, sFn] at h1 h2 <;> db_omega)
  have qs : ∀ d, d + 8 ≤ 256 → d + 8 ≤ 200 ∨ 208 ≤ d → ∀ r ∈ qDivRs w, d + 8 ≤ r.1 ∨ r.1 + r.2 ≤ d := by
    intro d hd hd'
    simp only [qDivRs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> db_omega
  have R1 : wv t₁.mem B (slot w 12) w = A2 % M := by
    rw [Key.wv_low (k := w) (n := w + 2) (by omega_arith) (by
      rw [r1]; exact Nat.lt_of_lt_of_le (Nat.lt_trans (Nat.mod_lt _ hMpos) hMlt)
        (Nat.pow_le_pow_right (by decide) (by omega_arith))), r1]
  have Q1 : wv t₁.mem B (slot w 11) w = A2 / M := by
    rw [Key.wv_low (k := w) (n := w + 2) (by omega_arith) (by
      rw [q1]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hA2lt), q1]
  have one₁ : wv t₁.mem B (slot w 1) w = 1 := by
    rw [f1.wv_eq (by
      simp only [qDivRs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> db_omega) (by db_omega), hone]
  have m₁ : mw t₁.mem B = mask c := by
    unfold mw at hm ⊢; rw [f1.word_eq (qs _ (by db_omega) (by db_omega)) (by db_omega), hm]
  refine wp_seqs_append (by simp) (by simp [eqA]) (WP.mono (zeroA_ok h₁ (j := 3) (by decide))
    fun t₂ ⟨z2, o2, k2⟩ => ?_)
  have h₂ := h₁.congrO o2 (by db_omega) k2 (by simp)
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok h₂ (a := 12) (b := 3) (by decide) (by decide))
    fun t₃ ⟨hz3, m3, k3⟩ => ?_)
  have z3 : wv t₂.mem B (slot w 3) w = 0 := by
    rw [Key.wv_low (k := w) (n := w + 2) (by omega_arith) (by rw [z2]; exact Nat.two_pow_pos _), z2]
  rw [z3, o2.wv (by db_omega) (by db_omega), R1] at hz3
  have h₃ : Ws t₃ B Z w := h₂.congrP (P := fun _ => False) (fun _ _ => by rw [m3]) (fun _ f => f.elim) k3 (by simp)
  simp only [seqs]
  refine WP.seq (WP.mono (andZero_ok h₃ (c := c) (by
    rw [m3, o2.word (by db_omega) (by db_omega)]; exact m₁) hz3) fun t₄ ⟨m4, k4⟩ => ?_)
  have h₄ := h₃.congrW m4 (by unfold DOk; simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega_arith) (by decide)
    k4 (by simp)
  have o4 : Outside B (8 * Impl.Bignum.X86_64.Public.sMask) 8 t₃.mem t₄.mem := by
    rw [m4]; exact writeW_outside _ _ _ (by db_omega)
  refine WP.seq (WP.mono (zeroA_ok h₄ (j := 4) (by decide)) fun t₅ ⟨_, o5, k5⟩ => ?_)
  have h₅ := h₄.congrO o5 (by db_omega) k5 (by simp)
  refine WP.mono (addA_ok h₅ (o := 4) (a := 11) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t ⟨v6, o6, k6⟩ => ?_
  have fr : ∀ {o n : Nat} {m m' : Mem}, Outside B o n m m' → (∀ y, o ≤ y → y < o + n → DbP w y) →
      FrmP B (DbP w) m m' := fun ho hP => FrmP.of_out ho hP
  refine ⟨?_, ?_, ?_, (((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).mono (by simp [mmRegs]),
    h₅.congrO o6 (by db_omega) k6 (by simp)⟩
  · rw [v6, o5.wv (by db_omega) (by db_omega), o4.wv (by db_omega) (by db_omega), m3,
      o2.wv (by db_omega) (by db_omega), Q1, o5.wv (by db_omega) (by db_omega), o4.wv (by db_omega) (by db_omega), m3,
      o2.wv (by db_omega) (by db_omega), one₁]
  · unfold mw
    rw [o6.word (by db_omega) (by db_omega), o5.word (by db_omega) (by db_omega), m4, word_writeW_self]
  · rw [show FrmP B (DbP w) s.mem t.mem = FrmP B (DbP w) s.mem t.mem from rfl]
    have f3 : FrmP B (DbP w) t₂.mem t₃.mem := by rw [m3]; exact FrmP.refl _ _ _
    exact ((((fq.trans (fr o2 fun y => by db_omega)).trans f3).trans (fr o4 fun y => by db_omega)).trans
      (fr o5 fun y => by db_omega)).trans (fr o6 fun y => by db_omega)

/-- `divB` (wide, `w = 2 h + 4`): for `n` (wide 0), `m` (wide 7), `r` (wide 6)
and the mask `c`, where `c` and `m, r < n < 2^(64 h)`: `q = ⌊(n - r) / (m + 1)⌋`;
`b = q + 1` into wide array 4 and the mask and'ed with `(n - r) mod (m + 1) = 0`. -/
theorem divB_ok {s : State} {B : Addr} {Z w h : Nat} (hw : Ws s B Z w) (hwh : w = 2 * h + 4) (h8 : 8 ≤ h)
    (h128 : h ≤ 128) {N M R : Nat} {c : Bool} (hN : wv s.mem B (slot w 0) w = N) (hNh : N < 2 ^ (64 * h))
    (hone : wv s.mem B (slot w 1) w = 1) (hM : wv s.mem B (slot w 7) w = M) (hR : wv s.mem B (slot w 6) w = R)
    (hm : mw s.mem B = mask c) (hc : c = true → M < N ∧ R < N) :
    WP isa (seqs divB) s fun t => ∃ q, (c = true → q = (N - R) / (M + 1)) ∧
      wv t.mem B (slot w 4) w = (q + 1) % 2 ^ (64 * w) ∧
      mw t.mem B = mask (c && decide ((N - R) % (M + 1) = 0)) ∧
      FrmP B (DbP w) s.mem t.mem ∧ Keep mmRegs s t ∧ Ws t B Z w := by
  unfold divB
  rw [show [zeroA 5, subA 5 0 6, zeroA 2, addA 2 7 1] ++ normDN ++ qDiv 1 ++ [zeroA 3] ++ eqA 12 3 ++
      [.block CrtValues.andZero, zeroA 4, addA 4 11 1] = [zeroA 5, subA 5 0 6, zeroA 2, addA 2 7 1] ++ (normDN ++
      (qDiv 1 ++ ([zeroA 3] ++ (eqA 12 3 ++ [.block CrtValues.andZero, zeroA 4, addA 4 11 1])))) by
    simp only [List.append_assoc]]
  refine wp_seqs_append (by simp) (by simp [normDN]) (WP.mono (divB1_ok hw hN hone hM hR)
    fun t₁ ⟨n1, d1, mm1, N1, one1, f1, k1, h₁⟩ => ?_)
  refine wp_seqs_append (by simp [normDN]) (by simp [qDiv]) (WP.mono (normDN_ok h₁ hwh h8 h128 (D := (M + 1) %
    2 ^ (64 * w)) (N := wv t₁.mem B (slot w 5) w) d1 rfl) fun t₂ ⟨top2, ex2, mm2, f2, k2, h₂⟩ => ?_)
  have one₂ : wv t₂.mem B (slot w 1) w = 1 := by rw [f2.wv_eq (fun y => by db_omega) (by db_omega), one1]
  refine WP.mono (divB3_ok h₂ hwh h8 (c := c) one₂ (by rw [mm2, mm1, hm]) top2) fun t ⟨v3, m3, f3, k3, h₃⟩ => ?_
  refine ⟨wv t₂.mem B (slot w 9) (2 * h) / wv t₂.mem B (slot w 8) h, fun hc' => ?_, v3, ?_, (f1.trans f2).trans f3,
    ((k1.trans k2).trans k3).mono (by simp [mmRegs]), h₃⟩
  · obtain ⟨hMN, hRN⟩ := hc hc'
    have hDw : M + 1 < 2 ^ (64 * w) :=
      Nat.lt_of_le_of_lt (by omega_arith) (Nat.lt_of_lt_of_le hNh (Nat.pow_le_pow_right (by decide) (by omega_arith)))
    rw [Nat.mod_eq_of_lt hDw] at ex2
    obtain ⟨sh, e8, e9⟩ := ex2 (by omega_arith) (by omega_arith) (by rw [n1 (by omega_arith)]; omega_arith)
    rw [e8, e9, n1 (by omega_arith), Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _)]
  · rw [m3]
    cases c
    · rfl
    · obtain ⟨hMN, hRN⟩ := hc rfl
      have hDw : M + 1 < 2 ^ (64 * w) :=
        Nat.lt_of_le_of_lt (by omega_arith) (Nat.lt_of_lt_of_le hNh (Nat.pow_le_pow_right (by decide) (by omega_arith)))
      rw [Nat.mod_eq_of_lt hDw] at ex2
      obtain ⟨sh, e8, e9⟩ := ex2 (by omega_arith) (by omega_arith) (by rw [n1 (by omega_arith)]; omega_arith)
      rw [e8, e9, n1 (by omega_arith), Nat.mul_mod_mul_right]
      have hp := Nat.two_pow_pos sh
      congr 2
      exact decide_eq_decide.mpr ⟨fun h0 => by
        rcases Nat.mul_eq_zero.mp h0 with h | h
        · exact h
        · omega_arith, fun h0 => by rw [h0, Nat.zero_mul]⟩

/-! ## `b²` with rows of `v` words -/

theorem half1_ofNat {W : Nat} (hW : 2 ≤ W) (hW' : W < 2 ^ 63) :
    BitVec.ofNat 64 W >>> 1 - 1 = BitVec.ofNat 64 (W / 2 - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    show (1 : BitVec 64).toNat = 1 from rfl]
  omega_arith

/-- `prodB` (wide, `w = 2 u + 2`): `M = (d mod 2^(64 u)) (e mod 2^(64 u))` with rows of
`u` words, for `e`'s length `8 u`. -/
theorem prodB_ok {s : State} {B : Addr} {Z w u : Nat} (h : Ws s B Z w) (hwu : w = 2 * u + 2) (hu : 1 ≤ u)
    (hel : word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 (8 * u)) :
    WP isa (seqs prodB) s fun t =>
      wv t.mem B (slot w Recover.aM) (2 * (w + 2)) =
        wv s.mem B (slot w Recover.aD) u * wv s.mem B (slot w Recover.aE) u ∧
      Outside B (slot w Recover.aM) (16 * (w + 2)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := h.scr.nowrap
  have hZ := h.hZ
  have hw1 := h.w1
  have hw2 := h.w2
  have sE := slot_lt (w := w) (show Recover.aE < 16 by decide)
  have sD := slot_lt (w := w) (show Recover.aD < 16 by decide)
  have sM := slot_lt (w := w) (show Recover.aM + 1 < 16 by decide)
  have eM1 : slot w (Recover.aM + 1) = slot w Recover.aM + 8 * (w + 2) := by
    simp only [slot, hdrBytes, Recover.aM]; omega_arith
  have eDM : slot w Recover.aD + 8 * (w + 2) = slot w Recover.aM := by
    simp only [slot, hdrBytes, Recover.aD, Recover.aM]; omega_arith
  have eEM : slot w Recover.aE + 8 * (w + 2) = slot w Recover.aD := by
    simp only [slot, hdrBytes, Recover.aE, Recover.aD]; omega_arith
  unfold prodB
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_ok h (j := Recover.aM) (by decide)) fun s₁ ⟨z₁, o₁, k₁⟩ => ?_)
  have h₁ := h.congr (Frm.of_outside o₁ (List.mem_singleton_self _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact Mut.ofSlot _ _ _) k₁ (by decide)
  refine WP.seq (WP.mono (zeroA_ok h₁ (j := Recover.aM + 1) (by decide)) fun s₂ ⟨z₂, o₂, k₂⟩ => ?_)
  have h₂ := h₁.congr (Frm.of_outside o₂ (List.mem_singleton_self _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact Mut.ofSlot _ _ _) k₂ (by decide)
  have o12 : Outside B (slot w Recover.aM) (16 * (w + 2)) s.mem s₂.mem := fun x hx => by
    rw [o₂ x (by omega_arith), o₁ x (by omega_arith)]
  have hel₂ : word s₂.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 (8 * u) := by
    have := hdr_lt_slot w Recover.aM (show Impl.Bignum.X86_64.Public.sElen < 32 by decide)
    rw [o12.word (Or.inl (by omega_arith)) (by simp only [Impl.Bignum.X86_64.Public.sElen, sFn]; omega_arith)]
    exact hel
  have hz : wv s₂.mem B (slot w Recover.aM) (2 * (w + 2)) = 0 := by
    rw [show 2 * (w + 2) = (w + 2) + (w + 2) by omega_arith, wv_add, ← eM1, z₂,
      o₂.wv (Or.inl (by omega_arith)) (by omega_arith), z₁, Nat.mul_zero]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (prodInit_ok h₂ hel₂ (by omega_arith))
    fun s₃ ⟨h12, hbx, h10, h15, h11, h13, hdi, m₃, k₃⟩ =>
    WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 u ∧ t.mem = s₃.mem)
      (by xrun [h12, half1_ofNat (W := w) (by omega_arith) (by omega_arith), show w / 2 - 1 = u by omega_arith])
      rfl) fun s₄ ⟨⟨h12', m₄⟩, k₄⟩ => (show WP isa (.loop _ .ne) s₄ _ from ?_)))
  have hs₄ := h₂.scr.congr (k₃.trans k₄).2.2
  rw [show (8 * u + 7) / 8 = u by omega_arith] at h11
  refine wp_upto (a := 0) (N := u) hu (ProdInv s₄ B Z w u)
    (fun j _ hj t hI => prodStep_ok hI hu (by omega_arith) (by omega_arith) hZ (by omega_arith) hj h12'
      ((k₄.gpr (by decide)).trans hbx) ((k₄.gpr (by decide)).trans h10) ((k₄.gpr (by decide)).trans h15)
      ((k₄.gpr (by decide)).trans h11))
    (fun t hI => ?_) ⟨hs₄, Keep.refl _ _, (k₄.gpr (by decide)).trans h13, Outside.refl _ _ _ _,
      by rw [m₄, m₃, hz, wv, Nat.mul_zero]⟩
  have k04 := (((k₁.trans k₂).trans k₃).trans k₄).trans hI.keep
  have hDs : wv s₄.mem B (slot w Recover.aD) u = wv s.mem B (slot w Recover.aD) u := by
    rw [m₄, m₃]; exact o12.wv (Or.inl (by omega_arith)) (by omega_arith)
  have hEs : wv s₄.mem B (slot w Recover.aE) u = wv s.mem B (slot w Recover.aE) u := by
    rw [m₄, m₃]; exact o12.wv (Or.inl (by omega_arith)) (by omega_arith)
  refine ⟨by rw [hI.val, hDs, hEs], fun x hx => by rw [hI.out x hx, m₄, m₃]; exact o12 x hx,
    k04.mono (by simp [mmRegs])⟩

/-! ## `b² - 4 n` (wide) -/

/-- What `minus4n` changes: wide arrays 0 and 7 to 15, and the mask. -/
def MnP (w y : Nat) : Prop := (slot w 0 ≤ y ∧ y < slot w 1) ∨ (slot w 7 ≤ y ∧ y < slot w 16) ∨ (176 ≤ y ∧ y < 184)

macro "mn_omega" : tactic =>
  `(tactic| (simp only [MnP, DOk, Bignum.slot, hdrBytes, Impl.Bignum.X86_64.Public.sMask,
    Impl.Bignum.X86_64.Public.sElen, sFn, ar]; omega_arith))

/-- `minus4n` (wide, `w = 2 v + 2`): `b²` (`b` in wide array 4, below
`2^(64 v)`), `4 n` (`n` in wide array 0, doubled twice in place), `X = b² - 4 n`
into wide array 7, and the mask and'ed with `b² > 4 n` as `ok4Of` says. -/
theorem minus4n_ok {s : State} {B : Addr} {Z w v : Nat} (h : Ws s B Z w) (hwv : w = 2 * v + 2) (hv1 : 1 ≤ v)
    {N b : Nat} {c : Bool} (hN : wv s.mem B (slot w 0) w = N) (hone : wv s.mem B (slot w 1) w = 1)
    (hb : wv s.mem B (slot w 4) w % 2 ^ (64 * v) = b)
    (hel : word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 (4 * w - 8))
    (hm : mw s.mem B = mask c) :
    WP isa (seqs minus4n) s fun t =>
      wv t.mem B (slot w 7) w = xOf (64 * v) (64 * w) N b ∧ mw t.mem B = mask (c && ok4Of (64 * v) (64 * w) N b) ∧
      FrmP B (MnP w) s.mem t.mem ∧ Keep mmRegs s t ∧ Ws t B Z w := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hZ := h.hZ
  have hZ' : 256 + 16 * (8 * (w + 2)) ≤ Z := hZ
  have hw1 := h.w1
  have hw2 := h.w2
  have hbv : b < 2 ^ (64 * v) := hb ▸ Nat.mod_lt _ (Nat.two_pow_pos _)
  have hbw : b < 2 ^ (64 * w) := Nat.lt_of_lt_of_le hbv (Nat.pow_le_pow_right (by decide) (by omega_arith))
  have hNw : N < 2 ^ (64 * w) := hN ▸ wv_lt _ _ _ _
  simp only [minus4n, List.cons_append, List.nil_append, seqs]
  refine WP.seq (WP.mono (copyA_ok h (o := 8) (a := 4) (by decide) (by decide) (by decide)) fun t₁ ⟨v1, o1, k1⟩ => ?_)
  have h₁ := h.congrO o1 (by mn_omega) k1 (by simp)
  refine WP.seq (WP.mono (copyA_ok h₁ (o := 9) (a := 4) (by decide) (by decide) (by decide)) fun t₂ ⟨v2, o2, k2⟩ => ?_)
  have h₂ := h₁.congrO o2 (by mn_omega) k2 (by simp)
  have E₂ : wv t₂.mem B (slot w 8) w = wv s.mem B (slot w 4) w := by rw [o2.wv (by mn_omega) (by mn_omega), v1]
  have D₂ : wv t₂.mem B (slot w 9) w = wv s.mem B (slot w 4) w := by rw [v2, o1.wv (by mn_omega) (by mn_omega)]
  have el₂ : word t₂.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 (4 * w - 8) := by
    rw [o2.word (by mn_omega) (by mn_omega), o1.word (by mn_omega) (by mn_omega), hel]
  -- `b²`.
  refine wp_seqs_append (by simp [prodB]) (by simp) (WP.mono (prodB_ok h₂ (u := v) hwv hv1
    (by rw [el₂]; congr 1; omega_arith)) fun t₃ ⟨v3, o3, k3⟩ => ?_)
  simp only [Recover.aE, Recover.aD, Recover.aM] at v3 o3
  rw [← wv_mod_low t₂.mem B (slot w 8) (c := v) (n := w) (by omega_arith), E₂, hb,
    ← wv_mod_low t₂.mem B (slot w 9) (c := v) (n := w) (by omega_arith), D₂, hb] at v3
  have h₃ := h₂.congrO o3 (by mn_omega) k3 (by simp [mmRegs])
  have S₃ : wv t₃.mem B (slot w 10) w = b * b % 2 ^ (64 * w) := by
    rw [← v3, show 2 * (w + 2) = w + (w + 4) by omega_arith]; exact wv_low_mod
  -- `4 n`.
  simp only [seqs]
  refine WP.seq (WP.mono (shlA_ok h₃ false (j := 0) (c₀ := false) (by decide) (shlPre_mask h₃ maskZero))
    fun t₄ ⟨_, _, e4, o4, k4⟩ => ?_)
  simp only [shlN, ↓reduceIte, Bool.false_eq_true] at e4 o4
  have h₄ := h₃.congrO o4 (by mn_omega) k4 (by simp)
  refine WP.seq (WP.mono (shlA_ok h₄ false (j := 0) (c₀ := false) (by decide) (shlPre_mask h₄ maskZero))
    fun t₅ ⟨_, _, e5, o5, k5⟩ => ?_)
  simp only [shlN, ↓reduceIte, Bool.false_eq_true] at e5 o5
  have h₅ := h₄.congrO o5 (by mn_omega) k5 (by simp)
  have N₃ : wv t₃.mem B (slot w 0) w = N := by
    rw [o3.wv (by mn_omega) (by mn_omega), o2.wv (by mn_omega) (by mn_omega), o1.wv (by mn_omega) (by mn_omega), hN]
  have F₅ : wv t₅.mem B (slot w 0) w = fourN (64 * w) N := by
    rw [N₃] at e4
    obtain ⟨v4', _⟩ := dbl_val e4 (wv_lt _ _ _ _)
    obtain ⟨v5', _⟩ := dbl_val e5 (wv_lt _ _ _ _)
    rw [v5', v4']
    simp only [Bool.toNat_false, Nat.add_zero, fourN]
  have S₅ : wv t₅.mem B (slot w 10) w = sqOf (64 * v) (64 * w) b := by
    rw [o5.wv (by mn_omega) (by mn_omega), o4.wv (by mn_omega) (by mn_omega), S₃]
    unfold sqOf
    rw [prod_iter _ _ _ hbw]
    simp only
    rw [Nat.mod_eq_of_lt hbv]
  -- `X = b² - 4 n` and the checks.
  refine WP.seq (WP.mono (subA_ok h₅ (t := 12) (a := 10) (b := 0) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t₆ ⟨hb6, e6, o6, k6⟩ => ?_)
  rw [S₅, F₅] at hb6 e6
  have h₆ := h₅.congrO o6 (by mn_omega) k6 (by simp)
  have hm₆ : mw t₆.mem B = mask c := by
    unfold mw at hm ⊢
    rw [o6.word (by mn_omega) (by mn_omega), o5.word (by mn_omega) (by mn_omega), o4.word (by mn_omega) (by mn_omega),
      o3.word (by mn_omega) (by mn_omega), o2.word (by mn_omega) (by mn_omega), o1.word (by mn_omega) (by mn_omega), hm]
  refine WP.seq (WP.mono (andB_ok h₆ hm₆ hb6) fun t₇ ⟨m7, k7⟩ => ?_)
  have h₇ := h₆.congrW m7 (by mn_omega) (by decide) k7 (by simp)
  have o7 : Outside B (8 * Impl.Bignum.X86_64.Public.sMask) 8 t₆.mem t₇.mem := by
    rw [m7]; exact writeW_outside _ _ _ (by mn_omega)
  have X₇ : wv t₇.mem B (slot w 12) w = xOf (64 * v) (64 * w) N b := by
    rw [o7.wv (by mn_omega) (by mn_omega)]
    exact wsub_of_eq e6 (wv_lt _ _ _ _) (S₅ ▸ wv_lt _ _ _ _) (F₅ ▸ wv_lt _ _ _ _)
  have one₇ : wv t₇.mem B (slot w 1) w = 1 := by
    rw [o7.wv (by mn_omega) (by mn_omega), o6.wv (by mn_omega) (by mn_omega), o5.wv (by mn_omega) (by mn_omega),
      o4.wv (by mn_omega) (by mn_omega), o3.wv (by mn_omega) (by mn_omega), o2.wv (by mn_omega) (by mn_omega),
      o1.wv (by mn_omega) (by mn_omega), hone]
  refine WP.seq (WP.mono (subA_ok h₇ (t := 13) (a := 12) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun t₈ ⟨hb8, _, o8, k8⟩ => ?_)
  rw [X₇, one₇] at hb8
  have h₈ := h₇.congrO o8 (by mn_omega) k8 (by simp)
  have hm₈ : mw t₈.mem B = mask (c && !decide (sqOf (64 * v) (64 * w) b < fourN (64 * w) N)) := by
    unfold mw
    rw [o8.word (by mn_omega) (by mn_omega), m7, word_writeW_self]
  refine WP.seq (WP.mono (andB_ok h₈ hm₈ hb8) fun t₉ ⟨m9, k9⟩ => ?_)
  have h₉ := h₈.congrW m9 (by mn_omega) (by decide) k9 (by simp)
  have o9 : Outside B (8 * Impl.Bignum.X86_64.Public.sMask) 8 t₈.mem t₉.mem := by
    rw [m9]; exact writeW_outside _ _ _ (by mn_omega)
  refine WP.mono (copyA_ok h₉ (o := 7) (a := 12) (by decide) (by decide) (by decide)) fun t ⟨v10, o10, k10⟩ => ?_
  have fr : ∀ {o n : Nat} {m m' : Mem}, Outside B o n m m' → (∀ y, o ≤ y → y < o + n → MnP w y) →
      FrmP B (MnP w) m m' := fun ho hP => FrmP.of_out ho hP
  refine ⟨?_, ?_, ?_, ?_, h₉.congrO o10 (by mn_omega) k10 (by simp)⟩
  · rw [v10, o9.wv (by mn_omega) (by mn_omega), o8.wv (by mn_omega) (by mn_omega), X₇]
  · unfold mw
    rw [o10.word (by mn_omega) (by mn_omega), m9, word_writeW_self, ok4Of, Bool.not_or, Bool.and_assoc]
  · exact (((((((((fr o1 fun y => by mn_omega).trans (fr o2 fun y => by mn_omega)).trans (fr o3 fun y => by mn_omega)).trans
      (fr o4 fun y => by mn_omega)).trans (fr o5 fun y => by mn_omega)).trans (fr o6 fun y => by mn_omega)).trans
      (fr o7 fun y => by mn_omega)).trans (fr o8 fun y => by mn_omega)).trans (fr o9 fun y => by mn_omega)).trans
      (fr o10 fun y => by mn_omega)
  · exact (((((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).trans k8).trans k9).trans k10).mono
      (by simp [mmRegs])

end VG.Proof.Rsa.X86_64.Rd
