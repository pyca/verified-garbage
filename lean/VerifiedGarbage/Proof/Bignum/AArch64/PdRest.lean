import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
import Mathlib.Data.Int.GCD

/-!
# `vg_rsa_public_precomputed` on AArch64: the computation

The input, the mask of `input < m`, `-m⁻¹` and the number 1 (`pdSetup_ok`),
then the exponentiation and the result (`pdRest_ok`), for any values of `m`
and `R² mod m` that pass the checks.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Precomputed
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

variable {M : Mont}

/-- What the public-key operation leaves: `i2osp r k` to `out`, the flag `c`
returned, and memory outside the working space and `out` unchanged. -/
structure MainPost (s t : State) (B : Addr) (Z k : Nat) (op : Addr) (r : Nat) (c : Bool) : Prop where
  bytes : (List.range k).map (fun i => t.mem (op + BitVec.ofNat 64 i)) = Spec.Rsa.i2osp r k
  x0 : t.gpr .x0 = BitVec.ofNat 64 c.toNat
  frame : ∀ x, Z ≤ ofs B x → (∀ j < k, x ≠ op + BitVec.ofNat 64 j) → t.mem x = s.mem x
  keep : Keep (.x0 :: mmRegs) s t

/-- What `rest` starts from: the header `entry` leaves, `m` and `R² mod m`
(here any `R < N`) in their arrays, as the checks accepted them. -/
structure PdPre (s : State) (B : Addr) (Z k : Nat) (op ep ip : Addr) (L : Nat) (eb xb : List Byte) (N R : Nat) :
    Prop where
  scr : Scr s B Z
  x0 : s.gpr .x0 = B
  z : slot ((k + 7) / 8) 8 ≤ Z
  k1 : 64 ≤ k
  k2 : k ≤ 1024
  hO : word s.mem B (8 * sOut) = op
  hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k
  hE : word s.mem B (8 * sE) = ep
  hL : word s.mem B (8 * sElen) = BitVec.ofNat 64 L
  hIn : word s.mem B (8 * sIn) = ip
  hW : word s.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8)
  hb : ∀ j < 8, word s.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j)
  n : wv s.mem B (slot ((k + 7) / 8) aN) ((k + 7) / 8) = N
  r : wv s.mem B (slot ((k + 7) / 8) aR2) ((k + 7) / 8) = R
  odd : N % 2 = 1
  n1 : 1 < N
  rlt : R < N
  x : Src s B Z ip xb
  e : Src s B Z ep eb
  xl : xb.length = k
  el : eb.length = L
  L1 : 1 ≤ L
  L2 : L ≤ k
  out : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1
  outSep : ∀ j < k, Z ≤ ofs B (op + BitVec.ofNat 64 j)

/-- `x` with `x R ≡ X`, for `R` invertible modulo `N > 1`. -/
theorem exists_mont {R N : Nat} (hR : Nat.Coprime R N) (hN1 : 1 < N) (X : Nat) :
    ∃ x, X % N = x * R % N := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hR hN1
  refine ⟨X * m, ?_⟩
  rw [Nat.mul_assoc, Nat.mul_mod, Nat.mul_comm m R, hm, Nat.mul_one, Nat.mod_mod]

/-- The input into its array. -/
theorem pdIn_ok {s : State} {B : Addr} {Z k : Nat} {ip : Addr} {xb : List Byte} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 9 ≤ k) (hk : k < 2 ^ 31)
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hIn : word s.mem B (8 * sIn) = ip)
    (hb : ∀ j < 8, word s.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j)) (hx : Src s B Z ip xb)
    (hxl : xb.length = k) :
    WP isa (.seq (.block [ldh .x1 sIn, ldh .x2 sK, ldh .x8 (sArr aX)]) loadBE) s fun t =>
      wv t.mem B (slot ((k + 7) / 8) aX) ((k + 7) / 8) = Spec.Rsa.os2ip xb ∧
      Arrays B ((k + 7) / 8) [aX] s.mem t.mem ∧ Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x8] s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
  have h0' := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
  have eK : sK = 18 := rfl
  have eIn : sIn = 21 := rfl
  have eAX : sArr aX = 9 := rfl
  refine WP.seq (WP.mono (WP.keep [.x1, .x2, .x8] (Q := fun t => t.gpr .x1 = ip ∧
      t.gpr .x2 = BitVec.ofNat 64 k ∧ t.gpr .x8 = off B (slot ((k + 7) / 8) aX) ∧ t.mem = s.mem) (by
    brun [h0, hdr_enc (show sIn < 32 by decide), hdr_enc (show sK < 32 by decide),
      hdr_enc (show sArr aX < 32 by decide), hs.ld (d := 8 * sIn) (by omega_using [hZ, h8, h0', eIn]),
          hs.ld (d := 8 * sK) (by omega_using [hZ, h8, h0', eK]),
      hs.ld (d := 8 * sArr aX) (by omega_using [hZ, h8, h0', eAX]), hIn, hK,
          hb aX (by decide)]) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨h1, h2, h8', hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (loadArr_ok (hs.congr k₁.wr) (by decide) hZ
    (hx.congrK (by rw [hm₁]; exact InScr.refl _ _ _) k₁) hxl (by omega_using [hk1]) hk h1 h2 h8')
    fun t ⟨hv, ha, k₂⟩ => ⟨hv, by rw [hm₁] at ha; exact ha, (k₁.trans k₂).mono (by decide)⟩

/-- After the setup: the modulus `N`, `-N⁻¹` in the header, the input `X`,
the number 1, and the mask of `X < N`. -/
structure SetupOut (t : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N X : Nat) : Prop where
  good : Good t B Z w minv
  n : wv t.mem B (slot w aN) w = N
  inv : ((word t.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0
  x : wv t.mem B (slot w aX) w = X
  one : wv t.mem B (slot w aOne) w = 1
  mask : word t.mem B (8 * sMask) = mask (decide (X < N))

theorem csel_mask (c : Bool) :
    (if (!c) = true then (0 : BitVec 64) else 0 - BitVec.ofNat 64 1) = mask c := by
  cases c <;> rfl

/-- The steps after the input: the mask of `X < N`, `-N⁻¹` and the number 1. -/
def setupSteps : List (Prog isa) := [
  .block [ldh .x12 sW, ldh .x16 (sArr aX), ldh .x17 (sArr aN), movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7],
  cmpLoop,
  .block ([.subImm .x .x4 .x7 1, .csel .x .x15 .x7 .x4, sth .x15 sMask, ldh .x8 (sArr aN), ld .x3 .x8] ++ minv ++
    [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0]),
  setWord aOne]

/-- The mask of `X < N`, `-N⁻¹` and the number 1. -/
theorem pdSetup_ok {s : State} {B : Addr} {Z w : Nat} {N X : Nat} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hW : word s.mem B (8 * sW) = BitVec.ofNat 64 w)
    (hb : ∀ j < 8, word s.mem B (8 * sArr j) = off B (slot w j))
    (hN : wv s.mem B (slot w aN) w = N) (hX : wv s.mem B (slot w aX) w = X) (hodd : N % 2 = 1) :
    WP isa (seqs setupSteps) s fun t => ∃ minv, SetupOut t B Z w minv N X ∧
      Frm B [(8 * sMinv, 8), (8 * sMask, 8), (slot w aOne, 8 * (w + 2))] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have h0' := slot_le (w := w) (show 0 < 8 by decide)
  have h8 := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have eW : sW = 6 := rfl
  have eM : sMinv = 7 := rfl
  have eK : sMask = 22 := rfl
  have eAX : sArr aX = 9 := rfl
  have eAN : sArr aN = 8 := rfl
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_using [hZ, h0', h8, hi])
  unfold setupSteps
  refine WP.seq (WP.mono (WP.keep [.x3, .x7, .x12, .x14, .x16, .x17] (Q := fun t =>
      t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x16 = off B (slot w aX) ∧ t.gpr .x17 = off B (slot w aN) ∧
      t.gpr .x7 = 0 ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧ t.c = true ∧ t.mem = s.mem) (by
    brun [h0, hdr_enc (show sW < 32 by decide), hdr_enc (show sArr aX < 32 by decide),
      hdr_enc (show sArr aN < 32 by decide), hl sW (by omega_arith), hl (sArr aX) (by omega_using [eAX]),
          hl (sArr aN) (by omega_using [eAN]),
      hW, hb aX (by decide), hb aN (by decide)]) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨h12, h16, h17, h7, h14, hc₁, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  refine WP.seq (WP.mono (cmpLoop_ok hs₁ h16 h17 h14 hc₁ (by omega_using [hw]) hw'
    (by have := slot_le (w := w) (show aX < 8 by decide); omega_using [hZ, this])
    (by have := slot_le (w := w) (show aN < 8 by decide); omega_using [hZ, this])) fun t₂ ⟨hc₂, hm₂, k₂⟩ => ?_)
  rw [hm₁, hN, hX] at hc₂
  have hs₂ := hs₁.congr k₂.wr
  have hm₂' : t₂.mem = s.mem := hm₂.trans hm₁
  have h0₂ : t₂.gpr .x0 = B := (k₂.gpr .x0 (by decide)).trans ((k₁.gpr .x0 (by decide)).trans h0)
  -- `-N⁻¹`.
  have hodd₀ : (word s.mem B (slot w aN)).toNat % 2 = 1 := by
    rw [← wv_mod64 _ _ _ (show 1 ≤ w by omega_using [hw]), Nat.mod_mod_of_dvd _ (by decide), hN, hodd]
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  have hst : ∀ i < 32, InRegions t₂.wr (off B (8 * i)) 8 := fun i hi => hs₂.st (by omega_using [hZ, h0', h8, hi])
  have hsN : (s.mem.writeW (off B (8 * sMask)) (mask (decide (X < N)))).readW (off B (8 * sArr aN)) 64 =
      off B (slot w aN) := by
    rw [← hb aN (by decide)]
    exact (writeW_outside _ B _ (by omega_using [eK])).word (by omega_using [eK, eAN]) (by omega_using [eAN])
  have hsN' : (s.mem.writeW (off B (8 * sMask)) (mask (decide (X < N)))).readW (off B (slot w aN)) 64 =
      word s.mem B (slot w aN) :=
    (writeW_outside _ B _ (by omega_using [eK])).word (by have := hdr_lt_slot w aN (show sMask < 32 by decide); omega_using [this])
      (by have := slot_le (w := w) (show aN < 8 by decide); omega_using [hZ, hn, this])
  refine WP.mono (WP.keep [.x3, .x4, .x8, .x15] (Q := fun t => t.gpr .x3 = word s.mem B (slot w aN) ∧
      t.mem = s.mem.writeW (off B (8 * sMask)) (mask (decide (X < N)))) (by
    brun [h0₂, (k₂.gpr .x7 (by decide)).trans h7, hc₂, hdr_enc (show sMask < 32 by decide),
      hdr_enc (show sArr aN < 32 by decide), hst sMask (by omega_using [eK]), hs₂.ld (d := 8 * sArr aN) (by omega_using [hZ, h0', h8, eAN]),
      hm₂', csel_mask, hsN, hsN', hs₂.ld (d := slot w aN) (by have := slot_le (w := w) (show aN < 8 by decide); omega_using [hZ, this])])
      (by decide) (by decide) (by decide +kernel))
    fun t₃ ⟨⟨h3₃, hm₃⟩, k₃⟩ => ?_
  refine WP.mono (minv_ok t₃ (by rw [h3₃]; exact hodd₀)) fun t₄ ⟨hinv, k₄, hm₄⟩ => ?_
  rw [h3₃] at hinv
  have hs₄ := (hs₂.congr k₃.wr).congr k₄.wr
  have h0₄ : t₄.gpr .x0 = B := (k₄.gpr .x0 (by decide)).trans ((k₃.gpr .x0 (by decide)).trans h0₂)
  have hW₄ : (t₄.mem.writeW (off B (8 * sMinv)) (t₄.gpr .x15)).readW (off B (8 * sW)) 64 = BitVec.ofNat 64 w := by
    rw [← hW]
    have e1 : (t₄.mem.writeW (off B (8 * sMinv)) (t₄.gpr .x15)).readW (off B (8 * sW)) 64 = word t₄.mem B (8 * sW) :=
      (writeW_outside _ B _ (d := 8 * sMinv) (by omega_using [eM])).word (d := 8 * sW) (by omega_using [eW, eM]) (by omega_using [eW])
    rw [e1, hm₄, hm₃]
    exact (writeW_outside _ B _ (d := 8 * sMask) (by omega_using [eK])).word (d := 8 * sW) (by omega_using [eW, eK]) (by omega_using [eW])
  refine WP.mono (WP.keep [.x9, .x12, .x13] (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x9 = 1 ∧
      t.gpr .x13 = BitVec.ofNat 64 0 ∧ t.mem = t₄.mem.writeW (off B (8 * sMinv)) (t₄.gpr .x15)) (by
    brun [h0₄, hdr_enc (show sMinv < 32 by decide), hdr_enc (show sW < 32 by decide),
      hs₄.st (d := 8 * sMinv) (by omega_using [hZ, h0', h8, eM]),
          hs₄.ld (d := 8 * sW) (by omega_using [hZ, h0', h8, eW]), hW₄]) (by decide) (by decide) (by decide +kernel))
    fun t₅ ⟨⟨h12₅, h9₅, h13₅, hm₅⟩, k₅⟩ => ?_
  have hs₅ := hs₄.congr k₅.wr
  have h0₅ : t₅.gpr .x0 = B := (k₅.gpr .x0 (by decide)).trans h0₄
  have hm₅' : t₅.mem = (s.mem.writeW (off B (8 * sMask)) (mask (decide (X < N)))).writeW (off B (8 * sMinv))
      (t₄.gpr .x15) := by rw [hm₅, hm₄, hm₃]
  have hwv : ∀ j < 8, wv t₅.mem B (slot w j) w = wv s.mem B (slot w j) w := fun j hj => by
    have := slot_le (w := w) hj
    rw [hm₅', (writeW_outside _ B _ (by omega_using [eM])).wv (by have := hdr_lt_slot w j (show sMinv < 32 by decide); omega_using [this])
      (by omega_using [hZ, hn, this]), (writeW_outside _ B _ (by omega_using [eK])).wv
      (by have := hdr_lt_slot w j (show sMask < 32 by decide); omega_using [this]) (by omega_arith)]
  have hw0 : word t₅.mem B (slot w aN) = word s.mem B (slot w aN) := by
    have := slot_le (w := w) (show aN < 8 by decide)
    rw [hm₅', (writeW_outside _ B _ (by omega_using [eM])).word
      (by have := hdr_lt_slot w aN (show sMinv < 32 by decide); omega_using [this]) (by omega_using [hZ, hn, this])]; exact hsN'
  have hhd : ∀ i < 32, i ≠ sMask → i ≠ sMinv → word t₅.mem B (8 * i) = word s.mem B (8 * i) := fun i hi h1 h2 => by
    rw [hm₅', hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h2), hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h1)]
  have hH : Hdr t₅.mem B w (t₄.gpr .x15) :=
    ⟨by rw [hhd sW (by decide) (by decide) (by decide)]; exact hW,
      by rw [hm₅', word_writeW_self],
      fun j hj => by rw [hhd (sArr j) (by unfold sArr; omega_using [hj]) (by unfold sArr sMask sFn; omega_using [hj])
        (by unfold sArr sMinv; omega_using [])]; exact hb j hj⟩
  refine WP.mono (setWord_ok hs₅ h0₅ hH hZ h12₅ hw' (o := aOne) (by decide) (i := 0) (by omega_using [hw]) h13₅)
    fun t ⟨hone, ho, k₆⟩ => ⟨t₄.gpr .x15, ?_, ?_, ?_⟩
  · have ha : Arrays B w [aOne] t₅.mem t.mem := Arrays.of_outside (List.mem_singleton_self _) ho
      (Nat.le_refl _) (Nat.le_refl _)
    have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_using [hZ, hn]
    refine ⟨⟨hs₅.congr k₆.wr, (k₆.gpr .x0 (by decide)).trans h0₅, ha.hdr hH⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ha.wv_of_not_mem (by decide) (by decide) hn', hwv aN (by decide), hN]
    · rw [ha.word0_of_not_mem (by decide) (by decide) hn' (by omega_using [hw]), hw0]; exact hinv
    · rw [ha.wv_of_not_mem (by decide) (by decide) hn', hwv aX (by decide), hX]
    · rw [hone, h9₅]; rfl
    · rw [ha.hslot (by decide), hm₅', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hm₅'] at ho
    exact ((Frm.of_outside (writeW_outside _ B _ (by omega_using [eK])) (by simp)).trans
      (Frm.of_outside (writeW_outside _ B _ (by omega_using [eM])) (by simp))).trans (Frm.of_outside ho (by simp))
  · exact (((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).mono (by decide)

/-! ## The result -/

theorem mask_and1 (c : Bool) : mask c &&& 1 = BitVec.ofNat 64 c.toNat := by
  cases c <;> decide

/-- A byte of the working space is not one of `out`'s. -/
theorem scr_ne_out {B out : Addr} {Z k : Nat} (hsep : ∀ j < k, Z ≤ ofs B (out + BitVec.ofNat 64 j))
    {d i : Nat} (hd : d + i < Z) (hZ : Z ≤ 2 ^ 64) :
    ∀ j < k, off B d + BitVec.ofNat 64 i ≠ out + BitVec.ofNat 64 j := by
  intro j hj he
  have h := hsep j hj
  rw [← he, ofs_off B (by omega_using [hd, hZ])] at h
  omega_using [hd, h]

/-- The steps of the result. -/
def outSteps : List (Prog isa) := [
  .block [ldh .x8 (sArr aY), ldh .x1 sOut, ldh .x9 sK, .add .x .x1 .x1 .x9, ldh .x15 sMask],
  storeBE,
  .block [ldh .x0 sMask, movi .x3 1, .logic .and .x .x0 .x0 .x3]]

/-- The result: `i2osp (c ? Y : 0)` to `out`, and `c` returned. -/
theorem outPhase_ok {s : State} {B : Addr} {Z k : Nat} {minv : BitVec 64} {Y : Nat} {out : Addr} {c : Bool}
    (hg : Good s B Z ((k + 7) / 8) minv) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hY : wv s.mem B (slot ((k + 7) / 8) aY) ((k + 7) / 8) = Y)
    (hO : word s.mem B (8 * sOut) = out) (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hM : word s.mem B (8 * sMask) = mask c)
    (hout : ∀ j < k, InRegions s.wr (out + BitVec.ofNat 64 j) 1)
    (hsep : ∀ j < k, Z ≤ ofs B (out + BitVec.ofNat 64 j)) :
    WP isa (seqs outSteps) s fun t =>
      (List.range k).map (fun i => t.mem (out + BitVec.ofNat 64 i)) = Spec.Rsa.i2osp (if c then Y else 0) k ∧
      t.gpr .x0 = BitVec.ofNat 64 c.toNat ∧
      (∀ x, (∀ j < k, x ≠ out + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧
      Keep (.x0 :: mmRegs) s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h0 := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
  have h0' := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_using [hZ, h0, h0', hi])
  unfold outSteps
  refine WP.seq (WP.mono (WP.keep [.x1, .x8, .x9, .x15] (Q := fun t =>
      t.gpr .x8 = off B (slot ((k + 7) / 8) aY) ∧ t.gpr .x1 = out + BitVec.ofNat 64 k ∧
      t.gpr .x9 = BitVec.ofNat 64 k ∧ t.gpr .x15 = mask c ∧ t.mem = s.mem) (by
    brun [hg.x0, hdr_enc (show sArr aY < 32 by decide), hdr_enc (show sOut < 32 by decide),
      hdr_enc (show sK < 32 by decide), hdr_enc (show sMask < 32 by decide),
      hl (sArr aY) (by decide), hl sOut (by decide), hl sK (by decide),
      hl sMask (by decide), hg.hdr.harr aY (by decide), hO, hK, hM]) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨h8, h1, h9, h15, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  refine WP.seq (WP.mono (storeBE_ok hs₁ h8 h1 h9 h15 hk1 hk' rfl
    (by have := slot_le (w := (k + 7) / 8) (show aY < 8 by decide); omega_using [hZ, this])
    (fun j hj => by rw [k₁.wr]; exact hout j hj) hsep) fun t₂ ⟨hb₂, hf₂, hwr₂, hrd₂, k₂⟩ => ?_)
  rw [hm₁, hY] at hb₂
  have hw₂ : ∀ i < 32, word t₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    apply Mem.readW_congr
    intro b hb
    rw [hf₂ _ (scr_ne_out hsep (d := 8 * i) (i := b) (by omega_using [hZ, h0, h0', hi, hb]) (by omega_using [hn])), hm₁]
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off B (8 * i)) 8 := fun i hi => by
    rw [hrd₂, hwr₂, k₁.rd, k₁.wr]; exact hl i hi
  have h0₂ : t₂.gpr .x0 = B := (k₂.gpr .x0 (by decide)).trans ((k₁.gpr .x0 (by decide)).trans hg.x0)
  refine WP.mono (WP.keep [.x0, .x3] (Q := fun t => t.gpr .x0 = BitVec.ofNat 64 c.toNat ∧ t.mem = t₂.mem) (by
    brun [h0₂, hdr_enc (show sMask < 32 by decide), hl₂ sMask (by decide), hw₂ sMask (by decide), hM,
      show BitVec.setWidth 64 (1#16) = (1 : BitVec 64) from rfl, mask_and1])
    (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨hx, hm⟩, k₃⟩ => ⟨by rw [hm]; exact hb₂, hx,
      fun x hx' => by rw [hm, hf₂ x hx', hm₁], ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-! ## `rest` -/

/-- `X = input R`, the exponentiation and `Y R⁻¹`. -/
def pdExp (M : Mont) : List (Prog isa) := [M.mm aXm aX aR2, Precomputed.expLoop M.mm, Precomputed.finish M.mm]

theorem pdRest_eq (M : Mont) : Precomputed.rest M.mm =
    seqs ((([.block [ldh .x1 sIn, ldh .x2 sK, ldh .x8 (sArr aX)], loadBE] : List (Prog isa)) ++ setupSteps) ++ (pdExp M ++ outSteps)) :=
  rfl

/-- The input, the mask, `-m⁻¹` and 1. -/
theorem pdSetupAll_ok {s : State} {B : Addr} {Z k : Nat} {op ep ip : Addr} {L : Nat} {eb xb : List Byte} {N R : Nat}
    (h : PdPre s B Z k op ep ip L eb xb N R) :
    WP isa (seqs (([.block [ldh .x1 sIn, ldh .x2 sK, ldh .x8 (sArr aX)], loadBE] : List (Prog isa)) ++ setupSteps)) s fun t => ∃ minv,
      SetupOut t B Z ((k + 7) / 8) minv N (Spec.Rsa.os2ip xb) ∧ Frm B (pdAll ((k + 7) / 8)) s.mem t.mem ∧
      Keep mmRegs s t ∧ wv t.mem B (slot ((k + 7) / 8) aR2) ((k + 7) / 8) = R := by
  have hk1 := h.k1
  have hk2 := h.k2
  have hZ := h.z
  have hs := h.scr
  have hn := hs.nowrap
  have hn' : B.toNat + slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega_using [hZ, hn]
  refine wp_seqs_append (by simp) (by simp [setupSteps])
    (WP.mono (pdIn_ok hs h.x0 hZ (by omega_using [hk1]) (by omega_using [hk2]) h.hK h.hIn h.hb h.x h.xl) fun t₁ ⟨hX₁, ha₁, k₁⟩ => ?_)
  have f₁ : Frm B (pdAll ((k + 7) / 8)) s.mem t₁.mem := Frm.of_arrays ha₁ (by simp [pdAll])
  refine WP.mono (pdSetup_ok (hs.congr k₁.wr) ((k₁.gpr .x0 (by decide)).trans h.x0) hZ (by omega_arith) (by omega_using [hk2])
      (by rw [ha₁.hslot (by decide)]; exact h.hW) (fun j hj => by rw [ha₁.hslot (by unfold sArr; omega_arith)]; exact h.hb j hj)
      (by rw [ha₁.wv_of_not_mem (by decide) (by decide) hn']; exact h.n) hX₁ h.odd)
      fun t₂ ⟨minv, so, f₂', k₂⟩ => ⟨minv, so, f₁.trans (f₂'.mono (by simp [pdAll])), (k₁.trans k₂).mono (by decide), ?_⟩
  rw [f₂'.wv_eq (fun r hr => by
      have := hdr_lt_slot ((k + 7) / 8) aR2 (show 31 < 32 by decide)
      have := slot_sep (w := (k + 7) / 8) (show aR2 ≠ aOne by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [sMinv, sMask, sFn] at * <;> omega_arith)
      (by have := slot_le (w := (k + 7) / 8) (show aR2 < 8 by decide); omega_using [hn', this]),
    ha₁.wv_of_not_mem (by decide) (by decide) hn']
  exact h.r

/-- `rest`, for values the checks accepted: `x^e mod N` (or zeros, if the
input is not below `N`) to `out`, for the `x` with `x R ≡ input R² R⁻¹`,
which is the input if `R ≡ R²`. -/
theorem pdRest_ok {s : State} {B : Addr} {Z k : Nat} {op ep ip : Addr} {L : Nat} {eb xb : List Byte} {N R : Nat}
    (h : PdPre s B Z k op ep ip L eb xb N R) :
    WP isa (Precomputed.rest M.mm) s fun t => ∃ x : Nat,
      (R % N = 2 ^ (64 * ((k + 7) / 8)) * 2 ^ (64 * ((k + 7) / 8)) % N → x % N = Spec.Rsa.os2ip xb % N) ∧
      MainPost s t B Z k op (if Spec.Rsa.os2ip xb < N then x ^ Spec.Rsa.os2ip eb % N else 0)
        (decide (Spec.Rsa.os2ip xb < N)) := by
  have hk1 := h.k1
  have hk2 := h.k2
  have hL2 := h.L2
  have hZ := h.z
  have hs := h.scr
  have hn := hs.nowrap
  have hn' : B.toNat + slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega_using [hZ, hn]
  have hw : 2 ≤ (k + 7) / 8 := by omega_using [hk1]
  have hR : Nat.Coprime (2 ^ (64 * ((k + 7) / 8))) N := VG.Proof.Bignum.coprime_pow2 h.odd _
  have hle := pdAll_le ((k + 7) / 8)
  have hle' : ∀ r ∈ pdAll ((k + 7) / 8), r.1 + r.2 ≤ Z := fun r hr => Nat.le_trans (hle r hr) hZ
  rw [pdRest_eq]
  refine wp_seqs_append (by simp) (by simp [pdExp])
    (WP.mono (pdSetupAll_ok h) fun t₂ ⟨minv, so, f₂, k₂, hR₂⟩ => ?_)
  refine wp_seqs_append (by simp [pdExp]) (by simp [outSteps]) ?_
  unfold pdExp
  -- `X = input R`.
  refine WP.seq (WP.mono (M.mm_ok (o := aXm) (a := aX) (b := aR2) so.good hZ hw (by omega_using [hk2]) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) so.inv (by rw [hR₂, so.n]; exact h.rlt))
    fun t₃ ⟨hg₃, hlt₃, hm₃, ha₃, k₃⟩ => ?_)
  rw [so.n] at hlt₃ hm₃
  rw [so.x, hR₂] at hm₃
  have hn₃ : wv t₃.mem B (slot ((k + 7) / 8) aN) ((k + 7) / 8) = N := by
    rw [ha₃.wv_of_not_mem (by decide) (by decide) hn']; exact so.n
  have hinv₃ : ((word t₃.mem B (slot ((k + 7) / 8) aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [ha₃.word0_of_not_mem (by decide) (by decide) hn' (by omega_using [hw])]; exact so.inv
  have f₃ : Frm B (pdAll ((k + 7) / 8)) t₂.mem t₃.mem :=
    Frm.of_arrays ha₃ (by simp [pdAll, pExpRanges, pBitRanges, bitRanges])
  have f₁₃ := f₂.trans f₃
  have x₁₃ := Fixed.of_frm f₁₃ (pdAll_fixed _)
  obtain ⟨x, hx⟩ := exists_mont hR h.n1 (wv t₃.mem B (slot ((k + 7) / 8) aXm) ((k + 7) / 8))
  have he₃ := h.e.congrK (InScr.of_frm f₁₃ hle') (k₂.trans k₃)
  -- The exponentiation.
  refine WP.seq (WP.mono (pExpLoop_ok (x := x) ⟨hg₃, hn₃, hinv₃, rfl⟩ hZ hw (by omega_using [hk2]) hR hlt₃ hx
    (by rw [x₁₃ sE (by decide)]; exact h.hE) (by rw [x₁₃ sElen (by decide)]; exact h.hL) h.el h.L1 (by omega_using [hk2, hL2])
    (fun i hi => he₃.rd i (by rw [h.el]; exact hi)) (fun i hi => he₃.val i (by rw [h.el]; exact hi))
    (fun i hi => he₃.out i (by rw [h.el]; exact hi)))
    fun t₄ ⟨hc₄, hy₄, f₄', k₄⟩ => ?_)
  have f₄ : Frm B (pdAll ((k + 7) / 8)) t₃.mem t₄.mem := f₄'.mono fun _ hr => List.mem_append_right _ hr
  have hone₄ : wv t₄.mem B (slot ((k + 7) / 8) aOne) ((k + 7) / 8) = 1 := by
    rw [f₄'.wv_eq (fun r hr => by
        have := hdr_lt_slot ((k + 7) / 8) aOne (show 31 < 32 by decide)
        have := slot_sep (w := (k + 7) / 8) (show aOne ≠ aAcc by decide)
        have := slot_sep (w := (k + 7) / 8) (show aOne ≠ aTmp by decide)
        have := slot_sep (w := (k + 7) / 8) (show aOne ≠ aY by decide)
        simp only [pExpRanges, pBitRanges, bitRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [sI, sV, sBit, sStarted, sFn] at * <;>
          omega_arith)
        (by have := slot_le (w := (k + 7) / 8) (show aOne < 8 by decide); omega_using [hn', this]),
      ha₃.wv_of_not_mem (by decide) (by decide) hn']
    exact so.one
  rw [seqs_one]
  refine WP.mono (pFinish_ok hc₄ hZ hw (by omega_using [hk2]) hR h.n1 hone₄ hy₄) fun t₅ ⟨hg₅, hY₅, f₅', k₅⟩ => ?_
  have f₅ : Frm B (pdAll ((k + 7) / 8)) t₄.mem t₅.mem :=
    f₅'.mono (by simp [finRanges, pdAll, pExpRanges, pBitRanges, bitRanges])
  have f₁₅ := (f₁₃.trans f₄).trans f₅
  have x₁₅ := Fixed.of_frm f₁₅ (pdAll_fixed _)
  have k₁₅ := ((k₂.trans k₃).trans k₄).trans k₅
  have hM₅ : word t₅.mem B (8 * sMask) = mask (decide (Spec.Rsa.os2ip xb < N)) := by
    rw [f₅'.word_eq (fun r hr => by
        have := hdr_lt_slot ((k + 7) / 8) aAcc (show sMask < 32 by decide)
        have := hdr_lt_slot ((k + 7) / 8) aTmp (show sMask < 32 by decide)
        have := hdr_lt_slot ((k + 7) / 8) aY (show sMask < 32 by decide)
        simp only [finRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> omega_arith) (by unfold sMask sFn; omega_using []),
      f₄'.word_eq (pExpRanges_hdr _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (by unfold sMask sFn; omega_using []),
      ha₃.hslot (by decide)]
    exact so.mask
  refine WP.mono (outPhase_ok hg₅ hZ (by omega_using [hw]) (by omega_using [hk2]) hY₅ (by rw [x₁₅ sOut (by decide)]; exact h.hO)
    (by rw [x₁₅ sK (by decide)]; exact h.hK) hM₅ (fun j hj => by rw [k₁₅.wr]; exact h.out j hj) h.outSep)
    fun t ⟨hb, hx0, hfr, k₆⟩ => ⟨x, fun hRR => ?_, ⟨?_, hx0,
      fun y hy hy' => by rw [hfr y hy', InScr.of_frm f₁₅ hle' y hy], (k₁₅.trans k₆).mono (by decide)⟩⟩
  · apply VG.Proof.Bignum.mont_cancel hR
    apply VG.Proof.Bignum.mont_cancel hR
    calc x * 2 ^ (64 * ((k + 7) / 8)) * 2 ^ (64 * ((k + 7) / 8)) % N
        = x * 2 ^ (64 * ((k + 7) / 8)) % N * 2 ^ (64 * ((k + 7) / 8)) % N := (Nat.mod_mul_mod _ _ _).symm
      _ = wv t₃.mem B (slot ((k + 7) / 8) aXm) ((k + 7) / 8) % N * 2 ^ (64 * ((k + 7) / 8)) % N := by rw [hx]
      _ = Spec.Rsa.os2ip xb * R % N := by rw [Nat.mod_mul_mod, hm₃]
      _ = Spec.Rsa.os2ip xb * (R % N) % N := (Nat.mul_mod_mod _ _ _).symm
      _ = Spec.Rsa.os2ip xb * 2 ^ (64 * ((k + 7) / 8)) * 2 ^ (64 * ((k + 7) / 8)) % N := by
        rw [hRR, Nat.mul_mod_mod, Nat.mul_assoc]
  · rw [hb]
    by_cases hc : Spec.Rsa.os2ip xb < N <;> simp [hc]

end VG.Proof.Bignum.AArch64
