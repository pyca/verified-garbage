module

public import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
public import VerifiedGarbage.Proof.Rsa.AArch64.RdOps
import VerifiedGarbage.Proof.Rsa.AArch64.Inv
import VerifiedGarbage.Proof.Bignum.ShiftStages
public import VerifiedGarbage.Impl.Rsa.AArch64.RecoverDet
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Ring

/-!
# `vg_rsa_recover_primes_det` on AArch64: shifts by masked stages

The loops of `RecoverDet.wstage` and `bstage`: a pass over the words of an array that moves each word
`2^k` words up or down, or shifts it `2^k` bits up or down with the bits shifted out carried to the
next word, where the mask `x15` is all ones, and leaves it where the mask is zero.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-! ## Words -/

/-- A masked select by `xor`: the mask's `b` where it is all ones. -/
theorem sel_mask (a b : BitVec 64) (c : Bool) : a ^^^ ((b ^^^ a) &&& mask c) = if c then b else a := by
  rw [BitVec.xor_comm b a]; exact cswap_x a b c

/-- A word shifted up by `sh` with the bits `x < 2^sh` below. -/
theorem shl_or_toNat (w x : BitVec 64) {sh : Nat} (hsh : sh < 64) (hx : x.toNat < 2 ^ sh) :
    ((w <<< sh) ||| x).toNat = w.toNat * 2 ^ sh % 2 ^ 64 + x.toNat := by
  have h1 : (w <<< sh).toNat = w.toNat * 2 ^ sh % 2 ^ 64 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have hd : 2 ^ sh ∣ (w <<< sh).toNat := by
    rw [h1]; exact (Nat.dvd_mod_iff (Nat.pow_dvd_pow 2 (by omega_using [hsh]))).mpr (Nat.dvd_mul_left _ _)
  rw [BitVec.toNat_or, ← h1]
  obtain ⟨q, hq⟩ := hd
  rw [hq, Nat.mul_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hx]

/-- The bits shifted out of the top of a word. -/
theorem shr_out_toNat (w : BitVec 64) {sh : Nat} (h0 : 0 < sh) (hsh : sh < 64) :
    (w >>> (64 - sh)).toNat = w.toNat * 2 ^ sh / 2 ^ 64 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    show (2 : Nat) ^ 64 = 2 ^ (64 - sh) * 2 ^ sh by rw [← Nat.pow_add]; congr 1; omega,
    Nat.mul_div_mul_right _ _ (Nat.two_pow_pos sh)]

/-- The low bits of a word shifted up leave room for `c < 2^sh` below them. -/
theorem shl_room {sh : Nat} (hsh : sh < 64) (w c : Nat) (hc : c < 2 ^ sh) : w * 2 ^ sh % 2 ^ 64 + c < 2 ^ 64 := by
  have e64 : (2 : Nat) ^ 64 = 2 ^ (64 - sh) * 2 ^ sh := by rw [← Nat.pow_add]; congr 1; omega_using [hsh]
  rw [e64, Nat.mul_mod_mul_right]
  have := Nat.mod_lt w (Nat.two_pow_pos (64 - sh))
  have : w % 2 ^ (64 - sh) * 2 ^ sh + 2 ^ sh ≤ 2 ^ (64 - sh) * 2 ^ sh := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ this
  omega_using [hc, this]

/-- A step of a shift up by `sh` bits over words: from `A` (`j` words) times `2^sh`, its low `j` words and
the bits above them (`c`), the next word `w` gives `(A + P w) 2^sh`'s low `j + 1` words and the bits above
them, `P = 2^(64 j)`. -/
theorem shl_step {sh : Nat} (hsh : sh < 64) {P A w : Nat} (hP : 0 < P) (hA : A < P) :
    (A + P * w) * 2 ^ sh % (P * 2 ^ 64) = A * 2 ^ sh % P + P * (w * 2 ^ sh % 2 ^ 64 + A * 2 ^ sh / P) ∧
      (A + P * w) * 2 ^ sh / (P * 2 ^ 64) = w * 2 ^ sh / 2 ^ 64 := by
  have hc : A * 2 ^ sh / P < 2 ^ sh := by
    rw [Nat.div_lt_iff_lt_mul hP]; exact Nat.mul_lt_mul_of_pos_right hA (Nat.two_pow_pos sh) |>.trans_le
      (by rw [Nat.mul_comm])
  have room := shl_room hsh w _ hc
  have eA := Nat.div_add_mod (A * 2 ^ sh) P
  have ew := Nat.div_add_mod (w * 2 ^ sh) (2 ^ 64)
  have hl := Nat.mod_lt (A * 2 ^ sh) hP
  generalize A * 2 ^ sh / P = c at *
  generalize A * 2 ^ sh % P = l at *
  generalize w * 2 ^ sh / 2 ^ 64 = h at *
  generalize w * 2 ^ sh % 2 ^ 64 = m at *
  have e : (A + P * w) * 2 ^ sh = (l + P * (m + c)) + P * 2 ^ 64 * h := by
    rw [Nat.add_mul, ← eA, Nat.mul_assoc, ← ew]; ring
  have hlo : l + P * (m + c) < P * 2 ^ 64 := by
    have : P * (m + c) + P ≤ P * 2 ^ 64 := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ room
    omega_using [hl, this]
  rw [e]
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]
  · rw [Nat.add_mul_div_left _ _ (Nat.mul_pos hP (Nat.two_pow_pos 64)), Nat.div_eq_of_lt hlo, Nat.zero_add]

/-! ## A shift up by bits -/

theorem k_cases {k : Nat} (hk : k < 6) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega_using [hk]

/-- `bWord`'s frame: it writes `x2`, `x3`, `x4` and `x16`, calls nothing, and keeps the vector registers. -/
theorem bWord_frame (up : Bool) {k : Nat} (hk : k < 6) :
    writesOnly [.x2, .x3, .x4, .x16] (.block (bWord up k) : Prog isa) = true ∧
      (.block (bWord up k) : Prog isa).noCalls = true ∧
      Code.allInstrs keepsV (.block (bWord up k) : Prog isa) = true := by
  rcases k_cases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> cases up <;>
    exact ⟨by decide, by decide, by decide +kernel⟩

/-- After `j` words of `bWord true k` from `s₀` (`sh = 2^k`): the low `j` words of `A 2^sh` where the mask
is set (`c`), `A` where it is not, for the first `j` words `A`; the bits above them in `x2`. -/
structure BUpInv (s₀ : State) (B : Addr) (Z e sh : Nat) (c : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x2, .x3, .x4, .x14, .x16] s₀ t
  x16 : t.gpr .x16 = off B (e + 8 * j)
  out : Outside B e (8 * j) s₀.mem t.mem
  cy : (t.gpr .x2).toNat = wv s₀.mem B e j * 2 ^ sh / 2 ^ (64 * j)
  val : wv t.mem B e j = if c then wv s₀.mem B e j * 2 ^ sh % 2 ^ (64 * j) else wv s₀.mem B e j

theorem bUpStep_ok {s₀ : State} {B : Addr} {Z N e k : Nat} {c : Bool} (hk : k < 6)
    (h15 : s₀.gpr .x15 = mask c) (he : e + 8 * N ≤ Z) {j : Nat} (hj : j < N) {t : State}
    (hI : BUpInv s₀ B Z e (2 ^ k) c j t) :
    WP isa (.block (bWord true k ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      BUpInv s₀ B Z e (2 ^ k) c (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have hsh : 2 ^ k < 64 := by
    have : 2 ^ k ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) (by omega_using [hk])
    omega_using [this]
  have hsh0 : 0 < 2 ^ k := Nat.two_pow_pos k
  have t15 : t.gpr .x15 = mask c := (hI.keep.gpr .x15 (by decide)).trans h15
  have hw : word t.mem B (e + 8 * j) = word s₀.mem B (e + 8 * j) :=
    hI.out.word (by omega_using []) (by omega_using [he, hj, hn])
  generalize hW : word s₀.mem B (e + 8 * j) = W at hw
  generalize hX : t.gpr .x2 = X
  have hcy : X.toNat < 2 ^ (2 ^ k) := by
    rw [← hX, hI.cy, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm (2 ^ (2 ^ k))]
    exact Nat.mul_lt_mul_of_pos_right (wv_lt _ _ _ _) (Nat.two_pow_pos _)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x2, .x3, .x4, .x16] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (e + 8 * j)) (if c then (W <<< (2 ^ k)) ||| X else W) ∧
      t₁.gpr .x2 = W >>> (64 - 2 ^ k) ∧ t₁.gpr .x16 = off B (e + 8 * j + 8))
    (by
      unfold bWord
      brun [hI.x16, hX, t15, hw, hI.scr.ld (show e + 8 * j + 8 ≤ Z by omega_using [he, hj]),
        hI.scr.st (show e + 8 * j + 8 ≤ Z by omega_using [he, hj]), hsh, show 64 - 2 ^ k < 64 by omega_using [hsh0], sel_mask])
    (bWord_frame true hk).1 (bWord_frame true hk).2.1 (bWord_frame true hk).2.2) fun t₁ ⟨⟨hm, h2, h16⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', _⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc], ?_, ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega_using [he, hj, hn]) x (by omega_arith)]
    exact hI.out x (by omega_arith)
  · have st := shl_step (P := 2 ^ (64 * j)) (A := wv s₀.mem B e j) (w := W.toNat) hsh (Nat.two_pow_pos _)
      (wv_lt _ _ _ _)
    rw [k'.gpr .x2 (by decide), h2, shr_out_toNat W hsh0 hsh, wv, hW, pow64_succ, st.2]
  · have st := shl_step (P := 2 ^ (64 * j)) (A := wv s₀.mem B e j) (w := W.toNat) hsh (Nat.two_pow_pos _)
      (wv_lt _ _ _ _)
    rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega_using [he, hj, hn]), hI.val, wv, hW, pow64_succ]
    cases c
    · simp
    · simp only [ite_true]
      rw [st.1, shl_or_toNat W X hsh hcy, ← hX, hI.cy]

/-- `countLoop .x14 (bWord true k)` over `N` words at `e`, from `x2 = 0`: `A 2^(2^k) mod 2^(64 N)` where the
mask is set (`c`), `A` where it is not, for the `N` words `A`. -/
theorem bUp_ok {s : State} {B : Addr} {Z N e k : Nat} {c : Bool} (hs : Scr s B Z) (hk : k < 6)
    (h15 : s.gpr .x15 = mask c) (h16 : s.gpr .x16 = off B e) (h14 : s.gpr .x14 = BitVec.ofNat 64 N)
    (h2 : s.gpr .x2 = 0) (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (he : e + 8 * N ≤ Z) :
    WP isa (countLoop .x14 (bWord true k)) s fun t =>
      wv t.mem B e N = (if c then wv s.mem B e N * 2 ^ (2 ^ k) % 2 ^ (64 * N) else wv s.mem B e N) ∧
      Outside B e (8 * N) s.mem t.mem ∧ Keep [.x2, .x3, .x4, .x14, .x16] s t := by
  have h0 : BUpInv s B Z e (2 ^ k) c 0 s :=
    ⟨hs, Keep.refl _ _, by rw [h16]; rfl, Outside.refl _ _ _ _, by rw [h2]; simp [wv], by simp [wv]⟩
  exact WP.mono (wp_countdown (N := N) (by omega_using [hN']) (by omega_using [hN]) (BUpInv s B Z e (2 ^ k) c)
    (fun j hj t hI _ => bUpStep_ok hk h15 he hj hI) h0 h14) fun t hI => ⟨hI.val, hI.out, hI.keep⟩

/-! ## A shift down by bits -/

/-- A word shifted down by `sh` with the bits `x = r 2^(64 - sh)` above, `r < 2^sh`. -/
theorem shr_or_toNat (w : BitVec 64) {sh r : Nat} (hsh : sh < 64) (x : BitVec 64)
    (hx : x.toNat = r * 2 ^ (64 - sh)) :
    ((w >>> sh) ||| x).toNat = w.toNat / 2 ^ sh + r * 2 ^ (64 - sh) := by
  have h1 : (w >>> sh).toNat = w.toNat / 2 ^ sh := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hlt : w.toNat / 2 ^ sh < 2 ^ (64 - sh) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, show 64 - sh + sh = 64 by omega_using [hsh]]; exact w.isLt
  rw [BitVec.toNat_or, h1, hx, Nat.add_comm (w.toNat / 2 ^ sh), ← Nat.shiftLeft_eq, Nat.or_comm,
    ← Nat.shiftLeft_add_eq_or_of_lt hlt]

/-- The bits of a word that a shift down by `sh` carries into the word below. -/
theorem shl_out_toNat (w : BitVec 64) {sh : Nat} (h0 : 0 < sh) (hsh : sh < 64) :
    (w <<< (64 - sh)).toNat = w.toNat % 2 ^ sh * 2 ^ (64 - sh) := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    show (2 : Nat) ^ 64 = 2 ^ sh * 2 ^ (64 - sh) by rw [← Nat.pow_add]; congr 1; omega, Nat.mul_mod_mul_right]

/-- A step of a shift down by `sh` over words, from the top: `T` (the words above) and the next word `w`
below them. -/
theorem shr_step {sh : Nat} (hsh : sh < 64) (T w : Nat) :
    (w + 2 ^ 64 * T) / 2 ^ sh = (w / 2 ^ sh + T % 2 ^ sh * 2 ^ (64 - sh)) + 2 ^ 64 * (T / 2 ^ sh) ∧
      (w + 2 ^ 64 * T) % 2 ^ sh = w % 2 ^ sh := by
  have e64 : (2 : Nat) ^ 64 = 2 ^ (64 - sh) * 2 ^ sh := by rw [← Nat.pow_add]; congr 1; omega_using [hsh]
  have eT := Nat.div_add_mod T (2 ^ sh)
  refine ⟨?_, ?_⟩
  · conv => lhs; rw [← eT]
    rw [e64, show w + 2 ^ (64 - sh) * 2 ^ sh * (2 ^ sh * (T / 2 ^ sh) + T % 2 ^ sh) =
      w + 2 ^ sh * (2 ^ (64 - sh) * (T % 2 ^ sh) + 2 ^ (64 - sh) * 2 ^ sh * (T / 2 ^ sh)) by ring,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos sh)]
    ring
  · rw [e64, show w + 2 ^ (64 - sh) * 2 ^ sh * T = w + 2 ^ sh * (2 ^ (64 - sh) * T) by ring, Nat.add_mul_mod_self_left]

/-- A number's words with its lowest word written: that word and the rest. -/
theorem wv_writeW_low (m : Mem) (B : Addr) (d j : Nat) (v : BitVec 64) (h : d + 8 * (j + 1) ≤ 2 ^ 64) :
    wv (m.writeW (off B d) v) B d (j + 1) = v.toNat + 2 ^ 64 * wv m B (d + 8) j := by
  have h1 : wv (m.writeW (off B d) v) B d 1 = v.toNat := by simp [wv, word_writeW_self]
  have h2 : wv (m.writeW (off B d) v) B (d + 8 * 1) j = wv m B (d + 8) j :=
    (writeW_outside m B v (by omega_using [h])).wv (.inr (by omega_using [])) (by omega_using [h])
  rw [Nat.add_comm j 1, wv_add, h1, h2]

/-- After `j` words of `bWord false k` from `s₀` (`sh = 2^k`), from the top of the `N` words at `e`: the
top `j` words `T` as `⌊T / 2^sh⌋` where the mask is set (`c`), `T` where it is not; the bits of `T`'s
lowest word below `sh` in `x2`, at its top. -/
structure BDnInv (s₀ : State) (B : Addr) (Z e N sh : Nat) (c : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x2, .x3, .x4, .x14, .x16] s₀ t
  x16 : t.gpr .x16 = off B (e + 8 * (N - j) - 8)
  out : Outside B (e + 8 * (N - j)) (8 * j) s₀.mem t.mem
  cy : (t.gpr .x2).toNat = wv s₀.mem B (e + 8 * (N - j)) j % 2 ^ sh * 2 ^ (64 - sh)
  val : wv t.mem B (e + 8 * (N - j)) j =
    if c then wv s₀.mem B (e + 8 * (N - j)) j / 2 ^ sh else wv s₀.mem B (e + 8 * (N - j)) j

theorem bDnStep_ok {s₀ : State} {B : Addr} {Z N e k : Nat} {c : Bool} (hk : k < 6)
    (h15 : s₀.gpr .x15 = mask c) (he : e + 8 * N ≤ Z) (he8 : 8 ≤ e) {j : Nat} (hj : j < N) {t : State}
    (hI : BDnInv s₀ B Z e N (2 ^ k) c j t) :
    WP isa (.block (bWord false k ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      BDnInv s₀ B Z e N (2 ^ k) c (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have hsh : 2 ^ k < 64 := by
    have : 2 ^ k ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) (by omega_using [hk])
    omega_using [this]
  have hsh0 : 0 < 2 ^ k := Nat.two_pow_pos k
  have t15 : t.gpr .x15 = mask c := (hI.keep.gpr .x15 (by decide)).trans h15
  have ei : e + 8 * (N - j) - 8 = e + 8 * (N - (j + 1)) := by omega_using [hj]
  have hw : word t.mem B (e + 8 * (N - (j + 1))) = word s₀.mem B (e + 8 * (N - (j + 1))) :=
    hI.out.word (by omega_using [hj]) (by omega_using [he, hj, hn])
  have h16' : t.gpr .x16 = off B (e + 8 * (N - (j + 1))) := by rw [hI.x16, ei]
  generalize hW : word s₀.mem B (e + 8 * (N - (j + 1))) = W at hw
  generalize hX : t.gpr .x2 = X
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x2, .x3, .x4, .x16] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (e + 8 * (N - (j + 1)))) (if c then (W >>> (2 ^ k)) ||| X else W) ∧
      t₁.gpr .x2 = W <<< (64 - 2 ^ k) ∧ t₁.gpr .x16 = off B (e + 8 * (N - (j + 1))) - BitVec.ofNat 64 8)
    (by
      unfold bWord
      brun [h16', hX, t15, hw, hI.scr.ld (show e + 8 * (N - (j + 1)) + 8 ≤ Z by omega_using [he, hj]),
        hI.scr.st (show e + 8 * (N - (j + 1)) + 8 ≤ Z by omega_using [he, hj]), hsh,
        show 64 - 2 ^ k < 64 by omega_using [hsh0], sel_mask])
    (bWord_frame false hk).1 (bWord_frame false hk).2.1 (bWord_frame false hk).2.2) fun t₁ ⟨⟨hm, h2, h16⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', _⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have eR : e + 8 * (N - (j + 1)) + 8 = e + 8 * (N - j) := by omega_using [hj]
  have ew := wv_add s₀.mem B (e + 8 * (N - (j + 1))) 1 j
  rw [eR] at ew
  have w1 : wv s₀.mem B (e + 8 * (N - (j + 1))) 1 = W.toNat := by simp [wv, hW]
  rw [w1, Nat.add_comm 1 j, show 64 * 1 = 64 by rfl] at ew
  have st := shr_step hsh (wv s₀.mem B (e + 8 * (N - j)) j) W.toNat (sh := 2 ^ k)
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide), ?_, ?_, ?_, ?_⟩
  · rw [k'.gpr .x16 (by decide), h16]
    have e8 : e + 8 * (N - (j + 1)) = (e + 8 * (N - (j + 1)) - 8) + 8 := by omega_using [he8]
    rw [e8, ← off_add, BitVec.add_sub_cancel, ← e8]
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega_using [he, hj, hn]) x (by omega_arith)]
    exact hI.out x (by omega_arith)
  · rw [k'.gpr .x2 (by decide), h2, shl_out_toNat W hsh0 hsh, ew, st.2]
  · rw [hm', hm, wv_writeW_low _ _ _ _ _ (by omega_using [he, hj, hn]), eR,
      hI.val, ew]
    cases c
    · simp
    · simp only [ite_true]
      rw [st.1, shr_or_toNat W hsh X (r := wv s₀.mem B (e + 8 * (N - j)) j % 2 ^ (2 ^ k)) (by rw [← hX, hI.cy])]

/-- `countLoop .x14 (bWord false k)` over the `N` words at `e`, from the top (`x16` at word `N - 1`) and
`x2 = 0`: `⌊A / 2^(2^k)⌋` where the mask is set (`c`), `A` where it is not. -/
theorem bDn_ok {s : State} {B : Addr} {Z N e k : Nat} {c : Bool} (hs : Scr s B Z) (hk : k < 6)
    (h15 : s.gpr .x15 = mask c) (h16 : s.gpr .x16 = off B (e + 8 * N - 8)) (h14 : s.gpr .x14 = BitVec.ofNat 64 N)
    (h2 : s.gpr .x2 = 0) (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (he : e + 8 * N ≤ Z) (he8 : 8 ≤ e) :
    WP isa (countLoop .x14 (bWord false k)) s fun t =>
      wv t.mem B e N = (if c then wv s.mem B e N / 2 ^ (2 ^ k) else wv s.mem B e N) ∧
      Outside B e (8 * N) s.mem t.mem ∧ Keep [.x2, .x3, .x4, .x14, .x16] s t := by
  have h0 : BDnInv s B Z e N (2 ^ k) c 0 s :=
    ⟨hs, Keep.refl _ _, by rw [h16, Nat.sub_zero], by rw [Nat.mul_zero]; exact Outside.refl _ _ _ _,
      by rw [h2]; simp [wv], by simp [wv]⟩
  refine WP.mono (wp_countdown (N := N) (by omega_using [hN']) (by omega_using [hN]) (BDnInv s B Z e N (2 ^ k) c)
    (fun j hj t hI _ => bDnStep_ok hk h15 he he8 hj hI) h0 h14) fun t hI => ?_
  have hv := hI.val
  have ho := hI.out
  rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero] at hv ho
  exact ⟨hv, ho, hI.keep⟩

/-! ## Moves and clears by words -/

/-- `wMove`'s and `wClear`'s frames. -/
theorem wMove_frame (up : Bool) :
    writesOnly [.x3, .x4, .x16, .x17] (.block (wMove up) : Prog isa) = true ∧
      (.block (wMove up) : Prog isa).noCalls = true ∧ Code.allInstrs keepsV (.block (wMove up) : Prog isa) = true := by
  cases up <;> exact ⟨by decide, by decide, by decide +kernel⟩

theorem wClear_frame (up : Bool) :
    writesOnly [.x3, .x4, .x16] (.block (wClear up) : Prog isa) = true ∧
      (.block (wClear up) : Prog isa).noCalls = true ∧ Code.allInstrs keepsV (.block (wClear up) : Prog isa) = true := by
  cases up <;> exact ⟨by decide, by decide, by decide +kernel⟩

theorem clear_mask (a : BitVec 64) (c : Bool) : a ^^^ (a &&& mask c) = if c then 0 else a := by
  cases c
  · simp [mask_false]
  · simp only [mask_true, BitVec.and_allOnes, BitVec.xor_self, ite_true]; rfl

/-- A number's lowest word and the rest. -/
theorem wv_cons (m : Mem) (B : Addr) (d j : Nat) :
    wv m B d (j + 1) = (word m B d).toNat + 2 ^ 64 * wv m B (d + 8) j := by
  rw [Nat.add_comm j 1, wv_add]; simp [wv]

/-- After `j` words of `wMove true` from `s₀` over the top `M` of the `N` words at `e`, from the top: the
top `j` words moved down from `d` words below where the mask is set. -/
structure MvUpInv (s₀ : State) (B : Addr) (Z e N d : Nat) (c : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x13, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (e + 8 * (N - j) - 8)
  x17 : t.gpr .x17 = off B (e + 8 * (N - j) - 8 - 8 * d)
  out : Outside B (e + 8 * (N - j)) (8 * j) s₀.mem t.mem
  val : wv t.mem B (e + 8 * (N - j)) j =
    if c then wv s₀.mem B (e + 8 * (N - j - d)) j else wv s₀.mem B (e + 8 * (N - j)) j

theorem mvUpStep_ok {s₀ : State} {B : Addr} {Z N e d : Nat} {c : Bool}
    (h15 : s₀.gpr .x15 = mask c) (he : e + 8 * N ≤ Z) (he8 : 8 ≤ e) {j : Nat} (hj : j < N - d) {t : State}
    (hI : MvUpInv s₀ B Z e N d c j t) :
    WP isa (.block (wMove true ++ ([.subImm .x .x13 .x13 1] : List Instr))) t fun t' =>
      MvUpInv s₀ B Z e N d c (j + 1) t' ∧ t'.gpr .x13 = t.gpr .x13 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t15 : t.gpr .x15 = mask c := (hI.keep.gpr .x15 (by decide)).trans h15
  have ei : e + 8 * (N - j) - 8 = e + 8 * (N - (j + 1)) := by omega_using [hj]
  have es : e + 8 * (N - j) - 8 - 8 * d = e + 8 * (N - (j + 1) - d) := by omega_using [hj]
  have hw : word t.mem B (e + 8 * (N - (j + 1))) = word s₀.mem B (e + 8 * (N - (j + 1))) :=
    hI.out.word (by omega_using [hj]) (by omega_using [he, hj, hn])
  have hv : word t.mem B (e + 8 * (N - (j + 1) - d)) = word s₀.mem B (e + 8 * (N - (j + 1) - d)) :=
    hI.out.word (by omega_using [hj]) (by omega_using [he, hj, hn])
  have h16' : t.gpr .x16 = off B (e + 8 * (N - (j + 1))) := by rw [hI.x16, ei]
  have h17' : t.gpr .x17 = off B (e + 8 * (N - (j + 1) - d)) := by rw [hI.x17, es]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x16, .x17] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (e + 8 * (N - (j + 1))))
        (if c then word s₀.mem B (e + 8 * (N - (j + 1) - d)) else word s₀.mem B (e + 8 * (N - (j + 1)))) ∧
      t₁.gpr .x16 = off B (e + 8 * (N - (j + 1))) - BitVec.ofNat 64 8 ∧
      t₁.gpr .x17 = off B (e + 8 * (N - (j + 1) - d)) - BitVec.ofNat 64 8)
    (by
      unfold wMove
      brun [h16', h17', t15, hw, hv, hI.scr.ld (show e + 8 * (N - (j + 1)) + 8 ≤ Z by omega_using [he, hj]),
        hI.scr.ld (show e + 8 * (N - (j + 1) - d) + 8 ≤ Z by omega_using [he, hj]),
        hI.scr.st (show e + 8 * (N - (j + 1)) + 8 ≤ Z by omega_using [he, hj]), sel_mask])
    (wMove_frame true).1 (wMove_frame true).2.1 (wMove_frame true).2.2) fun t₁ ⟨⟨hm, h16, h17⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x13) fun t' ⟨⟨h13, hm', _⟩, k'⟩ => ⟨?_, by rw [h13, k₁.gpr .x13 (by decide)]⟩
  have eR : e + 8 * (N - (j + 1)) + 8 = e + 8 * (N - j) := by omega_using [hj]
  have eS : e + 8 * (N - (j + 1) - d) + 8 = e + 8 * (N - j - d) := by omega_using [hj]
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide), ?_, ?_, ?_, ?_⟩
  · rw [k'.gpr .x16 (by decide), h16]
    have e8 : e + 8 * (N - (j + 1)) = (e + 8 * (N - (j + 1)) - 8) + 8 := by omega_using [he8]
    rw [e8, ← off_add, BitVec.add_sub_cancel, ← e8]
  · rw [k'.gpr .x17 (by decide), h17]
    have e8 : e + 8 * (N - (j + 1) - d) = (e + 8 * (N - (j + 1)) - 8 - 8 * d) + 8 := by omega_using [he8, hj]
    rw [e8, ← off_add, BitVec.add_sub_cancel]
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega_using [he, hj, hn]) x (by omega_arith)]
    exact hI.out x (by omega_arith)
  · rw [hm', hm, wv_writeW_low _ _ _ _ _ (by omega_using [he, hj, hn]), eR, hI.val,
      wv_cons s₀.mem B (e + 8 * (N - (j + 1) - d)), wv_cons s₀.mem B (e + 8 * (N - (j + 1))), eR, eS]
    cases c <;> simp

theorem mvUp_ok {s : State} {B : Addr} {Z N e d : Nat} {c : Bool} (hs : Scr s B Z)
    (h15 : s.gpr .x15 = mask c) (h16 : s.gpr .x16 = off B (e + 8 * N - 8))
    (h17 : s.gpr .x17 = off B (e + 8 * N - 8 - 8 * d)) (h13 : s.gpr .x13 = BitVec.ofNat 64 (N - d))
    (hd : d < N) (hN : N < 2 ^ 31) (he : e + 8 * N ≤ Z) (he8 : 8 ≤ e) :
    WP isa (countLoop .x13 (wMove true)) s fun t =>
      wv t.mem B (e + 8 * d) (N - d) = (if c then wv s.mem B e (N - d) else wv s.mem B (e + 8 * d) (N - d)) ∧
      Outside B (e + 8 * d) (8 * (N - d)) s.mem t.mem ∧ Keep [.x3, .x4, .x13, .x16, .x17] s t ∧
      t.gpr .x16 = off B (e + 8 * d - 8) := by
  have h0 : MvUpInv s B Z e N d c 0 s :=
    ⟨hs, Keep.refl _ _, by rw [h16, Nat.sub_zero], by rw [h17, Nat.sub_zero],
      by rw [Nat.mul_zero]; exact Outside.refl _ _ _ _, by simp [wv]⟩
  refine WP.mono (wp_countdown (N := N - d) (by omega_using [hN]) (by omega_using [hd]) (MvUpInv s B Z e N d c)
    (fun j hj t hI _ => mvUpStep_ok h15 he he8 hj hI) h0 h13) fun t hI => ?_
  have e1 : N - (N - d) = d := by omega_using [hd]
  have hv := hI.val
  have ho := hI.out
  have hx := hI.x16
  rw [e1, Nat.sub_self, Nat.mul_zero, Nat.add_zero] at hv
  rw [e1] at ho hx
  exact ⟨hv, ho, hI.keep, hx⟩

/-- After `j` words of `wClear true` from `s₀`, down from word `d - 1`: words `d - j` to `d - 1` cleared where
the mask is set. -/
structure ClrUpInv (s₀ : State) (B : Addr) (Z e d : Nat) (c : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x13, .x16] s₀ t
  x16 : t.gpr .x16 = off B (e + 8 * (d - j) - 8)
  out : Outside B (e + 8 * (d - j)) (8 * j) s₀.mem t.mem
  val : wv t.mem B (e + 8 * (d - j)) j = if c then 0 else wv s₀.mem B (e + 8 * (d - j)) j

theorem clrUpStep_ok {s₀ : State} {B : Addr} {Z e d : Nat} {c : Bool}
    (h15 : s₀.gpr .x15 = mask c) (he : e + 8 * d ≤ Z) (he8 : 8 ≤ e) {j : Nat} (hj : j < d) {t : State}
    (hI : ClrUpInv s₀ B Z e d c j t) :
    WP isa (.block (wClear true ++ ([.subImm .x .x13 .x13 1] : List Instr))) t fun t' =>
      ClrUpInv s₀ B Z e d c (j + 1) t' ∧ t'.gpr .x13 = t.gpr .x13 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t15 : t.gpr .x15 = mask c := (hI.keep.gpr .x15 (by decide)).trans h15
  have ei : e + 8 * (d - j) - 8 = e + 8 * (d - (j + 1)) := by omega_using [hj]
  have hw : word t.mem B (e + 8 * (d - (j + 1))) = word s₀.mem B (e + 8 * (d - (j + 1))) :=
    hI.out.word (by omega_using [hj]) (by omega_using [he, hj, hn])
  have h16' : t.gpr .x16 = off B (e + 8 * (d - (j + 1))) := by rw [hI.x16, ei]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x16] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (e + 8 * (d - (j + 1)))) (if c then 0 else word s₀.mem B (e + 8 * (d - (j + 1)))) ∧
      t₁.gpr .x16 = off B (e + 8 * (d - (j + 1))) - BitVec.ofNat 64 8)
    (by
      unfold wClear
      brun [h16', t15, hw, hI.scr.ld (show e + 8 * (d - (j + 1)) + 8 ≤ Z by omega_using [he, hj]),
        hI.scr.st (show e + 8 * (d - (j + 1)) + 8 ≤ Z by omega_using [he, hj]), clear_mask])
    (wClear_frame true).1 (wClear_frame true).2.1 (wClear_frame true).2.2) fun t₁ ⟨⟨hm, h16⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x13) fun t' ⟨⟨h13, hm', _⟩, k'⟩ => ⟨?_, by rw [h13, k₁.gpr .x13 (by decide)]⟩
  have eR : e + 8 * (d - (j + 1)) + 8 = e + 8 * (d - j) := by omega_using [hj]
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide), ?_, ?_, ?_⟩
  · rw [k'.gpr .x16 (by decide), h16]
    have e8 : e + 8 * (d - (j + 1)) = (e + 8 * (d - (j + 1)) - 8) + 8 := by omega_using [he8]
    rw [e8, ← off_add, BitVec.add_sub_cancel, ← e8]
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega_using [he, hj, hn]) x (by omega_arith)]
    exact hI.out x (by omega_arith)
  · rw [hm', hm, wv_writeW_low _ _ _ _ _ (by omega_using [he, hj, hn]), eR, hI.val,
      wv_cons s₀.mem B (e + 8 * (d - (j + 1))), eR]
    cases c <;> simp

theorem clrUp_ok {s : State} {B : Addr} {Z e d : Nat} {c : Bool} (hs : Scr s B Z)
    (h15 : s.gpr .x15 = mask c) (h16 : s.gpr .x16 = off B (e + 8 * d - 8)) (h13 : s.gpr .x13 = BitVec.ofNat 64 d)
    (hd : 1 ≤ d) (hd' : d < 2 ^ 31) (he : e + 8 * d ≤ Z) (he8 : 8 ≤ e) :
    WP isa (countLoop .x13 (wClear true)) s fun t =>
      wv t.mem B e d = (if c then 0 else wv s.mem B e d) ∧ Outside B e (8 * d) s.mem t.mem ∧
      Keep [.x3, .x4, .x13, .x16] s t := by
  have h0 : ClrUpInv s B Z e d c 0 s :=
    ⟨hs, Keep.refl _ _, by rw [h16, Nat.sub_zero], by rw [Nat.mul_zero]; exact Outside.refl _ _ _ _, by simp [wv]⟩
  refine WP.mono (wp_countdown (N := d) (by omega_using [hd']) (by omega_using [hd]) (ClrUpInv s B Z e d c)
    (fun j hj t hI _ => clrUpStep_ok h15 he he8 hj hI) h0 h13) fun t hI => ?_
  have hv := hI.val
  have ho := hI.out
  rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero] at hv ho
  exact ⟨hv, ho, hI.keep⟩

/-- After `j` words of `wMove false` from `s₀`: words `0` to `j - 1` moved up from `d` words above where the
mask is set. -/
structure MvDnInv (s₀ : State) (B : Addr) (Z e d : Nat) (c : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x13, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (e + 8 * j)
  x17 : t.gpr .x17 = off B (e + 8 * d + 8 * j)
  out : Outside B e (8 * j) s₀.mem t.mem
  val : wv t.mem B e j = if c then wv s₀.mem B (e + 8 * d) j else wv s₀.mem B e j

theorem mvDnStep_ok {s₀ : State} {B : Addr} {Z N e d : Nat} {c : Bool}
    (h15 : s₀.gpr .x15 = mask c) (he : e + 8 * N ≤ Z) {j : Nat} (hj : j < N - d) {t : State}
    (hI : MvDnInv s₀ B Z e d c j t) :
    WP isa (.block (wMove false ++ ([.subImm .x .x13 .x13 1] : List Instr))) t fun t' =>
      MvDnInv s₀ B Z e d c (j + 1) t' ∧ t'.gpr .x13 = t.gpr .x13 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t15 : t.gpr .x15 = mask c := (hI.keep.gpr .x15 (by decide)).trans h15
  have hw : word t.mem B (e + 8 * j) = word s₀.mem B (e + 8 * j) :=
    hI.out.word (by omega_using []) (by omega_using [he, hj, hn])
  have hv : word t.mem B (e + 8 * d + 8 * j) = word s₀.mem B (e + 8 * d + 8 * j) :=
    hI.out.word (by omega_using []) (by omega_using [he, hj, hn])
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x16, .x17] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (e + 8 * j))
        (if c then word s₀.mem B (e + 8 * d + 8 * j) else word s₀.mem B (e + 8 * j)) ∧
      t₁.gpr .x16 = off B (e + 8 * j + 8) ∧ t₁.gpr .x17 = off B (e + 8 * d + 8 * j + 8))
    (by
      unfold wMove
      brun [hI.x16, hI.x17, t15, hw, hv, hI.scr.ld (show e + 8 * j + 8 ≤ Z by omega_using [he, hj]),
        hI.scr.ld (show e + 8 * d + 8 * j + 8 ≤ Z by omega_using [he, hj]),
        hI.scr.st (show e + 8 * j + 8 ≤ Z by omega_using [he, hj]), sel_mask])
    (wMove_frame false).1 (wMove_frame false).2.1 (wMove_frame false).2.2) fun t₁ ⟨⟨hm, h16, h17⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x13) fun t' ⟨⟨h13, hm', _⟩, k'⟩ => ⟨?_, by rw [h13, k₁.gpr .x13 (by decide)]⟩
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega_using [he, hj, hn]) x (by omega_arith)]
    exact hI.out x (by omega_arith)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega_using [he, hj, hn]), hI.val, wv, wv]
    cases c <;> simp [Nat.add_assoc]

theorem mvDn_ok {s : State} {B : Addr} {Z N e d : Nat} {c : Bool} (hs : Scr s B Z)
    (h15 : s.gpr .x15 = mask c) (h16 : s.gpr .x16 = off B e) (h17 : s.gpr .x17 = off B (e + 8 * d))
    (h13 : s.gpr .x13 = BitVec.ofNat 64 (N - d)) (hd : d < N) (hN : N < 2 ^ 31) (he : e + 8 * N ≤ Z) :
    WP isa (countLoop .x13 (wMove false)) s fun t =>
      wv t.mem B e (N - d) = (if c then wv s.mem B (e + 8 * d) (N - d) else wv s.mem B e (N - d)) ∧
      Outside B e (8 * (N - d)) s.mem t.mem ∧ Keep [.x3, .x4, .x13, .x16, .x17] s t ∧
      t.gpr .x16 = off B (e + 8 * (N - d)) := by
  have h0 : MvDnInv s B Z e d c 0 s :=
    ⟨hs, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, Outside.refl _ _ _ _, by simp [wv]⟩
  exact WP.mono (wp_countdown (N := N - d) (by omega_using [hN]) (by omega_using [hd]) (MvDnInv s B Z e d c)
    (fun j hj t hI _ => mvDnStep_ok h15 he hj hI) h0 h13) fun t hI => ⟨hI.val, hI.out, hI.keep, hI.x16⟩

/-- After `j` words of `wClear false` from `s₀`, up from `e`: those words cleared where the mask is set. -/
structure ClrDnInv (s₀ : State) (B : Addr) (Z e : Nat) (c : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x13, .x16] s₀ t
  x16 : t.gpr .x16 = off B (e + 8 * j)
  out : Outside B e (8 * j) s₀.mem t.mem
  val : wv t.mem B e j = if c then 0 else wv s₀.mem B e j

theorem clrDnStep_ok {s₀ : State} {B : Addr} {Z d e : Nat} {c : Bool}
    (h15 : s₀.gpr .x15 = mask c) (he : e + 8 * d ≤ Z) {j : Nat} (hj : j < d) {t : State}
    (hI : ClrDnInv s₀ B Z e c j t) :
    WP isa (.block (wClear false ++ ([.subImm .x .x13 .x13 1] : List Instr))) t fun t' =>
      ClrDnInv s₀ B Z e c (j + 1) t' ∧ t'.gpr .x13 = t.gpr .x13 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t15 : t.gpr .x15 = mask c := (hI.keep.gpr .x15 (by decide)).trans h15
  have hw : word t.mem B (e + 8 * j) = word s₀.mem B (e + 8 * j) :=
    hI.out.word (by omega_using []) (by omega_using [he, hj, hn])
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x16] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (e + 8 * j)) (if c then 0 else word s₀.mem B (e + 8 * j)) ∧
      t₁.gpr .x16 = off B (e + 8 * j + 8))
    (by
      unfold wClear
      brun [hI.x16, t15, hw, hI.scr.ld (show e + 8 * j + 8 ≤ Z by omega_using [he, hj]),
        hI.scr.st (show e + 8 * j + 8 ≤ Z by omega_using [he, hj]), clear_mask])
    (wClear_frame false).1 (wClear_frame false).2.1 (wClear_frame false).2.2) fun t₁ ⟨⟨hm, h16⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x13) fun t' ⟨⟨h13, hm', _⟩, k'⟩ => ⟨?_, by rw [h13, k₁.gpr .x13 (by decide)]⟩
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega_using [he, hj, hn]) x (by omega_arith)]
    exact hI.out x (by omega_arith)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega_using [he, hj, hn]), hI.val, wv]
    cases c <;> simp

theorem clrDn_ok {s : State} {B : Addr} {Z e d : Nat} {c : Bool} (hs : Scr s B Z)
    (h15 : s.gpr .x15 = mask c) (h16 : s.gpr .x16 = off B e) (h13 : s.gpr .x13 = BitVec.ofNat 64 d)
    (hd : 1 ≤ d) (hd' : d < 2 ^ 31) (he : e + 8 * d ≤ Z) :
    WP isa (countLoop .x13 (wClear false)) s fun t =>
      wv t.mem B e d = (if c then 0 else wv s.mem B e d) ∧ Outside B e (8 * d) s.mem t.mem ∧
      Keep [.x3, .x4, .x13, .x16] s t :=
  WP.mono (wp_countdown (N := d) (by omega_using [hd']) (by omega_using [hd]) (ClrDnInv s B Z e c)
    (fun j hj t hI _ => clrDnStep_ok h15 he hj hI)
    ⟨hs, Keep.refl _ _, by rw [h16]; rfl, Outside.refl _ _ _ _, by simp [wv]⟩ h13)
    fun t hI => ⟨hI.val, hI.out, hI.keep⟩

/-! ## The header slots of the stages' own -/

/-- A header slot of the halvings', shifts' and square root's own: none of the arguments, the mask or
the stride. -/
def Own (sl : Nat) : Prop := 25 ≤ sl ∧ sl < 32 ∧ sl ≠ sStride

/-- After a store to a slot of the stages' own. -/
theorem G.own {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s t : State} (h : G I m₀ w c s) {sl : Nat} (hsl : Own sl)
    (hf : Frm I.B [(8 * sl, 8)] s.mem t.mem) {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) :
    G I m₀ w c t := by
  obtain ⟨h1, h2, h3⟩ := hsl
  have hn := h.ws.scr.nowrap
  have h256 := h.ws.h256
  have hw : ∀ i, i < 32 → i ≠ sl → word t.mem I.B (8 * i) = word s.mem I.B (8 * i) := fun i hi hne =>
    hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; dsimp only; omega_using [hne]) (by omega_using [hi])
  have hi : InScr I.B I.Z s.mem t.mem := InScr.of_frm hf (by
    simp only [List.mem_singleton]; rintro r rfl; dsimp only; omega_using [h2, h256])
  have hs3 : sl ≠ 28 := h3
  exact ⟨⟨h.ws.scr.congr k.wr, (k.gpr .x0 hr).trans h.ws.x0, (hw sW (by decide) (by simp only [sW]; omega_using [h1])).trans h.ws.hw,
      (hw sStride (by decide) (Ne.symm h3)).trans h.ws.hS,
      fun j hj => (hw (sArr j) (by unfold sArr; omega_using [hj]) (by unfold sArr; omega_using [h1, hj])).trans (h.ws.harr j hj),
      h.ws.hZ, h.ws.w1, h.ws.w2⟩,
    h.args.congr fun i hi => hw i (by unfold rArg at hi; omega_using [hi]) (by unfold rArg at hi; omega_using [h1, hi]),
    h.n.congrK hi k, h.e.congrK hi k, h.d.congrK hi k, h.inScr.trans hi, k.wr.trans h.wr,
    (hw Public.sMask (by simp only [Public.sMask, sFn]; omega_using []) (by simp only [Public.sMask, sFn]; omega_using [h1])).trans h.msk⟩

/-- After a piece that changes arrays (ranges past the header) and a slot of the stages' own. -/
theorem G.frmOwn {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s t : State} (h : G I m₀ w c s) {sl : Nat}
    (hsl : Own sl) {rs : List (Nat × Nat)} (hf : Frm I.B (rs ++ [(8 * sl, 8)]) s.mem t.mem)
    (hm : ∀ r ∈ rs, 8 * 32 ≤ r.1) (hz : ∀ r ∈ rs, r.1 + r.2 ≤ I.Z) {regs : List Reg} (k : Keep regs s t)
    (hr : .x0 ∉ regs) : G I m₀ w c t := by
  obtain ⟨h1, h2, h3⟩ := hsl
  have hn := h.ws.scr.nowrap
  have h256 := h.ws.h256
  have hw : ∀ i, i < 32 → i ≠ sl → word t.mem I.B (8 * i) = word s.mem I.B (8 * i) := fun i hi hne =>
    hf.word_eq (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · have := hm r hr; omega_using [hi, this]
      · rw [List.mem_singleton.mp hr]; dsimp only; omega_using [hne]) (by omega_using [hi])
  have hi : InScr I.B I.Z s.mem t.mem := InScr.of_frm hf (fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hz r hr
    · rw [List.mem_singleton.mp hr]; dsimp only; omega_using [h2, h256])
  have hs3 : sl ≠ 28 := h3
  exact ⟨⟨h.ws.scr.congr k.wr, (k.gpr .x0 hr).trans h.ws.x0, (hw sW (by decide) (by simp only [sW]; omega_using [h1])).trans h.ws.hw,
      (hw sStride (by decide) (Ne.symm h3)).trans h.ws.hS,
      fun j hj => (hw (sArr j) (by unfold sArr; omega_using [hj]) (by unfold sArr; omega_using [h1, hj])).trans (h.ws.harr j hj),
      h.ws.hZ, h.ws.w1, h.ws.w2⟩,
    h.args.congr fun i hi => hw i (by unfold rArg at hi; omega_using [hi]) (by unfold rArg at hi; omega_using [h1, hi]),
    h.n.congrK hi k, h.e.congrK hi k, h.d.congrK hi k, h.inScr.trans hi, k.wr.trans h.wr,
    (hw Public.sMask (by simp only [Public.sMask, sFn]; omega_using []) (by simp only [Public.sMask, sFn]; omega_using [h1])).trans h.msk⟩

/-- `sth r sl`: register `r` into a slot of the stages' own. -/
theorem sthOwn_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) {sl : Nat} (hsl : Own sl)
    (r : Reg) :
    WP isa (.block [sth r sl]) s fun t => G I m₀ w c t ∧ Frm I.B [(8 * sl, 8)] s.mem t.mem ∧
      word t.mem I.B (8 * sl) = s.gpr r ∧ Keep [] s t := by
  obtain ⟨h1, h2, h3⟩ := hsl
  have hn := h.ws.scr.nowrap
  have h256 := h.ws.h256
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off I.B (8 * sl)) (s.gpr r)) ?_
    (by simp [writesOnly, Code.allInstrs, dsts, dstOf, Option.toList, sth]) rfl rfl) fun t ⟨hm, k⟩ => ?_
  · brun [sth, h.ws.x0, hdr_enc h2, h.ws.scr.st (d := 8 * sl) (by omega_using [h2, h256])]
  · have o := writeW_outside s.mem I.B (s.gpr r) (d := 8 * sl) (by omega_using [h2])
    rw [← hm] at o
    have hf : Frm I.B [(8 * sl, 8)] s.mem t.mem := Frm.of_outside o (List.mem_singleton_self _)
    exact ⟨h.own ⟨h1, h2, h3⟩ hf k (by simp), hf, by rw [hm, word_writeW_self], k⟩

/-! ## A stage's mask -/

/-- The bit of a stage: bit `k` of `T` (`words`: of `⌊T / 64⌋`). -/
def stBit (T : Nat) (words : Bool) (k : Nat) : Bool := decide ((if words then T / 64 else T) / 2 ^ k % 2 = 1)

theorem stageMask_ok {s : State} {B : Addr} {Z T sl : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hsl : sl < 32)
    (hZ : 8 * 32 ≤ Z) (hT : word s.mem B (8 * sl) = BitVec.ofNat 64 T) (hT' : T < 2 ^ 64) (words : Bool) {k : Nat}
    (hk : k < 64) :
    WP isa (.block (stageMask sl words k)) s fun t =>
      (t.gpr .x15 = mask (stBit T words k) ∧ t.gpr .x7 = 0 ∧ t.mem = s.mem) ∧ Keep [.x3, .x4, .x7, .x10, .x15] s t := by
  refine WP.keep [.x3, .x4, .x7, .x10, .x15] ?_
    (by cases words <;> simp [stageMask, writesOnly, Code.allInstrs, dsts, dstOf, Option.toList, ldh, movi])
    (by cases words <;> rfl) (by cases words <;> rfl)
  cases words <;>
  · brun [stageMask, h0, hdr_enc hsl, hs.ld (d := 8 * sl) (by omega_using [hsl, hZ]), hT, hk, show 6 < 64 by decide]
    rw [mask_low']; congr 1
    simp only [stBit, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hT']
    rfl

/-- The scan's mask of a word `y ≠ 0`, from the carry of `0 - y`. -/
theorem nz_mask (y : BitVec 64) :
    0 + 0 + BitVec.ofNat 64 (decide (2 ^ 64 ≤ BitVec.toNat (0 : BitVec 64) + (~~~y).toNat + true.toNat)).toNat - 1#64 =
      mask (decide (y ≠ 0)) := by
  have e : (~~~y).toNat = 2 ^ 64 - 1 - y.toNat := by rw [BitVec.toNat_not]
  have hy := y.isLt
  have key : decide (2 ^ 64 ≤ BitVec.toNat (0 : BitVec 64) + (~~~y).toNat + true.toNat) = decide (y = 0) := by
    rw [e, show (0 : BitVec 64).toNat = 0 from rfl, Bool.toNat_true]
    apply decide_eq_decide.mpr
    constructor
    · intro h; apply BitVec.eq_of_toNat_eq; rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega_using [h]
    · intro h; subst h; rw [show (0 : BitVec 64).toNat = 0 from rfl]
      all_goals omega_using []
  rw [key]
  by_cases h : y = 0
  · simp only [h, decide_true, decide_not, Bool.not_true]; rfl
  · simp only [h, decide_false, decide_not, Bool.not_false]; rfl

theorem mask_or' (a b : Bool) : mask a ||| mask b = mask (a || b) := by
  cases a <;> cases b <;> rfl

/-! ## A stage's context -/

/-- A stage's width: the wide `W` (`wide`) or the narrow `v`. -/
abbrev nw (k : Nat) (wide : Bool) : Nat := if wide then Wk k else vk k

/-- What `setNar` and `setWid` leave of a header slot of the functions' own. -/
theorem hdrW_word {B : Addr} {m m' : Mem} (hf : Frm B hdrW m m') {sl : Nat} (hsl : 16 ≤ sl) (hsl' : sl < 32)
    (hslS : sl ≠ sStride) : word m' B (8 * sl) = word m B (8 * sl) :=
  hf.word_eq (fun r hr => by
    simp only [hdrW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [sW, sArr, sStride, sFn] at hslS ⊢ <;> omega_arith) (by omega_using [hsl'])

/-- `ctxOf wide`: the header and `x12`, `x11` at the stage's width. -/
theorem ctx_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I) (wide : Bool)
    (hw : wide = false → w = vk I.k) {N : Nat} (hN : nw I.k wide = N) :
    WP isa (.block (ctxOf wide)) s fun t =>
      (G I m₀ N c t ∧ Frm I.B hdrW s.mem t.mem ∧ t.gpr .x12 = BitVec.ofNat 64 N ∧
        t.gpr .x11 = BitVec.ofNat 64 (8 * (N + 2))) ∧ Keep [.x3, .x4, .x11, .x12] s t := by
  subst hN
  cases wide
  · obtain rfl := hw rfl
    refine WP.mono (ws_ok h.ws.scr h.ws.x0 h.ws.h256 h.ws.hw h.ws.hS) fun t ⟨⟨h12, h11, hm, _⟩, k⟩ =>
      ⟨⟨h.same hm k (by decide), by rw [hm]; exact Frm.refl _ _ _, h12, h11⟩, k.mono (by decide)⟩
  · unfold ctxOf
    simp only [↓reduceIte]
    rw [WP.block_append_iff]
    refine WP.mono (h.setWid_ok L) fun t₁ ⟨h₁, f₁, k₁⟩ => ?_
    refine WP.mono (ws_ok h₁.ws.scr h₁.ws.x0 h₁.ws.h256 h₁.ws.hw h₁.ws.hS) fun t ⟨⟨h12, h11, hm, _⟩, k⟩ =>
      ⟨⟨h₁.same hm k (by decide), by rw [hm]; exact f₁, h12, h11⟩, (k₁.trans k).mono (by decide)⟩

/-- A stage's prefix: the context, the base of array `j` into `r`, and the stage's mask. -/
theorem pre_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I) (wide : Bool)
    (hw : wide = false → w = vk I.k)
    {j : Nat} (r : Reg) (hr : r = .x8 ∨ r = .x16) {sl T : Nat} (hsl : 16 ≤ sl) (hsl' : sl < 32)
    (hslS : sl ≠ sStride) (hT : word s.mem I.B (8 * sl) = BitVec.ofNat 64 T) (hT' : T < 2 ^ 64) (words : Bool)
    {k : Nat} (hk : k < 64) {N : Nat} (hN : nw I.k wide = N) :
    WP isa (.block (ctxOf wide ++ base j r ++ stageMask sl words k)) s fun t =>
      (G I m₀ N c t ∧ Frm I.B hdrW s.mem t.mem ∧ t.gpr .x12 = BitVec.ofNat 64 N ∧
        t.gpr r = off I.B (slot N j) ∧ t.gpr .x15 = mask (stBit T words k) ∧ t.gpr .x7 = 0) ∧
      Keep [.x3, .x4, .x7, .x10, .x11, .x12, .x15, r] s t := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (ctx_ok h L wide hw hN) fun t₁ ⟨⟨h₁, f₁, h12, h11⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  have hb : WP isa (.block (base j r)) t₁ fun t =>
      (t.gpr r = off I.B (slot N j) ∧ t.mem = t₁.mem ∧ t.c = t₁.c) ∧ Keep [r] t₁ t := by
    rcases hr with rfl | rfl <;> exact base_ok j _ h₁.ws.x0 h11
  refine WP.mono hb fun t₂ ⟨⟨hr₂, m₂, _⟩, k₂⟩ => ?_
  have h₂ := h₁.same m₂ k₂ (by rcases hr with rfl | rfl <;> decide)
  refine WP.mono (stageMask_ok h₂.ws.scr h₂.ws.x0 hsl' h₂.ws.h256 (by rw [m₂, hdrW_word f₁ hsl hsl' hslS]; exact hT)
    hT' words hk) fun t ⟨⟨h15, h7, m₃⟩, k₃⟩ => ⟨⟨h₂.same m₃ k₃ (by decide), by rw [m₃, m₂]; exact f₁,
      by rw [k₃.gpr .x12 (by decide), k₂.gpr .x12 (by rcases hr with rfl | rfl <;> decide), h12],
      by rw [k₃.gpr r (by rcases hr with rfl | rfl <;> decide), hr₂], h15, h7⟩,
    ((k₁.trans k₂).trans k₃).mono (by rcases hr with rfl | rfl <;> decide)⟩

theorem off_top (B : Addr) {e N : Nat} (hN : 1 ≤ N) (hN' : N < 2 ^ 32) :
    off B e + BitVec.ofNat 64 N <<< 3 - 8#64 = off B (e + 8 * N - 8) := by
  apply BitVec.eq_of_toNat_eq
  have := B.isLt
  simp only [off, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

theorem ofNat_sub_ofNat {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem off_sub (B : Addr) {a b : Nat} (hb : b ≤ a) : off B a - BitVec.ofNat 64 b = off B (a - b) := by
  rw [show off B a = off B (a - b) + BitVec.ofNat 64 b by rw [off_add, Nat.sub_add_cancel hb], BitVec.add_sub_cancel]

/-- The guard of a word stage: `x3 := (N - 1) >> k`. -/
theorem guardT_ok {s : State} {N k : Nat} (h12 : s.gpr .x12 = BitVec.ofNat 64 N) (hN : 1 ≤ N) (hN' : N < 2 ^ 32)
    (hk : k < 64) :
    WP isa (.block [.subImm .x .x3 .x12 1, .lsr .x .x3 .x3 k]) s fun t =>
      (t.gpr .x3 = BitVec.ofNat 64 ((N - 1) / 2 ^ k) ∧ t.mem = s.mem) ∧ Keep [.x3] s t := by
  refine WP.keep [.x3] ?_ (by simp [writesOnly, Code.allInstrs, dsts, dstOf, Option.toList]) rfl rfl
  brun [h12, hk]
  have e1 : (2 ^ 64 - 1 % 2 ^ 64 + N % 2 ^ 64) % 2 ^ 64 = N - 1 := by omega_using [hN, hN']
  have e2 : (N - 1) / 2 ^ k < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_using [hN'])
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, e1,
    Nat.mod_eq_of_lt e2]

/-- The pointers of a word stage up: `x16` at the top word, `x17` `2^k` words below, `x13 := N - 2^k`. -/
theorem tailWU_ok {s : State} {B : Addr} {N e k : Nat} (h12 : s.gpr .x12 = BitVec.ofNat 64 N)
    (h8 : s.gpr .x8 = off B e) (hd : 2 ^ k < N) (hN' : N < 2 ^ 32) (hk : k < 9) :
    WP isa (.block [.lsl .x .x3 .x12 3, .add .x .x16 .x8 .x3, .subImm .x .x16 .x16 8,
        .subImm .x .x17 .x16 (8 * 2 ^ k), .subImm .x .x13 .x12 (2 ^ k)]) s fun t =>
      (t.gpr .x16 = off B (e + 8 * N - 8) ∧ t.gpr .x17 = off B (e + 8 * N - 8 - 8 * 2 ^ k) ∧
        t.gpr .x13 = BitVec.ofNat 64 (N - 2 ^ k) ∧ t.mem = s.mem) ∧ Keep [.x3, .x13, .x16, .x17] s t := by
  refine WP.keep [.x3, .x13, .x16, .x17] ?_ (by simp [writesOnly, Code.allInstrs, dsts, dstOf, Option.toList]) rfl rfl
  have : 2 ^ k ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega_using [hk])
  have := Nat.two_pow_pos k
  brun [h12, h8, show 8 * 2 ^ k < 4096 by omega_arith, show 2 ^ k < 4096 by omega_arith]
  rw [off_top B (by omega_using [hd, this]) hN', off_sub B (by omega_using [hd]), ofNat_sub_ofNat (by omega_using [hd]) (by omega_using [hN'])]
  exact ⟨rfl, rfl, rfl⟩

/-- The pointers of a word stage down: `x17` `2^k` words above `x16`, `x13 := N - 2^k`. -/
theorem tailWD_ok {s : State} {B : Addr} {N e k : Nat} (h12 : s.gpr .x12 = BitVec.ofNat 64 N)
    (h16 : s.gpr .x16 = off B e) (hd : 2 ^ k < N) (hN' : N < 2 ^ 32) (hk : k < 9) :
    WP isa (.block [.addImm .x .x17 .x16 (8 * 2 ^ k), .subImm .x .x13 .x12 (2 ^ k)]) s fun t =>
      (t.gpr .x17 = off B (e + 8 * 2 ^ k) ∧ t.gpr .x13 = BitVec.ofNat 64 (N - 2 ^ k) ∧ t.mem = s.mem) ∧
        Keep [.x13, .x17] s t := by
  refine WP.keep [.x13, .x17] ?_ (by simp [writesOnly, Code.allInstrs, dsts, dstOf, Option.toList]) rfl rfl
  have : 2 ^ k ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega_using [hk])
  brun [h12, h16, show 8 * 2 ^ k < 4096 by omega_using [this], show 2 ^ k < 4096 by omega_using [this]]
  exact ofNat_sub_ofNat (by omega_using [hd]) (by omega_using [hN'])

/-- The start of a bit stage down: `x16` at the top word, `x14 := N`, `x2 := 0`. -/
theorem tailBD_ok {s : State} {B : Addr} {N e : Nat} (h12 : s.gpr .x12 = BitVec.ofNat 64 N)
    (h16 : s.gpr .x16 = off B e) (hN : 1 ≤ N) (hN' : N < 2 ^ 32) :
    WP isa (.block [.lsl .x .x3 .x12 3, .add .x .x16 .x16 .x3, .subImm .x .x16 .x16 8, mov .x14 .x12, movi .x2 0]) s
      fun t => (t.gpr .x16 = off B (e + 8 * N - 8) ∧ t.gpr .x14 = BitVec.ofNat 64 N ∧ t.gpr .x2 = 0 ∧
        t.mem = s.mem) ∧ Keep [.x2, .x3, .x14, .x16] s t := by
  refine WP.keep [.x2, .x3, .x14, .x16] ?_ (by simp [writesOnly, Code.allInstrs, dsts, dstOf, Option.toList, mov, movi])
    rfl rfl
  brun [h12, h16]
  exact off_top B hN hN'

/-- The start of a bit stage up: `x14 := N`, `x2 := 0`. -/
theorem tailBU_ok {s : State} {N : Nat} (h12 : s.gpr .x12 = BitVec.ofNat 64 N) :
    WP isa (.block [mov .x14 .x12, movi .x2 0]) s
      fun t => (t.gpr .x14 = BitVec.ofNat 64 N ∧ t.gpr .x2 = 0 ∧ t.mem = s.mem) ∧ Keep [.x2, .x14] s t := by
  refine WP.keep [.x2, .x14] ?_ (by simp [writesOnly, Code.allInstrs, dsts, dstOf, Option.toList, mov, movi]) rfl rfl
  brun [h12]

/-! ## Word stages -/

/-- The registers a stage writes. -/
def stRegs : List Reg := [.x2, .x3, .x4, .x7, .x8, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

/-- The arrays are apart from the header slots `setNar` and `setWid` write. -/
theorem hdrW_wv {B : Addr} {m m' : Mem} (hf : Frm B hdrW m m') {d n : Nat} (hd : 256 ≤ d) (hd' : d + 8 * n ≤ 2 ^ 64) :
    wv m' B d n = wv m B d n :=
  hf.wv_eq (fun r hr => by
    simp only [hdrW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [sW, sArr, sStride, sFn] <;> omega_using [hd]) hd'

/-- A number times `2^(64 d)` modulo `2^(64 N)`: its low `N - d` words, moved up. -/
theorem wv_shl_words (m : Mem) (B : Addr) (e : Nat) {d N : Nat} (hd : d ≤ N) :
    wv m B e N * 2 ^ (64 * d) % 2 ^ (64 * N) = 2 ^ (64 * d) * wv m B e (N - d) := by
  have hs := wv_add m B e (N - d) d
  rw [Nat.sub_add_cancel hd] at hs
  rw [hs, show (wv m B e (N - d) + 2 ^ (64 * (N - d)) * wv m B (e + 8 * (N - d)) d) * 2 ^ (64 * d) =
      wv m B e (N - d) * 2 ^ (64 * d) + 2 ^ (64 * (N - d)) * 2 ^ (64 * d) * wv m B (e + 8 * (N - d)) d by ring,
    ← Nat.pow_add, show 64 * (N - d) + 64 * d = 64 * N by omega_using [hd], Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt,
    Nat.mul_comm]
  calc wv m B e (N - d) * 2 ^ (64 * d) < 2 ^ (64 * (N - d)) * 2 ^ (64 * d) :=
        Nat.mul_lt_mul_of_pos_right (wv_lt _ _ _ _) (Nat.two_pow_pos _)
    _ = 2 ^ (64 * N) := by rw [← Nat.pow_add]; congr 1; omega_using [hd]

/-- A number over `2^(64 d)`: its top `N - d` words. -/
theorem wv_shr_words (m : Mem) (B : Addr) (e : Nat) {d N : Nat} (hd : d ≤ N) :
    wv m B e N / 2 ^ (64 * d) = wv m B (e + 8 * d) (N - d) := by
  have hs := wv_add m B e d (N - d)
  rw [Nat.add_sub_cancel' hd] at hs
  rw [hs, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (wv_lt _ _ _ _), Nat.zero_add]

theorem stBit_false {T N k : Nat} (words : Bool) (hT : (if words then T / 64 else T) < N) (hk : N - 1 < 2 ^ k) :
    stBit T words k = false := by
  unfold stBit
  rw [Nat.div_eq_of_lt (by omega_using [hT, hk])]
  decide

theorem ofNat_beq_zero {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x == 0) = decide (x = 0) := by
  by_cases h : x = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 x ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this)
    rw [beq_eq_false_iff_ne.mpr this]; simp [h]

theorem movK_ok (s : State) (r : Reg) {k : Nat} (hk : k < 16) :
    WP isa (.block [movi r (2 ^ k)]) s fun t =>
      (t.gpr r = BitVec.ofNat 64 (2 ^ k) ∧ t.mem = s.mem) ∧ Keep [r] s t := by
  refine WP.keep [r] ?_ (by simp [writesOnly, Code.allInstrs, dsts, dstOf, Option.toList, movi]) rfl rfl
  brun
  apply BitVec.eq_of_toNat_eq
  have : 2 ^ k < 2 ^ 16 := Nat.pow_lt_pow_right (by decide) hk
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (Nat.lt_trans this (by decide))]

/-- The value of array `j` after a stage, by what changed in its words. -/
def stVal (V : Nat) (b up : Bool) (d N : Nat) : Nat :=
  if b then (if up then V * 2 ^ (64 * d) % 2 ^ (64 * N) else V / 2 ^ (64 * d)) else V

/-- Word stage `k` of a shift of array `j` by the count `T` in header slot `sl`. -/
theorem wstage_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I)
    (wide up : Bool) {j : Nat} (hj : j < 16) {sl T : Nat} (hsl : 16 ≤ sl) (hsl' : sl < 32) (hslS : sl ≠ sStride)
    (hT : word s.mem I.B (8 * sl) = BitVec.ofNat 64 T) (hT' : T < 2 ^ 64) (words : Bool) {k : Nat} (hk : k < 9)
    {N : Nat} (hN : nw I.k wide = N) (hTN : (if words then T / 64 else T) < N) :
    WP isa (wstage j wide up sl words k) s fun t =>
      G I m₀ (vk I.k) c t ∧ Frm I.B (hdrW ++ [(slot N j, 8 * N)]) s.mem t.mem ∧
      wv t.mem I.B (slot N j) N = stVal (wv s.mem I.B (slot N j) N) (stBit T words k) up (2 ^ k) N ∧
      Keep stRegs s t := by
  have hk1 := L.k1
  have hk2 := L.k2
  have hN2 : 2 ≤ N := by subst hN; cases wide <;> simp only [nw, Wk, vk, Bool.false_eq_true, ↓reduceIte] <;> omega_arith
  have hNl : N < 512 := by subst hN; cases wide <;> simp only [nw, Wk, vk, Bool.false_eq_true, ↓reduceIte] <;> omega_using [hk2]
  have hp : 2 ^ k ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega_using [hk])
  have hp0 := Nat.two_pow_pos k
  have he8 : 256 ≤ slot N j := hdr_lt_slot N j (i := 31) (by decide)
  unfold wstage
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (h.setNar_ok L) fun t₀ ⟨g₀, f₀, k₀⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ctx_ok g₀ L wide (fun _ => rfl) hN) fun t₁ ⟨⟨g₁, f₁, h12, _⟩, k₁⟩ => ?_
  refine WP.mono (guardT_ok (k := k) h12 (by omega_using [hTN]) (by omega_using [hNl]) (by omega_using [hk])) fun t₂ ⟨⟨h3, m₂⟩, k₂⟩ => ?_
  have g₂ := g₁.same m₂ k₂ (by decide)
  have hn := g₂.ws.scr.nowrap
  have hZ := g₂.ws.sl hj
  have f₂ : Frm I.B hdrW s.mem t₂.mem := by rw [m₂]; exact f₀.trans f₁
  have hT₂ : word t₂.mem I.B (8 * sl) = BitVec.ofNat 64 T := by
    rw [hdrW_word f₂ hsl hsl' hslS]; exact hT
  have hV : ∀ d n, 256 ≤ d → d + 8 * n ≤ 2 ^ 64 → wv t₂.mem I.B d n = wv s.mem I.B d n :=
    fun d n hd hd' => hdrW_wv f₂ hd hd'
  have hR : ∀ r ∈ hdrW, r ∈ hdrW ++ [(slot N j, 8 * N)] := fun r hr => List.mem_append_left _ hr
  have hA : (slot N j, 8 * N) ∈ hdrW ++ [(slot N j, 8 * N)] := List.mem_append_right _ (List.mem_singleton_self _)
  refine WP.ite (t₂.gpr .x3 == 0) (VG.Proof.MlKem.AArch64.eval_zero _ _) (fun hz => ?_) (fun hnz => ?_)
  · -- `2^k ≥ N`: the stage does nothing.
    rw [h3, ofNat_beq_zero (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_using [hNl]))] at hz
    have hlt : N - 1 < 2 ^ k := by
      have := of_decide_eq_true hz
      rw [Nat.div_eq_zero_iff] at this
      omega_using [hp0, this]
    refine WP.mono (g₂.setNar_ok L) fun t ⟨g, f, kk⟩ => ⟨g, (f₂.trans f).mono hR, ?_,
      (((k₀.trans k₁).trans k₂).trans kk).mono (by decide)⟩
    rw [stBit_false words hTN hlt, hdrW_wv f he8 (by omega_using [hn, hZ]), hV _ _ he8 (by omega_using [hn, hZ])]
    rfl
  · have hd : 2 ^ k < N := by
      rw [h3, ofNat_beq_zero (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_using [hNl]))] at hnz
      have := of_decide_eq_false hnz
      rw [Nat.div_eq_zero_iff] at this
      omega_using [this]
    have hw₂ : wide = false → N = vk I.k := fun hw => by rw [← hN, hw]; rfl
    generalize hb : stBit T words k = b
    cases up
    · -- Down.
      simp only [Bool.false_eq_true, ↓reduceIte, seqs]
      refine WP.seq ?_
      rw [WP.block_append_iff]
      refine WP.mono (pre_ok g₂ L wide hw₂ .x16 (.inr rfl) hsl hsl' hslS hT₂ hT' words (by omega_using [hk]) hN)
        fun t₃ ⟨⟨g₃, f₃, h12₃, h16₃, h15₃, _⟩, k₃⟩ => ?_
      rw [hb] at h15₃
      refine WP.mono (tailWD_ok h12₃ h16₃ hd (by omega_using [hNl]) hk) fun t₄ ⟨⟨h17₄, h13₄, m₄⟩, k₄⟩ => ?_
      have g₄ := g₃.same m₄ k₄ (by decide)
      have h15₄ : t₄.gpr .x15 = mask b := (k₄.gpr .x15 (by decide)).trans h15₃
      have h16₄ : t₄.gpr .x16 = off I.B (slot N j) := (k₄.gpr .x16 (by decide)).trans h16₃
      refine WP.seq (WP.mono (mvDn_ok (N := N) g₄.ws.scr h15₄ h16₄ h17₄ h13₄ hd (by omega_using [hNl]) (by omega_using [hZ]))
        fun t₅ ⟨v₅, o₅, k₅, h16₅⟩ => ?_)
      have g₅ := g₄.out hj (n := 8 * N) (by omega_using []) (o₅.mono (by omega_using []) (by omega_using [hp0])) k₅ (by decide)
      refine WP.seq (WP.mono (movK_ok t₅ .x13 (k := k) (by omega_using [hk])) fun t₆ ⟨⟨h13₆, m₆⟩, k₆⟩ => ?_)
      have g₆ := g₅.same m₆ k₆ (by decide)
      have h15₆ : t₆.gpr .x15 = mask b := (k₆.gpr .x15 (by decide)).trans ((k₅.gpr .x15 (by decide)).trans h15₄)
      have h16₆ := (k₆.gpr .x16 (by decide)).trans h16₅
      refine WP.seq (WP.mono (clrDn_ok (d := 2 ^ k) g₆.ws.scr h15₆ h16₆ h13₆ (by omega) (by omega_using [hp]) (by omega_using [hZ, hd]))
        fun t₇ ⟨v₇, o₇, k₇⟩ => ?_)
      have g₇ := g₆.out hj (n := 8 * N) (by omega_using []) (o₇.mono (by omega_using []) (by omega_using [hd])) k₇ (by decide)
      refine WP.mono (g₇.setNar_ok L) fun t ⟨g, f, kk⟩ => ⟨g, ?_, ?_, ?_⟩
      · exact ((((((f₂.trans f₃).mono hR).trans (by rw [m₄]; exact Frm.refl _ _ _)).trans
          (Frm.of_outside (o₅.mono (by omega_using []) (by omega_using [hp0])) hA)).trans (by rw [m₆]; exact Frm.refl _ _ _)).trans
          (Frm.of_outside (o₇.mono (by omega_using []) (by omega_using [hd])) hA)).trans (f.mono hR)
      · have hS : ∀ d n, 256 ≤ d → d + 8 * n ≤ 2 ^ 64 → wv t₄.mem I.B d n = wv s.mem I.B d n :=
          fun d n hd hd' => by rw [m₄, hdrW_wv f₃ hd hd', hV d n hd hd']
        have s₇ := wv_add t₇.mem I.B (slot N j) (N - 2 ^ k) (2 ^ k)
        rw [Nat.sub_add_cancel (by omega_using [hd])] at s₇
        have a2 : wv t₇.mem I.B (slot N j) (N - 2 ^ k) = if b then wv s.mem I.B (slot N j + 8 * 2 ^ k) (N - 2 ^ k)
            else wv s.mem I.B (slot N j) (N - 2 ^ k) := by
          rw [o₇.wv (by omega_using []) (by omega), m₆, v₅, hS _ _ (by omega_using [he8]) (by omega_using [hn, hZ, hd]), hS _ _ (by omega_using [he8]) (by omega_using [hp0, hn, hZ])]
        have a3 : wv t₇.mem I.B (slot N j + 8 * (N - 2 ^ k)) (2 ^ k) =
            if b then 0 else wv s.mem I.B (slot N j + 8 * (N - 2 ^ k)) (2 ^ k) := by
          rw [v₇, m₆, o₅.wv (by omega_using []) (by omega_using [hn, hZ, hd]), hS _ _ (by omega_using [he8]) (by omega_using [hn, hZ, hd])]
        rw [hdrW_wv f he8 (by omega_using [hn, hZ]), s₇, a2, a3]
        unfold stVal
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have sV := wv_add s.mem I.B (slot N j) (N - 2 ^ k) (2 ^ k)
          rw [Nat.sub_add_cancel (by omega_using [hd])] at sV
          exact sV.symm
        · simp only [↓reduceIte, Nat.mul_zero, Nat.add_zero]
          exact (wv_shr_words _ _ _ (by omega_using [hd])).symm
      · exact ((((((((k₀.trans k₁).trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans kk).mono
          (by decide)
    · -- Up.
      simp only [↓reduceIte, seqs]
      refine WP.seq ?_
      rw [WP.block_append_iff]
      refine WP.mono (pre_ok g₂ L wide hw₂ .x8 (.inl rfl) hsl hsl' hslS hT₂ hT' words (by omega_using [hk]) hN)
        fun t₃ ⟨⟨g₃, f₃, h12₃, h8₃, h15₃, _⟩, k₃⟩ => ?_
      rw [hb] at h15₃
      refine WP.mono (tailWU_ok h12₃ h8₃ hd (by omega_using [hNl]) hk) fun t₄ ⟨⟨h16₄, h17₄, h13₄, m₄⟩, k₄⟩ => ?_
      have g₄ := g₃.same m₄ k₄ (by decide)
      have h15₄ : t₄.gpr .x15 = mask b := (k₄.gpr .x15 (by decide)).trans h15₃
      refine WP.seq (WP.mono (mvUp_ok (N := N) g₄.ws.scr h15₄ h16₄ h17₄ h13₄ hd (by omega_using [hNl]) (by omega_using [hZ]) (by omega_using [he8]))
        fun t₅ ⟨v₅, o₅, k₅, h16₅⟩ => ?_)
      have g₅ := g₄.out hj (n := 8 * N) (by omega_using []) (o₅.mono (by omega_using []) (by omega_using [hd])) k₅ (by decide)
      refine WP.seq (WP.mono (movK_ok t₅ .x13 (k := k) (by omega_using [hk])) fun t₆ ⟨⟨h13₆, m₆⟩, k₆⟩ => ?_)
      have g₆ := g₅.same m₆ k₆ (by decide)
      have h15₆ : t₆.gpr .x15 = mask b := (k₆.gpr .x15 (by decide)).trans ((k₅.gpr .x15 (by decide)).trans h15₄)
      have h16₆ := (k₆.gpr .x16 (by decide)).trans h16₅
      refine WP.seq (WP.mono (clrUp_ok (d := 2 ^ k) g₆.ws.scr h15₆ h16₆ h13₆ (by omega) (by omega_using [hp]) (by omega_using [hZ, hd])
        (by omega_using [he8])) fun t₇ ⟨v₇, o₇, k₇⟩ => ?_)
      have g₇ := g₆.out hj (n := 8 * N) (by omega_using []) (o₇.mono (by omega_using []) (by omega_using [hd])) k₇ (by decide)
      refine WP.mono (g₇.setNar_ok L) fun t ⟨g, f, kk⟩ => ⟨g, ?_, ?_, ?_⟩
      · exact ((((((f₂.trans f₃).mono hR).trans (by rw [m₄]; exact Frm.refl _ _ _)).trans
          (Frm.of_outside (o₅.mono (by omega_using []) (by omega_using [hd])) hA)).trans (by rw [m₆]; exact Frm.refl _ _ _)).trans
          (Frm.of_outside (o₇.mono (by omega_using []) (by omega_using [hd])) hA)).trans (f.mono hR)
      · have hS : ∀ d n, 256 ≤ d → d + 8 * n ≤ 2 ^ 64 → wv t₄.mem I.B d n = wv s.mem I.B d n :=
          fun d n hd hd' => by rw [m₄, hdrW_wv f₃ hd hd', hV d n hd hd']
        have s₇ := wv_add t₇.mem I.B (slot N j) (2 ^ k) (N - 2 ^ k)
        rw [Nat.add_sub_cancel' (by omega_using [hd])] at s₇
        have a2 : wv t₇.mem I.B (slot N j) (2 ^ k) = if b then 0 else wv s.mem I.B (slot N j) (2 ^ k) := by
          rw [v₇, m₆, o₅.wv (by omega_using []) (by omega_using [hn, hZ, hd]), hS _ _ (by omega_using [he8]) (by omega_using [hn, hZ, hd])]
        have a3 : wv t₇.mem I.B (slot N j + 8 * 2 ^ k) (N - 2 ^ k) = if b then wv s.mem I.B (slot N j) (N - 2 ^ k)
            else wv s.mem I.B (slot N j + 8 * 2 ^ k) (N - 2 ^ k) := by
          rw [o₇.wv (by omega_using []) (by omega_using [hn, hZ, hd]), m₆, v₅, hS _ _ (by omega_using [he8]) (by omega_using [hp0, hn, hZ]), hS _ _ (by omega_using [he8]) (by omega_using [hn, hZ, hd])]
        rw [hdrW_wv f he8 (by omega_using [hn, hZ]), s₇, a2, a3]
        unfold stVal
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have sV := wv_add s.mem I.B (slot N j) (2 ^ k) (N - 2 ^ k)
          rw [Nat.add_sub_cancel' (by omega_using [hd])] at sV
          exact sV.symm
        · simp only [↓reduceIte, Nat.zero_add]
          exact (wv_shl_words _ _ _ (by omega_using [hd])).symm
      · exact ((((((((k₀.trans k₁).trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans kk).mono
          (by decide)

/-! ## Bit stages -/

/-- The value of array `j` after a bit stage. -/
def sbVal (V : Nat) (b up : Bool) (sh N : Nat) : Nat :=
  if b then (if up then V * 2 ^ sh % 2 ^ (64 * N) else V / 2 ^ sh) else V

/-- Bit stage `k < 6` of a shift of array `j` by the count `T` in header slot `sl`. -/
theorem bstage_ok {I : RpIn} {m₀ : Mem} {c : Bool} {s : State} (h : G I m₀ (vk I.k) c s) (L : RpLens I)
    (wide up : Bool) {j : Nat} (hj : j < 16) {sl T : Nat} (hsl : 16 ≤ sl) (hsl' : sl < 32) (hslS : sl ≠ sStride)
    (hT : word s.mem I.B (8 * sl) = BitVec.ofNat 64 T) (hT' : T < 2 ^ 64) {k : Nat} (hk : k < 6)
    {N : Nat} (hN : nw I.k wide = N) :
    WP isa (bstage j wide up sl k) s fun t =>
      G I m₀ (vk I.k) c t ∧ Frm I.B (hdrW ++ [(slot N j, 8 * N)]) s.mem t.mem ∧
      wv t.mem I.B (slot N j) N = sbVal (wv s.mem I.B (slot N j) N) (stBit T false k) up (2 ^ k) N ∧
      Keep stRegs s t := by
  have hk1 := L.k1
  have hk2 := L.k2
  have hN2 : 2 ≤ N := by subst hN; cases wide <;> simp only [nw, Wk, vk, Bool.false_eq_true, ↓reduceIte] <;> omega_arith
  have hNl : N < 512 := by subst hN; cases wide <;> simp only [nw, Wk, vk, Bool.false_eq_true, ↓reduceIte] <;> omega_using [hk2]
  have he8 : 256 ≤ slot N j := hdr_lt_slot N j (i := 31) (by decide)
  have hR : ∀ r ∈ hdrW, r ∈ hdrW ++ [(slot N j, 8 * N)] := fun r hr => List.mem_append_left _ hr
  have hA : (slot N j, 8 * N) ∈ hdrW ++ [(slot N j, 8 * N)] := List.mem_append_right _ (List.mem_singleton_self _)
  generalize hb : stBit T false k = b
  cases up
  · simp only [bstage, Bool.false_eq_true, ↓reduceIte, seqs]
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (pre_ok h L wide (fun _ => rfl) .x16 (.inr rfl) hsl hsl' hslS hT hT' false (by omega_using [hk]) hN)
      fun t₃ ⟨⟨g₃, f₃, h12₃, h16₃, h15₃, _⟩, k₃⟩ => ?_
    rw [hb] at h15₃
    have hn := g₃.ws.scr.nowrap
    have hZ := g₃.ws.sl hj
    refine WP.mono (tailBD_ok h12₃ h16₃ (by omega_using [hN2]) (by omega_using [hNl])) fun t₄ ⟨⟨h16₄, h14₄, h2₄, m₄⟩, k₄⟩ => ?_
    have g₄ := g₃.same m₄ k₄ (by decide)
    have h15₄ : t₄.gpr .x15 = mask b := (k₄.gpr .x15 (by decide)).trans h15₃
    refine WP.seq (WP.mono (bDn_ok g₄.ws.scr hk h15₄ h16₄ h14₄ h2₄ (by omega_using [hN2]) (by omega_using [hNl]) (by omega_using [hZ]) (by omega_using [he8]))
      fun t₅ ⟨v₅, o₅, k₅⟩ => ?_)
    have g₅ := g₄.out hj (n := 8 * N) (by omega_using []) o₅ k₅ (by decide)
    refine WP.mono (g₅.setNar_ok L) fun t ⟨g, f, kk⟩ => ⟨g, ?_, ?_, ?_⟩
    · exact ((((f₃.mono hR).trans (by rw [m₄]; exact Frm.refl _ _ _)).trans (Frm.of_outside o₅ hA)).trans
        (f.mono hR))
    · rw [hdrW_wv f he8 (by omega_using [hn, hZ]), v₅, m₄, hdrW_wv f₃ he8 (by omega_using [hn, hZ])]
      cases b <;> rfl
    · exact ((((k₃.trans k₄).trans k₅).trans kk)).mono (by decide)
  · simp only [bstage, ↓reduceIte, seqs]
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (pre_ok h L wide (fun _ => rfl) .x16 (.inr rfl) hsl hsl' hslS hT hT' false (by omega_using [hk]) hN)
      fun t₃ ⟨⟨g₃, f₃, h12₃, h16₃, h15₃, _⟩, k₃⟩ => ?_
    rw [hb] at h15₃
    have hn := g₃.ws.scr.nowrap
    have hZ := g₃.ws.sl hj
    refine WP.mono (tailBU_ok h12₃) fun t₄ ⟨⟨h14₄, h2₄, m₄⟩, k₄⟩ => ?_
    have g₄ := g₃.same m₄ k₄ (by decide)
    have h15₄ : t₄.gpr .x15 = mask b := (k₄.gpr .x15 (by decide)).trans h15₃
    have h16₄ : t₄.gpr .x16 = off I.B (slot N j) := (k₄.gpr .x16 (by decide)).trans h16₃
    refine WP.seq (WP.mono (bUp_ok g₄.ws.scr hk h15₄ h16₄ h14₄ h2₄ (by omega_using [hN2]) (by omega_using [hNl]) (by omega_using [hZ]))
      fun t₅ ⟨v₅, o₅, k₅⟩ => ?_)
    have g₅ := g₄.out hj (n := 8 * N) (by omega_using []) o₅ k₅ (by decide)
    refine WP.mono (g₅.setNar_ok L) fun t ⟨g, f, kk⟩ => ⟨g, ?_, ?_, ?_⟩
    · exact ((((f₃.mono hR).trans (by rw [m₄]; exact Frm.refl _ _ _)).trans (Frm.of_outside o₅ hA)).trans
        (f.mono hR))
    · rw [hdrW_wv f he8 (by omega_using [hn, hZ]), v₅, m₄, hdrW_wv f₃ he8 (by omega_using [hn, hZ])]
      cases b <;> rfl
    · exact ((((k₃.trans k₄).trans k₅).trans kk)).mono (by decide)

/-- Word `j` of a number of `n` words. -/
theorem wv_word_at (m : Mem) (B : Addr) (e : Nat) {n j : Nat} (hj : j < n) :
    wv m B e n / 2 ^ (64 * j) % 2 ^ 64 = (word m B (e + 8 * j)).toNat := by
  have hs := wv_add m B e j (n - j)
  rw [Nat.add_sub_cancel' (by omega_using [hj])] at hs
  rw [hs, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (wv_lt _ _ _ _), Nat.zero_add,
    wv_mod64 _ _ _ (by omega_using [hj])]

/-! ## Shifts by stages -/

/-- Stages `0, …, M - 1` in sequence. -/
theorem seqs_range_ok {f : Nat → Prog isa} {P : Nat → State → Prop} {M : Nat} (hM : 1 ≤ M)
    (hstep : ∀ m < M, ∀ t, P m t → WP isa (f m) t (P (m + 1))) {s : State} (h0 : P 0 s) :
    WP isa (seqs ((List.range M).map f)) s (P M) := by
  induction M with
  | zero => omega
  | succ M ih =>
    rcases Nat.eq_zero_or_pos M with rfl | hM'
    · exact hstep 0 (by omega_using []) s h0
    · rw [List.range_succ, List.map_append, List.map_singleton]
      exact wp_seqs_append (by simp only [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]; omega_using [hM']) (by simp)
        (WP.mono (ih hM' fun m hm => hstep m (by omega_using [hm])) fun t ht => hstep M (by omega_using []) t ht)

/-- A shift of `V` by `a` bits, up modulo `2^(64 N)` (`up`) or down. -/
def shV (V : Nat) (up : Bool) (a N : Nat) : Nat := if up then V * 2 ^ a % 2 ^ (64 * N) else V / 2 ^ a

theorem stVal_shV (V : Nat) (up b : Bool) (a d N : Nat) :
    stVal (shV V up a N) b up d N = shV V up (a + (if b then 64 * d else 0)) N := by
  unfold stVal shV
  cases b <;> cases up <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
    ShiftStages.div_pow_add, ShiftStages.mul_pow_add_mod]

theorem sbVal_shV (V : Nat) (up b : Bool) (a sh N : Nat) :
    sbVal (shV V up a N) b up sh N = shV V up (a + (if b then sh else 0)) N := by
  unfold sbVal shV
  cases b <;> cases up <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
    ShiftStages.div_pow_add, ShiftStages.mul_pow_add_mod]

theorem stBit_add (T : Nat) (words : Bool) (m : Nat) (sc : Nat) :
    sc * ((if words then T / 64 else T) % 2 ^ m) + (if stBit T words m then sc * 2 ^ m else 0) =
      sc * ((if words then T / 64 else T) % 2 ^ (m + 1)) := by
  rw [ShiftStages.mod_two_pow_succ]
  unfold stBit
  generalize (if words then T / 64 else T) = X
  rcases Nat.mod_two_eq_zero_or_one (X / 2 ^ m) with h | h <;> simp [h, Nat.mul_add]

/-- A header slot of the functions' own, after a stage. -/
theorem stage_word {B : Addr} {m m' : Mem} {N j : Nat} (hf : Frm B (hdrW ++ [(slot N j, 8 * N)]) m m') {sl : Nat}
    (hsl : 16 ≤ sl) (hsl' : sl < 32) (hslS : sl ≠ sStride) : word m' B (8 * sl) = word m B (8 * sl) :=
  hf.word_eq (fun r hr => by
    have := hdr_lt_slot N j (i := 31) (by decide)
    simp only [hdrW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl) | rfl <;> simp only [sW, sArr, sStride, sFn] at hslS ⊢ <;> omega_arith) (by omega_using [hsl'])

/-- `shiftBy j wide up sl`: array `j` shifted by the `T < 64 N` bits in header slot `sl`, up modulo its width
(`up`) or down. -/
theorem shiftBy_ok {I : RpIn} {m₀ : Mem} {w : Nat} {c : Bool} {s : State} (h : G I m₀ w c s) (L : RpLens I)
    (wide up : Bool) {j : Nat} (hj : j < 16) {sl T : Nat} (hsl : 16 ≤ sl) (hsl' : sl < 32) (hslS : sl ≠ sStride)
    (hT : word s.mem I.B (8 * sl) = BitVec.ofNat 64 T) {N : Nat} (hN : nw I.k wide = N) (hTN : T < 64 * N) :
    WP isa (seqs (shiftBy j wide up sl)) s fun t =>
      G I m₀ (vk I.k) c t ∧ Frm I.B (hdrW ++ [(slot N j, 8 * N)]) s.mem t.mem ∧
      wv t.mem I.B (slot N j) N = shV (wv s.mem I.B (slot N j) N) up T N ∧ Keep stRegs s t := by
  have hk1 := L.k1
  have hk2 := L.k2
  have hNl : N < 512 := by subst hN; cases wide <;> simp only [nw, Wk, vk, Bool.false_eq_true, ↓reduceIte] <;> omega_using [hk2]
  have hT' : T < 2 ^ 64 := by omega_using [hTN, hNl]
  have hT8 : T / 64 < 2 ^ 9 := by omega_using [hTN, hNl]
  let V := wv s.mem I.B (slot N j) N
  let P : Nat → Nat → State → Prop := fun a m t =>
    (∃ w', G I m₀ w' c t ∧ (0 < m → w' = vk I.k)) ∧ Frm I.B (hdrW ++ [(slot N j, 8 * N)]) s.mem t.mem ∧
      wv t.mem I.B (slot N j) N = shV V up a N ∧ Keep stRegs s t
  have hV0 : V = shV V up 0 N := by
    unfold shV
    cases up
    · simp
    · simp only [↓reduceIte, Nat.pow_zero, Nat.mul_one]; exact (Nat.mod_eq_of_lt (wv_lt _ _ _ _)).symm
  have hP0 : P 0 0 s := ⟨⟨w, h, fun h => absurd h (Nat.lt_irrefl 0)⟩, Frm.refl _ _ _, hV0, Keep.refl _ _⟩
  have hTt : ∀ a m t, P a m t → word t.mem I.B (8 * sl) = BitVec.ofNat 64 T := fun _ _ t ht =>
    (stage_word ht.2.1 hsl hsl' hslS).trans hT
  unfold shiftBy
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (seqs_range_ok (P := fun m => P (64 * (T / 64 % 2 ^ m)) m) (M := 9) (by decide)
    (fun m hm t ht => ?_) (by simp only [Nat.pow_zero, Nat.mod_one, Nat.mul_zero]; exact hP0)) fun t ht => ?_
  · obtain ⟨w', g₀, _⟩ := ht.1
    refine WP.mono (wstage_ok g₀ L wide up hj hsl hsl' hslS (hTt (64 * (T / 64 % 2 ^ m)) m t ht) hT' true hm hN (by simp only [↓reduceIte]; omega_using [hTN]))
      fun u ⟨g, f, v, k⟩ => ⟨⟨_, g, fun _ => rfl⟩, ht.2.1.trans f, ?_, (ht.2.2.2.trans k).mono (by decide)⟩
    rw [v, ht.2.2.1, stVal_shV]
    congr 1
    have := stBit_add T true m 64
    simp only [↓reduceIte] at this
    rw [← this]
  · rw [Nat.mod_eq_of_lt hT8] at ht
    refine WP.mono (seqs_range_ok (P := fun m => P (64 * (T / 64) + T % 2 ^ m) (m + 9)) (M := 6) (by decide)
      (fun m hm t ht => ?_) (by simp only [Nat.pow_zero, Nat.mod_one, Nat.add_zero]; exact ht)) fun t ht => ?_
    · obtain ⟨w', g₀, hw'⟩ := ht.1
      rw [hw' (by omega_using [])] at g₀
      refine WP.mono (bstage_ok g₀ L wide up hj hsl hsl' hslS (hTt (64 * (T / 64) + T % 2 ^ m) _ t ht) hT' hm hN)
        fun u ⟨g, f, v, k⟩ => ⟨⟨_, g, fun _ => rfl⟩, ht.2.1.trans f, ?_, (ht.2.2.2.trans k).mono (by decide)⟩
      rw [v, ht.2.2.1, sbVal_shV]
      congr 1
      have := stBit_add T false m 1
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.one_mul] at this
      rw [Nat.add_assoc, this]
    · rw [show 64 * (T / 64) + T % 2 ^ 6 = T by omega_using []] at ht
      obtain ⟨⟨w', g₀, hw'⟩, hf, hv, hk⟩ := ht
      rw [hw' (by omega_using [])] at g₀
      exact ⟨g₀, hf, hv, hk⟩

end VG.Proof.Rsa.AArch64.Rd
