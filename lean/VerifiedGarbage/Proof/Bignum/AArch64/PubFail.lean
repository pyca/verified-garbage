import VerifiedGarbage.Proof.Bignum.AArch64.PubValid

/-!
# RSA on AArch64: refusals

`Precompute.fail` writes `2 w` zero words to `pre` (`pcFail_ok`), and
`Precomputed.fail` `k` zero bytes to `out` (`pdFail_ok`); both return 0.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.WriteBytes (writeW8_apply)

theorem readW_zero {m : Mem} {a : Addr} (h : ∀ i < 8, m (a + BitVec.ofNat 64 i) = 0) : m.readW a 64 = 0 :=
  (Mem.readW_congr (m' := fun _ => 0) fun i hi => h i (by omega)).trans (by simp [Mem.readW, Mem.read])

theorem two_w (k : Nat) (hk : k < 2 ^ 32) :
    (BitVec.ofNat 64 k + BitVec.ofNat 64 7) >>> 3 <<< 1 = BitVec.ofNat 64 (2 * ((k + 7) / 8)) := by
  rw [shr3_w k hk]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-! ## Zero words -/

/-- After `j` zero words from `s₀`. -/
structure ZInv (s₀ : State) (op : Addr) (j : Nat) (t : State) : Prop where
  keep : Keep [.x1, .x2] s₀ t
  x1 : t.gpr .x1 = off op (8 * j)
  done : ∀ i < j, word t.mem op (8 * i) = 0
  frame : Outside op 0 (8 * j) s₀.mem t.mem

theorem zStep_ok {s₀ : State} {op : Addr} {N : Nat} (hN : 8 * N ≤ 2 ^ 64) (h3 : s₀.gpr .x3 = 0)
    (hwr : ∀ j < N, InRegions s₀.wr (off op (8 * j)) 8) {j : Nat} (hj : j < N) {t : State}
    (hI : ZInv s₀ op j t) :
    WP isa (.block ([st .x3 .x1, next .x1] ++ ([.subImm .x .x2 .x2 1] : List Instr))) t
      fun t' => ZInv s₀ op (j + 1) t' ∧ t'.gpr .x2 = t.gpr .x2 - BitVec.ofNat 64 1 := by
  have hst : InRegions t.wr (off op (8 * j)) 8 := by rw [hI.keep.wr]; exact hwr j hj
  have h3' : t.gpr .x3 = 0 := (hI.keep.gpr .x3 (by decide)).trans h3
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x1] (Q := fun t₁ => t₁.mem = t.mem.writeW (off op (8 * j)) (0 : BitVec 64) ∧
      t₁.gpr .x1 = off op (8 * j + 8)) (by brun [hI.x1, hst, h3']) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨hm, h1⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x2) fun t' ⟨⟨h2, hm', _⟩, k'⟩ => ⟨?_, by rw [h2, k₁.gpr .x2 (by decide)]⟩
  refine ⟨((hI.keep.trans k₁).trans k').mono (by decide),
    by rw [k'.gpr .x1 (by decide), h1, Nat.mul_succ], fun i hi => ?_, ?_⟩
  · rw [hm', hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [(writeW_outside t.mem op _ (by omega)).word (by omega) (by omega)]; exact hI.done i hi
    · exact word_writeW_self _ _ _ _
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem op _ (by omega) x (by omega)]
    exact hI.frame x (by omega)

/-- What `Precompute`'s branches leave: the words `ws` to `pre`, the flag
`c` returned, and memory outside the working space and `pre` unchanged. -/
structure PcPost (s t : State) (B : Addr) (Z w : Nat) (op : Addr) (ws : List (BitVec 64)) (c : Bool) :
    Prop where
  words : Spec.Rsa.wordsAt t.mem op (2 * w) = ws
  x0 : t.gpr .x0 = BitVec.ofNat 64 c.toNat
  frame : ∀ x, Z ≤ ofs B x → 16 * w ≤ ofs op x → t.mem x = s.mem x
  keep : Keep (.x0 :: mmRegs) s t

/-- `Precompute.fail`: `2 w` zero words to `pre`, and 0 returned. -/
theorem pcFail_ok {s : State} {B : Addr} {Z k : Nat} {op : Addr} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (hZ : 8 * 32 ≤ Z) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hO : word s.mem B (8 * sOut) = op) (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hout : ∀ i < 2 * ((k + 7) / 8), InRegions s.wr (off op (8 * i)) 8) :
    WP isa Precompute.fail s fun t =>
      PcPost s t B Z ((k + 7) / 8) op (List.replicate (2 * ((k + 7) / 8)) 0) false := by
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  unfold Precompute.fail
  refine WP.seq (WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => t.gpr .x1 = off op 0 ∧
      t.gpr .x2 = BitVec.ofNat 64 (2 * ((k + 7) / 8)) ∧ t.gpr .x3 = 0 ∧ t.mem = s.mem) (by
    brun [h0, hdr_enc (show sOut < 32 by decide), hdr_enc (show sK < 32 by decide), hl sOut (by decide),
      hl sK (by decide), hO, hK, two_w k (by omega)]) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h1, h2, h3, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (wp_countdown (N := 2 * ((k + 7) / 8)) (by omega) (by omega) (ZInv s₁ op)
    (fun j hj t hI _ => zStep_ok (by omega) h3 (fun i hi => by rw [k₁.wr]; exact hout i hi) hj hI)
    ⟨Keep.refl _ _, h1, fun i hi => absurd hi (Nat.not_lt_zero _), Outside.refl _ _ _ _⟩ h2) fun t₂ hI => ?_)
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0 ∧ t.mem = t₂.mem) (by brun) (by decide) (by decide)
    (by decide +kernel)) fun t ⟨⟨hx, hm⟩, k₃⟩ => ⟨?_, hx, fun x _ hx' => ?_, ((k₁.trans hI.keep).trans k₃).mono
      (by decide)⟩
  · rw [Spec.Rsa.wordsAt, List.eq_replicate_iff]
    refine ⟨by simp, fun x hx => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hm]
    exact hI.done i (List.mem_range.mp hi)
  · rw [hm, hI.frame x (by omega), hm₁]

/-! ## Zero bytes -/

/-- After `j` zero bytes from `s₀`. -/
structure BInv (s₀ : State) (op : Addr) (j : Nat) (t : State) : Prop where
  keep : Keep [.x1, .x2] s₀ t
  x1 : t.gpr .x1 = op + BitVec.ofNat 64 j
  bytes : ∀ i < j, t.mem (op + BitVec.ofNat 64 i) = 0
  frame : ∀ x, (∀ i < j, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s₀.mem x

theorem bStep_ok {s₀ : State} {op : Addr} {N : Nat} (hN : N < 2 ^ 63) (h3 : s₀.gpr .x3 = 0)
    (hwr : ∀ j < N, InRegions s₀.wr (op + BitVec.ofNat 64 j) 1) {j : Nat} (hj : j < N) {t : State}
    (hI : BInv s₀ op j t) :
    WP isa (.block ([.strb .x3 .x1 0, .addImm .x .x1 .x1 1] ++ ([.subImm .x .x2 .x2 1] : List Instr))) t
      fun t' => BInv s₀ op (j + 1) t' ∧ t'.gpr .x2 = t.gpr .x2 - BitVec.ofNat 64 1 := by
  have hst : InRegions t.wr (op + BitVec.ofNat 64 j) 1 := by rw [hI.keep.wr]; exact hwr j hj
  have h3' : t.gpr .x3 = 0 := (hI.keep.gpr .x3 (by decide)).trans h3
  have hw8 : ∀ (m : Mem) (a : Addr) (v : BitVec 8), m.write a 1 v = m.writeW a v := fun _ _ _ => rfl
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x1] (Q := fun t₁ => t₁.mem = t.mem.writeW (op + BitVec.ofNat 64 j) (0 : BitVec 8) ∧
      t₁.gpr .x1 = op + BitVec.ofNat 64 (j + 1)) (by
    brun [hI.x1, hst, h3', hw8, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; rfl) (by decide) (by decide)
      (by decide +kernel))
    fun t₁ ⟨⟨hm, h1⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x2) fun t' ⟨⟨h2, hm', _⟩, k'⟩ => ⟨?_, by rw [h2, k₁.gpr .x2 (by decide)]⟩
  refine ⟨((hI.keep.trans k₁).trans k').mono (by decide), by rw [k'.gpr .x1 (by decide), h1], fun i hi => ?_,
    fun x hx => ?_⟩
  · rw [hm', hm, writeW8_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) hij))]
      exact hI.bytes i (by omega)
  · rw [hm', hm, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
    exact hI.frame x fun i hi => hx i (by omega)

/-- `Precomputed.fail`: `k` zero bytes to `out`, and 0 returned. -/
theorem pdFail_ok {s : State} {B : Addr} {Z k : Nat} {op : Addr} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (hZ : 8 * 32 ≤ Z) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hO : word s.mem B (8 * sOut) = op) (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hout : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1) :
    WP isa Precomputed.fail s fun t => Spec.Rsa.bytesAt t.mem op k = List.replicate k 0 ∧
      t.gpr .x0 = 0 ∧ (∀ x, (∀ i < k, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep (.x0 :: mmRegs) s t := by
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  unfold Precomputed.fail
  refine WP.seq (WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => t.gpr .x1 = op + BitVec.ofNat 64 0 ∧
      t.gpr .x2 = BitVec.ofNat 64 k ∧ t.gpr .x3 = 0 ∧ t.mem = s.mem) (by
    brun [h0, hdr_enc (show sOut < 32 by decide), hdr_enc (show sK < 32 by decide), hl sOut (by decide),
      hl sK (by decide), hO, hK]) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h1, h2, h3, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (wp_countdown (N := k) (by omega) (by omega) (BInv s₁ op)
    (fun j hj t hI _ => bStep_ok (by omega) h3 (fun i hi => by rw [k₁.wr]; exact hout i hi) hj hI)
    ⟨Keep.refl _ _, h1, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩ h2) fun t₂ hI => ?_)
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0 ∧ t.mem = t₂.mem) (by brun) (by decide) (by decide)
    (by decide +kernel)) fun t ⟨⟨hx, hm⟩, k₃⟩ => ⟨?_, hx, fun x hx' => ?_, ((k₁.trans hI.keep).trans k₃).mono
      (by decide)⟩
  · rw [bytesAt_eq, List.eq_replicate_iff]
    refine ⟨by simp, fun x hx => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hm]
    exact hI.bytes i (List.mem_range.mp hi)
  · rw [hm, hI.frame x hx', hm₁]

end VG.Proof.Bignum.AArch64
