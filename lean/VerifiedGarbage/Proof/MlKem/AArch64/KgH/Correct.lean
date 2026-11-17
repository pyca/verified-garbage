module

public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16P
import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Prefix
public import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Pair
public import VerifiedGarbage.Proof.Sha3.AArch64.Variant
import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Tail
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Permute
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenPrefix
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
public import VerifiedGarbage.Proof.MlKem.AArch64.KgCommon

/-! ### `MlKem.AArch64.KgH.Matrix`, which this module and modules that import it used -/

section

/-! # The matrix with the rows of `t̂` between its pairs

`matrixRows_ok`: `Kem16P.kgMatrixRows`, from the interleaved invariant with
the first two pairs done (`Kem16P.kgPairP`, which absorb nothing,
`rowsBy_two`) to the whole matrix, every row and the blocks `hashedBy (k² / 2)`
of `ek`. Pair `p` starts after `2 p` entries, `rowsBy p` rows and
`hashedBy p` blocks; it absorbs only blocks the rows before it encoded
(`hashed_le`), and the rows after it use only entries it or its predecessors
sampled. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen
variable {sha3 : Bool}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64.Kem16 (rowsBy hashedBy kgRows kgPair)

variable {P : KemLay}

theorem rowsBy_mono (P : KemLay) (p : Nat) : rowsBy P p ≤ rowsBy P (p + 1) := by
  simp only [rowsBy]
  have := Nat.div_le_div_right (c := P.k) (show 2 * p ≤ 2 * (p + 1) by omega_using [])
  omega_using [this]

/-- The first `rowsBy p` rows use only the first `2 p` entries. -/
theorem rowsBy_mul (P : KemLay) (p : Nat) : P.k * rowsBy P p ≤ 2 * p := by
  simp only [rowsBy]
  exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.min_le_right _ _)) (Nat.mul_div_le _ _)

theorem rowsBy_le (P : KemLay) (p : Nat) : rowsBy P p ≤ P.k := Nat.min_le_left _ _

/-- The blocks absorbed before pair `p` are among those the rows before it encoded. -/
theorem hashed_le (P : KemLay) : ∀ p, 136 * hashedBy P p ≤ 384 * rowsBy P p
  | 0 => by simp [hashedBy]
  | p + 1 => by
    have ih := hashed_le P p
    have hm := rowsBy_mono P p
    have hA : hashedBy P p ≤ 384 * rowsBy P p / 136 := (Nat.le_div_iff_mul_le (by decide)).2 (by omega_using [ih])
    have hB : 136 * (384 * rowsBy P p / 136) ≤ 384 * rowsBy P p := Nat.mul_div_le _ _
    simp only [hashedBy]
    have := Nat.min_le_right 3 (384 * rowsBy P p / 136 - hashedBy P p)
    omega_using [ih, hm]

theorem hashed_succ (P : KemLay) (p : Nat) :
    hashedBy P (p + 1) = hashedBy P p + (hashedBy P (p + 1) - hashedBy P p) := by
  simp only [hashedBy]; omega_using []

/-- `n` steps, each a list of programs, by an invariant `I i` before step `i`. -/
theorem wps_flatMap_range {f : Nat → List (Prog isa)} {I : Nat → State → Prop} :
    ∀ {n : Nat}, (∀ i < n, ∀ s, I i s → WPs (f i) s (I (i + 1))) →
      ∀ {s : State}, I 0 s → WPs ((List.range n).flatMap f) s (I n)
  | 0, _, _, h => h
  | n + 1, hf, _, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WPs.append (WPs.mono (wps_flatMap_range (fun i hi => hf i (by omega_using [hi])) h)
      fun s' h' => hf n (by omega_using []) s' h')

/-- Rows `a` to `a + d - 1` of `t̂`, once the matrix holds their entries. -/
theorem rows_ok {s₀ : State} (hp : Pre P s₀) (hr : Noise.Room P) {n h : Nat} :
    ∀ (d a : Nat), a + d ≤ P.k → P.k * (a + d) ≤ n → ∀ {s : State}, IL P s₀ n a h s →
      WPs (kgRows P a (a + d)) s (IL P s₀ n (a + d) h)
  | 0, a, _, _, _, H => by
    simp only [kgRows, Nat.add_zero, Nat.sub_self, List.range'_zero, List.map_nil, WPs]
    exact H
  | d + 1, a, hd, hn, s, H => by
    have e : kgRows P a (a + (d + 1)) = Kem16.kgRow P a :: kgRows P (a + 1) (a + 1 + d) := by
      simp only [kgRows, show a + (d + 1) - a = d + 1 by omega_using [], show a + 1 + d - (a + 1) = d by omega_using [],
        List.range'_succ, List.map_cons]
    rw [e]
    refine WPs.cons (WP.mono (row_step hp hr (by omega_using [hd])
      (Nat.le_trans (Nat.mul_le_mul_left _ (by omega_using [])) hn) H) fun t ht => ?_)
    have e2 : a + 1 + d = a + (d + 1) := by omega_using []
    have r := rows_ok hp hr d (a + 1) (by omega_using [hd]) (by rw [e2]; exact hn) ht
    exact WPs.mono r fun u hu => by rwa [e2] at hu

/-- Pair `p` of the matrix and the rows of `t̂` it completes. -/
theorem pairRows_ok {s₀ : State} (hp : Pre P s₀) (hk : Stk128K P s₀) (hr : Noise.Room P) {p : Nat}
    (hp' : p < P.k * P.k / 2) {s : State} (Hs : IL P s₀ (2 * p) (rowsBy P p) (hashedBy P p) s) :
    WPs (kgPair sha3 P p :: kgRows P (rowsBy P p) (rowsBy P (p + 1))) s
      (IL P s₀ (2 * (p + 1)) (rowsBy P (p + 1)) (hashedBy P (p + 1))) := by
  have hw := hp.wf
  have hf := hw.facts
  have hek : 384 * P.k < P.ekLen := by simp only [KemLay.ekLen]; omega_using []
  have hmono := rowsBy_mono P p
  have hle := rowsBy_le P (p + 1)
  have h2 := hashed_le P (p + 1)
  have hrk := rowsBy_le P p
  refine WPs.cons (WP.mono (pair_step (sha3 := sha3) hp hk hr (p := p) (r := rowsBy P p) (h := hashedBy P p)
    (m := hashedBy P (p + 1) - hashedBy P p) (by omega_using [hp'])
    (by simp only [hashedBy]; omega_using []) (fun k hk' => ?_) ?_ Hs) fun t ht => ?_)
  · have := Nat.mul_le_mul_left 384 hrk
    have h3 := hashed_le P (p + 1)
    simp only [hashedBy] at h3 hk' ⊢
    have : 136 * (384 * rowsBy P p / 136) ≤ 384 * rowsBy P p := Nat.mul_div_le _ _
    omega_using [hek, hmono, hle, hk']
  · rw [← hashed_succ]
    have hA : hashedBy P p ≤ 384 * rowsBy P p / 136 :=
      (Nat.le_div_iff_mul_le (by decide)).2 (by have := hashed_le P p; omega_using [this])
    have hB : 136 * (384 * rowsBy P p / 136) ≤ 384 * rowsBy P p := Nat.mul_div_le _ _
    simp only [hashedBy]
    have := Nat.min_le_right 3 (384 * rowsBy P p / 136 - hashedBy P p)
    omega_using [hA]
  · rw [← hashed_succ] at ht
    have r := rows_ok hp hr (n := 2 * p + 2) (rowsBy P (p + 1) - rowsBy P p) (rowsBy P p) (by omega_using [hmono, hle])
      (by rw [Nat.add_sub_cancel' hmono]; exact Nat.le_trans (rowsBy_mul P (p + 1)) (by omega_using [])) ht
    rw [Nat.add_sub_cancel' hmono] at r
    exact r

/-- No row is complete, and no block of `ek` absorbed, before the third pair. -/
theorem rowsBy_two (hk3 : 3 ≤ P.k) : rowsBy P 1 = 0 ∧ hashedBy P 2 = 0 := by
  have r1 : rowsBy P 1 = 0 := by
    simp only [rowsBy, Nat.mul_one, Nat.div_eq_of_lt (show 2 < P.k by omega_using [hk3]), Nat.min_zero]
  refine ⟨r1, ?_⟩
  simp only [hashedBy, r1, show rowsBy P 0 = 0 by simp [rowsBy]]
  rfl

/-- **The matrix after its first two pairs, and the rows of `t̂`.** -/
theorem matrixRows_ok {s₀ s : State} (hp : Pre P s₀) (hk : Stk128K P s₀) (hr : Noise.Room P)
    (hk3 : 3 ≤ P.k) (H : IL P s₀ 4 0 0 s) :
    WPs (Impl.MlKem.AArch64.Kem16P.kgMatrixRows sha3 P) s
      (IL P s₀ (P.k * P.k) P.k (hashedBy P (P.k * P.k / 2))) := by
  have hw := hp.wf
  have hf := hw.facts
  have hkk := Nat.mul_le_mul hk3 hk3
  have h2 := (rowsBy_two (P := P) hk3).2
  have first := rows_ok hp hr (n := 4) (h := 0) (rowsBy P 2) 0 (by have := rowsBy_le P 2; omega_using [this])
    (by rw [Nat.zero_add]; exact rowsBy_mul P 2) H
  rw [Nat.zero_add] at first
  unfold Impl.MlKem.AArch64.Kem16P.kgMatrixRows Impl.MlKem.AArch64.Kem16P.pairs
    Impl.MlKem.AArch64.Kem16P.single
  refine WPs.append (WPs.append (WPs.mono first fun t ht => WPs.mono (wps_flatMap_range (n := P.k * P.k / 2 - 2)
    (I := fun q s => IL P s₀ (2 * (q + 2)) (rowsBy P (q + 2)) (hashedBy P (q + 2)) s)
    (f := fun q => kgPair sha3 P (q + 2) :: kgRows P (rowsBy P (q + 2)) (rowsBy P (q + 3)))
    (fun q hq s Hs => pairRows_ok hp hk hr (p := q + 2) (by omega_using [hq]) Hs)
    (show IL P s₀ 4 (rowsBy P 2) (hashedBy P 2) t by rw [h2]; exact ht)) fun u hu => ?_))
  have e2 : P.k * P.k / 2 - 2 + 2 = P.k * P.k / 2 := by omega_using [hkk]
  rw [e2] at hu
  have hle := rowsBy_le P (P.k * P.k / 2)
  by_cases ho : P.k * P.k % 2 = 1
  · rw [show decide (P.k * P.k % 2 = 1) = true from decide_eq_true ho, ite_eq_left rfl]
    have e : 2 * (P.k * P.k / 2) = P.k * P.k - 1 := by omega_using [ho]
    rw [e] at hu
    refine WPs.cons (WP.mono (last_step (sha3 := sha3) hp hr ho hu) fun v hv => ?_)
    have r := rows_ok hp hr (n := P.k * P.k) (P.k - rowsBy P (P.k * P.k / 2)) (rowsBy P (P.k * P.k / 2))
      (by omega_using [hle]) (by rw [Nat.add_sub_cancel' hle]) hv
    rwa [Nat.add_sub_cancel' hle] at r
  · rw [show decide (P.k * P.k % 2 = 1) = false from decide_eq_false ho, ite_eq_right Bool.false_ne_true]
    have e : 2 * (P.k * P.k / 2) = P.k * P.k := by omega_using [ho]
    have er : rowsBy P (P.k * P.k / 2) = P.k := by
      simp only [rowsBy, e, Nat.mul_div_cancel_left _ (show 0 < P.k by omega_using [hk3]), Nat.min_self]
    rw [e, er] at hu
    exact hu

end VG.Proof.MlKem.AArch64.KeyGen

end

end

/-! ### `MlKem.AArch64.KgH.Tail`, which only this module used -/

section

/-! # The tail of the key generation hashing `ek` during the matrix

`tail_ok`: once every row of `t̂` is encoded and the third state has absorbed
the first `h` blocks of `ek`, `Kem16.kgTail`: `ρ` into both keys, each further
block of `ek` absorbed and permuted by `v`'s single-state permutation
(`block_step`), `H(ek)`, the first 32 bytes of the third state, and `z` into
`dk`, and the epilogue. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen
variable {sha3 : Bool}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt keccakF)
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Proof.MlKem.AArch64.Hybrid (hstate)

variable {P : KemLay}

/-- `ek`, encoded. -/
abbrev ekK (P : KemLay) (s₀ : State) (mB : Mem) : List Byte := KPke.ekPKE P.params (aMW P s₀ mB) (dB s₀)

/-- After `ρ` and `b` blocks of `ek` in the third state. -/
structure TT (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (b : Nat) (s : State) : Prop where
  kb : KB P s₀ s
  e : EndInvW P s₀ mB v (P.k * P.k) s
  hash : stateAt s.mem (kA s₀ 3) = hstate (ekK P s₀ mB) b (Hybrid.dB (Kem16.kgSrc P))

theorem TT.ek {s₀ s : State} {mB : Mem} {v : BitVec 64} {b : Nat} (h : TT P s₀ mB v b s) :
    bytesAt s.mem (kA s₀ 1) P.ekLen = ekK P s₀ mB :=
  ek_at (T := tVW P s₀ mB) (ρ := rhoK P s₀) (fun i hi => (h.e.tl.ek i hi).1) h.e.rek

/-- The third state and the permutation's working space. -/
theorem st_wk_far {s₀ : State} (hp : Pre P s₀) {o l : Nat} (f : o + l ≤ 840) :
    Far P s₀ (R (kA s₀) 3 o l) := by
  have hw := hp.wf
  exact far_R hp (by decide) (by simp only [kL]; lom) (fun _ => .inl f) (by decide) (fun h => absurd h (by decide))

/-- **One more block of `ek`**, absorbed and permuted. -/
theorem block_step (v : Proof.Sha3.AArch64.Permutation) {s₀ s : State} (hp : Pre P s₀)
    {mB : Mem} {vv : BitVec 64} {b : Nat} (hb : 136 * b < P.ekLen) (H : TT P s₀ mB vv b s) :
    WP isa (.seq (.block (Hybrid.absorbBlock (Kem16.kgSrc P) b)) (Kem16.kgPerm v.callee)) s
      (TT P s₀ mB vv (b + 1)) := by
  have hw := hp.wf
  obtain hsv : 200 ≤ SV P := by lom
  have kb := H.kb
  obtain ek : (⟨kA s₀ 1, (Kem16.kgSrc P).len⟩ : Region) = R (kA s₀) 1 0 (kL P 1) := ekR s₀
  obtain fS : 0 + 200 ≤ kL P 3 := by
    show 0 + 200 ≤ P.scl; omega_using [hw.facts.2.2.2.2.2.2.2.2.1]
  obtain fE : 0 + kL P 1 ≤ kL P 1 := by omega_using []
  refine WP.seq (WP.mono (Hybrid.absorbBlock_ok (Kem16.kgSrc P) (srcOkK hw)
    (by show s.gpr .x26 + BitVec.ofNat 64 0 = kA s₀ 1; rw [kb.x26, ptr_zero]) kb.x28 hb H.ek H.hash
    (by rw [ek]; exact cov_r hp kb (b := 1) (o := 0) (l := kL P 1) (by decide) fE)
    (by rw [stR_scratch]; exact cov_w hp kb (b := 3) (o := 0) (l := 200) (by decide) fS)
    (by rw [stR_scratch, ek]
        exact hp.args.rdisj (b₁ := 3) (o₁ := 0) (l₁ := 200) (b₂ := 1) (o₂ := 0) (l₂ := kL P 1)
          (by decide) (by decide) fS fE (.inl (by decide)))) fun t ⟨kt, ft, st⟩ => ?_)
  rw [stR_scratch] at ft
  obtain kbt := kb.frame kt ft (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨(st_far hp (b := 3) (o := SV P) (l := 48) (by decide) hp.sv (.inr hsv)),
      (st_far hp (by decide) (by kl) (.inl (by decide)))⟩
  obtain et := H.e.frame hp kbt (kt.get .x24) ft fun r hr => by
    rw [List.mem_singleton.mp hr]; exact st_wk_far hp (by decide)
  refine WP.mono (FixedHash.permute_ok v (hsetup hp kbt (rate := 136) (by decide))
    ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩) fun w ⟨kw, sw⟩ => ?_
  obtain e3 : STr .x28 KG.ST t = R (kA s₀) 3 0 200 := by simp only [STr, R, kbt.x28, KG.ST]
  obtain e4 : (⟨t.gpr .x28 + BitVec.ofNat 64 KG.WK, 512⟩ : Region) = R (kA s₀) 3 KG.WK 512 := by
    simp only [R, kbt.x28]
  rw [e3, e4] at kw
  obtain far : ∀ r ∈ [R (kA s₀) 3 0 200, R (kA s₀) 3 KG.WK 512], Far P s₀ r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact st_wk_far hp (by decide)
    · exact st_wk_far hp (by decide)
  obtain kbw := kbt.call kw fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨(st_far hp (b := 3) (o := SV P) (l := 48) (by decide) hp.sv (.inr hsv)),
        (st_far hp (by decide) (by kl) (.inl (by decide)))⟩
    · exact ⟨hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (.inr (.inr (by lom))),
        hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (.inl (by decide))⟩
  refine ⟨kbw, et.frame hp kbw (kw.cs .x24 (by decide) (by decide)) kw.frame far, ?_⟩
  rw [kbt.x28, show KG.ST = 0 from rfl, ptr_zero] at sw
  rw [sw, ← st]

/-- Blocks `b` to `b + d - 1` of `ek`. -/
theorem blocks_ok (v : Proof.Sha3.AArch64.Permutation) {s₀ : State} (hp : Pre P s₀) {mB : Mem}
    {vv : BitVec 64} : ∀ (d b : Nat), b + d ≤ Hybrid.blocks (Kem16.kgSrc P) → ∀ {s : State},
      TT P s₀ mB vv b s →
      WPs ((List.range' b d).map fun b => .seq (.block (Hybrid.absorbBlock (Kem16.kgSrc P) b))
        (Kem16.kgPerm v.callee)) s (TT P s₀ mB vv (b + d))
  | 0, b, _, s, H => by simpa only [List.range'_zero, List.map_nil, WPs, Nat.add_zero] using H
  | d + 1, b, hd, s, H => by
    have hw := hp.wf
    have hf := hw.facts
    obtain hb : 136 * b < P.ekLen := by
      simp only [Hybrid.blocks, Kem16.kgSrc, KemLay.ekLen] at hd ⊢
      have := Nat.lt_succ_iff.mp (show b < (384 * P.k + 32) / 136 + 1 by omega_using [hd])
      have := (Nat.le_div_iff_mul_le (by decide)).1 this
      omega_using [hd, hf]
    rw [List.range'_succ, List.map_cons]
    refine WPs.cons (WP.mono (block_step v hp hb H) fun t ht => ?_)
    obtain r := blocks_ok v hp d (b + 1) (by omega_using [hd]) ht
    rwa [show b + 1 + d = b + (d + 1) by omega_using []] at r

/-- `H(ek)` and `z` into `dk`, and the epilogue. -/
theorem final_ok {s₀ s : State} (hp : Pre P s₀) {mB : Mem} {vv : BitVec 64}
    (HT : TT P s₀ mB vv (Hybrid.blocks (Kem16.kgSrc P)) s) :
    WP isa (.block (copy32 .x28 KG.ST .x27 (768 * P.k + 32) ++ copy32 .x25 32 .x27 (768 * P.k + 64) ++
      [mov .x0 .x24, .ldr .x .x30 .x28 (KG.SV P + 40), .ldr .x .x24 .x28 (KG.SV P),
        .ldr .x .x25 .x28 (KG.SV P + 8), .ldr .x .x26 .x28 (KG.SV P + 16),
        .ldr .x .x27 .x28 (KG.SV P + 24), .ldr .x .x28 .x28 (KG.SV P + 32)])) s (DoneW P s₀ mB vv) := by
  have hw := hp.wf
  have kb := HT.kb
  obtain hfull : stateAt s.mem (kA s₀ 3) = Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 (BitVec.ofNat 8 6) (ekK P s₀ mB)) := by
    rw [HT.hash]
    apply Hybrid.hstate_done
    rw [← HT.ek, VG.Proof.MlKem.bytesAt_length]
    simp only [Hybrid.blocks, Kem16.kgSrc]
    omega_using []
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copy_ok (S := kA s₀ 3) (D := kA s₀ 2) (so := KG.ST) (dO := 768 * P.k + 32) (by decide) (by decide)
    (by decide) (by lom) (hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl))
    kb.x28 kb.x27 (cov_r hp kb (b := 3) (by decide) (by kl))
    (cov_w hp kb (b := 2) (by decide) (by kl))) fun s₂ ⟨k₂, f₂, b₂⟩ => ?_
  obtain kb₂ := kb.frame k₂ f₂ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact kb_disj hp (b := 2) (o := 768 * P.k + 32) (l := 32) (by decide) (by kl) (.inl (by decide)) (by decide)
  obtain h₂ := HT.e.frame hp kb₂ (k₂.get .x24) f₂ fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact far_R hp (by decide) (by kl) (by kl) (by decide) (by kl)
  obtain hh₂ : bytesAt s₂.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k + 32)) 32 = H (ekK P s₀ mB) := by
    rw [b₂, show KG.ST = 0 from rfl, ptr_zero, H_eq, Hybrid.bytesAt_squeeze, hfull]; rfl
  refine WP.mono (copy_ok (S := kA s₀ 0) (D := kA s₀ 2) (so := 32) (dO := 768 * P.k + 64) (by decide) (by decide)
    (by decide) (by lom) (hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl))
    kb₂.x25 kb₂.x27 (cov_r hp kb₂ (b := 0) (by decide) (by kl))
    (cov_w hp kb₂ (b := 2) (by decide) (by kl))) fun s₃ ⟨k₃, f₃, b₃⟩ => ?_
  obtain kb₃ := kb₂.frame k₃ f₃ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact kb_disj hp (b := 2) (o := 768 * P.k + 64) (l := 32) (by decide) (by kl) (.inl (by decide)) (by decide)
  obtain far₃ : ∀ r ∈ [R (kA s₀) 2 (768 * P.k + 64) 32], Far P s₀ r := fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact far_R hp (by decide) (by kl) (by kl) (by decide) (by kl)
  obtain h₃ := h₂.frame hp kb₃ (k₃.get .x24) f₃ far₃
  obtain hh₃ : bytesAt s₃.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k + 32)) 32 = H (ekK P s₀ mB) := by
    rw [bytesAt_frame f₃ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (by kl)) (by decide)]
    exact hh₂
  obtain z₃ : bytesAt s₃.mem (kA s₀ 2 + BitVec.ofNat 64 (768 * P.k + 64)) 32 = zB s₀ := by rw [b₃]; exact kb₂.z
  obtain ek₃ : bytesAt s₃.mem (kA s₀ 1) P.ekLen = ekK P s₀ mB :=
    ek_at (T := tVW P s₀ mB) (ρ := rhoK P s₀) (fun i hi => (h₃.tl.ek i hi).1) h₃.rek
  obtain dk₃ : bytesAt s₃.mem (kA s₀ 2) P.dkLen = KPke.dkPKE P.params (dB s₀) ++
      ekK P s₀ mB ++ H (ekK P s₀ mB) ++ zB s₀ :=
    dk_at (cat_at (T := KPke.kgS P.params (dB s₀)) fun j hj => h₃.tl.dk j hj)
      (ek_at (T := tVW P s₀ mB) (ρ := rhoK P s₀) (fun i hi => by rw [ptr_add]; exact (h₃.tl.ek i hi).2)
        (by rw [ptr_add, show 384 * P.k + 384 * P.k = 768 * P.k by omega_using []]; exact h₃.rdk)) hh₃ z₃
  refine WP.mono (restore_ok hp kb₃) fun s' ⟨abi, x0, hm⟩ => ⟨abi, by rw [x0, h₃.tl.c.x24], ?_, ?_⟩
  · rw [hm]; exact ek₃
  · rw [hm]; exact dk₃

/-- **The tail**, once every row is encoded and the matrix has absorbed its blocks of `ek`. -/
theorem tail_ok (v : Proof.Sha3.AArch64.Permutation) {s₀ s : State} (hp : Pre P s₀)
    (H : IL P s₀ (P.k * P.k) P.k (Kem16.hashedBy P (P.k * P.k / 2)) s) :
    WP isa (Kem16.kgTail v.callee P) s (DoneW P s₀ s.mem (s.gpr .x24)) := by
  have hw := hp.wf
  have hf := hw.facts
  have kb := H.b.kb
  have hh := H.hr
  obtain hle : 136 * Kem16.hashedBy P (P.k * P.k / 2) ≤ P.ekLen := by
    simp only [KemLay.ekLen]; omega_using [hh]
  obtain tl : TLW P s₀ s.mem (s.gpr .x24) (P.k * P.k) P.k s :=
    ⟨⟨kb, H.b.rho, H.b.sig, rfl, Nat.le_refl _, fun e he => ⟨H.b.red e he, rfl⟩⟩, H.sp, H.dk, H.rows⟩
  unfold Kem16.kgTail
  refine WPs.seqs (by simp) (WPs.append (WPs.append ?_))
  refine WPs.cons (WP.mono (rho_okW hp tl) fun s₁ ⟨kb₁, e₁, f₁⟩ => ?_)
  simp only [WPs]
  obtain ek₁ : bytesAt s₁.mem (kA s₀ 1) P.ekLen = ekK P s₀ s.mem :=
    ek_at (T := tVW P s₀ s.mem) (ρ := rhoK P s₀) (fun i hi => (e₁.tl.ek i hi).1) e₁.rek
  obtain hs₁ : stateAt s₁.mem (kA s₀ 3) = hstate (ekK P s₀ s.mem) (Kem16.hashedBy P (P.k * P.k / 2))
      (Hybrid.dB (Kem16.kgSrc P)) := by
    rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame f₁ (fun r hr => by
      rw [stR_scratch]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (st_far hp (by decide) (by kl) (.inl (by decide))).symm
      · exact (st_far hp (by decide) (by kl) (.inl (by decide))).symm), H.hash, ← ek₁]
    refine hstate_prefix hle ?_
    obtain e1 : kA s₀ 1 = kA s₀ 1 + BitVec.ofNat 64 0 := (ptr_zero _).symm
    rw [e1, bytesAt_frame f₁ (fun q hq => ?_) (by have := kL_le hw 1; simp only [kL] at this; omega_using [hf, hh])]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hp.args.rdisj (b₁ := 1) (o₁ := 0) (l₁ := 136 * Kem16.hashedBy P (P.k * P.k / 2)) (by decide) (by decide)
        (by simp only [kL]; omega_using [hle]) (by kl) (.inr (.inl (by omega_using [hh])))
    · exact hp.args.rdisj (b₁ := 1) (o₁ := 0) (by decide) (by decide) (by simp only [kL]; omega_using [hle]) (by kl)
        (.inl (by decide))
  obtain hb : Kem16.hashedBy P (P.k * P.k / 2) ≤ Hybrid.blocks (Kem16.kgSrc P) := by
    simp only [Hybrid.blocks, Kem16.kgSrc]
    have := (Nat.le_div_iff_mul_le (k := 136) (by decide)).2
      (show Kem16.hashedBy P (P.k * P.k / 2) * 136 ≤ P.ekLen by omega_using [hle])
    omega_using [hle]
  obtain r := blocks_ok v hp (Hybrid.blocks (Kem16.kgSrc P) - Kem16.hashedBy P (P.k * P.k / 2))
    (Kem16.hashedBy P (P.k * P.k / 2)) (by omega_using [hb]) (s := s₁) ⟨kb₁, e₁, hs₁⟩
  rw [Nat.add_sub_cancel' hb] at r
  exact WPs.mono r fun u hu => WPs.single (final_ok hp hu)

end VG.Proof.MlKem.AArch64.KeyGen

end

end


/-! # The key generation hashing `ek` during the matrix is correct

`using_correctP`: `G` (`a_using_ok`), the first two pairs of the matrix
computing the first PRF outputs (`first_step`), the noise, `ŝ` and the
all-zero third state (`pre_ok`), the rest of the matrix with the rows of `t̂`
between its pairs (`matrixRows_ok`), and the tail (`tail_ok`). -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen
variable {sha3 : Bool}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem.AArch64.Hybrid (TStk)

variable {P : KemLay}

theorem matrixRows_ne_nil (P : KemLay) (hk3 : 3 ≤ P.k) : Impl.MlKem.AArch64.Kem16P.kgMatrixRows sha3 P ≠ [] := by
  intro h
  unfold Impl.MlKem.AArch64.Kem16P.kgMatrixRows Impl.MlKem.AArch64.Kem16P.pairs at h
  obtain h2 := (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).2
  obtain hp : 0 < P.k * P.k / 2 - 2 := by
    have := Nat.mul_le_mul hk3 hk3
    omega_using [this]
  exact List.cons_ne_nil _ _ (List.flatMap_eq_nil_iff.mp h2 0 (List.mem_range.mpr hp))

/-- **The key generation computing the first PRF outputs in the matrix is correct.** -/
theorem using_correctP (v : Proof.Sha3.AArch64.Permutation) (hash : FixedHash.HashFn)
    (hG : FixedHash.HashCorrect hash .x28 ST WK 72 6
      [⟨.x25,0,32⟩,⟨.x28,BK,1⟩] [⟨.x28,SB,32⟩,⟨.x28,SG,32⟩])
    {s₀ : State} (hp : Pre P s₀) (hk : Stk128K P s₀) (hr : Noise.Room P) (hk3 : 3 ≤ P.k) (tables : Tables s₀)
    (ts : TStk s₀) (depthA : (FixedHashCallers.kgAUsing hash P).aarch64Depth ≤ 1)
    (depthP : (Impl.MlKem.AArch64.Kem16P.kgPre sha3 P).aarch64Depth ≤ 1) :
    WP isa (Impl.MlKem.AArch64.Kem16P.keyGen sha3 hash v.callee P) s₀ fun t =>
      abiPreserved s₀ t ∧ (keyGenAArch64 P).post s₀ t := by
  unfold Impl.MlKem.AArch64.Kem16P.keyGen
  refine WPs.seqs (by simp) ?_
  refine WPs.cons (WP.mono_syms (WP.tablesDepth (a_using_ok hash hG hp) tables depthA) fun sA ⟨hA, ta⟩ hs => ?_)
  refine WPs.cons (WP.mono (first_step (sha3 := sha3) hp hk (p := 0) (by decide) hk3
    (FInv.zero hA ta (ts.of hs hA.kb.sp))) fun s₁ h₁ => ?_)
  refine WPs.cons (WP.mono (first_step (sha3 := sha3) hp hk (p := 1) (by decide) hk3 h₁) fun s₂ h₂ => ?_)
  refine WPs.cons (WP.mono (pre_ok (sha3 := sha3) hp hr hk3 h₂ depthP) fun s₃ h₃ => ?_)
  refine WPs.cons (WP.mono (WPs.seqs (matrixRows_ne_nil (sha3 := sha3) P hk3) (matrixRows_ok (sha3 := sha3) hp hk hr hk3 h₃))
    fun s₄ h₄ => ?_)
  exact WPs.single (WP.mono (tail_ok v hp h₄) fun t ht => ⟨ht.abi, post_ofW h₄.b ht⟩)

end VG.Proof.MlKem.AArch64.KeyGen
