module

public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Candidate
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A candidate on PPC64LE: the working space's header and arrays

`setup_ok`: `scratch_len` (`SL` words, in `r11`) into header word 0, `w =
out_len / 8` into word 6, the arrays' stride `8 (w + 2)` into word 28 and
`r29`, array 0's address into `r10`, `2 w` into `r11`, the first eight
arrays' addresses into words 8–15 (`Lay`), and the first `nArr` arrays
zeroed: `Env` holds.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (setup nArr)
open VG.Impl.MillerRabin.PPC64LE.Search (ldh sth hWsLen hW hStride)
open VG.Impl.Bignum.PPC64LE.PublicChecked (base)
open VG.Proof.MillerRabin.PPC64LE (Env)
open VG.Proof.Bignum (slot)

/-- The header words of the layout. -/
structure Lay (m : Mem) (B : Addr) (SL w : Nat) : Prop where
  len : word m B 0 = BitVec.ofNat 64 SL
  wW : word m B 48 = BitVec.ofNat 64 w
  strideW : word m B 224 = BitVec.ofNat 64 (8 * (w + 2))
  arrW : ∀ j < 8, word m B (8 * (8 + j)) = off B (slot w j)

/-- What changes through `setup`: the header's first 29 words and the arrays. -/
def setupRanges (w : Nat) : List (Nat × Nat) := [(0, 232), (256, nArr * (8 * (w + 2)))]

/-- The arrays' addresses into header words 8 to `8 + k`. -/
theorem hdrs_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (h31 : s.gpr .r31 = B)
    (h10 : s.gpr .r10 = off B (slot w 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (hZ : 128 ≤ Z) :
    ∀ k ≤ 8, WP isa (.block ((List.range k).flatMap (fun j => base .r3 j ++ [sth .r3 (8 + j)]))) s fun t =>
      ((∀ j < k, word t.mem B (8 * (8 + j)) = off B (slot w j)) ∧ Outside B 64 (8 * k) s.mem t.mem) ∧
        Keep [.r3] s t
  | 0, _ => WP.block_nil ⟨⟨fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _⟩, Keep.refl _ _⟩
  | k + 1, hk => by
    have hnw := hs.nowrap
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (hdrs_ok hs h31 h10 h29 hZ k (by omega)) fun t ⟨⟨tw, tout⟩, tk⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [WP.block_append_iff]
    refine WP.mono (Pub.base_ok (rd := .r3) (by decide) (by decide) ((tk.gpr _ (by decide)).trans h10)
      ((tk.gpr _ (by decide)).trans h29) k) fun u ⟨⟨u3, um⟩, uk⟩ => ?_
    have hs' := hs.congr (uk.wr.trans tk.wr)
    have h31' : u.gpr .r31 = B := (uk.gpr _ (by decide)).trans ((tk.gpr _ (by decide)).trans h31)
    have hst := hs'.st (d := 8 * (8 + k)) (n := 8) (by omega)
    rw [← h31'] at hst
    refine WP.mono (WP.keep [] (Q := fun v => v.mem = u.mem.writeW (off B (8 * (8 + k))) (off B (slot w k)))
      (by simp only [sth]; prun [exec_store_d (show Reg.r31 ≠ .r0 by decide) ⟨by omega, by omega⟩ hst, h31', u3])
      rfl rfl)
      fun v ⟨vm, vk⟩ => ⟨⟨fun j hj => ?_, ?_⟩, ((tk.trans uk).trans vk).mono⟩
    · rw [vm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [(writeW_outside u.mem B (d := 8 * (8 + k)) _ (by omega)).word (by omega) (by omega), um]
        exact tw j hj
      · exact word_writeW_self _ _ _ _
    · rw [vm, um]
      exact (tout.mono (Nat.le_refl _) (by omega)).trans
        ((writeW_outside t.mem B (d := 8 * (8 + k)) _ (by omega)).mono (by omega) (by omega))

theorem setup_ok {s : State} {B : Addr} {SL w : Nat} (hs : Scr s B (8 * SL)) (h31 : s.gpr .r31 = B)
    (h11 : s.gpr .r11 = BitVec.ofNat 64 SL) (h24 : s.gpr .r24 = BitVec.ofNat 64 (8 * w)) (hw : 4 ≤ w)
    (hw' : w ≤ 64) (hZ : slot w nArr ≤ 8 * SL) :
    WP isa setup s fun t =>
      (Env t B (8 * SL) w ∧ Lay t.mem B SL w ∧ (∀ i < nArr * (w + 2), word t.mem B (256 + 8 * i) = 0) ∧
        Outs B (setupRanges w) s.mem t.mem) ∧
        Keep [.r0, .r3, .r10, .r11, .r14, .r17, .r29] s t := by
  have hnw := hs.nowrap
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hZ' : 256 + 35 * (8 * (w + 2)) ≤ 8 * SL := by rw [← es]; exact hZ
  unfold setup
  rw [WP.seq_iff, WP.block_append_iff, WP.block_append_iff]
  -- The header's lengths and stride.
  have hA : WP isa (.block [sth .r11 hWsLen, .lsr .d .r3 .r24 3, sth .r3 hW, .addi .r29 .r3 2,
      .lsl .r29 .r29 3, sth .r29 hStride, .addi .r10 .r31 VG.Impl.Bignum.hdrBytes, .lsl .r11 .r3 1]) s fun t =>
      (t.mem = ((s.mem.writeW (off B 0) (BitVec.ofNat 64 SL)).writeW (off B 48) (BitVec.ofNat 64 w)).writeW
          (off B 224) (BitVec.ofNat 64 (8 * (w + 2))) ∧ t.gpr .r10 = off B (slot w 0) ∧
        t.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * w) ∧ t.gpr .r31 = B) ∧
        Keep [.r3, .r10, .r11, .r29] s t := by
    refine WP.keep _ ?_ (by decide)
    have e3 : BitVec.ofNat 64 (8 * w) >>> 3 = BitVec.ofNat 64 w := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      omega
    have e29 : (BitVec.ofNat 64 w + BitVec.ofNat 64 2) <<< 3 = BitVec.ofNat 64 (8 * (w + 2)) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftLeft_eq]
      omega
    have e11 : BitVec.ofNat 64 w <<< 1 = BitVec.ofNat 64 (2 * w) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega
    have s0 := hs.st (d := 0) (n := 8) (by omega)
    have s48 := hs.st (d := 48) (n := 8) (by omega)
    have s224 := hs.st (d := 224) (n := 8) (by omega)
    simp only [sth, hWsLen, hW, hStride, VG.Impl.Bignum.hdrBytes]
    prun [h31, h11, h24, e3, e29, e11, s0, s48, s224]
    rw [es, Nat.zero_mul, Nat.add_zero]
  refine WP.mono hA fun t₁ ⟨⟨m₁, a10, a29, a11, a31⟩, k₁⟩ => ?_
  have hs₁ := hs.congr k₁.wr
  refine WP.mono (hdrs_ok hs₁ a31 a10 a29 (by omega) 8 (Nat.le_refl _)) fun t₂ ⟨⟨hw₂, out₂⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.wr
  have b10 : t₂.gpr .r10 = off B (slot w 0) := (k₂.gpr _ (by decide)).trans a10
  have b29 : t₂.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) := (k₂.gpr _ (by decide)).trans a29
  have hC : WP isa (.block [.addi .r14 .r10 0, .li .r17 nArr, .mul .r17 .r17 .r29, .lsr .d .r17 .r17 3, .li .r0 0])
      t₂ fun t =>
      (t.mem = t₂.mem ∧ t.gpr .r14 = off B 256 ∧ t.gpr .r17 = BitVec.ofNat 64 (35 * (w + 2)) ∧ t.gpr .r0 = 0) ∧
        Keep [.r0, .r14, .r17] t₂ t := by
    refine WP.keep _ ?_ (by decide)
    have e17 : (BitVec.ofNat 64 35 * BitVec.ofNat 64 (8 * (w + 2))) >>> 3 = BitVec.ofNat 64 (35 * (w + 2)) := by
      apply BitVec.eq_of_toNat_eq
      have h1 : 8 * (w + 2) < 2 ^ 64 := by omega
      have h2 : 35 * (8 * (w + 2)) < 2 ^ 64 := by omega
      have h3 : 35 * (w + 2) < 2 ^ 64 := by omega
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show 35 < 2 ^ 64 by decide), Nat.mod_eq_of_lt h1,
        Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3]
      omega
    prun [b10, b29, e17, nArr]
    refine ⟨?_, rfl⟩
    rw [es, Nat.zero_mul, Nat.add_zero]
  refine WP.mono hC fun t₃ ⟨⟨m₃, c14, c17, c0⟩, k₃⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off B (256 + 8 * i) ∧ t.gpr .r0 = 0 ∧ Outside B 256 (8 * i) t₃.mem t.mem ∧
      (∀ k < i, word t.mem B (256 + 8 * k) = 0) ∧ Keep [.r0, .r14, .r17] t₃ t
  refine WP.mono (wp_countdown (body := .block ([.store .d .r0 .r14 0, .addi .r14 .r14 8] ++
      ([.subi .r17 .r17 1] : List Instr))) (cnt := .r17) (N := 35 * (w + 2)) (by omega)
      (by omega) Inv (fun i hi t ⟨j14, j0, jout, jz, jk⟩ _ => ?_)
      ⟨by rw [c14], c0, Outside.refl _ _ _ _, fun _ h => absurd h (by omega), Keep.refl _ _⟩ c17)
    fun t ⟨_, _, tout, tz, tk⟩ => ?_
  · have hst : WP isa (.block [.store .d .r0 .r14 0, .addi .r14 .r14 8, .subi .r17 .r17 1]) t
        fun t' => t' = ((({ t with mem := t.mem.writeW (off B (256 + 8 * i)) (0 : BitVec 64) } : State).write
          .r14 (off B (256 + 8 * i + 8))).write .r17 (t.gpr .r17 - BitVec.ofNat 64 1)) := by
      prun [j14, j0, ((hs₂.congr k₃.wr).congr jk.wr).st (show 256 + 8 * i + 8 ≤ 8 * SL by omega)]
    refine WP.mono hst fun t' e => ?_
    subst e
    have hw := writeW_outside t.mem B (d := 256 + 8 * i) 0 (by omega)
    refine ⟨⟨by gsimp; rw [show 256 + 8 * i + 8 = 256 + 8 * (i + 1) by omega], by gsimp; exact j0, ?_, ?_, ?_⟩,
      by gsimp⟩
    · gsimp
      exact (jout.mono (o' := 256) (n' := 8 * (i + 1)) (Nat.le_refl _) (by omega)).trans
        (hw.mono (o' := 256) (n' := 8 * (i + 1)) (by omega_arith) (by omega_arith))
    · intro k hk
      gsimp
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · rw [hw.word (by omega) (by omega)]; exact jz k hk
      · exact word_writeW_self _ _ _ _
    · exact jk.trans' ((((Keep.mem _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono)
  · have K := (k12.trans k₃).trans tk
    have e10 : t.gpr .r10 = off B (slot w 0) := (tk.gpr _ (by decide)).trans ((k₃.gpr _ (by decide)).trans b10)
    have e29 : t.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) :=
      (tk.gpr _ (by decide)).trans ((k₃.gpr _ (by decide)).trans b29)
    have e11 : t.gpr .r11 = BitVec.ofNat 64 (2 * w) :=
      (tk.gpr _ (by decide)).trans ((k₃.gpr _ (by decide)).trans ((k₂.gpr _ (by decide)).trans a11))
    have e31 : t.gpr .r31 = B := (tk.gpr _ (by decide)).trans ((k₃.gpr _ (by decide)).trans ((k₂.gpr _ (by decide)).trans a31))
    -- Memory below the arrays is as after the header.
    have lo : ∀ d, d + 8 ≤ 256 → word t.mem B d = word t₂.mem B d := fun d hd => by
      rw [tout.word (by omega) (by omega), m₃]
    have lo1 : ∀ d, d + 8 ≤ 64 ∨ 128 ≤ d → d + 8 ≤ 256 → word t.mem B d = word t₁.mem B d := fun d hd hd' => by
      rw [lo d hd', out₂.word (by omega) (by omega)]
    refine ⟨⟨⟨hs.congr K.wr, e10, e29, e11, e31, hw, by omega_arith, by rw [es]; omega_arith⟩, ⟨?_, ?_, ?_, fun j hj => ?_⟩, tz, ?_⟩, K.mono⟩
    · rw [lo1 0 (by omega) (by omega), m₁]
      rw [(writeW_outside _ B (d := 224) _ (by omega)).word (by omega) (by omega),
        (writeW_outside _ B (d := 48) _ (by omega)).word (by omega) (by omega)]
      exact word_writeW_self _ _ _ _
    · rw [lo1 48 (by omega) (by omega), m₁]
      rw [(writeW_outside _ B (d := 224) _ (by omega)).word (by omega) (by omega)]
      exact word_writeW_self _ _ _ _
    · rw [lo1 224 (by omega) (by omega), m₁]
      exact word_writeW_self _ _ _ _
    · rw [lo _ (by omega)]; exact hw₂ j hj
    · intro x hx
      simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
      rw [tout x (by simp only [nArr] at hx; omega), m₃, out₂ x (by omega), m₁]
      have w1 := writeW_outside s.mem B (d := 0) (BitVec.ofNat 64 SL) (by omega)
      have w2 := writeW_outside (s.mem.writeW (off B 0) (BitVec.ofNat 64 SL)) B (d := 48) (BitVec.ofNat 64 w)
        (by omega)
      have w3 := writeW_outside ((s.mem.writeW (off B 0) (BitVec.ofNat 64 SL)).writeW (off B 48)
        (BitVec.ofNat 64 w)) B (d := 224) (BitVec.ofNat 64 (8 * (w + 2))) (by omega)
      rw [w3 x (by omega), w2 x (by omega), w1 x (by omega)]

end VG.Proof.RsaKeyGen.PPC64LE.Cand
