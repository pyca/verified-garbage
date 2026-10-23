module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad

/-!
# The RSA public-key operation on PPC64LE: the power

`step_ok`: a step of the scan, as congruences: `S R ≡ a² (mod n)`,
`P R ≡ S (x R) (mod n)` and `a := P` or `S` by the top bit of `r24`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pub

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.PublicChecked
open VG.Proof.Bignum.PPC64LE

/-- A digit apart from every range that changed. -/
theorem Outs.w32 {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m')
    {d : Nat} (hd : ∀ r ∈ rs, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 4 ≤ 2 ^ 64) :
    w32 m' base d = w32 m base d := by
  have := h.val32 (d := d) (k := 1) (by simpa using hd) (by omega)
  simpa [val32] using this

theorem top_bit (x : BitVec 64) :
    x >>> 63 = BitVec.ofNat 64 (if 2 ^ 63 ≤ x.toNat then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  have := x.isLt
  split <;> omega

/-- The block before the selection: the mask of `r24`'s top bit in `r20`,
`r24` shifted, and the bases of arrays 1, 4 and 5. -/
theorem selBlock_ok {t : State} {B : Addr} {w : Nat} (h10 : t.gpr .r10 = off B (slot w 0))
    (h29 : t.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) :
    WP isa (.block (([.lsr .d .r0 .r24 63, .li .r3 0, .sub .r20 .r3 .r0, .lsl .r24 .r24 1] : List Instr) ++
        base .r8 1 ++ base .r9 4 ++ base .r5 5)) t fun t' =>
      (t'.gpr .r20 = BitVec.ofNat 64 0 -
          BitVec.ofNat 64 (if decide (2 ^ 63 ≤ (t.gpr .r24).toNat) then 1 else 0) ∧
        t'.gpr .r24 = t.gpr .r24 <<< 1 ∧ t'.gpr .r8 = off B (slot w 1) ∧ t'.gpr .r9 = off B (slot w 4) ∧
        t'.gpr .r5 = off B (slot w 5) ∧ t'.mem = t.mem) ∧
      Keep [.r0, .r3, .r20, .r24, .r8, .r9, .r5] t t' := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r0, .r3, .r20, .r24] (Q := fun t₁ => t₁.gpr .r20 = BitVec.ofNat 64 0 -
      BitVec.ofNat 64 (if decide (2 ^ 63 ≤ (t.gpr .r24).toNat) then 1 else 0) ∧
      t₁.gpr .r24 = t.gpr .r24 <<< 1 ∧ t₁.mem = t.mem) (by prun [top_bit]; simp) (by decide))
    fun t₁ ⟨⟨a20, a24, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .r8) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h10)
    ((k1.gpr _ (by decide)).trans h29) 1) fun t₂ ⟨⟨a8, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .r9) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29) 4) fun t₃ ⟨⟨a9, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  refine WP.mono (base_ok (rd := .r5) (by decide) (by decide) ((k13.gpr _ (by decide)).trans h10)
    ((k13.gpr _ (by decide)).trans h29) 5) fun t₄ ⟨⟨a5, m4⟩, k4⟩ => ⟨⟨?_, ?_, ?_, ?_, a5, ?_⟩, (k13.trans k4).mono⟩
  · rw [k4.gpr .r20 (by decide), k3.gpr .r20 (by decide), k2.gpr .r20 (by decide), a20]
  · rw [k4.gpr .r24 (by decide), k3.gpr .r24 (by decide), k2.gpr .r24 (by decide), a24]
  · rw [k4.gpr .r8 (by decide), k3.gpr .r8 (by decide), a8]
  · rw [k4.gpr .r9 (by decide), a9]
  · rw [m4, m3, m2, m1]

/-- The arrays a step changes. -/
def stepRs (w : Nat) : List (Nat × Nat) :=
  [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w 4, 8 * (w + 2)), (slot w 1, 8 * (w + 2)),
    (slot w 5, 8 * (w + 2))]

/-- The registers a step writes. -/
def stepRegs : List Reg := montRegs ++ [.r0, .r3, .r20, .r24, .r14, .r15, .r16, .r17]

/-- A step of the scan, `a` in array 5 and `x R mod n` in array 6, both below
`n` (array 0). -/
theorem step_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hA : val32 s.mem B (slot w 5) (2 * w) < val32 s.mem B (slot w 0) (2 * w))
    (hX : val32 s.mem B (slot w 6) (2 * w) < val32 s.mem B (slot w 0) (2 * w)) :
    WP isa PublicChecked.step s fun t =>
      (∃ S P, S < val32 s.mem B (slot w 0) (2 * w) ∧ P < val32 s.mem B (slot w 0) (2 * w) ∧
        S * 2 ^ (64 * w) % val32 s.mem B (slot w 0) (2 * w) =
          val32 s.mem B (slot w 5) (2 * w) * val32 s.mem B (slot w 5) (2 * w) %
            val32 s.mem B (slot w 0) (2 * w) ∧
        P * 2 ^ (64 * w) % val32 s.mem B (slot w 0) (2 * w) =
          S * val32 s.mem B (slot w 6) (2 * w) % val32 s.mem B (slot w 0) (2 * w) ∧
        val32 t.mem B (slot w 5) (2 * w) = if decide (2 ^ 63 ≤ (s.gpr .r24).toNat) then P else S) ∧
      Outs B (stepRs w) s.mem t.mem ∧ t.gpr .r24 = s.gpr .r24 <<< 1 ∧ Keep stepRegs s t := by
  have hnw := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have sp : ∀ {j k}, j ≠ k → slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j :=
    fun h => slot_sep h
  unfold PublicChecked.step
  -- `S := a²` into array 4.
  refine WP.seq (WP.mono (montOp_ok (o := 4) (a := 5) (b := 5) hs (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hw2 hw' hZ h10 h29 h11 h12 hinv hA)
    fun s₁ ⟨⟨hS, eS, o1⟩, k1⟩ => ?_)
  have ap : ∀ {j : Nat} {ks : List Nat}, (∀ k ∈ ks, k ≠ j) →
      ∀ r ∈ ks.map (fun k => (slot w k, 8 * (w + 2))), slot w j + 8 * (w + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
    intro j ks h r hr
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
    exact sp (Ne.symm (h k hk))
  have o1' : Outs B ([2, 3, 4].map fun k => (slot w k, 8 * (w + 2))) s.mem s₁.mem := o1
  have hd1 : ∀ {j}, j < 8 → j ≠ 2 → j ≠ 3 → j ≠ 4 →
      val32 s₁.mem B (slot w j) (2 * w) = val32 s.mem B (slot w j) (2 * w) := by
    intro j hj h2 h3 h4
    exact o1'.val32 (fun r hr => by have := ap (j := j) (ks := [2, 3, 4]) (by simp; omega) r hr; omega)
      (by have := sl _ hj; omega)
  have hw1 : w32 s₁.mem B (slot w 0) = w32 s.mem B (slot w 0) :=
    Outs.w32 o1' (fun r hr => by have := ap (j := 0) (ks := [2, 3, 4]) (by decide) r hr; omega)
      (by have := sl 0 (by decide); omega)
  have N1 := hd1 (j := 0) (by decide) (by decide) (by decide) (by decide)
  have X1 := hd1 (j := 6) (by decide) (by decide) (by decide) (by decide)
  -- `P := S x` into array 1.
  refine WP.seq (WP.mono (montOp_ok (o := 1) (a := 4) (b := 6) (hs.congr k1.wr) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' hZ
    ((k1.gpr _ (by decide)).trans h10) ((k1.gpr _ (by decide)).trans h29) ((k1.gpr _ (by decide)).trans h11)
    (by rw [k1.gpr .r12 (by decide)]; exact h12) (by rw [hw1, k1.gpr .r12 (by decide)]; exact hinv)
    (by rw [X1, N1]; exact hX)) fun s₂ ⟨⟨hP, eP, o2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  have o2' : Outs B ([2, 3, 1].map fun k => (slot w k, 8 * (w + 2))) s₁.mem s₂.mem := o2
  have hd2 : ∀ {j}, j < 8 → j ≠ 2 → j ≠ 3 → j ≠ 1 →
      val32 s₂.mem B (slot w j) (2 * w) = val32 s₁.mem B (slot w j) (2 * w) := by
    intro j hj h2 h3 h1
    exact o2'.val32 (fun r hr => by have := ap (j := j) (ks := [2, 3, 1]) (by simp; omega) r hr; omega)
      (by have := sl _ hj; omega)
  rw [N1] at hP
  rw [N1, X1] at eP
  -- The selection.
  refine WP.seq (WP.mono (selBlock_ok (B := B) (w := w) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29)) fun s₃ ⟨⟨a20, a24, a8, a9, a5, m3⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  refine WP.mono (selectAcc_ok (n := 2 * w) (dA := slot w 1) (dT := slot w 4) (dO := slot w 5)
    (hs.congr k13.wr) a8 a9 a5 ((k13.gpr _ (by decide)).trans h11) a20 (by omega) (by omega)
    (by have := sl 1 (by decide); omega) (by have := sl 4 (by decide); omega)
    (by have := sl 5 (by decide); omega) (by have := sp (show (5 : Nat) ≠ 1 by decide); omega)
    (by have := sp (show (5 : Nat) ≠ 4 by decide); omega)) fun t ⟨hv, out, k4⟩ => ?_
  refine ⟨⟨val32 s₁.mem B (slot w 4) (2 * w), val32 s₂.mem B (slot w 1) (2 * w), hS, hP, eS, eP, ?_⟩,
    ?_, ?_, ((k13.trans k4).mono)⟩
  · rw [hv, m3, hd2 (j := 4) (by decide) (by decide) (by decide) (by decide), k12.gpr .r24 (by decide)]
  · refine Outs.trans (Outs.mono o1 (by simp [stepRs])) (Outs.trans (Outs.mono o2 (by simp [stepRs])) ?_)
    rw [m3] at out
    exact Outs.of_outside (o := slot w 5) (n := 8 * (w + 2)) (out.mono (Nat.le_refl _) (by omega))
      (by simp [stepRs])
  · rw [k4.gpr .r24 (by decide), a24, k12.gpr .r24 (by decide)]

/-! ## The arithmetic of the scan -/

theorem sq_step {A S X c R N : Nat} (hR : Nat.Coprime R N) (hA : A % N = X ^ c * R % N)
    (hS : S * R % N = A * A % N) : S % N = X ^ (2 * c) * R % N := by
  refine VG.Proof.Bignum.mont_cancel hR ?_
  rw [hS, Nat.mul_mod, hA, ← Nat.mul_mod, Nat.two_mul, Nat.pow_add]
  congr 1
  grind

theorem mul_step {S P X c R N XM : Nat} (hR : Nat.Coprime R N) (hS : S % N = X ^ (2 * c) * R % N)
    (hX : XM % N = X * R % N) (hP : P * R % N = S * XM % N) : P % N = X ^ (2 * c + 1) * R % N := by
  refine VG.Proof.Bignum.mont_cancel hR ?_
  rw [hP, Nat.mul_mod, hS, hX, ← Nat.mul_mod, Nat.pow_succ]
  congr 1
  grind

/-- `one`: 1 in array 7. -/
theorem oneP_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (hw1 : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) :
    WP isa PublicChecked.one s fun t =>
      (val32 t.mem B (slot w 7) (2 * w) = 1 ∧ Outside B (slot w 7) (8 * w) s.mem t.mem) ∧
        Keep [.r0, .r14, .r17] s t := by
  have hnw := hs.nowrap
  have s7 := slot_le (w := w) (j := 7) (by decide)
  unfold PublicChecked.one
  refine WP.seq (WP.mono (base_ok (rd := .r14) (by decide) (by decide) h10 h29 7) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (hs.congr k1.wr) a14 ((k1.gpr _ (by decide)).trans h11) hw1 hw'
    (by omega)) fun s₂ ⟨⟨_, hz, out₂⟩, k₂⟩ => ?_)
  have k12 := k1.trans k₂
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .r14) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29) 7) fun s₃ ⟨⟨b14, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  refine WP.mono (WP.keep [.r0] (Q := fun t =>
    t.mem = s₃.mem.writeW (off B (slot w 7)) ((1 : BitVec 64).setWidth 32)) ?_ (by decide))
    fun t ⟨tm, k4⟩ => ⟨⟨?_, ?_⟩, (k13.trans k4).mono⟩
  · prun [b14, BitVec.add_zero, (hs.congr k13.wr).st (d := slot w 7) (n := 4) (by omega)]
    rfl
  · rw [m3] at tm
    have hz32 : ∀ j < 2 * w, w32 s₂.mem B (slot w 7 + 4 * j) = 0 := fun j hj => by
      have hword := word_eq_w32 s₂.mem B (slot w 7 + 8 * (j / 2))
      rw [hz (j / 2) (by omega)] at hword
      have : w32 s₂.mem B (slot w 7 + 8 * (j / 2)) = 0 ∧ w32 s₂.mem B (slot w 7 + 8 * (j / 2) + 4) = 0 := by
        rw [show (0 : BitVec 64).toNat = 0 from rfl] at hword; omega
      rcases Nat.mod_two_eq_zero_or_one j with h | h
      · rw [show slot w 7 + 4 * j = slot w 7 + 8 * (j / 2) by omega]; exact this.1
      · rw [show slot w 7 + 4 * j = slot w 7 + 8 * (j / 2) + 4 by omega]; exact this.2
    have ho := writeW32_outside s₂.mem B (d := slot w 7) ((1 : BitVec 64).setWidth 32) (by omega)
    have e := val32_append (s₂.mem.writeW (off B (slot w 7)) ((1 : BitVec 64).setWidth 32)) B (slot w 7) 1
      (2 * w - 1)
    rw [show 1 + (2 * w - 1) = 2 * w by omega] at e
    have hrest : val32 (s₂.mem.writeW (off B (slot w 7)) ((1 : BitVec 64).setWidth 32)) B (slot w 7 + 4 * 1)
        (2 * w - 1) = 0 := by
      rw [ho.val32 (by omega) (by omega)]
      exact val32_zero fun j hj => by
        rw [show slot w 7 + 4 * 1 + 4 * j = slot w 7 + 4 * (j + 1) by omega]; exact hz32 _ (by omega)
    have h1 := val32_succ (s₂.mem.writeW (off B (slot w 7)) ((1 : BitVec 64).setWidth 32)) B (slot w 7) 0
    rw [show slot w 7 + 4 * 0 = slot w 7 from rfl, w32_write_self] at h1
    rw [tm, e, hrest, Nat.mul_zero, Nat.add_zero, h1]
    rfl
  · rw [m3] at tm
    rw [m1] at out₂
    rw [tm]
    exact out₂.trans ((writeW32_outside s₂.mem B (d := slot w 7) _ (by omega)).mono (by omega) (by omega))

/-! ## The power -/

/-- The arrays the power changes: all but array 0. -/
def powRs (w : Nat) : List (Nat × Nat) :=
  [1, 2, 3, 4, 5, 6, 7].map fun k => (slot w k, 8 * (w + 2))

/-- The registers the power writes. -/
def powRegs : List Reg := stepRegs ++ [.r25]

theorem r24_step (x : BitVec 64) :
    (x <<< 1).toNat = 2 * x.toNat - (if decide (2 ^ 63 ≤ x.toNat) then 1 else 0) * 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have := x.isLt
  split <;> simp_all <;> omega

/-- `power`: `x^(E mod 2^33) mod n` into array 4, for the input `x` in array 4,
`E 2^31` in `r24` and something below `n` in array 1: if it is `R² mod n`. -/
theorem power_ok {s : State} {B : Addr} {Z w E : Nat} (hs : Scr s B Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hN : 2 ≤ val32 s.mem B (slot w 0) (2 * w)) (hodd : val32 s.mem B (slot w 0) (2 * w) % 2 = 1)
    (hRRlt : val32 s.mem B (slot w 1) (2 * w) < val32 s.mem B (slot w 0) (2 * w))
    (h24 : s.gpr .r24 = BitVec.ofNat 64 E <<< 31) :
    WP isa power s fun t =>
      ((val32 s.mem B (slot w 1) (2 * w) = 2 ^ (64 * w) * 2 ^ (64 * w) % val32 s.mem B (slot w 0) (2 * w) →
          val32 t.mem B (slot w 4) (2 * w) =
            val32 s.mem B (slot w 4) (2 * w) ^ (E % 2 ^ 33) % val32 s.mem B (slot w 0) (2 * w)) ∧
        Outs B (powRs w) s.mem t.mem) ∧ Keep powRegs s t := by
  have hnw := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have sp : ∀ {j k}, j ≠ k → slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j :=
    fun h => slot_sep h
  have ap : ∀ {j : Nat} {ks : List Nat}, (∀ k ∈ ks, k ≠ j) →
      ∀ r ∈ ks.map (fun k => (slot w k, 8 * (w + 2))), slot w j + 8 * (w + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
    intro j ks h r hr
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
    exact sp (Ne.symm (h k hk))
  have v0 : ∀ {m : Mem}, Outs B (powRs w) s.mem m →
      val32 m B (slot w 0) (2 * w) = val32 s.mem B (slot w 0) (2 * w) := fun h =>
    h.val32 (fun r hr => by have := ap (j := 0) (ks := [1, 2, 3, 4, 5, 6, 7]) (by decide) r hr; omega)
      (by have := sl 0 (by decide); omega)
  have w0 : ∀ {m : Mem}, Outs B (powRs w) s.mem m → w32 m B (slot w 0) = w32 s.mem B (slot w 0) := fun h =>
    Outs.w32 h (fun r hr => by have := ap (j := 0) (ks := [1, 2, 3, 4, 5, 6, 7]) (by decide) r hr; omega)
      (by have := sl 0 (by decide); omega)
  generalize hNd : val32 s.mem B (slot w 0) (2 * w) = N at hN hodd hRRlt v0 ⊢
  generalize hR : 2 ^ (64 * w) = R
  generalize hRRd : val32 s.mem B (slot w 1) (2 * w) = RRv at hRRlt ⊢
  have hcop : Nat.Coprime R N := by rw [← hR]; exact VG.Proof.Bignum.coprime_pow2 hodd _
  generalize hXd : val32 s.mem B (slot w 4) (2 * w) = X
  have hN0 : 0 < N := by omega
  have outs_of : ∀ {m m' : Mem} {js : List Nat}, (∀ j ∈ js, j ∈ [1, 2, 3, 4, 5, 6, 7]) →
      Outs B (js.map fun k => (slot w k, 8 * (w + 2))) m m' → Outs B (powRs w) m m' := fun hjs h =>
    h.mono fun r hr => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
      exact List.mem_map.mpr ⟨k, hjs k hk, rfl⟩
  have vj : ∀ {m m' : Mem} {js : List Nat} {j : Nat}, j < 8 → (∀ k ∈ js, k ≠ j) →
      Outs B (js.map fun k => (slot w k, 8 * (w + 2))) m m' →
      val32 m' B (slot w j) (2 * w) = val32 m B (slot w j) (2 * w) := fun hj hjs h =>
    h.val32 (fun r hr => by have := ap hjs r hr; omega) (by have := sl _ hj; omega)
  unfold power
  -- 1 in array 7.
  refine WP.seq (WP.mono (oneP_ok hs (by omega) hw' hZ h10 h29 h11) fun s₁ ⟨⟨h7, out1⟩, k1⟩ => ?_)
  have o1 : Outs B ([7].map fun k => (slot w k, 8 * (w + 2))) s.mem s₁.mem :=
    Outs.of_outside (o := slot w 7) (n := 8 * (w + 2)) (out1.mono (Nat.le_refl _) (by omega)) (by simp)
  have N1 : val32 s₁.mem B (slot w 0) (2 * w) = N := (vj (by decide) (by decide) o1).trans hNd
  have R1 : val32 s₁.mem B (slot w 1) (2 * w) = RRv := by rw [vj (by decide) (by decide) o1, hRRd]
  have X1 : val32 s₁.mem B (slot w 4) (2 * w) = X := (vj (by decide) (by decide) o1).trans hXd
  have hRRN : RRv < N := hRRlt
  -- `a := R mod n` into array 5.
  refine WP.seq (WP.mono (montOp_ok (o := 5) (a := 1) (b := 7) (hs.congr k1.wr) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' hZ ((k1.gpr _ (by decide)).trans h10)
    ((k1.gpr _ (by decide)).trans h29) ((k1.gpr _ (by decide)).trans h11) (by rw [k1.gpr .r12 (by decide)]; exact h12)
    (by rw [w0 (outs_of (by decide) o1), k1.gpr .r12 (by decide)]; exact hinv) (by rw [h7, N1]; omega))
    fun s₂ ⟨⟨hA0, eA0, o2⟩, k2⟩ => ?_)
  rw [N1, R1, h7, hR] at eA0
  rw [N1] at hA0
  have o2' : Outs B ([2, 3, 5].map fun k => (slot w k, 8 * (w + 2))) s₁.mem s₂.mem := o2
  have k12 := k1.trans k2
  have A0 : RRv = R * R % N → val32 s₂.mem B (slot w 5) (2 * w) % N = X ^ 0 * R % N := fun hE => by
    refine VG.Proof.Bignum.mont_cancel hcop ?_
    rw [eA0, hE, Nat.pow_zero, Nat.one_mul, Nat.mul_one, Nat.mod_mod]
  -- `x R mod n` into array 6.
  have O12 : Outs B (powRs w) s.mem s₂.mem := (outs_of (by decide) o1).trans (outs_of (by decide) o2')
  refine WP.seq (WP.mono (montOp_ok (o := 6) (a := 4) (b := 1) (hs.congr k12.wr) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' hZ ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29) ((k12.gpr _ (by decide)).trans h11)
    (by rw [k12.gpr .r12 (by decide)]; exact h12)
    (by rw [w0 O12, k12.gpr .r12 (by decide)]; exact hinv)
    (by rw [vj (by decide) (by decide) o2', R1, v0 O12]; exact hRRN)) fun s₃ ⟨⟨hXM, eXM, o3⟩, k3⟩ => ?_)
  rw [v0 O12, vj (by decide) (by decide) o2', vj (by decide) (by decide) o2', X1, R1, hR] at eXM
  rw [v0 O12] at hXM
  have o3' : Outs B ([2, 3, 6].map fun k => (slot w k, 8 * (w + 2))) s₂.mem s₃.mem := o3
  have k13 := k12.trans k3
  have O13 : Outs B (powRs w) s.mem s₃.mem := O12.trans (outs_of (by decide) o3')
  have XM : RRv = R * R % N → val32 s₃.mem B (slot w 6) (2 * w) % N = X * R % N := fun hE => by
    refine VG.Proof.Bignum.mont_cancel hcop ?_
    rw [eXM, hE, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  generalize hXMd : val32 s₃.mem B (slot w 6) (2 * w) = XMv at hXM XM
  have A3 : val32 s₃.mem B (slot w 5) (2 * w) = val32 s₂.mem B (slot w 5) (2 * w) :=
    vj (by decide) (by decide) o3'
  have S7 : val32 s₃.mem B (slot w 7) (2 * w) = 1 := by
    rw [vj (by decide) (by decide) o3', vj (by decide) (by decide) o2', h7]
  -- The count.
  refine WP.seq ?_
  refine WP.mono (WP.keep [.r25] (Q := fun s₄ => s₄.gpr .r25 = BitVec.ofNat 64 33 ∧ s₄.mem = s₃.mem)
    (by prun) (by decide)) fun s₄ ⟨⟨h25, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  let Inv : Nat → State → Prop := fun i t =>
    Keep powRegs s t ∧ Outs B (powRs w) s.mem t.mem ∧ val32 t.mem B (slot w 6) (2 * w) = XMv ∧
      val32 t.mem B (slot w 7) (2 * w) = 1 ∧ val32 t.mem B (slot w 5) (2 * w) < N ∧
      ∃ c, c * 2 ^ 64 + (t.gpr .r24).toNat = E % 2 ^ 33 * 2 ^ 31 * 2 ^ i ∧
        (RRv = R * R % N → val32 t.mem B (slot w 5) (2 * w) % N = X ^ c * R % N)
  refine WP.seq (WP.mono (wp_countdown (cnt := .r25) (N := 33) (by decide) (by decide) Inv
    (fun i _ t ⟨kt, ot, t6, t7, tA, c, hc, hcA⟩ _ => ?_)
    ⟨k14.mono, by rw [m4]; exact O13, by rw [m4, hXMd], by rw [m4, S7], by rw [m4, A3]; exact hA0,
      0, ?_, fun hE => by rw [m4, A3]; exact A0 hE⟩ h25) fun t hI => ?_)
  · -- A step.
    refine WP.seq (WP.mono (step_ok (hs.congr kt.wr) hw2 hw' hZ ((kt.gpr _ (by decide)).trans h10)
      ((kt.gpr _ (by decide)).trans h29) ((kt.gpr _ (by decide)).trans h11)
      (by rw [kt.gpr .r12 (by decide)]; exact h12) (by rw [w0 ot, kt.gpr .r12 (by decide)]; exact hinv)
      (by rw [v0 ot]; exact tA) (by rw [v0 ot, t6]; exact hXM))
      fun t₁ ⟨⟨S, P, hSN, hPN, eS, eP, hv⟩, os, h24', k'⟩ => ?_)
    rw [v0 ot] at hSN hPN eS eP
    rw [t6] at eP
    refine WP.mono (subi_ok t₁ .r25 (by decide)) fun t₂ e => ?_
    subst e
    have os' : Outs B ([2, 3, 4, 1, 5].map fun k => (slot w k, 8 * (w + 2))) t.mem t₁.mem := os
    refine ⟨⟨((kt.trans k').trans (Keep.write _ _ _)).mono, ot.trans (outs_of (by decide) os'), ?_, ?_, ?_,
      2 * c + (if decide (2 ^ 63 ≤ (t.gpr .r24).toNat) then 1 else 0), ?_, ?_⟩,
      by gsimp; rw [k'.gpr .r25 (by decide)]⟩
    · rw [mem_write, vj (by decide) (by decide) os', t6]
    · rw [mem_write, vj (by decide) (by decide) os', t7]
    · rw [mem_write, hv]; split <;> with_reducible assumption
    · simp only [gpr_write, reduceCtorEq, ↓reduceIte]
      rw [h24', r24_step, show (2 : Nat) ^ (i + 1) = 2 ^ i * 2 from Nat.pow_succ 2 i, ← Nat.mul_assoc]
      have hlt := (t.gpr .r24).isLt
      generalize (t.gpr .r24).toNat = r at hc hlt ⊢
      generalize E % 2 ^ 33 * 2 ^ 31 * 2 ^ i = Y at hc ⊢
      split
      · rename_i hb; simp only [decide_eq_true_eq] at hb
        omega_using [hc, hlt, hb]
      · omega_using [hc, hlt]
    · intro hE
      have hS := sq_step hcop (hcA hE) (by rw [← hR]; exact eS)
      have hP := mul_step hcop hS (XM hE) (by rw [← hR]; exact eP)
      rw [mem_write, hv]
      split
      · exact hP
      · rw [Nat.add_zero]; exact hS
  · -- The start: `c = 0`.
    rw [Nat.zero_mul, Nat.zero_add, Nat.pow_zero, Nat.mul_one, k14.gpr .r24 (by decide), h24,
      BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    omega
  · -- Out of Montgomery form.
    obtain ⟨kt, ot, _, t7, tA, c, hc, hcA⟩ := hI
    have hc' : c = E % 2 ^ 33 := by
      have := (t.gpr .r24).isLt
      rw [show E % 2 ^ 33 * 2 ^ 31 * 2 ^ 33 = E % 2 ^ 33 * 2 ^ 64 by rw [Nat.mul_assoc]] at hc
      omega
    subst hc'
    refine WP.mono (montOp_ok (o := 4) (a := 5) (b := 7) (hs.congr kt.wr) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' hZ ((kt.gpr _ (by decide)).trans h10)
      ((kt.gpr _ (by decide)).trans h29) ((kt.gpr _ (by decide)).trans h11)
      (by rw [kt.gpr .r12 (by decide)]; exact h12) (by rw [w0 ot, kt.gpr .r12 (by decide)]; exact hinv)
      (by rw [t7, v0 ot]; omega)) fun u ⟨⟨hU, eU, o5⟩, k5⟩ =>
      ⟨⟨?_, ot.trans (outs_of (js := [2, 3, 4]) (by decide) o5)⟩, (kt.trans k5).mono⟩
    · intro hE
      rw [v0 ot] at hU eU
      rw [t7, hR, Nat.mul_one] at eU
      have : val32 u.mem B (slot w 4) (2 * w) % N = X ^ (E % 2 ^ 33) % N :=
        VG.Proof.Bignum.mont_cancel hcop (by rw [eU, hcA hE])
      rw [← Nat.mod_eq_of_lt hU, this]

end VG.Proof.Bignum.PPC64LE.Pub
