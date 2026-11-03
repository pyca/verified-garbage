module

public import VerifiedGarbage.Proof.Bignum.RISCV64.Double64
public import VerifiedGarbage.Proof.Bignum.RISCV64.MontCore
public import VerifiedGarbage.Proof.Bignum.RISCV64.MontSqr
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The precomputed values of an RSA modulus on RISC-V: `R² mod n`

`r2_ok`: `Precompute.r2` leaves `x = 2^(128 w) mod n` in array 1. `r2Top_ok`
writes `2^(64 (w - 1))`, below a valid `n`; `r2HiDbl_ok` doubles it `64 + w`
times, to `2^w R mod n`; `minv_ok` computes `-n⁻¹ mod 2⁶⁴` by Newton's
iteration (3, 6, 12, 24, 48 and 96 bits), and `r2Squares_ok` squares `x` six
times in Montgomery form (`MontCore.tail_ok`), to `2^(64 w) R mod n = R² mod
n`.

`lz_ok` and `r2Rest_ok`: the precompute's own `lz` then `r2Rest`, to the
same `x`. `lz_ok` leaves the leading zeros of `n`'s top word `T`, `zOf T =
63 - log₂ T`, in `a1` (63 steps that double `T` while its top bit is clear);
`r2TopBit_ok` writes `2^(64 (w - 1) + 63 - z)`, below an odd `n`, which `w + 1
+ z` doublings take to `2^w R mod n`; `r2SquaresS_ok` squares six times by
`MontSqr.sqrTail_ok`, its temporary array 4.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Impl.Bignum.RISCV64.Precompute
open VG.Proof.Bignum (slot Arrays newton_step emod_pow_weaken odd_sq)

/-- Words that are all 0. -/
theorem wordsVal_zero {m : Mem} {B : Addr} {d : Nat} :
    ∀ {k : Nat}, (∀ i < k, Mont.word m B (d + 8 * i) = 0) → wordsVal m B d k = 0
  | 0, _ => rfl
  | k + 1, h => by
    rw [wordsVal_succ_top, wordsVal_zero (fun i hi => h i (by omega)), h k (by omega)]
    rfl

/-- `li` of 1. -/
theorem r2_exec_li_one {s : State} {d : Reg} : exec (.li d 1) s = some (s.write d 1) := by
  rw [exec_li (by decide)]; rfl

/-- The top word of `w ≥ 1` words. -/
theorem wordsVal_top (m : Mem) (B : Addr) (d : Nat) {w : Nat} (hw : 1 ≤ w) :
    wordsVal m B d w = wordsVal m B d (w - 1) + 2 ^ (64 * (w - 1)) * (Mont.word m B (d + 8 * (w - 1))).toNat := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  rw [wordsVal_succ_top]; rfl

/-- `2^(64 (w - 1))` in array 1, from `a2` and `t0`. -/
theorem r2Top_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (h2 : s.gpr .a2 = off B (slot w 1)) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : slot w 1 + 8 * w ≤ Z) :
    WP isa r2Top s fun t =>
      (wordsVal t.mem B (slot w 1) w = 2 ^ (64 * (w - 1)) ∧ Outside B (slot w 1) (8 * w) s.mem t.mem) ∧
        Keep [.s0, .t3, .t5] s t := by
  have hnw := hs.nowrap
  have al := slot_al8 w
  unfold r2Top
  refine WP.seq (WP.mono (WP.keep [.t3] (Q := fun t => t.gpr .t3 = off B (slot w 1) ∧ t.mem = s.mem)
    (by brun [h2, BitVec.add_zero]) (by rfl) (by rfl)) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (hs.congr k1.2.2) a3 ((k1.gpr (by decide)).trans ht0) hw hw' (al 1) hZ)
    fun s₂ ⟨⟨_, hz, out2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  have ea : BitVec.ofNat 64 w <<< 3 + off B (slot w 1) - BitVec.ofNat 64 8 = off B (slot w 1 + 8 * (w - 1)) := by
    simp only [off]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    have := B.isLt
    unfold slot hdrBytes at hZ ⊢
    omega
  have hs₂ := hs.congr k12.2.2
  have al1 := al 1
  refine WP.mono (WP.keep [.s0, .t3] (Q := fun t =>
      t.mem = s₂.mem.writeW (off B (slot w 1 + 8 * (w - 1))) (1 : BitVec 64)) (by
    brun [r2_exec_li_one, (k12.gpr (by decide)).trans ht0, (k12.gpr (by decide)).trans h2, ea, BitVec.add_zero,
      hs₂.st (show slot w 1 + 8 * (w - 1) + 8 ≤ Z by omega),
      hs₂.al8 (show slot w 1 + 8 * (w - 1) + 8 ≤ Z by omega) (by omega)]) (by rfl) (by rfl))
    fun t ⟨tm, k3⟩ => ⟨⟨?_, ?_⟩, (k12.trans k3).mono (by decide)⟩
  · rw [tm, wordsVal_top _ _ _ hw, Mont.word_writeW_self, Outside.wordsVal (writeW_outside _ _ _ (by omega)) (by omega) (by omega),
      wordsVal_zero (fun i hi => hz i (by omega))]
    simp
  · rw [tm, m1] at *
    exact Outside.trans out2 (Outside.mono (writeW_outside s₂.mem B (d := slot w 1 + 8 * (w - 1)) _ (by omega))
      (by omega) (by omega))

/-! ## The doublings -/

theorem pow_mod_double {a N : Nat} : 2 * (2 ^ a % N) % N = 2 ^ (a + 1) % N := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.pow_succ, Nat.mul_comm]

/-- The registers the doublings write. -/
def dblLoopRegs : List Reg := dblRegs ++ ([.a1] : List Reg)

/-- `M` doublings counted by `a1`, of `x = 2^a mod N` in array 1, for `N` in
array 0: `x := 2^(a + M) mod N`, changing only arrays 1–3. -/
theorem r2Dbl_ok {s : State} {B : Addr} {Z w N a M : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .a5 = off B (slot w 2)) (h6 : s.gpr .a6 = off B (slot w 3))
    (h7 : s.gpr .a7 = off B (slot w 0)) (h2 : s.gpr .a2 = off B (slot w 1))
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z)
    (hN : wordsVal s.mem B (slot w 0) w = N) (hN0 : 0 < N) (hx : wordsVal s.mem B (slot w 1) w = 2 ^ a % N)
    (h1 : s.gpr .a1 = BitVec.ofNat 64 M) (hM : 0 < M) (hM' : M < 2 ^ 64) :
    WP isa (.loop (.seq doubleMod64 (.block [.addi .a1 .a1 (-1)])) (.nonzero .a1)) s fun t =>
      wordsVal t.mem B (slot w 1) w = 2 ^ (a + M) % N ∧
      Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧ Keep dblLoopRegs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  let Inv : Nat → State → Prop := fun j t =>
    wordsVal t.mem B (slot w 1) w = 2 ^ (a + j) % N ∧
      Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧ Keep dblLoopRegs s t
  refine wp_countdown (cnt := .a1) (N := M) hM' hM Inv (fun j _ t ⟨tx, to, tk⟩ _ => ?_)
    ⟨by rw [Nat.add_zero]; exact hx, Outside.refl _ _ _ _, Keep.refl _ _⟩ h1
  have n0 : wordsVal t.mem B (slot w 0) w = N := by rw [Outside.wordsVal to (by omega) (by omega), hN]
  refine WP.seq (WP.mono (doubleMod64_ok (hs.congr tk.2.2) ((tk.gpr (by decide)).trans h5)
    ((tk.gpr (by decide)).trans h6) ((tk.gpr (by decide)).trans h7) ((tk.gpr (by decide)).trans h2)
    ((tk.gpr (by decide)).trans ht0) hw hw' hZ (by rw [tx, n0]; exact Nat.mod_lt _ hN0))
    fun t₁ ⟨d1, od, kd⟩ => ?_)
  refine WP.mono (dec_ok t₁ .a1) fun t₂ e2 => ?_
  subst e2
  refine ⟨⟨?_, by rw [mem_write]; exact Outside.trans to od,
    Keep.trans' tk ((kd.trans (Keep.write _ _ _)).mono (by decide))⟩, ?_⟩
  · rw [mem_write, d1, tx, n0, pow_mod_double, Nat.add_assoc]
  · gsimp; rw [kd.gpr (by decide)]

/-- The registers `r2HiDbl` writes. -/
def hiDblRegs : List Reg := [.a0, .a1, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4]

/-- `r2HiDbl`, with `N` above `2^(64 (w - 1))` in array 0: `x := 2^w R mod N` in
array 1, changing only arrays 1–3. -/
theorem r2HiDbl_ok {s : State} {B : Addr} {Z w N : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .a5 = off B (slot w 2)) (h6 : s.gpr .a6 = off B (slot w 3))
    (h7 : s.gpr .a7 = off B (slot w 0)) (h2 : s.gpr .a2 = off B (slot w 1))
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z)
    (hN : wordsVal s.mem B (slot w 0) w = N) (hNt : 2 ^ (64 * (w - 1)) < N) :
    WP isa r2HiDbl s fun t =>
      wordsVal t.mem B (slot w 1) w = 2 ^ (w + 64 * w) % N ∧
      Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧ Keep hiDblRegs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4
  have hh : hdrBytes = 256 := rfl
  unfold r2HiDbl
  refine WP.seq (WP.mono (r2Top_ok hs h2 ht0 (by omega) hw' (by omega)) fun s₁ ⟨⟨x1, o1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.a1] (Q := fun t => t.gpr .a1 = BitVec.ofNat 64 (w + 64) ∧ t.mem = s₁.mem)
    (by
      brun [(k1.gpr (by decide)).trans ht0]
      exact (BitVec.ofNat_add _ _).symm) (by rfl) (by rfl)) fun s₂ ⟨⟨a1, m2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  have O2 : Outside B (slot w 1) (24 * (w + 2)) s.mem s₂.mem := by
    rw [m2]; exact Outside.mono o1 (Nat.le_refl _) (by omega)
  refine WP.mono (r2Dbl_ok (N := N) (a := 64 * (w - 1)) (M := w + 64) (hs.congr k12.2.2)
    ((k12.gpr (by decide)).trans h5) ((k12.gpr (by decide)).trans h6) ((k12.gpr (by decide)).trans h7)
    ((k12.gpr (by decide)).trans h2) ((k12.gpr (by decide)).trans ht0) (by omega) hw' hZ
    (by rw [Outside.wordsVal O2 (by omega) (by omega), hN])
    (by omega) ?_ a1 (by omega) (by omega)) fun t ⟨tx, to, tk⟩ =>
      ⟨?_, Outside.trans O2 to, (k12.trans tk).mono (by decide)⟩
  · rw [m2, x1]
    exact (Nat.mod_eq_of_lt hNt).symm
  · rw [tx, show 64 * (w - 1) + (w + 64) = w + 64 * w by omega]

/-! ## `-n⁻¹ mod 2⁶⁴` -/

/-- A Newton step computed on words is the step on integers, modulo `2⁶⁴`. -/
theorem newton_val (a x : BitVec 64) :
    (((x * (BitVec.ofNat 64 2 - a * x)).toNat : Int) - x.toNat * (2 - a.toNat * x.toNat)) % 2 ^ 64 = 0 := by
  have hx := x.isLt; have ha := a.isLt
  have hR : (x * (BitVec.ofNat 64 2 - a * x)).toNat = x.toNat * (BitVec.ofNat 64 2 - a * x).toNat % 2 ^ 64 :=
    BitVec.toNat_mul _ _
  have hD : (BitVec.ofNat 64 2 - a * x).toNat = (2 ^ 64 - a.toNat * x.toNat % 2 ^ 64 + 2) % 2 ^ 64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat]
  generalize (BitVec.ofNat 64 2 - a * x).toNat = D at hR hD
  generalize (x * (BitVec.ofNat 64 2 - a * x)).toNat = R at hR ⊢
  generalize x.toNat = X at *
  generalize a.toNat = A at *
  have hDj : (D : Int) = 2 - (A * X : Nat) + 2 ^ 64 * (((D : Int) - 2 + (A * X : Nat)) / 2 ^ 64) := by
    have : ((A * X : Nat) : Int) % 2 ^ 64 = ((A * X % 2 ^ 64 : Nat) : Int) := by omega_arith
    omega_arith
  generalize (((D : Int) - 2 + (A * X : Nat)) / 2 ^ 64) = j at hDj
  have hXD : ((X * D : Nat) : Int) = 2 * X - (X : Int) * (A * X : Nat) + 2 ^ 64 * (X * j) := by
    rw [Int.natCast_mul, hDj, Int.mul_add, Int.mul_sub, Int.mul_left_comm (X : Int) (2 ^ 64) j]
    omega_arith
  have e : (X : Int) * (2 - (A : Int) * X) = 2 * X - (X : Int) * (A * X : Nat) := by
    rw [Int.mul_sub, Int.natCast_mul, Int.mul_comm (X : Int) 2]
  rw [e]
  have : ((X * D % 2 ^ 64 : Nat) : Int) = ((X * D : Nat) : Int) % 2 ^ 64 := by omega_arith
  rw [hR, this, hXD]
  omega_arith

/-- `li` of 2. -/
theorem r2_exec_li_two {s : State} {d : Reg} : exec (.li d 2) s = some (s.write d (BitVec.ofNat 64 2)) := by
  rw [exec_li (by decide)]; rfl

/-- A step: `a x' ≡ 1 (mod 2^(2j))` from `a x ≡ 1 (mod 2^j)`, `a` in `s3`
and `x` in `s0`. -/
theorem nstep_ok (t : State) {j : Nat} (hj : 2 * j ≤ 64)
    (h : (((t.gpr .s3).toNat : Int) * (t.gpr .s0).toNat - 1) % (2 ^ j : Int) = 0) :
    WP isa (.block newton) t fun t' =>
      ((((t'.gpr .s3).toNat : Int) * (t'.gpr .s0).toNat - 1) % (2 ^ (2 * j) : Int) = 0 ∧
        t'.gpr .s3 = t.gpr .s3 ∧ t'.mem = t.mem) ∧ Keep [.s0, .s1, .s2] t t' := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold newton
  brun [r2_exec_li_two]
  exact newton_step hj h (newton_val _ _)

/-- `-x mod 2⁶⁴` is an inverse of `-a` when `x` is one of `a`. -/
theorem neg_inv64 {a x : Nat} (h : ((a : Int) * x - 1) % (2 ^ 64 : Int) = 0) :
    (a * ((2 ^ 64 - x % 2 ^ 64) % 2 ^ 64) + 1) % 2 ^ 64 = 0 := by
  generalize hy : (2 ^ 64 - x % 2 ^ 64) % 2 ^ 64 = y
  have hxy : (x + y) % 2 ^ 64 = 0 := by omega_arith
  have h1 : (2 ^ 64 : Int) ∣ (a : Int) * x - 1 := Int.dvd_of_emod_eq_zero h
  have h2 : (2 ^ 64 : Int) ∣ ((x + y : Nat) : Int) :=
    Int.dvd_of_emod_eq_zero (show ((x + y : Nat) : Int) % (2 ^ 64 : Int) = 0 by omega_arith)
  have h3 : (2 ^ 64 : Int) ∣ ((a * y + 1 : Nat) : Int) := by
    have e : ((a * y + 1 : Nat) : Int) = (a : Int) * ((x + y : Nat) : Int) - ((a : Int) * x - 1) := by
      push_cast; grind
    rw [e]
    exact Int.dvd_sub (Int.dvd_mul_of_dvd_right h2) h1
  exact Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mp (by exact_mod_cast h3))

theorem minv_split : minv = ([.load .d .s3 .a7 0, .addi .s0 .s3 0] : List Instr) ++ (newton ++ (newton ++
    (newton ++ (newton ++ (newton ++ ([.li .s1 0, .sub .t1 .s1 .s0] : List Instr)))))) := by
  simp only [minv, List.append_assoc]

/-- `minv`, `n` at `d` of the working space (`a7`), odd: `t1` is
`-n⁻¹ mod 2⁶⁴`. -/
theorem minv_ok {s : State} {B : Addr} {Z d : Nat} (hs : Scr s B Z) (h7 : s.gpr .a7 = off B d)
    (hd8 : d % 8 = 0) (hd : d + 8 ≤ Z) (hodd : (Mont.word s.mem B d).toNat % 2 = 1) :
    WP isa (.block minv) s fun t =>
      (((Mont.word s.mem B d).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0 ∧ t.mem = s.mem) ∧
        Keep [.s0, .s1, .s2, .s3, .t1] s t := by
  rw [minv_split, WP.block_append_iff]
  refine WP.mono (WP.keep [.s3, .s0] (Q := fun t => t.gpr .s3 = Mont.word s.mem B d ∧
    t.gpr .s0 = Mont.word s.mem B d ∧ t.mem = s.mem)
    (by brun [h7, BitVec.add_zero, hs.ld hd, hs.al8 hd hd8]) (by rfl) (by rfl))
    fun t₀ ⟨⟨h0, h12, hm₀⟩, k₀⟩ => ?_
  have e₀ : (((t₀.gpr .s3).toNat : Int) * (t₀.gpr .s0).toNat - 1) % (2 ^ 3 : Int) = 0 := by
    rw [h0, h12]
    have h1 := odd_sq _ hodd
    have h2 : (((Mont.word s.mem B d).toNat : Int) * (Mont.word s.mem B d).toNat) % 8 = 1 := by
      simpa only [Int.natCast_mul, Int.natCast_emod, show ((8 : Nat) : Int) = 8 from rfl,
        show ((1 : Nat) : Int) = 1 from rfl] using congrArg (fun n : Nat => (n : Int)) h1
    show (((Mont.word s.mem B d).toNat : Int) * (Mont.word s.mem B d).toNat - 1) % 8 = 0
    omega_arith
  rw [WP.block_append_iff]
  refine WP.mono (nstep_ok t₀ (j := 3) (by decide) e₀) fun t₁ ⟨⟨e₁, hb₁, hm₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (nstep_ok t₁ (j := 6) (by decide) e₁) fun t₂ ⟨⟨e₂, hb₂, hm₂⟩, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (nstep_ok t₂ (j := 12) (by decide) e₂) fun t₃ ⟨⟨e₃, hb₃, hm₃⟩, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (nstep_ok t₃ (j := 24) (by decide) e₃) fun t₄ ⟨⟨e₄, hb₄, hm₄⟩, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (nstep_ok t₄ (j := 32) (by decide) (emod_pow_weaken (by decide) e₄))
    fun t₅ ⟨⟨e₅, hb₅, hm₅⟩, k₅⟩ => ?_
  have hb : t₅.gpr .s3 = Mont.word s.mem B d := hb₅.trans (hb₄.trans (hb₃.trans (hb₂.trans (hb₁.trans h0))))
  have kk := ((((k₀.trans k₁).trans k₂).trans k₃).trans k₄).trans k₅
  rw [hb] at e₅
  refine WP.mono (WP.keep [.s1, .t1] (Q := fun t =>
    t.gpr .t1 = 0 - t₅.gpr .s0 ∧ t.mem = t₅.mem) (by brun [fin64_exec_li_zero]) (by rfl) (by rfl))
    fun t ⟨⟨h1', hm⟩, k⟩ => ⟨⟨?_, by rw [hm, hm₅, hm₄, hm₃, hm₂, hm₁, hm₀]⟩, (kk.trans k).mono (by decide)⟩
  have hv : (t.gpr .t1).toNat = (2 ^ 64 - (t₅.gpr .s0).toNat % 2 ^ 64) % 2 ^ 64 := by
    rw [h1', BitVec.toNat_sub, show (0 : BitVec 64).toNat = 0 from rfl]
    have := (t₅.gpr .s0).isLt
    omega_arith
  rw [hv]
  exact neg_inv64 e₅

/-! ## Montgomery squares -/

/-- The registers a square writes. -/
def sqRegs : List Reg := [.a3, .a4] ++ tailRegs

/-- `r2Sq`: `x := x² R⁻¹ mod n`, `x` in array 1. -/
theorem r2Sq_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h2 : s.gpr .a2 = off B (slot w 1)) (h5 : s.gpr .a5 = off B (slot w 2))
    (h6 : s.gpr .a6 = off B (slot w 3)) (h7 : s.gpr .a7 = off B (slot w 0))
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hinv : ((Mont.word s.mem B (slot w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hB : wordsVal s.mem B (slot w 1) w < wordsVal s.mem B (slot w 0) w) :
    WP isa r2Sq s fun t =>
      (wordsVal t.mem B (slot w 1) w < wordsVal s.mem B (slot w 0) w ∧
        wordsVal t.mem B (slot w 1) w * 2 ^ (64 * w) % wordsVal s.mem B (slot w 0) w =
          wordsVal s.mem B (slot w 1) w * wordsVal s.mem B (slot w 1) w % wordsVal s.mem B (slot w 0) w ∧
        Arrays B w [2, 3, 1] s.mem t.mem) ∧
      Keep sqRegs s t := by
  unfold r2Sq
  refine WP.seq (WP.mono (WP.keep [.a3, .a4] (Q := fun t => t.gpr .a3 = off B (slot w 1) ∧
    t.gpr .a4 = off B (slot w 1) ∧ t.mem = s.mem) (by brun [h2, BitVec.add_zero]) (by rfl) (by rfl))
    fun t₀ ⟨⟨a3, a4, m0⟩, k0⟩ => ?_)
  rw [← m0] at hinv hB ⊢
  refine WP.mono (tail_ok (hs.congr k0.2.2) (o := 1) (a := 1) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hw2 hw' hZ ((k0.gpr (by decide)).trans h2) a3 a4
    ((k0.gpr (by decide)).trans h5) ((k0.gpr (by decide)).trans h6) ((k0.gpr (by decide)).trans h7)
    ((k0.gpr (by decide)).trans ht0) (by rw [k0.gpr (by decide)]; exact hinv) hB)
    fun t ⟨h, k⟩ => ⟨h, (k0.trans k).mono (by decide)⟩

/-- Arrays 1–3 are `24 (w + 2)` bytes from array 1's offset. -/
theorem arrays_outside {B : Addr} {w : Nat} {m m' : Mem} (h : Arrays B w [2, 3, 1] m m') :
    Outside B (slot w 1) (24 * (w + 2)) m m' := fun x hx => h x fun j hj => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  unfold slot hdrBytes at hx ⊢
  rcases hj with rfl | rfl | rfl <;> omega

theorem sq_step {A S X c R N : Nat} (hR : Nat.Coprime R N) (hA : A % N = X ^ c * R % N)
    (hS : S * R % N = A * A % N) : S % N = X ^ (2 * c) * R % N := by
  refine VG.Proof.Bignum.mont_cancel hR ?_
  rw [hS, Nat.mul_mod, hA, ← Nat.mul_mod, Nat.two_mul, Nat.pow_add]
  congr 1
  grind

/-- What holds between the squares, with `x ≡ 2^e R (mod N)`. -/
structure SqI (s : State) (B : Addr) (Z w N e : Nat) (t : State) : Prop where
  scr : Scr t B Z
  a2 : t.gpr .a2 = off B (slot w 1)
  a5 : t.gpr .a5 = off B (slot w 2)
  a6 : t.gpr .a6 = off B (slot w 3)
  a7 : t.gpr .a7 = off B (slot w 0)
  t0 : t.gpr .t0 = BitVec.ofNat 64 w
  inv : ((Mont.word t.mem B (slot w 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
  n : wordsVal t.mem B (slot w 0) w = N
  lt : wordsVal t.mem B (slot w 1) w < N
  x : wordsVal t.mem B (slot w 1) w % N = 2 ^ e * 2 ^ (64 * w) % N
  out : Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem
  keep : Keep sqRegs s t

theorem sqI_step {s t : State} {B : Addr} {Z w N e : Nat} (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z)
    (hodd : N % 2 = 1) (h : SqI s B Z w N e t) : WP isa r2Sq t (SqI s B Z w N (2 * e)) := by
  have hnw := h.scr.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  refine WP.mono (r2Sq_ok h.scr hw2 hw' hZ h.a2 h.a5 h.a6 h.a7 h.t0 h.inv (by rw [h.n]; exact h.lt))
    fun u ⟨⟨ul, ue, uo⟩, k⟩ => ?_
  rw [h.n] at ul ue
  have uo' := arrays_outside uo
  have n0 : wordsVal u.mem B (slot w 0) w = N := by rw [Outside.wordsVal uo' (by omega) (by omega), h.n]
  have w0 : Mont.word u.mem B (slot w 0) = Mont.word t.mem B (slot w 0) := Outside.word uo' (by omega) (by omega)
  have g : ∀ r ∈ [Reg.a2, .a5, .a6, .a7, .t0, .t1], u.gpr r = t.gpr r := fun r hr =>
    k.gpr (by revert r hr; decide)
  exact ⟨h.scr.congr k.2.2, (g .a2 (by decide)).trans h.a2, (g .a5 (by decide)).trans h.a5,
    (g .a6 (by decide)).trans h.a6, (g .a7 (by decide)).trans h.a7, (g .t0 (by decide)).trans h.t0,
    by rw [g .t1 (by decide), w0]; exact h.inv, n0, ul, sq_step hR h.x ue, Outside.trans h.out uo',
    Keep.trans' h.keep (k.mono (by decide))⟩

/-- `r2Squares`, with an odd `N` in array 0, `-N⁻¹ mod 2⁶⁴` in `t1` and `x ≡
2^w R (mod N)` below `N` in array 1: `x := 2^(128 w) mod N`, changing only
arrays 1–3. -/
theorem r2Squares_ok {s : State} {B : Addr} {Z w N : Nat} (hs : Scr s B Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h2 : s.gpr .a2 = off B (slot w 1)) (h5 : s.gpr .a5 = off B (slot w 2))
    (h6 : s.gpr .a6 = off B (slot w 3)) (h7 : s.gpr .a7 = off B (slot w 0))
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hinv : ((Mont.word s.mem B (slot w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hN : wordsVal s.mem B (slot w 0) w = N) (hodd : N % 2 = 1)
    (hlt : wordsVal s.mem B (slot w 1) w < N)
    (hx : wordsVal s.mem B (slot w 1) w % N = 2 ^ w * 2 ^ (64 * w) % N) :
    WP isa r2Squares s fun t =>
      wordsVal t.mem B (slot w 1) w = 2 ^ (128 * w) % N ∧
      Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧ Keep sqRegs s t := by
  have I0 : SqI s B Z w N w s := ⟨hs, h2, h5, h6, h7, ht0, hinv, hN, hlt, hx, Outside.refl _ _ _ _, Keep.refl _ _⟩
  have st := fun {e : Nat} {t : State} (h : SqI s B Z w N e t) => sqI_step hw2 hw' hZ hodd h
  refine WP.seq (WP.mono (st I0) fun u₁ I1 => WP.seq (WP.mono (st I1) fun u₂ I2 => WP.seq (WP.mono (st I2)
    fun u₃ I3 => WP.seq (WP.mono (st I3) fun u₄ I4 => WP.seq (WP.mono (st I4) fun u₅ I5 =>
      WP.mono (st I5) fun t I6 => ?_)))))
  refine ⟨?_, I6.out, I6.keep⟩
  rw [← Nat.mod_eq_of_lt I6.lt, I6.x, show 2 * (2 * (2 * (2 * (2 * (2 * w))))) = 64 * w by omega,
    ← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega]

/-! ## `R² mod n` -/

/-- The registers `r2` may write. -/
def r2Regs : List Reg := [.a0, .a1, .a3, .a4, .t1, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4]

/-- `r2`: `x := R² mod n = 2^(128 w) mod n` in array 1, for an odd `n` of `w`
words, at least `2^(64 (w - 1))`, in array 0, changing only arrays 1–3. -/
theorem r2_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (h2 : s.gpr .a2 = off B (slot w 1)) (h5 : s.gpr .a5 = off B (slot w 2)) (h6 : s.gpr .a6 = off B (slot w 3))
    (h7 : s.gpr .a7 = off B (slot w 0)) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z)
    (hN : 2 ^ (64 * (w - 1)) ≤ wordsVal s.mem B (slot w 0) w) (hodd : wordsVal s.mem B (slot w 0) w % 2 = 1) :
    WP isa Impl.Bignum.RISCV64.Precompute.r2 s fun t =>
      wordsVal t.mem B (slot w 1) w = 2 ^ (128 * w) % wordsVal s.mem B (slot w 0) w ∧
      Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧ Keep r2Regs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hlow : (Mont.word s.mem B (slot w 0)).toNat % 2 = 1 := by
    rw [fios_wordsVal_pred _ _ _ (show 1 ≤ w by omega)] at hodd
    omega
  generalize hNd : wordsVal s.mem B (slot w 0) w = N at hN hodd ⊢
  replace hN : 2 ^ (64 * (w - 1)) < N := Nat.lt_of_le_of_ne hN fun h => by
    rw [← h, show 64 * (w - 1) = (64 * (w - 1) - 1) + 1 by omega, Nat.pow_succ, Nat.mul_mod_left] at hodd
    exact absurd hodd (by decide)
  have hN0 : 0 < N := by omega
  unfold Impl.Bignum.RISCV64.Precompute.r2
  -- The doublings.
  refine WP.seq (WP.mono (r2HiDbl_ok hs h5 h6 h7 h2 ht0 hw hw' (by omega) hNd hN) fun s₃ ⟨x3, o3, k3⟩ => ?_)
  have n3 : wordsVal s₃.mem B (slot w 0) w = N := by rw [Outside.wordsVal o3 (by omega) (by omega), hNd]
  have w3 : Mont.word s₃.mem B (slot w 0) = Mont.word s.mem B (slot w 0) := Outside.word o3 (by omega) (by omega)
  -- `-n⁻¹ mod 2⁶⁴`.
  refine WP.seq (WP.mono (minv_ok (hs.congr k3.2.2) ((k3.gpr (by decide)).trans h7) (slot_al8 w 0) (by omega)
    (by rw [w3]; exact hlow)) fun s₄ ⟨⟨i4, m4⟩, k4⟩ => ?_)
  have k34 := k3.trans k4
  -- The squares.
  rw [← m4] at x3 n3 w3
  refine WP.mono (r2Squares_ok (N := N) (hs.congr k34.2.2) hw hw' hZ ((k34.gpr (by decide)).trans h2)
    ((k34.gpr (by decide)).trans h5) ((k34.gpr (by decide)).trans h6) ((k34.gpr (by decide)).trans h7)
    ((k34.gpr (by decide)).trans ht0) (by rw [m4]; exact i4) n3 hodd
    (by rw [x3]; exact Nat.mod_lt _ hN0) (by rw [x3, Nat.mod_mod, Nat.pow_add]))
    fun t ⟨tx, to, tk⟩ => ⟨tx, Outside.trans (by rw [m4]; exact o3) to, (k34.trans tk).mono (by decide)⟩

/-! ## Montgomery squares by `sqrTail` -/

/-- The registers a square by `sqrTail` writes. -/
def sqSRegs : List Reg := [.a3] ++ sqrRegs

/-- `r2SqS`: `x := x² R⁻¹ mod n`, `x` in array 1, `sqrTail`'s temporary
array 4. -/
theorem r2SqS_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h2 : s.gpr .a2 = off B (slot w 1)) (h5 : s.gpr .a5 = off B (slot w 2))
    (h6 : s.gpr .a6 = off B (slot w 4)) (h7 : s.gpr .a7 = off B (slot w 0))
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hinv : ((Mont.word s.mem B (slot w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hB : wordsVal s.mem B (slot w 1) w < wordsVal s.mem B (slot w 0) w) :
    WP isa r2SqS s fun t =>
      (wordsVal t.mem B (slot w 1) w < wordsVal s.mem B (slot w 0) w ∧
        wordsVal t.mem B (slot w 1) w * 2 ^ (64 * w) % wordsVal s.mem B (slot w 0) w =
          wordsVal s.mem B (slot w 1) w * wordsVal s.mem B (slot w 1) w % wordsVal s.mem B (slot w 0) w ∧
        Arrays B w [2, 3, 4, 1] s.mem t.mem) ∧
      Keep sqSRegs s t := by
  unfold r2SqS
  refine WP.seq (WP.mono (WP.keep [.a3] (Q := fun t => t.gpr .a3 = off B (slot w 1) ∧ t.mem = s.mem)
    (by brun [h2, BitVec.add_zero]) (by rfl) (by rfl)) fun t₀ ⟨⟨a3, m0⟩, k0⟩ => ?_)
  rw [← m0] at hinv hB ⊢
  refine WP.mono (sqrTail_ok (hs.congr k0.2.2) (o := 1) (a := 1) (p := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' hZ
    ((k0.gpr (by decide)).trans h2) a3 ((k0.gpr (by decide)).trans h5) ((k0.gpr (by decide)).trans h6)
    ((k0.gpr (by decide)).trans h7) ((k0.gpr (by decide)).trans ht0) (by rw [k0.gpr (by decide)]; exact hinv) hB)
    fun t ⟨h, k⟩ => ⟨h, (k0.trans k).mono (by decide)⟩

/-- Arrays 1–4 are `32 (w + 2)` bytes from array 1's offset. -/
theorem arrays4_outside {B : Addr} {w : Nat} {m m' : Mem} (h : Arrays B w [2, 3, 4, 1] m m') :
    Outside B (slot w 1) (32 * (w + 2)) m m' := fun x hx => h x fun j hj => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  unfold slot hdrBytes at hx ⊢
  rcases hj with rfl | rfl | rfl | rfl <;> omega

/-- What holds between the squares by `sqrTail`, with `x ≡ 2^e R (mod N)`. -/
structure SqS (s : State) (B : Addr) (Z w N e : Nat) (t : State) : Prop where
  scr : Scr t B Z
  a2 : t.gpr .a2 = off B (slot w 1)
  a5 : t.gpr .a5 = off B (slot w 2)
  a6 : t.gpr .a6 = off B (slot w 4)
  a7 : t.gpr .a7 = off B (slot w 0)
  t0 : t.gpr .t0 = BitVec.ofNat 64 w
  inv : ((Mont.word t.mem B (slot w 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
  n : wordsVal t.mem B (slot w 0) w = N
  lt : wordsVal t.mem B (slot w 1) w < N
  x : wordsVal t.mem B (slot w 1) w % N = 2 ^ e * 2 ^ (64 * w) % N
  out : Outside B (slot w 1) (32 * (w + 2)) s.mem t.mem
  keep : Keep (.a6 :: sqSRegs) s t

theorem sqS_step {s t : State} {B : Addr} {Z w N e : Nat} (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z)
    (hodd : N % 2 = 1) (h : SqS s B Z w N e t) : WP isa r2SqS t (SqS s B Z w N (2 * e)) := by
  have hnw := h.scr.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  refine WP.mono (r2SqS_ok h.scr hw2 hw' hZ h.a2 h.a5 h.a6 h.a7 h.t0 h.inv (by rw [h.n]; exact h.lt))
    fun u ⟨⟨ul, ue, uo⟩, k⟩ => ?_
  rw [h.n] at ul ue
  have uo' := arrays4_outside uo
  have n0 : wordsVal u.mem B (slot w 0) w = N := by rw [Outside.wordsVal uo' (by omega) (by omega), h.n]
  have w0 : Mont.word u.mem B (slot w 0) = Mont.word t.mem B (slot w 0) := Outside.word uo' (by omega) (by omega)
  have g : ∀ r ∈ [Reg.a2, .a5, .a6, .a7, .t0, .t1], u.gpr r = t.gpr r := fun r hr =>
    k.gpr (by revert r hr; decide)
  exact ⟨h.scr.congr k.2.2, (g .a2 (by decide)).trans h.a2, (g .a5 (by decide)).trans h.a5,
    (g .a6 (by decide)).trans h.a6, (g .a7 (by decide)).trans h.a7, (g .t0 (by decide)).trans h.t0,
    by rw [g .t1 (by decide), w0]; exact h.inv, n0, ul, sq_step hR h.x ue, Outside.trans h.out uo',
    Keep.trans' h.keep (k.mono (by decide))⟩

/-- `a6 := a6 + 8 w + 16`, through `s0`: from array 3 to array 4. -/
theorem a6Up_ok {s : State} {B : Addr} {w : Nat} (h6 : s.gpr .a6 = off B (slot w 3))
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) :
    WP isa (.block [.shift .sll .d .s0 .t0 3, .addi .s0 .s0 16, .add .a6 .a6 .s0]) s fun t =>
      (t.gpr .a6 = off B (slot w 4) ∧ t.mem = s.mem) ∧ Keep [.s0, .a6] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [h6, ht0]
  simp only [off]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  unfold slot hdrBytes
  omega_arith

/-- `r2SquaresS`, as `r2Squares_ok` with `a6` at array 3: `x := 2^(128 w) mod N`,
changing only arrays 1–4 (and `a6`, now at array 4). -/
theorem r2SquaresS_ok {s : State} {B : Addr} {Z w N : Nat} (hs : Scr s B Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h2 : s.gpr .a2 = off B (slot w 1)) (h5 : s.gpr .a5 = off B (slot w 2))
    (h6 : s.gpr .a6 = off B (slot w 3)) (h7 : s.gpr .a7 = off B (slot w 0))
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hinv : ((Mont.word s.mem B (slot w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hN : wordsVal s.mem B (slot w 0) w = N) (hodd : N % 2 = 1)
    (hlt : wordsVal s.mem B (slot w 1) w < N)
    (hx : wordsVal s.mem B (slot w 1) w % N = 2 ^ w * 2 ^ (64 * w) % N) :
    WP isa r2SquaresS s fun t =>
      wordsVal t.mem B (slot w 1) w = 2 ^ (128 * w) % N ∧
      Outside B (slot w 1) (32 * (w + 2)) s.mem t.mem ∧ Keep (.a6 :: sqSRegs) s t := by
  unfold r2SquaresS
  refine WP.seq (WP.mono (a6Up_ok h6 ht0) fun s₀ ⟨⟨a6', m0⟩, k0⟩ => ?_)
  have g : ∀ r ∈ [Reg.a2, .a5, .a7, .t0, .t1], s₀.gpr r = s.gpr r := fun r hr =>
    k0.gpr (by revert r hr; decide)
  have I0 : SqS s B Z w N w s₀ := ⟨hs.congr k0.2.2, (g .a2 (by decide)).trans h2, (g .a5 (by decide)).trans h5,
    a6', (g .a7 (by decide)).trans h7, (g .t0 (by decide)).trans ht0,
    by rw [g .t1 (by decide), m0]; exact hinv, by rw [m0]; exact hN, by rw [m0]; exact hlt,
    by rw [m0]; exact hx, by rw [m0]; exact Outside.refl _ _ _ _, k0.mono (by decide)⟩
  have st := fun {e : Nat} {t : State} (h : SqS s B Z w N e t) => sqS_step hw2 hw' hZ hodd h
  refine WP.seq (WP.mono (st I0) fun u₁ I1 => WP.seq (WP.mono (st I1) fun u₂ I2 => WP.seq (WP.mono (st I2)
    fun u₃ I3 => WP.seq (WP.mono (st I3) fun u₄ I4 => WP.seq (WP.mono (st I4) fun u₅ I5 =>
      WP.mono (st I5) fun t I6 => ?_)))))
  refine ⟨?_, I6.out, I6.keep⟩
  rw [← Nat.mod_eq_of_lt I6.lt, I6.x, show 2 * (2 * (2 * (2 * (2 * (2 * w))))) = 64 * w by omega,
    ← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega]

/-! ## `n`'s leading zeros -/

theorem exec_sllReg {s : State} {d n m : Reg} :
    exec (.shiftReg .sll .d d n m) s = some (s.write d (s.gpr n <<< ((s.gpr m).toNat % 64))) := rfl

/-- `(x >>> 63) ^^^ 1` is 1 when `x`'s top bit is clear, else 0. -/
theorem topClear (x : BitVec 64) :
    ((x >>> 63) ^^^ 1).toNat = if x.toNat < 2 ^ 63 then 1 else 0 := by
  have h : (x >>> 63).toNat = x.toNat / 2 ^ 63 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hx := x.isLt
  by_cases hc : x.toNat < 2 ^ 63
  · have : x >>> 63 = 0 := BitVec.eq_of_toNat_eq (by rw [h]; show x.toNat / 2 ^ 63 = 0; omega)
    rw [this]; simp only [hc, ↓reduceIte]; rfl
  · have : x >>> 63 = 1 := BitVec.eq_of_toNat_eq (by rw [h]; show x.toNat / 2 ^ 63 = 1; omega)
    rw [this]; simp only [hc, ↓reduceIte]; rfl

/-- What `lz` keeps after `j` steps, from the top word `T`: `s0 = T 2^z`, `a1 = z`. -/
def LzI (s : State) (T : Nat) (j : Nat) (t : State) : Prop :=
  ∃ z, (t.gpr .s0).toNat = T * 2 ^ z ∧ t.gpr .a1 = BitVec.ofNat 64 z ∧ z ≤ j ∧
    (z < j → 2 ^ 63 ≤ T * 2 ^ z) ∧ t.mem = s.mem ∧ Keep [.s0, .s1, .a1, .t5] s t

theorem lzStep_ok {s t : State} {T j : Nat} (h : LzI s T j t) :
    WP isa (.block (lzStep ++ ([.addi .t5 .t5 (-1)] : List Instr))) t fun t' =>
      LzI s T (j + 1) t' ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1 := by
  obtain ⟨z, h0, h1, hz, hlt, hm, hk⟩ := h
  have hT := (t.gpr .s0).isLt
  unfold lzStep
  refine WP.mono (WP.keep [.s0, .s1, .a1, .t5] (Q := fun u =>
      (u.gpr .s0 = t.gpr .s0 <<< (((t.gpr .s0 >>> 63) ^^^ 1).toNat % 64)) ∧
      u.gpr .a1 = t.gpr .a1 + ((t.gpr .s0 >>> 63) ^^^ 1) ∧ u.mem = t.mem ∧
      u.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1)
    (by brun [exec_sllReg]; exact ⟨rfl, rfl⟩) (by rfl) (by rfl)) fun u ⟨⟨u0, u1, um, u5⟩, ku⟩ => ⟨?_, u5⟩
  have hc := topClear (t.gpr .s0)
  by_cases c : (t.gpr .s0).toNat < 2 ^ 63
  · simp only [c, ↓reduceIte] at hc
    refine ⟨z + 1, ?_, ?_, by omega, fun _ => ?_, by rw [um, hm], (hk.trans ku).mono (by decide)⟩
    · rw [u0, hc, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, h0, show 1 % 64 = 1 from rfl, Nat.pow_one,
        show (2 : Nat) ^ (z + 1) = 2 ^ z * 2 from Nat.pow_succ .., ← Nat.mul_assoc]
      rw [h0] at c
      exact Nat.mod_eq_of_lt (by omega)
    · rw [u1, h1]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, hc, BitVec.toNat_ofNat]
      omega
    · rw [h0] at c
      exact absurd (hlt (by omega)) (by omega)
  · simp only [c, ↓reduceIte] at hc
    refine ⟨z, ?_, ?_, by omega, fun _ => by rw [← h0]; omega, by rw [um, hm], (hk.trans ku).mono (by decide)⟩
    · rw [u0, hc, show 0 % 64 = 0 from rfl, BitVec.shiftLeft_zero]; exact h0
    · have hz0 : (t.gpr .s0 >>> 63 ^^^ 1) = 0 := BitVec.eq_of_toNat_eq (by rw [hc]; rfl)
      rw [u1, hz0, h1]; exact BitVec.add_zero _

theorem exec_li_zero' {s : State} {d : Reg} : exec (.li d 0) s = some (s.write d (BitVec.ofNat 64 0)) := by
  rw [exec_li (by decide)]; rfl

theorem exec_li_63 {s : State} {d : Reg} : exec (.li d 63) s = some (s.write d (BitVec.ofNat 64 63)) := by
  rw [exec_li (by decide)]; rfl

/-- `n`'s leading zeros from its top word `T > 0`: `63 - log₂ T`. -/
def zOf (T : Nat) : Nat := 63 - Nat.log2 T

theorem zOf_eq {T z : Nat} (hT : 0 < T) (h1 : 2 ^ 63 ≤ T * 2 ^ z) (h2 : T * 2 ^ z < 2 ^ 64) :
    z = zOf T ∧ 2 ^ Nat.log2 T ≤ T ∧ T < 2 ^ (Nat.log2 T + 1) ∧ Nat.log2 T + z = 63 := by
  have l1 := Nat.log2_self_le (Nat.pos_iff_ne_zero.mp hT)
  have l2 := Nat.lt_log2_self (n := T)
  have a : 2 ^ (Nat.log2 T + z) < 2 ^ 64 := by
    rw [Nat.pow_add]; exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ l1) h2
  have b : 2 ^ 63 < 2 ^ (Nat.log2 T + 1 + z) := by
    rw [Nat.pow_add]; exact Nat.lt_of_le_of_lt h1 (Nat.mul_lt_mul_of_pos_right l2 (Nat.two_pow_pos _))
  have a' := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp a
  have b' := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp b
  exact ⟨by unfold zOf; omega, l1, l2, by omega⟩

/-- `lz`: `a1 := zOf T` for `n`'s top word `T > 0` (word `w - 1` of array 0). -/
theorem lz_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (h7 : s.gpr .a7 = off B (slot w 0))
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hZ : slot w 0 + 8 * w ≤ Z)
    (hT : 0 < (Mont.word s.mem B (slot w 0 + 8 * (w - 1))).toNat) :
    WP isa lz s fun t =>
      (t.gpr .a1 = BitVec.ofNat 64 (zOf (Mont.word s.mem B (slot w 0 + 8 * (w - 1))).toNat) ∧
        2 ^ 63 ≤ (Mont.word s.mem B (slot w 0 + 8 * (w - 1))).toNat *
          2 ^ zOf (Mont.word s.mem B (slot w 0 + 8 * (w - 1))).toNat ∧
        (Mont.word s.mem B (slot w 0 + 8 * (w - 1))).toNat *
          2 ^ zOf (Mont.word s.mem B (slot w 0 + 8 * (w - 1))).toNat < 2 ^ 64 ∧ t.mem = s.mem) ∧
        Keep [.t3, .s0, .s1, .a1, .t5] s t := by
  have hnw := hs.nowrap
  have al := slot_al8 w
  generalize hTd : (Mont.word s.mem B (slot w 0 + 8 * (w - 1))).toNat = T at hT ⊢
  have ea : BitVec.ofNat 64 w <<< 3 + off B (slot w 0) - BitVec.ofNat 64 8 = off B (slot w 0 + 8 * (w - 1)) := by
    simp only [off]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    have := B.isLt
    unfold slot hdrBytes at hZ ⊢
    omega
  have a0 := al 0
  unfold lz
  refine WP.seq (WP.mono (WP.keep [.t3, .s0, .a1, .t5] (Q := fun t => (t.gpr .s0).toNat = T ∧
      t.gpr .a1 = BitVec.ofNat 64 0 ∧ t.gpr .t5 = BitVec.ofNat 64 63 ∧ t.mem = s.mem)
    (by
      brun [exec_li_zero', exec_li_63, h7, ht0, ea, BitVec.add_zero,
        hs.ld (show slot w 0 + 8 * (w - 1) + 8 ≤ Z by omega),
        hs.al8 (show slot w 0 + 8 * (w - 1) + 8 ≤ Z by omega) (by omega)]
      exact hTd) (by rfl) (by rfl)) fun s₁ ⟨⟨i0, i1, i5, m1⟩, k1⟩ => ?_)
  refine WP.mono (wp_countdown (cnt := .t5) (N := 63) (by decide) (by decide) (LzI s₁ T)
    (fun j _ t h _ => lzStep_ok h) ⟨0, by rw [i0, Nat.pow_zero, Nat.mul_one], i1, Nat.le_refl _,
      fun h => absurd h (by omega), rfl, Keep.refl _ _⟩ i5) fun t ⟨z, h0, h1, hz, hlt, hm, hk⟩ => ?_
  have hb := (t.gpr .s0).isLt
  have hlo : 2 ^ 63 ≤ T * 2 ^ z := by
    rcases Nat.lt_or_ge z 63 with h | h
    · exact hlt h
    · have : z = 63 := by omega
      subst this
      have : T = 1 := by
        rw [h0] at hb
        have : T * 2 ^ 63 < 1 * 2 ^ 64 := by omega
        have : T < 2 := by omega
        omega
      subst this; omega
  obtain ⟨ez, -, -, -⟩ := zOf_eq hT hlo (by rw [← h0]; exact hb)
  subst ez
  exact ⟨⟨h1, hlo, by rw [← h0]; exact hb, by rw [hm, m1]⟩, (k1.trans hk).mono (by decide)⟩

/-- `1 <<< (63 - z)`, for `z ≤ 63`. -/
theorem topBit_val {z : Nat} (hz : z ≤ 63) :
    ((1 : BitVec 64) <<< ((BitVec.ofNat 64 63 - BitVec.ofNat 64 z).toNat % 64)).toNat = 2 ^ (63 - z) := by
  have e : (BitVec.ofNat 64 63 - BitVec.ofNat 64 z).toNat % 64 = 63 - z := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  rw [e, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show BitVec.toNat (1 : BitVec 64) = 1 from rfl, Nat.one_mul]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))

/-- `r2TopBit`, for `z ≤ 63` in `a1`: `x := 2^(64 (w - 1) + 63 - z)` in array 1 and
`a1 := w + 1 + z`. -/
theorem r2TopBit_ok {s : State} {B : Addr} {Z w z : Nat} (hs : Scr s B Z)
    (h2 : s.gpr .a2 = off B (slot w 1)) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w) (h1 : s.gpr .a1 = BitVec.ofNat 64 z)
    (hz : z ≤ 63) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 1 + 8 * w ≤ Z) :
    WP isa r2TopBit s fun t =>
      (wordsVal t.mem B (slot w 1) w = 2 ^ (64 * (w - 1) + (63 - z)) ∧
        t.gpr .a1 = BitVec.ofNat 64 (w + 1 + z) ∧ Outside B (slot w 1) (8 * w) s.mem t.mem) ∧
        Keep [.s0, .s1, .t3, .t5, .a1] s t := by
  have hnw := hs.nowrap
  have al := slot_al8 w
  unfold r2TopBit
  refine WP.seq (WP.mono (WP.keep [.t3] (Q := fun t => t.gpr .t3 = off B (slot w 1) ∧ t.mem = s.mem)
    (by brun [h2, BitVec.add_zero]) (by rfl) (by rfl)) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (hs.congr k1.2.2) a3 ((k1.gpr (by decide)).trans ht0) hw hw' (al 1) hZ)
    fun s₂ ⟨⟨_, hz', out2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  have ea : BitVec.ofNat 64 w <<< 3 + off B (slot w 1) - BitVec.ofNat 64 8 = off B (slot w 1 + 8 * (w - 1)) := by
    simp only [off]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    have := B.isLt
    unfold slot hdrBytes at hZ ⊢
    omega
  have hs₂ := hs.congr k12.2.2
  have al1 := al 1
  have a1₂ : s₂.gpr .a1 = BitVec.ofNat 64 z := (k12.gpr (by decide)).trans h1
  refine WP.mono (WP.keep [.s0, .s1, .t3, .a1] (Q := fun t =>
      t.mem = s₂.mem.writeW (off B (slot w 1 + 8 * (w - 1)))
        ((1 : BitVec 64) <<< ((BitVec.ofNat 64 63 - BitVec.ofNat 64 z).toNat % 64)) ∧
      t.gpr .a1 = BitVec.ofNat 64 z + BitVec.ofNat 64 w + BitVec.ofNat 64 1) (by
    brun [exec_li_63, r2_exec_li_one, exec_sllReg, a1₂, (k12.gpr (by decide)).trans ht0,
      (k12.gpr (by decide)).trans h2, ea, BitVec.add_zero,
      hs₂.st (show slot w 1 + 8 * (w - 1) + 8 ≤ Z by omega),
      hs₂.al8 (show slot w 1 + 8 * (w - 1) + 8 ≤ Z by omega) (by omega)]) (by rfl) (by rfl))
    fun t ⟨⟨tm, ta⟩, k3⟩ => ⟨⟨?_, ?_, ?_⟩, (k12.trans k3).mono (by decide)⟩
  · rw [tm, wordsVal_top _ _ _ hw, Mont.word_writeW_self, Outside.wordsVal (writeW_outside _ _ _ (by omega)) (by omega) (by omega),
      wordsVal_zero (fun i hi => hz' i (by omega)), topBit_val hz, Nat.zero_add, Nat.pow_add]
  · rw [ta]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · rw [tm, m1] at *
    exact Outside.trans out2 (Outside.mono (writeW_outside s₂.mem B (d := slot w 1 + 8 * (w - 1)) _ (by omega))
      (by omega) (by omega))

/-- `n`'s top word, word `w - 1` of array 0. -/
abbrev topW (m : Mem) (B : Addr) (w : Nat) : Nat := (Mont.word m B (slot w 0 + 8 * (w - 1))).toNat

/-- The top word of `N ≥ 2^(64 (w - 1))` is not zero. -/
theorem topW_pos {m : Mem} {B : Addr} {w : Nat} (hw : 1 ≤ w)
    (hN : 2 ^ (64 * (w - 1)) ≤ wordsVal m B (slot w 0) w) : 0 < topW m B w := by
  rw [wordsVal_top _ _ _ hw] at hN
  have := wordsVal_lt m B (slot w 0) (w - 1)
  unfold topW
  rcases Nat.eq_zero_or_pos (Mont.word m B (slot w 0 + 8 * (w - 1))).toNat with h | h
  · rw [h, Nat.mul_zero, Nat.add_zero] at hN; omega
  · exact h

/-- The registers `r2Rest` may write. -/
def r2RestRegs : List Reg := [.a0, .a1, .a3, .a6, .t1, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4]

/-- `r2Rest`, after `lz` (`a1 = zOf T`, `T` the top word): `x := R² mod n =
2^(128 w) mod n` in array 1, for an odd `n` of `w` words, at least
`2^(64 (w - 1))`, in array 0, changing only arrays 1–4. -/
theorem r2Rest_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (h2 : s.gpr .a2 = off B (slot w 1)) (h5 : s.gpr .a5 = off B (slot w 2)) (h6 : s.gpr .a6 = off B (slot w 3))
    (h7 : s.gpr .a7 = off B (slot w 0)) (ht0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (h1 : s.gpr .a1 = BitVec.ofNat 64 (zOf (topW s.mem B w)))
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z)
    (hN : 2 ^ (64 * (w - 1)) ≤ wordsVal s.mem B (slot w 0) w) (hodd : wordsVal s.mem B (slot w 0) w % 2 = 1) :
    WP isa r2Rest s fun t =>
      wordsVal t.mem B (slot w 1) w = 2 ^ (128 * w) % wordsVal s.mem B (slot w 0) w ∧
      Outside B (slot w 1) (32 * (w + 2)) s.mem t.mem ∧ Keep r2RestRegs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hlow : (Mont.word s.mem B (slot w 0)).toNat % 2 = 1 := by
    rw [fios_wordsVal_pred _ _ _ (show 1 ≤ w by omega)] at hodd
    omega
  have hT := topW_pos (by omega) hN
  generalize hTd : topW s.mem B w = T at hT h1
  -- `T`'s bounds: `2^(63 - z) ≤ T`.
  have hb1 : 2 ^ 63 ≤ T * 2 ^ (zOf T) := by
    have l1 := Nat.log2_self_le (Nat.pos_iff_ne_zero.mp hT)
    have l2 := Nat.lt_log2_self (n := T)
    have hl : Nat.log2 T < 64 := by
      have : T < 2 ^ 64 := by rw [← hTd]; exact BitVec.isLt _
      have := Nat.lt_of_le_of_lt l1 this
      exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp this
    unfold zOf
    calc 2 ^ 63 = 2 ^ Nat.log2 T * 2 ^ (63 - Nat.log2 T) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ T * 2 ^ (63 - Nat.log2 T) := Nat.mul_le_mul_right _ l1
  have hb2 : T * 2 ^ (zOf T) < 2 ^ 64 := by
    have l2 := Nat.lt_log2_self (n := T)
    unfold zOf
    have hl : Nat.log2 T < 64 := by
      have l1 := Nat.log2_self_le (Nat.pos_iff_ne_zero.mp hT)
      have : T < 2 ^ 64 := by rw [← hTd]; exact BitVec.isLt _
      exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (Nat.lt_of_le_of_lt l1 this)
    calc T * 2 ^ (63 - Nat.log2 T) < 2 ^ (Nat.log2 T + 1) * 2 ^ (63 - Nat.log2 T) :=
          Nat.mul_lt_mul_of_pos_right l2 (Nat.two_pow_pos _)
      _ = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega
  obtain ⟨-, l1, -, lz⟩ := zOf_eq hT hb1 hb2
  generalize hz : zOf T = z at h1 hb1 hb2 lz
  generalize hNd : wordsVal s.mem B (slot w 0) w = N at hN hodd ⊢
  -- `x₀ = 2^(64 (w - 1) + 63 - z) < N`.
  have hx0 : 2 ^ (64 * (w - 1) + (63 - z)) < N := by
    have hle : 2 ^ (64 * (w - 1) + (63 - z)) ≤ N := by
      rw [← hNd, wordsVal_top _ _ _ (show 1 ≤ w by omega), Nat.pow_add]
      have : 2 ^ (63 - z) ≤ T := by rw [show 63 - z = Nat.log2 T by omega]; exact l1
      rw [← hTd] at this
      exact Nat.le_add_left_of_le (Nat.mul_le_mul_left _ this)
    refine Nat.lt_of_le_of_ne hle fun h => ?_
    rw [← h, show 64 * (w - 1) + (63 - z) = (64 * (w - 1) + (63 - z) - 1) + 1 by omega, Nat.pow_succ,
      Nat.mul_mod_left] at hodd
    exact absurd hodd (by decide)
  have hN0 : 0 < N := by omega
  unfold r2Rest
  refine WP.seq (WP.mono (r2TopBit_ok hs h2 ht0 h1 (by omega) (by omega) hw' (by omega))
    fun s₁ ⟨⟨x1, a1, o1⟩, k1⟩ => ?_)
  have O1 : Outside B (slot w 1) (24 * (w + 2)) s.mem s₁.mem := Outside.mono o1 (Nat.le_refl _) (by omega)
  refine WP.seq (WP.mono (r2Dbl_ok (N := N) (a := 64 * (w - 1) + (63 - z)) (M := w + 1 + z) (hs.congr k1.2.2)
    ((k1.gpr (by decide)).trans h5) ((k1.gpr (by decide)).trans h6) ((k1.gpr (by decide)).trans h7)
    ((k1.gpr (by decide)).trans h2) ((k1.gpr (by decide)).trans ht0) (by omega) hw' (by omega)
    (by rw [Outside.wordsVal O1 (by omega) (by omega), hNd])
    hN0 (by rw [x1]; exact (Nat.mod_eq_of_lt hx0).symm) a1 (by omega) (by omega))
    fun s₃ ⟨x3, o3, k3⟩ => ?_)
  have k13 := k1.trans k3
  have O3 : Outside B (slot w 1) (24 * (w + 2)) s.mem s₃.mem := Outside.trans O1 o3
  have n3 : wordsVal s₃.mem B (slot w 0) w = N := by rw [Outside.wordsVal O3 (by omega) (by omega), hNd]
  have w3 : Mont.word s₃.mem B (slot w 0) = Mont.word s.mem B (slot w 0) := Outside.word O3 (by omega) (by omega)
  rw [show 64 * (w - 1) + (63 - z) + (w + 1 + z) = w + 64 * w by omega] at x3
  refine WP.seq (WP.mono (minv_ok (hs.congr k13.2.2) ((k13.gpr (by decide)).trans h7) (slot_al8 w 0) (by omega)
    (by rw [w3]; exact hlow)) fun s₄ ⟨⟨i4, m4⟩, k4⟩ => ?_)
  have k34 := k13.trans k4
  rw [← m4] at x3 n3 w3
  refine WP.mono (r2SquaresS_ok (N := N) (hs.congr k34.2.2) hw hw' hZ ((k34.gpr (by decide)).trans h2)
    ((k34.gpr (by decide)).trans h5) ((k34.gpr (by decide)).trans h6) ((k34.gpr (by decide)).trans h7)
    ((k34.gpr (by decide)).trans ht0) (by rw [m4]; exact i4) n3 hodd
    (by rw [x3]; exact Nat.mod_lt _ hN0) (by rw [x3, Nat.mod_mod, Nat.pow_add]))
    fun t ⟨tx, to, tk⟩ => ⟨tx, Outside.trans (Outside.mono (by rw [m4]; exact O3) (Nat.le_refl _) (by omega)) to,
      (k34.trans tk).mono (by decide)⟩

end VG.Proof.Bignum.RISCV64
