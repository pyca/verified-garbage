module

public import VerifiedGarbage.Proof.Bignum.RISCV64.Double64
public import VerifiedGarbage.Proof.Bignum.RISCV64.MontCore
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

end VG.Proof.Bignum.RISCV64
