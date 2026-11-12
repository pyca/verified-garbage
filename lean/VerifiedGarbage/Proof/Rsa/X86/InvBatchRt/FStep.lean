module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FBatch
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Framework.Omega
public import Mathlib.Data.Int.ModEq
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Abs

/-! # The fused batches on i686: a batch

The state between batches: `f, g` and `d, e` as two's complement numbers of `n + 1` words
(`sval`) at one half of the interleaved elements (`FAt`), `p` at byte 16 of the `d, e`
elements. `batchF_ok`: a batch from one half to the other.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt.F

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass

/-! ## Two's complement over strided words -/

/-- The `n + 1` words at `b + sz w` as a two's complement number. -/
def sval (m : Mem) (W : Addr) (b sz n : Nat) : Int :=
  (sv m W b sz (n + 1) : Int) - if 2 ^ 31 ≤ VG.Proof.Mont.w32 m W (b + sz * n) then 2 ^ (32 * (n + 1)) else 0

theorem sv_top (m : Mem) (W : Addr) (b sz n : Nat) :
    sv m W b sz (n + 1) = sv m W b sz n + 2 ^ (32 * n) * VG.Proof.Mont.w32 m W (b + sz * n) := rfl

/-- The top bit of the top word is the number's: `2^(32 n + 31) ≤ sv`. -/
theorem top_iff (m : Mem) (W : Addr) (b sz n : Nat) :
    2 ^ 31 ≤ VG.Proof.Mont.w32 m W (b + sz * n) ↔ 2 ^ (32 * n) * 2 ^ 31 ≤ sv m W b sz (n + 1) := by
  rw [sv_top]
  have hl := sv_lt m W b sz n
  generalize sv m W b sz n = l at hl ⊢
  generalize VG.Proof.Mont.w32 m W (b + sz * n) = t
  generalize hK : 2 ^ (32 * n) = K at hl ⊢
  constructor
  · intro h; have := Nat.mul_le_mul_left K h; omega
  · intro h
    by_contra hc
    have : K * t ≤ K * (2 ^ 31 - 1) := Nat.mul_le_mul_left K (by omega)
    have : K * (2 ^ 31 - 1) = K * 2 ^ 31 - K := by rw [Nat.mul_sub, Nat.mul_one]
    have : K ≤ K * 2 ^ 31 := Nat.le_mul_of_pos_right K (by decide)
    omega

/-- The low word of the number. -/
theorem sval_low (m : Mem) (W : Addr) (b sz n : Nat) :
    (VG.Proof.Mont.w32 m W b : Int) ≡ sval m W b sz n [ZMOD 2 ^ 32] := by
  unfold sval Int.ModEq
  rw [sv_cons, show 32 * (n + 1) = 32 + 32 * n by omega, pow_add]
  generalize VG.Proof.Mont.w32 m W b = w
  generalize sv m W (b + sz) sz n = v
  split
  · have : ((w + 2 ^ 32 * v : Nat) : Int) - 2 ^ 32 * 2 ^ (32 * n) = (w : Int) + 2 ^ 32 * ((v : Int) - 2 ^ (32 * n)) := by
      push_cast; ring
    rw [this, Int.add_mul_emod_self_left]
  · have : ((w + 2 ^ 32 * v : Nat) : Int) - 0 = (w : Int) + 2 ^ 32 * (v : Int) := by push_cast; ring
    rw [this, Int.add_mul_emod_self_left]

/-- The sign mask of the top word is the number's. -/
theorem maskW_top (m : Mem) (W : Addr) (b sz n : Nat) :
    maskW (m.readW (off W (b + sz * n)) 32) = if sval m W b sz n < 0 then -1 else 0 := by
  unfold maskW sval
  have hlt := sv_lt m W b sz (n + 1)
  have ht := top_iff m W b sz n
  simp only [VG.Proof.Mont.w32] at ht ⊢
  have e : 2 ^ (32 * (n + 1)) = 2 ^ (32 * n) * 2 ^ 32 := by rw [show 32 * (n + 1) = 32 * n + 32 by omega, Nat.pow_add]
  have hK := Nat.two_pow_pos (32 * n)
  by_cases h : 2 ^ 31 ≤ (m.readW (off W (b + sz * n)) 32).toNat
  · have h2 := ht.mp h
    simp only [h, ↓reduceIte]
    have : (sv m W b sz (n + 1) : Int) < 2 ^ (32 * (n + 1)) := by exact_mod_cast hlt
    split
    · rfl
    · omega
  · have h2 : ¬ 2 ^ (32 * n) * 2 ^ 31 ≤ sv m W b sz (n + 1) := fun h' => h (ht.mpr h')
    simp only [h, ↓reduceIte]
    split
    · omega
    · rfl

/-- Words holding `X mod 2^(32 (n + 1))` hold `X` in two's complement, for `X` in range. -/
theorem sval_of_mod {m : Mem} {W : Addr} {b sz n : Nat} {X : Int}
    (h : sv m W b sz (n + 1) = (X % 2 ^ (32 * (n + 1))).toNat)
    (h1 : -(2 ^ (32 * n) * 2 ^ 31) ≤ X) (h2 : X < 2 ^ (32 * n) * 2 ^ 31) : sval m W b sz n = X := by
  have ht := top_iff m W b sz n
  have e : (2 : Int) ^ (32 * (n + 1)) = 2 ^ (32 * n) * 2 ^ 32 := by
    rw [show 32 * (n + 1) = 32 * n + 32 by omega, pow_add]
  have hK : (0 : Int) < 2 ^ (32 * n) := by positivity
  have hM : (0 : Int) < 2 ^ (32 * (n + 1)) := by positivity
  have r0 := Int.emod_nonneg X hM.ne'
  have hv : (sv m W b sz (n + 1) : Int) = X % 2 ^ (32 * (n + 1)) := by rw [h, Int.toNat_of_nonneg r0]
  unfold sval
  rcases Int.lt_or_le X 0 with hX | hX
  · have : X % 2 ^ (32 * (n + 1)) = X + 2 ^ (32 * (n + 1)) := by
      rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by rw [e] at *; nlinarith)]
    have top : 2 ^ 31 ≤ VG.Proof.Mont.w32 m W (b + sz * n) := by
      apply ht.mpr
      have : ((2 ^ (32 * n) * 2 ^ 31 : Nat) : Int) ≤ (sv m W b sz (n + 1) : Int) := by
        push_cast; rw [hv, this, e]; nlinarith
      exact_mod_cast this
    simp only [top, ↓reduceIte]; rw [hv, this]; ring
  · have : X % 2 ^ (32 * (n + 1)) = X := Int.emod_eq_of_lt hX (by rw [e]; nlinarith)
    have top : ¬ 2 ^ 31 ≤ VG.Proof.Mont.w32 m W (b + sz * n) := by
      intro h'
      have := ht.mp h'
      have : ((2 ^ (32 * n) * 2 ^ 31 : Nat) : Int) ≤ (sv m W b sz (n + 1) : Int) := by exact_mod_cast this
      push_cast at this; rw [hv, ‹X % _ = X›] at this; linarith
    simp only [top, ↓reduceIte]; rw [hv, this]; ring

/-! ## The rows' values -/

theorem top_addr (a sz n x : Nat) : a + sz * (n + 1) + x = a + sz + x + sz * n := by rw [Nat.mul_succ]; omega

theorem coef_sval (m : Mem) (W : Addr) (a sz n : Nat) (t : Term) :
    (m.readW (off W t.c) 32).toInt * (sv m W (a + sz + t.x) sz (n + 1) : Int) -
      2 ^ (32 * (n + 1)) * (if 2 ^ 31 ≤ VG.Proof.Mont.w32 m W (a + sz * (n + 1) + t.x)
        then (m.readW (off W t.c) 32).toInt else 0) =
      (m.readW (off W t.c) 32).toInt * sval m W (a + sz + t.x) sz n := by
  unfold sval
  rw [top_addr]
  split <;> ring

/-- Two signed terms: `c₁ x₁ + c₂ x₂`. -/
theorem rowT_two (m : Mem) (W : Addr) (a sz n : Nat) (t₁ t₂ : Term) :
    rowT m W a sz n [t₁, t₂] [t₁, t₂] =
      (m.readW (off W t₁.c) 32).toInt * sval m W (a + sz + t₁.x) sz n +
      (m.readW (off W t₂.c) 32).toInt * sval m W (a + sz + t₂.x) sz n := by
  rw [← coef_sval, ← coef_sval]
  simp only [rowT, rowA, topF, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

/-- Two signed terms and an unsigned one: `c₁ x₁ + c₂ x₂ + c₃ y`. -/
theorem rowT_three (m : Mem) (W : Addr) (a sz n : Nat) (t₁ t₂ t₃ : Term) :
    rowT m W a sz n [t₁, t₂, t₃] [t₁, t₂] =
      (m.readW (off W t₁.c) 32).toInt * sval m W (a + sz + t₁.x) sz n +
      (m.readW (off W t₂.c) 32).toInt * sval m W (a + sz + t₂.x) sz n +
      (m.readW (off W t₃.c) 32).toInt * (sv m W (a + sz + t₃.x) sz (n + 1) : Int) := by
  rw [← coef_sval, ← coef_sval]
  simp only [rowT, rowA, topF, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

/-! ## Reading through a row's writes -/

theorem RowWr.w32 {B : Addr} {A0 sz o n : Nat} {m m' : Mem} (h : RowWr B A0 sz o n m m') {d : Nat}
    (hd : ∀ j < n + 2, d + 4 ≤ A0 + o + sz * j ∨ A0 + o + sz * j + 4 ≤ d) (hp : d + 4 ≤ sP ∨ sP + 8 ≤ d)
    (hd' : d + 4 ≤ 2 ^ 64) : VG.Proof.Mont.w32 m' B d = VG.Proof.Mont.w32 m B d := by
  unfold VG.Proof.Mont.w32
  congr 1
  refine (Mem.readW_congr fun i hi => ?_).symm
  have hi' : i < 4 := by simpa using hi
  have e := ofs_off B (d := d) (i := i) (by omega)
  refine (h _ (fun j hj => ?_) ?_).symm
  · rw [e]; have := hd j hj; omega
  · rw [e]; omega

/-- A word of another region, or of another byte of the same elements, survives a row. -/
theorem RowWr.w32_apart {B : Addr} {A0 sz o n : Nat} {m m' : Mem} (h : RowWr B A0 sz o n m m') (ho : o + 4 ≤ sz)
    {d : Nat} (hd : d + 4 ≤ A0 ∨ A0 + sz * (n + 2) ≤ d ∨ ∃ j x, d = A0 + sz * j + x ∧ x + 4 ≤ sz ∧ (x + 4 ≤ o ∨ o + 4 ≤ x))
    (hp : d + 4 ≤ sP ∨ sP + 8 ≤ d) (hd' : d + 4 ≤ 2 ^ 64) :
    VG.Proof.Mont.w32 m' B d = VG.Proof.Mont.w32 m B d := by
  refine h.w32 (fun j hj => ?_) hp hd'
  rcases hd with hd | hd | ⟨j', x, rfl, hx, hxo⟩
  · omega
  · have := mul_step (sz := sz) hj; omega
  · exact elem_sep hx ho hxo j

/-! ## The state between batches -/

/-- `f, g` and `d, e` at byte `i` of the interleaved elements, `p` at byte 16 of the second's. -/
structure FAt (len : Nat) (B : Addr) (p iv : Nat) (dl f g d e : Int) (i : Nat) (s : State) (n : Nat := kw len / 2) :
    Prop where
  dl : s.mem.readW (off B win) 32 = BitVec.ofInt 32 dl
  inverse : VG.Proof.Mont.w32 s.mem B (win + 28) = iv
  f : sval s.mem B (rv (kw len) { arr := fgArr } n + fgSz + i) fgSz (n) = f
  g : sval s.mem B (rv (kw len) { arr := fgArr } n + fgSz + (i + 4)) fgSz (n) = g
  d : sval s.mem B (rv (kw len) { arr := deArr } n + deSz + i) deSz (n) = d
  e : sval s.mem B (rv (kw len) { arr := deArr } n + deSz + (i + 4)) deSz (n) = e
  p : sv s.mem B (rv (kw len) { arr := deArr } n + deSz + 16) deSz (n + 1) = p

/-! ## Words that stay -/

/-- The words at `b + sz w`, `w < K`, are the same in `m'` as in `m`. -/
def Same (B : Addr) (b sz K : Nat) (m m' : Mem) : Prop :=
  ∀ w < K, VG.Proof.Mont.w32 m' B (b + sz * w) = VG.Proof.Mont.w32 m B (b + sz * w)

theorem Same.refl (B : Addr) (b sz K : Nat) (m : Mem) : Same B b sz K m m := fun _ _ => rfl

theorem Same.trans {B : Addr} {b sz K : Nat} {m₁ m₂ m₃ : Mem} (h₁ : Same B b sz K m₁ m₂) (h₂ : Same B b sz K m₂ m₃) :
    Same B b sz K m₁ m₃ := fun w hw => (h₂ w hw).trans (h₁ w hw)

theorem Same.sv {B : Addr} {b sz K : Nat} {m m' : Mem} (h : Same B b sz K m m') :
    VG.Proof.Rsa.X86.InvBatchRt.F.sv m' B b sz K = VG.Proof.Rsa.X86.InvBatchRt.F.sv m B b sz K := sv_congr h

theorem Same.sval_eq {B : Addr} {b sz n : Nat} {m m' : Mem} (h : Same B b sz (n + 1) m m') :
    VG.Proof.Rsa.X86.InvBatchRt.F.sval m' B b sz n = VG.Proof.Rsa.X86.InvBatchRt.F.sval m B b sz n := by
  unfold VG.Proof.Rsa.X86.InvBatchRt.F.sval; rw [h.sv, h n (by omega)]

/-- From a frame `Unch` apart from the words. -/
theorem Same.of_unch {B : Addr} {W : List (Nat × Nat)} {m m' : Mem} (h : Unch B W m m') {b sz K : Nat}
    (hw : ∀ w < K, ∀ r ∈ W, b + sz * w + 4 ≤ r.1 ∨ r.1 + r.2 ≤ b + sz * w) (hb : ∀ w < K, b + sz * w + 4 ≤ 2 ^ 64) :
    Same B b sz K m m' := fun w hwK => by
  unfold VG.Proof.Mont.w32
  congr 1
  refine (Mem.readW_congr fun i hi => ?_).symm
  have hi' : i < 4 := by simpa using hi
  have e := ofs_off B (d := b + sz * w) (i := i) (by have := hb w hwK; omega)
  refine (h _ fun r hr => ?_).symm
  rw [e]; have := hw w hwK r hr; omega

/-- Through a row: words of another byte of its elements, or of another region. -/
theorem Same.of_row {B : Addr} {A0 sz o n : Nat} {m m' : Mem} (h : RowWr B A0 sz o n m m') (ho : o + 4 ≤ sz)
    {b sz' K : Nat}
    (hw : ∀ w < K, (b + sz' * w + 4 ≤ A0 ∨ A0 + sz * (n + 2) ≤ b + sz' * w ∨
      ∃ j x, b + sz' * w = A0 + sz * j + x ∧ x + 4 ≤ sz ∧ (x + 4 ≤ o ∨ o + 4 ≤ x)) ∧
      (b + sz' * w + 4 ≤ sP ∨ sP + 8 ≤ b + sz' * w) ∧ b + sz' * w + 4 ≤ 2 ^ 64) :
    Same B b sz' K m m' := fun w hwK => by
  obtain ⟨h1, h2, h3⟩ := hw w hwK; exact h.w32_apart ho h1 h2 h3

/-- A row's writes as a frame. -/
theorem RowWr.unch {B : Addr} {A0 sz o n : Nat} {m m' : Mem} (h : RowWr B A0 sz o n m m') (ho : o + 4 ≤ sz) :
    Unch B [(A0, sz * (n + 2)), (sP, 8)] m m' := fun x hx => by
  have h1 := hx _ (List.mem_cons_self ..)
  have h2 := hx (sP, 8) (by simp)
  refine h x (fun j hj => ?_) h2
  have := mul_step (sz := sz) hj
  simp only at h1; omega

/-- The elements of an interleaved array: element `w` of the `n + 1` at byte `x`. -/
theorem elem_of (A0 sz x w : Nat) : A0 + sz + x + sz * w = A0 + sz * (w + 1) + x := by rw [Nat.mul_succ]; omega

/-- Through a row: another byte of the same elements. -/
theorem Same.row_slot {B : Addr} {A0 sz o n x : Nat} {m m' : Mem} (h : RowWr B A0 sz o n m m') (ho : o + 4 ≤ sz)
    (hx : x + 4 ≤ sz) (hxo : x + 4 ≤ o ∨ o + 4 ≤ x) (hA : sP + 8 ≤ A0) (hb : A0 + sz * (n + 2) ≤ 2 ^ 32) :
    Same B (A0 + sz + x) sz (n + 1) m m' :=
  h.unch ho |> fun _ => Same.of_row h ho fun w hw => by
    have := mul_step (sz := sz) (show w + 1 < n + 2 by omega)
    have := elem_of A0 sz x w
    refine ⟨.inr (.inr ⟨w + 1, x, this, hx, hxo⟩), .inr (by omega), by omega⟩

/-- Through a row: elements of another region. -/
theorem Same.row_far {B : Addr} {A0 sz o n A1 sz' x : Nat} {m m' : Mem} (h : RowWr B A0 sz o n m m') (ho : o + 4 ≤ sz)
    (hx : x + 4 ≤ sz') (hfar : A1 + sz' * (n + 2) ≤ A0 ∨ A0 + sz * (n + 2) ≤ A1) (hA : sP + 8 ≤ A1)
    (hb : A1 + sz' * (n + 2) ≤ 2 ^ 32) : Same B (A1 + sz' + x) sz' (n + 1) m m' :=
  Same.of_row h ho fun w hw => by
    have := mul_step (sz := sz') (show w + 1 < n + 2 by omega)
    rw [elem_of]
    refine ⟨?_, .inr (by omega), by omega⟩
    rcases hfar with hf | hf
    · exact .inl (by omega)
    · exact .inr (.inl (by omega))

/-- Through a write below the elements. -/
theorem Same.below {B : Addr} {o c : Nat} {m m' : Mem} (h : Outside B o c m m') {A1 sz' x n : Nat} (hx : x + 4 ≤ sz')
    (hb : o + c ≤ A1) (hb' : A1 + sz' * (n + 2) ≤ 2 ^ 32) : Same B (A1 + sz' + x) sz' (n + 1) m m' :=
  Same.of_unch h.unch (fun w hw r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact .inr (by omega))
    fun w hw => by have := mul_step (sz := sz') (show w + 1 < n + 2 by omega); rw [elem_of]; omega

/-- A header word through a row. -/
theorem hdr_row {B : Addr} {A0 sz o n : Nat} {m m' : Mem} (h : RowWr B A0 sz o n m m') {d : Nat} (hd : d + 4 ≤ A0)
    (hp : d + 4 ≤ sP ∨ sP + 8 ≤ d) (hA : A0 ≤ 2 ^ 32) : m'.readW (off B d) 32 = m.readW (off B d) 32 :=
  BitVec.eq_of_toNat_eq (h.w32 (fun j _ => .inl (by omega)) hp (by omega))

/-- A header word through another write. -/
theorem hdr_out {B : Addr} {o c : Nat} {m m' : Mem} (h : Outside B o c m m') {d : Nat} (hd : d + 4 ≤ o ∨ o + c ≤ d)
    (hd' : d + 4 ≤ 2 ^ 64) : m'.readW (off B d) 32 = m.readW (off B d) 32 :=
  BitVec.eq_of_toNat_eq (h.w32 hd hd')

/-! ## The batch's rows -/

variable {L : Lay} {B : Addr} {Z len N n : Nat}

theorem ofInt_toInt {c : Int} (h : |c| ≤ 2 ^ 31 - 1) : (BitVec.ofInt 32 c).toInt = c := by
  rw [abs_le] at h
  exact BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)

/-- A row of two signed terms with coefficients `U`, `V`: `(U x₁ + V x₂) / 2^30`. -/
theorem rowTwo_ok {s : State} (h : Bx L s B Z len N n) (hn2 : 2 ≤ n) (he : n % 2 = 0)
    {arr sz o : Nat} {t₁ t₂ : Term} (hsz : sz = 16 ∨ sz = 20) (ho : o + 4 ≤ sz)
    (hfit : rv (kw len) { arr := arr } n + sz * (n + 2) < Z) (harr : sP + 8 ≤ rv (kw len) { arr := arr } n)
    (hts : TermsOk s.mem B (rv (kw len) { arr := arr } n) sz o [t₁, t₂]) {U V : Int}
    (hU : s.mem.readW (off B t₁.c) 32 = BitVec.ofInt 32 U) (hV : s.mem.readW (off B t₂.c) 32 = BitVec.ofInt 32 V)
    (huv : |U| + |V| ≤ 2 ^ 30)
    (hr : -(2 ^ (32 * n) * 2 ^ 31) ≤ (U * sval s.mem B (rv (kw len) { arr := arr } n + sz + t₁.x) sz (n) +
        V * sval s.mem B (rv (kw len) { arr := arr } n + sz + t₂.x) sz (n)) / 2 ^ 30 ∧
      (U * sval s.mem B (rv (kw len) { arr := arr } n + sz + t₁.x) sz (n) +
        V * sval s.mem B (rv (kw len) { arr := arr } n + sz + t₂.x) sz (n)) / 2 ^ 30 < 2 ^ (32 * n) * 2 ^ 31) :
    WP isa (row L false arr sz o [t₁, t₂] [t₁, t₂]) s fun t =>
      Bx L t B Z len N n ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧
      RowWr B (rv (kw len) { arr := arr } n) sz o (n) s.mem t.mem ∧
      sval t.mem B (rv (kw len) { arr := arr } n + sz + o) sz (n) =
        (U * sval s.mem B (rv (kw len) { arr := arr } n + sz + t₁.x) sz (n) +
          V * sval s.mem B (rv (kw len) { arr := arr } n + sz + t₂.x) sz (n)) / 2 ^ 30 := by
  have hu : |U| ≤ 2 ^ 31 - 1 := by have := abs_nonneg V; omega
  have hv : |V| ≤ 2 ^ 31 - 1 := by have := abs_nonneg U; omega
  have bound : cB s.mem B [t₁, t₂] * 2 ^ 32 ≤ if false = true then 2 ^ 94 else 2 ^ 62 := by
    simp only [cB, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hU, hV, ofInt_toInt hu,
      ofInt_toInt hv, Bool.false_eq_true, ↓reduceIte]
    have : (U.natAbs : Int) + V.natAbs ≤ 2 ^ 30 := by rw [Int.natCast_natAbs, Int.natCast_natAbs]; exact huv
    omega
  refine WP.mono (row_ok h hn2 he hsz ho hfit harr hts (fun t ht => ht) bound) fun t ⟨Ht, Kt, Ft, Vt⟩ =>
    ⟨Ht, Kt, Ft, ?_⟩
  rw [rowT_two, hU, hV, ofInt_toInt hu, ofInt_toInt hv] at Vt
  rw [show rv (kw len) { arr := arr } n + sz + o = rv (kw len) { arr := arr } n + o + sz by omega]
  exact sval_of_mod Vt hr.1 hr.2

/-- A row of two signed terms and `md p`: `(U x₁ + V x₂ + M y) / 2^30`. -/
theorem rowThree_ok {s : State} (h : Bx L s B Z len N n) (hn2 : 2 ≤ n) (he : n % 2 = 0)
    {arr sz o : Nat} {t₁ t₂ t₃ : Term} (hsz : sz = 16 ∨ sz = 20) (ho : o + 4 ≤ sz)
    (hfit : rv (kw len) { arr := arr } n + sz * (n + 2) < Z) (harr : sP + 8 ≤ rv (kw len) { arr := arr } n)
    (hts : TermsOk s.mem B (rv (kw len) { arr := arr } n) sz o [t₁, t₂, t₃]) {U V M : Int}
    (hU : s.mem.readW (off B t₁.c) 32 = BitVec.ofInt 32 U) (hV : s.mem.readW (off B t₂.c) 32 = BitVec.ofInt 32 V)
    (hM : (s.mem.readW (off B t₃.c) 32).toInt = M) (huv : |U| + |V| ≤ 2 ^ 30) (hm : |M| ≤ 2 ^ 31)
    (hr : -(2 ^ (32 * n) * 2 ^ 31) ≤ (U * sval s.mem B (rv (kw len) { arr := arr } n + sz + t₁.x) sz (n) +
        V * sval s.mem B (rv (kw len) { arr := arr } n + sz + t₂.x) sz (n) +
        M * (sv s.mem B (rv (kw len) { arr := arr } n + sz + t₃.x) sz (n + 1) : Int)) / 2 ^ 30 ∧
      (U * sval s.mem B (rv (kw len) { arr := arr } n + sz + t₁.x) sz (n) +
        V * sval s.mem B (rv (kw len) { arr := arr } n + sz + t₂.x) sz (n) +
        M * (sv s.mem B (rv (kw len) { arr := arr } n + sz + t₃.x) sz (n + 1) : Int)) / 2 ^ 30 <
        2 ^ (32 * n) * 2 ^ 31) :
    WP isa (row L true arr sz o [t₁, t₂, t₃] [t₁, t₂]) s fun t =>
      Bx L t B Z len N n ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧
      RowWr B (rv (kw len) { arr := arr } n) sz o (n) s.mem t.mem ∧
      sval t.mem B (rv (kw len) { arr := arr } n + sz + o) sz (n) =
        (U * sval s.mem B (rv (kw len) { arr := arr } n + sz + t₁.x) sz (n) +
          V * sval s.mem B (rv (kw len) { arr := arr } n + sz + t₂.x) sz (n) +
          M * (sv s.mem B (rv (kw len) { arr := arr } n + sz + t₃.x) sz (n + 1) : Int)) / 2 ^ 30 := by
  have hu : |U| ≤ 2 ^ 31 - 1 := by have := abs_nonneg V; omega
  have hv : |V| ≤ 2 ^ 31 - 1 := by have := abs_nonneg U; omega
  have bound : cB s.mem B [t₁, t₂, t₃] * 2 ^ 32 ≤ if true = true then 2 ^ 94 else 2 ^ 62 := by
    simp only [cB, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hU, hV, hM, ofInt_toInt hu,
      ofInt_toInt hv, ↓reduceIte]
    have : (U.natAbs : Int) + V.natAbs + M.natAbs ≤ 2 ^ 30 + 2 ^ 31 := by
      rw [Int.natCast_natAbs, Int.natCast_natAbs, Int.natCast_natAbs]; omega
    omega
  refine WP.mono (row_ok h hn2 he hsz ho hfit harr hts (fun t ht => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht ⊢; rcases ht with h | h <;> simp [h]) bound)
    fun t ⟨Ht, Kt, Ft, Vt⟩ => ⟨Ht, Kt, Ft, ?_⟩
  rw [rowT_three, hU, hV, hM, ofInt_toInt hu, ofInt_toInt hv] at Vt
  rw [show rv (kw len) { arr := arr } n + sz + o = rv (kw len) { arr := arr } n + o + sz by omega]
  exact sval_of_mod Vt hr.1 hr.2

end VG.Proof.Rsa.X86.InvBatchRt.F
