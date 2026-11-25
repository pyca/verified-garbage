module

import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Weierstrass.X86.MontRow
import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
import VerifiedGarbage.Proof.Mont.X86.Loop
import VerifiedGarbage.Proof.Mont.X86.Row
public import VerifiedGarbage.Proof.Weierstrass.X86.MontBase
import VerifiedGarbage.Proof.X25519.X86.Arith
public import VerifiedGarbage.Proof.X25519.X86.Column
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Montgomery arithmetic as functions on x86 (32-bit): the product

The operands' words copied, and the numbers of X25519's column lemmas as
numbers of the working space; then the rows of the product, P-521's square,
and the product by columns, each up to the final subtraction (`mulBody_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Mont

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

section

variable {s : State} {base : Addr} {size : Nat}

theorem copyWords_ok (hb : Bx s base size) {r : Reg} {a d : Nat} (hp : Ptr s r a) (hr : r ≠ .eax)
    {N : Nat} (ha : a + 4 * N ≤ d) (hd : d + 4 * N ≤ size) : ∀ j, j ≤ N →
    WP isa (.block (copyWords r d j)) s fun u =>
      Outside base d (4 * j) s.mem u.mem ∧ Keeps [.eax] s u ∧
      ∀ i < j, w32 u.mem base (d + 4 * i) = w32 s.mem base (a + 4 * i)
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, Keeps.refl _ _, by omega_using []⟩
  | j + 1, hj => by
    have hn := hb.nowrap
    rw [copyWords]
    refine WP.block_append (WP.mono (copyWords_ok hb hp hr ha hd j (by omega_using [hj])) fun t ⟨O, K, V⟩ => ?_)
    have hbt := hb.of_keeps K (by decide)
    have hpt := hp.of_keeps K (by simp only [List.mem_singleton]; exact hr) (by decide)
    refine wp_movS (readSrc_ptr hbt hpt (d := 4 * j) (by omega_using [ha, hj, hd])) fun v R _ => ?_
    have hbv := hbt.of_keeps R.keeps (by decide)
    refine wp_storeS (hbv.ea (d := d + 4 * j) (by omega_using [hj, hd])) (hbv.write (n := 4) (by omega_using [hj, hd]))
      fun u M => WP.block_nil ?_
    have hm : u.mem = t.mem.writeW (off base (d + 4 * j))
        (t.mem.readW (off base (a + 4 * j)) 32) := by rw [M.mem, R.mem, R.gpr]
    have U := writeW32_outside t.mem base (d := d + 4 * j)
      (t.mem.readW (off base (a + 4 * j)) 32) (by omega_using [hj, hd, hn])
    rw [← hm] at U
    refine ⟨(O.mono (Nat.le_refl _) (by omega_using [])).trans (U.mono (by omega_using []) (by omega_using [])),
      (K.trans R.keeps).trans (M.keeps _), ?_⟩
    intro i hi
    by_cases hij : i = j
    · subst i
      rw [hm, w32_write_self]
      exact O.w32 (by omega_using [ha, hj, hd, hn]) (by omega_using [ha, hj, hd, hn])
    · rw [U.w32 (by omega_using [hij]) (by omega_using [hj, hd, hi, hn])]
      exact V i (by omega_using [hi, hij])

end

theorem square_wv_eq (m : Mem) {x : BitVec 32} {d : Nat} (hd : x.toNat + d < 2 ^ 32) :
    VG.Proof.X25519.X86.wv m x d = w32 m (x.setWidth 64) d := by
  simp only [VG.Proof.X25519.X86.wv, VG.Proof.X25519.X86.wd, w32, addr_eq hd, off]

theorem square_num_eq (m : Mem) {x : BitVec 32} {o : Nat} : ∀ n,
    x.toNat + o + 4 * n ≤ 2 ^ 32 →
    VG.Proof.X25519.X86.num (fun j => VG.Proof.X25519.X86.wv m x (o + 4 * j)) n = val32 m (x.setWidth 64) o n
  | 0, _ => rfl
  | n + 1, hn => by
    rw [VG.Proof.X25519.X86.num_succ, square_num_eq m n (by omega_using [hn]), val32_succ,
      square_wv_eq m (by omega_using [hn]), ← Nat.pow_mul]

theorem square_frame_outside {m m' : Mem} {x : BitVec 32} {o n : Nat}
    (hx : x.toNat + o + n ≤ 2 ^ 32) (hn : 0 < n)
    (F : Frame [VG.Proof.X25519.X86.sub x o n] m m') : Outside (x.setWidth 64) o n m m' := by
  intro y hy
  apply F y
  intro r hr
  rw [List.mem_singleton.mp hr]
  simp only [VG.Proof.X25519.X86.sub, addr_eq (by omega_using [hx, hn] : x.toNat + o < 2 ^ 32)]
  change ¬ ((y - (x.setWidth 64 + BitVec.ofNat 64 o)).toNat + 1 ≤ n)
  have h := (Offset.lt_iff y (x.setWidth 64) (d := o) (n := n) (by omega_using [hx])).mp
  simp only [ofs] at hy
  intro h'
  have := h (by omega_using [h'])
  omega_using [hy, h, h']

/-- Equal words at different offsets represent equal numbers. -/
theorem square_val_congr {m m' : Mem} {base : Addr} {d d' : Nat} : ∀ n,
    (∀ i < n, w32 m' base (d' + 4 * i) = w32 m base (d + 4 * i)) →
    val32 m' base d' n = val32 m base d n
  | 0, _ => rfl
  | n + 1, h => by
    rw [val32_succ, val32_succ, square_val_congr n (fun i hi => h i (by omega_using [hi])), h n (by omega_using [])]

end VG.Proof.Weierstrass.X86.Mont

end

/-! ### `Weierstrass.X86.MontMul`, which this module and modules that import it used -/

section

/-!
# Montgomery arithmetic as functions on x86 (32-bit): the rows of the product

Row `i` of `mulFn` (`rowF`), the working space at `ebp`, `[a]` at `edi` and
`[b]` at `esi`: `ecx = a_i`, the window of the accumulator at `own + 4i`
`+= a_i B` (row 0 writes it: `rowZ`), then `+= q m` for the `q` that makes its
low word zero (`redDigit`, `redRowI`), so that the accumulator's words from
`i + 1` hold `(T + a_i B + q m) / 2³²`, below `2m` again (`rowF_ok`). After
the `N` rows, the words from `N` hold `T < 2m` with `R T ≡ A B` (`rowsF_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Mont

open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

/-- What the functions need of the modulus `m` of `k` words: `m` odd (its
inverse), below `R = 2^(64 k)`, and the reduction's certificate. -/
structure MulOk (k m : Nat) : Prop where
  k0 : 0 < k
  m_lt : m < 2 ^ (64 * k)
  inv : (m * (minv m) + 1) % 2 ^ 64 = 0

theorem MulOk.m_pos {k m : Nat} (h : MulOk k m) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with rfl | h'
  · have := h.inv; simp at this
  · exact h'

theorem mod_ok (k m : Nat) : (mod k m).ok m = true := rfl

theorem minv_lt (m : Nat) : minv m < 2 ^ 64 := by unfold minv; exact Nat.mod_lt _ (by decide)

theorem minv32_mod {k m : Nat} (h : MulOk k m) : (m * (minv32 (mod k m)).toNat + 1) % 2 ^ 32 = 0 := by
  apply minv32_inv
  have e : (mod k m).minv.toNat = minv m := by
    show (BitVec.ofNat 64 (minv m)).toNat = minv m
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (minv_lt m)]
  rw [e]; exact h.inv

theorem words_mod (k m : Nat) : words (mod k m) = 2 * k := rfl

variable {s : State} {base : Addr} {size : Nat}

/-- The reduction digit `q = t₀ m' mod 2³²`, from the window's low word. -/
theorem redDigitB_ok {M : Mod} (hb : Bx s base size) {acc : Nat} (ha : acc + 4 ≤ size) :
    WP isa (.block (redDigit M acc)) s fun t =>
      (t.gpr .ecx).toNat = (s.mem.readW (off base acc) 32).toNat * (minv32 M).toNat % 2^32 ∧
      Keeps [.eax, .ecx, .edx] s t ∧ t.mem = s.mem := by
  unfold redDigit
  split
  next h =>
    refine wp_movS (readSrc_bp hb ha) fun _t u _ => WP.block_nil ⟨?_, u.keeps.mono (by decide), u.mem⟩
    rw [u.gpr, h]
    change _ = _ * 1 % 2^32
    rw [Nat.mul_one, Nat.mod_eq_of_lt (s.mem.readW (off base acc) 32).isLt]
  next _ =>
    refine wp_movS (readSrc_bp hb ha) fun _s₁ u₁ _ => ?_
    refine wp_movS rfl fun _s₂ u₂ _ => ?_
    refine wp_mul fun _s₃ m₃ => ?_
    refine wp_movS rfl fun _s₄ u₄ _ => WP.block_nil ⟨?_, ?_, ?_⟩
    · rw [u₄.gpr, m₃.eax, u₂.other .eax (by decide), u₁.gpr, u₂.gpr, BitVec.toNat_ofNat]
    · exact ((u₁.keeps.mono (by decide) |>.widen u₂.keeps).widen m₃.keeps).widen u₄.keeps
    · rw [u₄.mem, m₃.mem, u₂.mem, u₁.mem]

/-- The words of `m`. -/
theorem yVal_mw (m : Nat) : ∀ k, yVal (mw m) k = m % 2 ^ (32 * k)
  | 0 => by simp [yVal, Nat.mod_one]
  | k + 1 => by
    rw [yVal, yVal_mw m k, mw, BitVec.toNat_ofNat, pow32_add, show 32 * 1 = 32 from rfl, Nat.mod_mul,
      Nat.shiftRight_eq_div_pow]

theorem ysOk_m (m : Nat) {base : Addr} {acc len N : Nat} {s : State} :
    YsOk (mWord m) (mw m) base acc len N s := fun _ _ _ _ => rfl

/-- The words of `[b]`, at `esi`, apart from the window. -/
theorem ysOk_b (hb : Bx s base size) {pb : Nat} (hp : Ptr s .esi pb) {acc len N : Nat}
    (hfit : pb + 4 * N ≤ size) (hsep : pb + 4 * N ≤ acc ∨ acc + len ≤ pb) :
    YsOk bWord (fun j => s.mem.readW (off base (pb + 4 * j)) 32) base acc len N s := by
  intro j hj t K
  have hn := hb.nowrap
  have hbt : Bx t base size := ⟨by rw [K.ebp]; exact hb.ebp, K.wr ▸ hb.wr, hb.nowrap⟩
  have hpt : Ptr t .esi pb := by
    change t.gpr .esi = t.gpr .ebp + _
    rw [K.esi, K.ebp]; exact hp
  rw [bWord, readSrc_ptr hbt hpt (by omega_arith)]
  exact congrArg some (BitVec.eq_of_toNat_eq (K.out.w32 (by omega_arith) (by omega_arith)))

/-- `-p⁻¹ mod 2³² = 1` for P-521's `p`, which is `-1` modulo `2³²`. -/
theorem p521_minv {x : Nat} (hx : (p521Prime * x + 1) % 2 ^ 32 = 0) (hx32 : x < 2 ^ 32) : x = 1 := by
  obtain ⟨a, hm⟩ : ∃ a, p521Prime = 2 ^ 32 * a + (2 ^ 32 - 1) := ⟨2 ^ 489 - 1, by decide +kernel⟩
  rw [hm, Nat.add_mul, Nat.mul_assoc] at hx
  generalize a * x = y at hx
  omega_arith

/-- The window `+= q m`, `q` in `ecx`, for `q = t₀ m'` (which P-521's sparse
reduction needs). -/
theorem redRowI_ok (hb : Bx s base size) {k m acc : Nat} (hM : MulOk k m)
    (hacc : acc + 4 * (2 * k) + 8 ≤ size)
    (hq : minv32 (mod k m) = 1 → (s.gpr .ecx).toNat = w32 s.mem base acc)
    (hlt : val32 s.mem base acc (2 * k + 2) + (s.gpr .ecx).toNat * m < 2 ^ (32 * (2 * k + 2))) :
    WP isa (.block (redRowI (mod k m) m acc)) s fun u =>
      Outside base acc (4 * (2 * k) + 8) s.mem u.mem ∧
      val32 u.mem base acc (2 * k + 2) = val32 s.mem base acc (2 * k + 2) + (s.gpr .ecx).toNat * m ∧
      Keeps [.eax, .ebx, .ecx, .edx] s u := by
  have hk := hM.k0
  have hm2 : m < 2 ^ (32 * (2 * k)) := by rw [← Nat.mul_assoc]; exact hM.m_lt
  unfold redRowI
  split
  next he =>
    simp only [p521RedEnabled, Bool.and_eq_true, beq_iff_eq] at he
    obtain ⟨hk9, hm5⟩ := he
    have h1 : minv32 (mod k m) = 1 :=
      BitVec.eq_of_toNat_eq (p521_minv (by rw [← hm5]; exact minv32_mod hM) (minv32 (mod k m)).isLt)
    have hk9' : k = 9 := hk9
    subst hk9'
    rw [hm5] at hlt ⊢
    simp only [Nat.reduceMul, Nat.reduceAdd] at hlt hacc ⊢
    unfold p521Prime at hlt ⊢
    exact WP.mono (p521RedB_ok hb rfl hacc (hq h1) hlt) fun u ⟨O, V, K⟩ => ⟨O, V, K.mono (by decide)⟩
  next _ =>
    rw [words_mod]
    refine WP.mono (rowG_ok hb (by omega_arith) (ysOk_m m) hacc ?_) fun u ⟨O, V, K⟩ => ⟨O, ?_, K.mono (by decide)⟩
    · rw [yVal_mw, Nat.mod_eq_of_lt hm2]; exact hlt
    · rw [V, yVal_mw, Nat.mod_eq_of_lt hm2]

/-- The reduction of a row: `q = t₀ m' mod 2³²`, then the window `+= q m`,
whose low word becomes zero. -/
theorem rowTail_ok (hb : Bx s base size) {k m w : Nat} (hM : MulOk k m) (hacc : w + 4 * (2 * k) + 8 ≤ size)
    (hlt : val32 s.mem base w (2 * k + 2) + (2 ^ 32 - 1) * m < 2 ^ (32 * (2 * k + 2))) :
    WP isa (.block (redDigit (mod k m) w ++ redRowI (mod k m) m w)) s fun u =>
      Outside base w (4 * (2 * k) + 8) s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s u ∧
      ∃ q, q < 2 ^ 32 ∧ val32 u.mem base w (2 * k + 2) = val32 s.mem base w (2 * k + 2) + q * m ∧
        w32 u.mem base w = 0 := by
  have hn := hb.nowrap
  refine WP.block_append (WP.mono (redDigitB_ok (M := mod k m) hb (acc := w) (by omega_arith))
    fun s₁ ⟨q₁, K₁, mem₁⟩ => ?_)
  have hb₁ := hb.of_keeps K₁ (by decide)
  have hq := (s₁.gpr .ecx).isLt
  refine WP.mono (redRowI_ok hb₁ hM (by omega_arith) (fun h1 => ?_) ?_) fun u ⟨O, V, K⟩ =>
    ⟨by rw [mem₁] at O; exact O, (K₁.mono (rs' := [.eax, .ebx, .ecx, .edx]) (by decide)).widen K (by decide),
      ⟨_, hq, by rw [V, mem₁], ?_⟩⟩
  · rw [q₁, h1, mem₁]
    change _ * 1 % _ = _
    rw [Nat.mul_one, Nat.mod_eq_of_lt (s.mem.readW (off base w) 32).isLt]
  · rw [mem₁]
    have : (s₁.gpr .ecx).toNat * m ≤ (2 ^ 32 - 1) * m := Nat.mul_le_mul_right _ (by omega_arith)
    omega_arith
  · have hv : ∀ mem : Mem, val32 mem base w (2 * k + 2) = w32 mem base w + 2 ^ 32 * val32 mem base (w + 4) (2 * k + 1) :=
      fun _ => rfl
    have h0 : (val32 u.mem base w (2 * k + 2)) % 2 ^ 32 = w32 u.mem base w := by
      rw [hv]; have := (u.mem.readW (off base w) 32).isLt; simp only [w32] at *; omega_arith
    rw [← h0, V, mem₁, hv, q₁]
    have := mont_low32 (w32 s.mem base w) (minv32 (mod k m)).toNat m (minv32_mod hM)
    rw [Nat.add_assoc, Nat.add_comm (2 ^ 32 * _), ← Nat.add_assoc, Nat.add_mul_mod_self_left]
    exact this

/-- Where the product's numbers are: `[a]` and `[b]` (`N = 2k` words) below
the accumulator (`2N + 1` words at `A`), in the working space. -/
structure MulLayB (k size pa pb A : Nat) : Prop where
  pa : pa + 4 * (2 * k) ≤ A
  pb : pb + 4 * (2 * k) ≤ A
  acc : A + 4 * (2 * (2 * k) + 1) ≤ size

/-- Row `i` of the product. -/
theorem rowF_ok (hb : Bx s base size) {k m pa pb i : Nat} (hM : MulOk k m)
    (hpa : Ptr s .edi pa) (hpb : Ptr s .esi pb) (hL : MulLayB k size pa pb (own k)) (hi : i < 2 * k)
    (hB : val32 s.mem base pb (2 * k) < m)
    (hT : 0 < i → val32 s.mem base (own k + 4 * i) (2 * k + 1) < 2 * m) :
    WP isa (.block (rowF k m i)) s fun u =>
      Outside base (own k) (4 * (2 * (2 * k) + 1)) s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s u ∧
      (∃ q, 2 ^ 32 * val32 u.mem base (own k + 4 * (i + 1)) (2 * k + 1) =
        (if i = 0 then 0 else val32 s.mem base (own k + 4 * i) (2 * k + 1)) +
          w32 s.mem base (pa + 4 * i) * val32 s.mem base pb (2 * k) + q * m) ∧
      val32 u.mem base (own k + 4 * (i + 1)) (2 * k + 1) < 2 * m := by
  have hn := hb.nowrap
  have := hL.pa; have := hL.pb; have := hL.acc
  have hk := hM.k0
  have hmP : m < 2 ^ (32 * (2 * k)) := by rw [← Nat.mul_assoc]; exact hM.m_lt
  have hP : 0 < 2 ^ (32 * (2 * k)) := Nat.two_pow_pos _
  obtain ⟨w, hw⟩ : ∃ w, own k + 4 * i = w := ⟨_, rfl⟩
  -- The product row, into a state `s₂` whose window holds `T₀ + a_i B`.
  have prod : WP isa (.block ([.mov .ecx (.mem (at_ .edi (4 * i)))] ++
      (if i = 0 then rowZ (own k) (2 * k)
        else rowG bWord (own k + 4 * i) (2 * k) (carryUp1 (own k + 4 * i) (2 * k))))) s fun s₂ =>
      Outside base w (4 * (2 * k) + 8) s.mem s₂.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s s₂ ∧
      val32 s₂.mem base w (2 * k + 2) = (if i = 0 then 0 else val32 s.mem base w (2 * k + 1)) +
        w32 s.mem base (pa + 4 * i) * val32 s.mem base pb (2 * k) := by
    refine wp_movS (readSrc_ptr hb hpa (d := 4 * i) (by omega_arith)) fun s₁ u₁ _ => ?_
    have k₁ : Keeps [.eax, .ebx, .ecx, .edx] s s₁ := u₁.keeps.mono (by decide)
    have hb₁ := hb.of_keeps k₁ (by decide)
    have hpb₁ : Ptr s₁ .esi pb := hpb.of_keeps k₁ (by decide) (by decide)
    have ecx₁ : (s₁.gpr .ecx).toNat = w32 s.mem base (pa + 4 * i) := by rw [u₁.gpr]
    have mem₁ : s₁.mem = s.mem := u₁.mem
    have hY := ysOk_b hb₁ hpb₁ (acc := w) (len := 4 * (2 * k) + 8) (N := 2 * k) (by omega_arith) (by omega_arith)
    have hYv : yVal (fun j => s₁.mem.readW (off base (pb + 4 * j)) 32) (2 * k) = val32 s.mem base pb (2 * k) := by
      rw [yVal_val32, mem₁]
    by_cases h0 : i = 0
    · subst h0
      have hw0 : w = own k := by omega_arith
      subst hw0
      simp only [ite_true]
      refine WP.mono (rowZ_ok hb₁ (by omega_arith) hY (by omega_arith)) fun u ⟨O, V, K⟩ =>
        ⟨by rw [mem₁] at O; exact O, k₁.widen K (by decide), ?_⟩
      rw [V, hYv, ecx₁, Nat.zero_add]
    · simp only [h0, ite_false]
      rw [hw]
      refine WP.mono (rowG1_ok hb₁ (by omega_arith) hY (by omega_arith)) fun u ⟨O, V, K⟩ =>
        ⟨by rw [mem₁] at O; exact O, k₁.widen K (by decide), ?_⟩
      rw [V, hYv, ecx₁, mem₁]
  simp only [rowF, List.append_assoc]
  rw [← List.append_assoc]
  refine WP.block_append (WP.mono prod fun s₂ ⟨O₂, K₂, V₂⟩ => ?_)
  have hb₂ := hb.of_keeps K₂ (by decide)
  have hA := (s.mem.readW (off base (pa + 4 * i)) 32).isLt
  have hT0 : (if i = 0 then 0 else val32 s.mem base w (2 * k + 1)) < 2 * m := by
    split
    · exact Nat.mul_pos (by decide) hM.m_pos
    · rename_i h; rw [← hw]; exact hT (by omega_arith)
  have hlt := row_lt (T := if i = 0 then 0 else val32 s.mem base w (2 * k + 1))
    (a := w32 s.mem base (pa + 4 * i)) (B := val32 s.mem base pb (2 * k)) (m := m) (q := 2 ^ 32 - 1)
    hT0 hA hB (by decide)
  have hpow : 2 ^ (32 * (2 * k + 2)) = 2 ^ (32 * (2 * k)) * 2 ^ 64 := by rw [pow32_add]
  rw [hw]
  refine WP.mono (rowTail_ok hb₂ hM (w := w) (by omega_arith) ?_) fun u ⟨O, K, q, hq, V, z⟩ => ?_
  · rw [V₂, hpow]
    have : m * 2 ^ 64 < 2 ^ (32 * (2 * k)) * 2 ^ 64 := Nat.mul_lt_mul_of_pos_right hmP (by decide)
    omega_arith
  have hlt' := row_lt (T := if i = 0 then 0 else val32 s.mem base w (2 * k + 1))
    (a := w32 s.mem base (pa + 4 * i)) (B := val32 s.mem base pb (2 * k)) (m := m) (q := q) hT0 hA hB hq
  have hv : val32 u.mem base w (2 * k + 2) = w32 u.mem base w + 2 ^ 32 * val32 u.mem base (w + 4) (2 * k + 1) :=
    rfl
  rw [z, Nat.zero_add] at hv
  have ew : own k + 4 * (i + 1) = w + 4 := by omega_arith
  have e : (if i = 0 then 0 else val32 s.mem base w (2 * k + 1)) +
      w32 s.mem base (pa + 4 * i) * val32 s.mem base pb (2 * k) + q * m =
      2 ^ 32 * val32 u.mem base (w + 4) (2 * k + 1) := by rw [← V₂, ← V, hv]
  refine ⟨(O₂.trans O).mono (by omega_arith) (by omega_arith), K₂.trans K, ⟨q, ?_⟩, ?_⟩
  · rw [ew, ← e]
  · rw [ew]
    rw [e] at hlt'
    omega_arith

/-- The rows `0 … r - 1` of the product: the accumulator's words from `r`
hold `T < 2m` with `2^(32 r) T ≡ A_r B`, `A_r` the low `r` words of `[a]`. -/
theorem rowsF_ok (hb : Bx s base size) {k m pa pb : Nat} (hM : MulOk k m)
    (hpa : Ptr s .edi pa) (hpb : Ptr s .esi pb) (hL : MulLayB k size pa pb (own k))
    (hB : val32 s.mem base pb (2 * k) < m) :
    ∀ r, 1 ≤ r → r ≤ 2 * k →
    WP isa (.block (rowsF k m r)) s fun u =>
      Outside base (own k) (4 * (2 * (2 * k) + 1)) s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s u ∧
      val32 u.mem base (own k + 4 * r) (2 * k + 1) < 2 * m ∧
      ∃ U, 2 ^ (32 * r) * val32 u.mem base (own k + 4 * r) (2 * k + 1) =
        val32 s.mem base pa r * val32 s.mem base pb (2 * k) + U * m
  | 0, h, _ => absurd h (by decide)
  | 1, _, hr => by
    simp only [rowsF, List.nil_append]
    refine WP.mono (rowF_ok hb hM hpa hpb hL (i := 0) (by omega_arith) hB (fun h => absurd h (by decide)))
      fun u ⟨O, K, ⟨q, hq⟩, hT⟩ => ⟨O, K, hT, ⟨q, ?_⟩⟩
    rw [show 32 * 1 = 32 from rfl, hq, val32_one]
    simp
  | r + 2, _, hr => by
    have hn := hb.nowrap
    have := hL.pa; have := hL.pb; have := hL.acc
    rw [rowsF]
    refine WP.block_append (WP.mono (rowsF_ok hb hM hpa hpb hL hB (r + 1) (by omega_arith) (by omega_arith))
      fun s₁ ⟨O₁, K₁, T₁, ⟨U, hU⟩⟩ => ?_)
    have hb₁ := hb.of_keeps K₁ (by decide)
    have hpa₁ : Ptr s₁ .edi pa := hpa.of_keeps K₁ (by decide) (by decide)
    have hpb₁ : Ptr s₁ .esi pb := hpb.of_keeps K₁ (by decide) (by decide)
    have hb' : val32 s₁.mem base pb (2 * k) = val32 s.mem base pb (2 * k) := O₁.val32 (by omega_arith) (by omega_arith)
    have ha' : w32 s₁.mem base (pa + 4 * (r + 1)) = w32 s.mem base (pa + 4 * (r + 1)) :=
      O₁.w32 (by omega_arith) (by omega_arith)
    refine WP.mono (rowF_ok hb₁ hM hpa₁ hpb₁ hL (i := r + 1) (by omega_arith) (hb' ▸ hB) (fun _ => T₁))
      fun u ⟨O, K, ⟨q, hq⟩, hT⟩ => ⟨O₁.trans O, K₁.trans K, hT, ?_⟩
    simp only [Nat.add_one_ne_zero, ite_false] at hq
    rw [hb', ha'] at hq
    refine ⟨U + 2 ^ (32 * (r + 1)) * q, ?_⟩
    rw [show r + 1 + 1 = r + 2 from rfl] at hq
    rw [show 2 ^ (32 * (r + 2)) = 2 ^ (32 * (r + 1)) * 2 ^ 32 by rw [pow32_succ (r + 1), Nat.mul_comm],
      Nat.mul_assoc, hq, val32_succ s.mem base pa (r + 1)]
    generalize 2 ^ (32 * (r + 1)) = P at *
    grind

end VG.Proof.Weierstrass.X86.Mont

end

end

/-! # P-521's square: the products of different words, doubled, the squares, and the reduction -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Mont

open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

variable {s : State} {base : Addr} {size : Nat}

/-- The stores of `zeroWords`, `eax` being zero. -/
theorem zeroStores_ok {acc : Nat} : ∀ (n : Nat) {s : State}, Bx s base size → s.gpr .eax = 0 →
    acc + 4 * n ≤ size →
    WP isa (.block ((List.range n).map fun j => .store (bp (acc + 4 * j)) .eax)) s fun u =>
      Outside base acc (4 * n) s.mem u.mem ∧ val32 u.mem base acc n = 0 ∧ Keeps [] s u
  | 0, s, _, _, _ => WP.block_nil ⟨Outside.refl _ _ _ _, rfl, Keeps.refl _ _⟩
  | n + 1, s, hb, h0, hsz => by
    have hn := hb.nowrap
    rw [List.range_succ, List.map_append]
    refine WP.block_append (WP.mono (zeroStores_ok n hb h0 (by omega_arith)) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have hb₁ := hb.of_keeps K₁ (by decide)
    simp only [List.map_cons, List.map_nil]
    refine wp_storeS (hb₁.ea (d := acc + 4 * n) (by omega_arith)) (hb₁.write (n := 4) (by omega_arith))
      fun u m => WP.block_nil ?_
    obtain W := writeW32_outside s₁.mem base (d := acc + 4 * n) (s₁.gpr .eax) (by omega_arith)
    rw [← m.mem] at W
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega_arith)).trans (W.mono (by omega_arith) (by omega_arith)), ?_,
      K₁.trans (m.keeps _)⟩
    rw [val32_succ, W.val32 (Or.inl (Nat.le_refl _)) (by omega_arith), V₁, m.mem, w32_write_self,
      K₁.1 _ (by decide), h0]
    rfl

/-- The accumulator's `n` words cleared. -/
theorem zeroWords_ok (hb : Bx s base size) {acc n : Nat} (hsz : acc + 4 * n ≤ size) :
    WP isa (.block (zeroWords acc n)) s fun u =>
      Outside base acc (4 * n) s.mem u.mem ∧ val32 u.mem base acc n = 0 ∧ Keeps [.eax] s u := by
  unfold zeroWords
  refine wp_movS rfl fun s₁ u₁ _ => ?_
  refine WP.mono (zeroStores_ok n (hb.of_keeps u₁.keeps (by decide)) u₁.gpr hsz) fun u ⟨O, V, K⟩ =>
    ⟨by rw [u₁.mem] at O; exact O, V, u₁.keeps.trans (K.mono (by decide))⟩

/-- The words at `[ebp + d]`, apart from the window. -/
theorem ysOk_acc (hb : Bx s base size) {d acc len N : Nat} (hfit : d + 4 * N ≤ size)
    (hsep : d + 4 * N ≤ acc ∨ acc + len ≤ d) :
    YsOk (accWord d) (fun j => s.mem.readW (off base (d + 4 * j)) 32) base acc len N s := by
  intro j hj t K
  have hn := hb.nowrap
  have hbt : Bx t base size := ⟨by rw [K.ebp]; exact hb.ebp, K.wr ▸ hb.wr, hb.nowrap⟩
  rw [accWord, readSrc_bp hbt (by omega_arith)]
  exact congrArg some (BitVec.eq_of_toNat_eq (K.out.w32 (by omega_arith) (by omega_arith)))

/-- A number that is zero: its two parts are. -/
theorem val32_zero_parts {m : Mem} {d a b : Nat} (h : val32 m base d (a + b) = 0) :
    val32 m base d a = 0 ∧ val32 m base (d + 4 * a) b = 0 := by
  rw [val32_append] at h
  have hP := Nat.two_pow_pos (32 * a)
  refine ⟨(Nat.eq_zero_of_add_eq_zero h).1, ?_⟩
  rcases Nat.mul_eq_zero.mp (Nat.eq_zero_of_add_eq_zero h).2 with h' | h'
  · omega_using [h', hP]
  · exact h'

/-- Row `i` of the products of different words, the accumulator's words from
`2i` being zero: its `2i + 2 + r` words `+= 2^(32 i) a_i (a_0 … a_{i-1})`. -/
theorem sqRow_ok (hb : Bx s base size) {pa acc i r : Nat} (hp : Ptr s .esi pa) (hi : 0 < i)
    (hpa : pa + 4 * (i + 1) ≤ acc) (hsz : acc + 4 * (2 * i + 2 + r) ≤ size)
    (hZ : val32 s.mem base (acc + 8 * i) (2 + r) = 0) :
    WP isa (.block (sqRow acc i)) s fun u =>
      Outside base acc (4 * (2 * i + 2 + r)) s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s u ∧
      val32 u.mem base acc (2 * i + 2 + r) = val32 s.mem base acc (2 * i + 2 + r) +
        2 ^ (32 * i) * (w32 s.mem base (pa + 4 * i) * val32 s.mem base pa i) ∧
      val32 u.mem base (acc + 8 * i + 8) r = 0 := by
  have hn := hb.nowrap
  simp only [sqRow, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_ptr hb hp (d := 4 * i) (by omega_arith)) fun s₁ u₁ _ => ?_
  have k₁ : Keeps [.eax, .ebx, .ecx, .edx] s s₁ := u₁.keeps.mono (by decide)
  have hb₁ := hb.of_keeps k₁ (by decide)
  have hp₁ : Ptr s₁ .esi pa := hp.of_keeps k₁ (by decide) (by decide)
  have ecx₁ : (s₁.gpr .ecx).toNat = w32 s.mem base (pa + 4 * i) := by rw [u₁.gpr]
  have mem₁ : s₁.mem = s.mem := u₁.mem
  have hY := ysOk_b hb₁ hp₁ (acc := acc + 4 * i) (len := 4 * i + 8) (N := i) (by omega_arith)
    (Or.inl (by omega_arith))
  have hYv : yVal (fun j => s₁.mem.readW (off base (pa + 4 * j)) 32) i = val32 s.mem base pa i := by
    rw [yVal_val32, mem₁]
  obtain ⟨z2, zr⟩ := val32_zero_parts hZ
  have e8 : acc + 4 * i + 4 * i = acc + 8 * i := by omega_arith
  have e88 : acc + 8 * i + 4 * 2 = acc + 8 * i + 8 := by omega_arith
  rw [e88] at zr
  have hw : ∀ m : Mem, val32 m base (acc + 4 * i) (i + 2) =
      val32 m base (acc + 4 * i) i + 2 ^ (32 * i) * val32 m base (acc + 8 * i) 2 := fun m => by
    rw [val32_append, e8]
  have hA := val32_lt s.mem base pa i
  have ha := (s.mem.readW (off base (pa + 4 * i)) 32).isLt
  have hX := val32_lt s.mem base (acc + 4 * i) i
  have hP : 0 < 2 ^ (32 * i) := Nat.two_pow_pos _
  have haA : w32 s.mem base (pa + 4 * i) * val32 s.mem base pa i < 2 ^ 32 * 2 ^ (32 * i) :=
    Nat.mul_lt_mul_of_lt_of_lt ha hA
  refine WP.mono (rowG_ok hb₁ hi hY (by omega_arith) ?_) fun u ⟨O, V, K⟩ => ?_
  · rw [hw, hYv, mem₁, z2, ecx₁, pow32_add i 2, Nat.mul_zero, Nat.add_zero]
    generalize 2 ^ (32 * i) = P at *
    generalize w32 s.mem base (pa + 4 * i) * val32 s.mem base pa i = t at *
    omega_arith
  · rw [hYv, ecx₁] at V
    rw [mem₁] at O V
    have es : ∀ m : Mem, val32 m base acc (2 * i + 2 + r) = val32 m base acc i +
        2 ^ (32 * i) * (val32 m base (acc + 4 * i) (i + 2) +
          2 ^ (32 * (i + 2)) * val32 m base (acc + 8 * i + 8) r) := fun m => by
      rw [show 2 * i + 2 + r = i + (i + 2 + r) by omega_arith, val32_append, val32_append,
        show acc + 4 * i + 4 * (i + 2) = acc + 8 * i + 8 by omega_arith]
    have t1 : val32 u.mem base acc i = val32 s.mem base acc i :=
      O.val32 (Or.inl (Nat.le_refl _)) (by omega_arith)
    have t2 : val32 u.mem base (acc + 8 * i + 8) r = val32 s.mem base (acc + 8 * i + 8) r :=
      O.val32 (Or.inr (by omega_arith)) (by omega_arith)
    refine ⟨O.mono (by omega_arith) (by omega_arith), k₁.widen K (by decide), ?_, by rw [t2, zr]⟩
    rw [es, es, t1, t2, V, Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
    omega_arith

/-- The products of different words: `∑ 2^(32 l) a_l (a_0 … a_{l-1})` for `1 ≤ l ≤ r`. -/
def sqCross (m : Mem) (base : Addr) (pa : Nat) : Nat → Nat
  | 0 => 0
  | r + 1 => sqCross m base pa r +
      2 ^ (32 * (r + 1)) * (w32 m base (pa + 4 * (r + 1)) * val32 m base pa (r + 1))

/-- The squares of the words `0 … n - 1`: `∑ 2^(64 l) a_l²`. -/
def sqDiag (m : Mem) (base : Addr) (pa : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sqDiag m base pa n + 2 ^ (64 * n) * (w32 m base (pa + 4 * n) * w32 m base (pa + 4 * n))

/-- A square is twice the products of different words, and the squares. -/
theorem sq_identity (m : Mem) (base : Addr) (pa : Nat) : ∀ n,
    2 * sqCross m base pa n + sqDiag m base pa (n + 1) = val32 m base pa (n + 1) * val32 m base pa (n + 1)
  | 0 => by
    rw [sqCross, sqDiag, sqDiag, val32_one]
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero]
  | n + 1 => by
    have ih := sq_identity m base pa n
    rw [sqCross, sqDiag, val32_succ m base pa (n + 1)]
    have hp : 2 ^ (64 * (n + 1)) = 2 ^ (32 * (n + 1)) * 2 ^ (32 * (n + 1)) := by
      rw [← Nat.pow_add]
      exact congrArg _ (by omega_arith)
    rw [hp]
    generalize 2 ^ (32 * (n + 1)) = P at *
    grind

/-- The rows `1 … r` of the products of different words, from the
accumulator's 37 words being zero. -/
theorem sqRows_ok {pa acc : Nat} (hpa : pa + 4 * 17 ≤ acc) (hsz : acc + 4 * 37 ≤ size) :
    ∀ (r : Nat) {s : State}, Bx s base size → Ptr s .esi pa → r ≤ 16 → val32 s.mem base acc 37 = 0 →
    WP isa (.block (sqRows acc r)) s fun u =>
      Outside base acc (4 * 37) s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s u ∧
      val32 u.mem base acc 37 = sqCross s.mem base pa r ∧
      val32 u.mem base (acc + 8 * r + 8) (35 - 2 * r) = 0
  | 0, s, _, _, _, hz => WP.block_nil ⟨Outside.refl _ _ _ _, Keeps.refl _ _, hz,
      (val32_zero_parts (a := 2) (b := 35) hz).2⟩
  | r + 1, s, hb, hp, hr, hz => by
    have hn := hb.nowrap
    rw [sqRows]
    refine WP.block_append (WP.mono (sqRows_ok hpa hsz r hb hp (by omega_arith) hz)
      fun s₁ ⟨O₁, K₁, V₁, Z₁⟩ => ?_)
    have hb₁ := hb.of_keeps K₁ (by decide)
    have hp₁ : Ptr s₁ .esi pa := hp.of_keeps K₁ (by decide) (by decide)
    have e37 : 2 * (r + 1) + 2 + (33 - 2 * r) = 37 := by omega_arith
    have eZ : val32 s₁.mem base (acc + 8 * (r + 1)) (2 + (33 - 2 * r)) = 0 := by
      rw [show 2 + (33 - 2 * r) = 35 - 2 * r by omega_arith,
        show acc + 8 * (r + 1) = acc + 8 * r + 8 by omega_arith]
      exact Z₁
    have ha' : w32 s₁.mem base (pa + 4 * (r + 1)) = w32 s.mem base (pa + 4 * (r + 1)) :=
      O₁.w32 (Or.inl (by omega_arith)) (by omega_arith)
    have hA' : val32 s₁.mem base pa (r + 1) = val32 s.mem base pa (r + 1) :=
      O₁.val32 (Or.inl (by omega_arith)) (by omega_arith)
    refine WP.mono (sqRow_ok hb₁ (i := r + 1) (r := 33 - 2 * r) hp₁ (by omega_arith) (by omega_arith)
      (by rw [e37]; exact hsz) eZ) fun u ⟨O, K, V, Z⟩ => ?_
    rw [e37] at O V
    refine ⟨O₁.trans O, K₁.trans K, ?_, ?_⟩
    · rw [V, V₁, ha', hA', sqCross]
    · rw [show 35 - 2 * (r + 1) = 33 - 2 * r by omega_arith]
      exact Z

/-- Words `0 … n - 1` doubled, with the carry word: a row's steps by one of
the words themselves. -/
theorem dblSteps_ok {acc : Nat} : ∀ (n : Nat) {s : State}, Bx s base size → (s.gpr .ecx).toNat = 1 →
    acc + 4 * n ≤ size →
    WP isa (.block (dblSteps acc n)) s fun u =>
      Outside base acc (4 * n) s.mem u.mem ∧
      val32 u.mem base acc n + 2 ^ (32 * n) * (u.gpr .ebx).toNat =
        2 * val32 s.mem base acc n + (s.gpr .ebx).toNat ∧
      Keeps [.eax, .ebx, .edx] s u
  | 0, s, _, _, _ => WP.block_nil ⟨Outside.refl _ _ _ _, by
      simp only [val32, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add], Keeps.refl _ _⟩
  | n + 1, s, hb, h1, hsz => by
    have hn := hb.nowrap
    rw [dblSteps]
    refine WP.block_append (WP.mono (dblSteps_ok n hb h1 (by omega_arith)) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have hb₁ := hb.of_keeps K₁ (by decide)
    have hy : readSrc s₁ (accWord acc n) = some (s₁.mem.readW (off base (acc + 4 * n)) 32) :=
      readSrc_bp hb₁ (by omega_arith)
    refine WP.mono (stepG_ok hb₁ hy (acc := acc) (j := n) (by omega_arith)) fun u ⟨m₂, b₂, K₂⟩ => ?_
    have ecx₁ : (s₁.gpr .ecx).toNat = 1 := by rw [K₁.1 _ (by decide)]; exact h1
    have hyw : (s₁.mem.readW (off base (acc + 4 * n)) 32).toNat = w32 s₁.mem base (acc + 4 * n) := rfl
    have tk : w32 s₁.mem base (acc + 4 * n) = w32 s.mem base (acc + 4 * n) :=
      O₁.w32 (Or.inr (Nat.le_refl _)) (by omega_arith)
    rw [ecx₁, hyw, tk, Nat.one_mul] at m₂ b₂
    obtain W := writeW32_outside s₁.mem base (d := acc + 4 * n)
      (BitVec.ofNat 32 (w32 s.mem base (acc + 4 * n) + (s₁.gpr .ebx).toNat + w32 s.mem base (acc + 4 * n)))
      (by omega_arith)
    rw [← m₂] at W
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega_arith)).trans (W.mono (by omega_arith) (by omega_arith)), ?_,
      K₁.trans K₂⟩
    obtain hlow : val32 u.mem base acc n = val32 s₁.mem base acc n :=
      W.val32 (Or.inl (Nat.le_refl _)) (by omega_arith)
    obtain htop : w32 u.mem base (acc + 4 * n) = (w32 s.mem base (acc + 4 * n) + (s₁.gpr .ebx).toNat +
        w32 s.mem base (acc + 4 * n)) % 2 ^ 32 := by
      rw [m₂, w32_write_self, BitVec.toNat_ofNat]
    rw [val32_succ u.mem base acc n, val32_succ s.mem base acc n, hlow, htop, b₂, pow32_succ n]
    generalize hxd : w32 s.mem base (acc + 4 * n) + (s₁.gpr .ebx).toNat + w32 s.mem base (acc + 4 * n) = x at *
    obtain hx := Nat.div_add_mod x (2 ^ 32)
    generalize 2 ^ (32 * n) = P at *
    grind

/-- The squares of the words `0 … n - 1` added at words `0 … 2n - 1`, with
the carry word. -/
theorem diagSteps_ok {pa acc : Nat} : ∀ (n : Nat) {s : State}, Bx s base size → Ptr s .esi pa →
    pa + 4 * n ≤ acc → acc + 8 * n ≤ size →
    WP isa (.block (diagSteps acc n)) s fun u =>
      Outside base acc (8 * n) s.mem u.mem ∧
      val32 u.mem base acc (2 * n) + 2 ^ (64 * n) * (u.gpr .ebx).toNat =
        val32 s.mem base acc (2 * n) + (s.gpr .ebx).toNat + sqDiag s.mem base pa n ∧
      Keeps [.eax, .ebx, .ecx, .edx] s u
  | 0, s, _, _, _, _ => WP.block_nil ⟨Outside.refl _ _ _ _, by
      simp only [Nat.mul_zero, val32, sqDiag, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero],
      Keeps.refl _ _⟩
  | n + 1, s, hb, hp, hpa, hsz => by
    have hn := hb.nowrap
    rw [diagSteps]
    refine WP.block_append (WP.mono (diagSteps_ok n hb hp (by omega_arith) (by omega_arith))
      fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have hb₁ := hb.of_keeps K₁ (by decide)
    have hp₁ : Ptr s₁ .esi pa := hp.of_keeps K₁ (by decide) (by decide)
    simp only [diagStep, List.cons_append, List.nil_append]
    refine wp_movS (readSrc_ptr hb₁ hp₁ (d := 4 * n) (by omega_arith)) fun s₂ u₂ _ => ?_
    have k₂ : Keeps [.eax, .ebx, .ecx, .edx] s₁ s₂ := u₂.keeps.mono (by decide)
    have hb₂ := hb₁.of_keeps k₂ (by decide)
    have hp₂ : Ptr s₂ .esi pa := hp₁.of_keeps k₂ (by decide) (by decide)
    have mem₂ : s₂.mem = s₁.mem := u₂.mem
    have a₁ : w32 s₁.mem base (pa + 4 * n) = w32 s.mem base (pa + 4 * n) :=
      O₁.w32 (Or.inl (by omega_arith)) (by omega_arith)
    have ecx₂ : (s₂.gpr .ecx).toNat = w32 s.mem base (pa + 4 * n) := by rw [u₂.gpr]; exact a₁
    have hy₂ : readSrc s₂ (bWord n) = some (s₂.mem.readW (off base (pa + 4 * n)) 32) :=
      readSrc_ptr hb₂ hp₂ (by omega_arith)
    have y₂ : (s₂.mem.readW (off base (pa + 4 * n)) 32).toNat = w32 s.mem base (pa + 4 * n) := by
      rw [mem₂]; exact a₁
    have ebx₂ : s₂.gpr .ebx = s₁.gpr .ebx := u₂.other _ (by decide)
    have w0 : w32 s₂.mem base (acc + 4 * (2 * n)) = w32 s.mem base (acc + 4 * (2 * n)) := by
      rw [mem₂]; exact O₁.w32 (Or.inr (by omega_arith)) (by omega_arith)
    refine WP.block_append (WP.mono (stepG_ok hb₂ hy₂ (acc := acc) (j := 2 * n) (by omega_arith))
      fun s₃ ⟨m₃, b₃, K₃⟩ => ?_)
    rw [ecx₂, y₂, ebx₂, w0] at m₃ b₃
    have hb₃ := hb₂.of_keeps K₃ (by decide)
    have w1 : w32 s₃.mem base (acc + 4 * (2 * n + 1)) = w32 s.mem base (acc + 4 * (2 * n + 1)) := by
      rw [m₃, w32_write_ne hn (by omega_arith) (by omega_arith) (Or.inr (by omega_arith)), mem₂]
      exact O₁.w32 (Or.inr (by omega_arith)) (by omega_arith)
    refine WP.mono (stepG_ok hb₃ (ys := .imm 0) (y := 0) rfl (acc := acc) (j := 2 * n + 1) (by omega_arith))
      fun u ⟨m₄, b₄, K₄⟩ => ?_
    have z0 : (0 : BitVec 32).toNat = 0 := rfl
    rw [z0, Nat.mul_zero, Nat.zero_add, b₃, w1] at m₄ b₄
    have W₃ : Outside base (acc + 4 * (2 * n)) 4 s₁.mem s₃.mem := by
      rw [m₃, mem₂]; exact writeW32_outside _ _ _ (by omega_arith)
    have W₄ : Outside base (acc + 4 * (2 * n + 1)) 4 s₃.mem u.mem := by
      rw [m₄]; exact writeW32_outside _ _ _ (by omega_arith)
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega_arith)).trans ((W₃.mono (by omega_arith) (by omega_arith)).trans
      (W₄.mono (by omega_arith) (by omega_arith))), ?_,
      K₁.trans (k₂.trans ((K₃.mono (by decide)).trans (K₄.mono (by decide))))⟩
    have hlow : val32 u.mem base acc (2 * n) = val32 s₁.mem base acc (2 * n) := by
      rw [W₄.val32 (Or.inl (by omega_arith)) (by omega_arith),
        W₃.val32 (Or.inl (by omega_arith)) (by omega_arith)]
    have h0 : w32 u.mem base (acc + 4 * (2 * n)) = (w32 s.mem base (pa + 4 * n) * w32 s.mem base (pa + 4 * n) +
        (s₁.gpr .ebx).toNat + w32 s.mem base (acc + 4 * (2 * n))) % 2 ^ 32 := by
      rw [W₄.w32 (Or.inl (by omega_arith)) (by omega_arith), m₃, w32_write_self, BitVec.toNat_ofNat]
    have h1 : w32 u.mem base (acc + 4 * (2 * n + 1)) = ((w32 s.mem base (pa + 4 * n) * w32 s.mem base (pa + 4 * n) +
        (s₁.gpr .ebx).toNat + w32 s.mem base (acc + 4 * (2 * n))) / 2 ^ 32 +
        w32 s.mem base (acc + 4 * (2 * n + 1))) % 2 ^ 32 := by
      rw [m₄, w32_write_self, BitVec.toNat_ofNat]
    rw [show 64 * n = 32 * (2 * n) by omega_arith] at V₁
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega_arith, val32_succ u.mem, val32_succ u.mem,
      val32_succ s.mem, val32_succ s.mem, hlow, h0, h1, b₄, sqDiag,
      show 64 * (n + 1) = 32 * (2 * n + 1 + 1) by omega_arith, show 64 * n = 32 * (2 * n) by omega_arith,
      pow32_succ (2 * n + 1), pow32_succ (2 * n)]
    generalize hx1 : w32 s.mem base (pa + 4 * n) * w32 s.mem base (pa + 4 * n) + (s₁.gpr .ebx).toNat +
      w32 s.mem base (acc + 4 * (2 * n)) = x1 at *
    generalize hx2 : x1 / 2 ^ 32 + w32 s.mem base (acc + 4 * (2 * n + 1)) = x2 at *
    obtain e1 := Nat.div_add_mod x1 (2 ^ 32)
    obtain e2 := Nat.div_add_mod x2 (2 ^ 32)
    generalize 2 ^ (32 * (2 * n)) = P at *
    grind

/-- The reduction's arithmetic: `P = L₀ + E H` with `E = 2⁵¹²`, the first
row leaves `H + 2⁹ L₀ = L₁ + F (M + D G)` (`F = 2⁶⁴`, `F D = E`), the second
`R = M + D (G + 2⁹ L₁)`: `E F R = P + (L₀ + E L₁) p` and `R < 2p`. -/
theorem p521_fold_arith {E F D L0 L1 H M G A p R : Nat} (hE : F * D = E) (hp : p + 1 = 512 * E)
    (hF : 512 ≤ F) (hL0 : L0 < E) (hL1 : L1 < F) (hV : L0 + E * H = A * A)
    (hH : H + 512 * L0 = L1 + F * (M + D * G)) (hR : R = M + D * (G + 512 * L1)) (hA : A < p) :
    E * F * R = A * A + (L0 + E * L1) * p ∧ R < 2 * p := by
  have key : E * F * R + (L0 + E * L1) + 512 * E * L0 =
      A * A + (L0 + E * L1) * (p + 1) + 512 * E * L0 := by
    rw [hp, ← hV, hR]
    have h2 : E * (H + 512 * L0) = E * (L1 + F * (M + D * G)) := congrArg _ hH
    subst hE
    grind
  have eq : E * F * R = A * A + (L0 + E * L1) * p := by
    rw [Nat.mul_add (L0 + E * L1) p 1, Nat.mul_one] at key
    omega_arith
  refine ⟨eq, ?_⟩
  apply Nat.lt_of_not_le
  intro h
  have h1 : E * F * (2 * p) ≤ E * F * R := Nat.mul_le_mul_left _ h
  have hE0 : 0 < E := by omega_using [hL0]
  have hEF : E * 512 ≤ E * F := Nat.mul_le_mul_left _ hF
  have hpEF : p ≤ E * F := by omega_using [hp, hEF]
  have h2 : A * A < p * p := Nat.mul_lt_mul_of_lt_of_lt hA hA
  have h3 : p * p ≤ E * F * p := Nat.mul_le_mul_right _ hpEF
  have hU : L0 + E * L1 ≤ E * F := by
    have : E * (L1 + 1) ≤ E * F := Nat.mul_le_mul_left _ hL1
    rw [Nat.mul_add, Nat.mul_one] at this
    omega_using [this, hL0]
  have h4 : (L0 + E * L1) * p ≤ E * F * p := Nat.mul_le_mul_right _ hU
  rw [Nat.mul_left_comm (E * F) 2 p] at h1
  omega_using [h1, h2, h3, h4, eq]

/-- `2⁵²¹ = 2⁹ 2⁵¹²`. -/
theorem p521_succ : p521Prime + 1 = 512 * 2 ^ (32 * 16) := by
  have h := Nat.pow_add 2 9 (32 * 16)
  simp only [Nat.reduceMul, Nat.reduceAdd] at h
  have hpos := Nat.two_pow_pos 512
  unfold p521Prime
  simp only [Nat.reduceMul]
  generalize (2 : Nat) ^ 521 = Q at *
  generalize (2 : Nat) ^ 512 = E at *
  omega_arith

/-- Powers of two with equal exponents. -/
theorem two_pow_congr {a b : Nat} (h : a = b) : (2 : Nat) ^ a = 2 ^ b := h ▸ rfl

theorem sq_512 (E : Nat) : 512 * E * (512 * E) = E * (262144 * E) := by grind

/-- A carry word that a sum below `P` cannot have. -/
theorem no_carry {X P e Y : Nat} (h : X + P * e = Y) (hY : Y < P) : X = Y := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rw [Nat.mul_zero, Nat.add_zero] at h; exact h
  · have := Nat.le_mul_of_pos_right P he
    omega_using [h, hY, this]

/-- A number's two parts, the power of two that is between them named. -/
theorem val32_split (m : Mem) (d j k : Nat) {P : Nat} (hP : 2 ^ (32 * j) = P) :
    val32 m base d (j + k) = val32 m base d j + P * val32 m base (d + 4 * j) k :=
  hP ▸ val32_append m base d j k

/-- The reduction: from the square `A²` of `A < p` in the accumulator's 37
words, its words `18 … 36` hold `(A² + U p) / 2⁵⁷⁶`, below `2p`. -/
theorem p521Fold_ok (hb : Bx s base size) {acc A : Nat} (hsz : acc + 4 * 37 ≤ size)
    (hV : val32 s.mem base acc 37 = A * A) (hA : A < p521Prime) :
    WP isa (.block (p521Fold acc)) s fun u =>
      Outside base acc (4 * 37) s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s u ∧
      val32 u.mem base (acc + 72) 19 < 2 * p521Prime ∧
      ∃ U, 2 ^ (32 * 18) * val32 u.mem base (acc + 72) 19 = A * A + U * p521Prime := by
  have hn := hb.nowrap
  -- the powers of two, named
  have hp1 := p521_succ
  have hE0 := Nat.two_pow_pos (32 * 16)
  have h18 := pow32_add 16 2
  simp only [Nat.reduceAdd] at h18
  have hFD := (pow32_add 2 14).symm
  simp only [Nat.reduceAdd] at hFD
  have h4 : (2 : Nat) ^ (32 * 4) = 340282366920938463463374607431768211456 := by decide
  generalize hF : (2 : Nat) ^ (32 * 2) = F at h18 hFD
  have hF64 : F = 18446744073709551616 := by rw [← hF]
  generalize hD : (2 : Nat) ^ (32 * 14) = D at hFD
  generalize hE : (2 : Nat) ^ (32 * 16) = E at h18 hFD hp1 hE0
  generalize hB : (2 : Nat) ^ (32 * 18) = B at h18
  have d37 : val32 s.mem base acc 37 = val32 s.mem base acc 16 + E *
      (val32 s.mem base (acc + 64) 18 + B * val32 s.mem base (acc + 136) 3) := by
    rw [show 37 = 16 + (18 + 3) from rfl, val32_split _ _ 16 (18 + 3) hE, val32_split _ _ 18 3 hB,
      show acc + 4 * 16 = acc + 64 by omega_arith, show acc + 64 + 4 * 18 = acc + 136 by omega_arith]
  have hL0 : val32 s.mem base acc 16 < E := hE ▸ val32_lt s.mem base acc 16
  have hAE : A < 512 * E := by omega_using [hA, hp1]
  have hAA : A * A < 512 * E * (512 * E) := Nat.mul_lt_mul_of_lt_of_lt hAE hAE
  rw [sq_512 E] at hAA
  rw [hV, h18] at d37
  have hX : val32 s.mem base (acc + 64) 18 + E * F * val32 s.mem base (acc + 136) 3 < 262144 * E := by
    refine Nat.lt_of_mul_lt_mul_left (a := E) ?_
    omega_using [d37, hAA]
  have hT : val32 s.mem base (acc + 136) 3 = 0 := by
    rcases Nat.eq_zero_or_pos (val32 s.mem base (acc + 136) 3) with h | h
    · exact h
    · have := Nat.le_mul_of_pos_right (E * F) h
      rw [hF64] at this hX
      omega_using [hX, this, hE0]
  rw [hT, Nat.mul_zero, Nat.add_zero] at hX d37
  have z136 := (val32_zero_parts (a := 2) (b := 1) hT).1
  have z144 : val32 s.mem base (acc + 144) 1 = 0 := by
    have := (val32_zero_parts (a := 2) (b := 1) hT).2
    rw [show acc + 136 + 4 * 2 = acc + 144 by omega_arith] at this
    exact this
  simp only [p521Fold, List.cons_append, List.nil_append]
  refine wp_movS rfl fun s₁ u₁ _ => ?_
  have k₁ : Keeps [.eax, .ebx, .ecx, .edx] s s₁ := u₁.keeps.mono (by decide)
  have hb₁ := hb.of_keeps k₁ (by decide)
  have mem₁ : s₁.mem = s.mem := u₁.mem
  have ecx₁ : (s₁.gpr .ecx).toNat = 512 := by rw [u₁.gpr]; rfl
  have hY₁ := ysOk_acc hb₁ (d := acc) (acc := acc + 64) (len := 4 * 16 + 8) (N := 16) (by omega_arith)
    (Or.inl (by omega_arith))
  have hYv₁ : yVal (fun j => s₁.mem.readW (off base (acc + 4 * j)) 32) 16 = val32 s.mem base acc 16 := by
    rw [yVal_val32, mem₁]
  refine WP.block_append (WP.mono (rowG_ok hb₁ (by decide) hY₁ (by omega_arith) ?_) fun s₂ ⟨O₂, V₂, K₂⟩ => ?_)
  · rewrite [hYv₁, mem₁, ecx₁]
    simp only [Nat.reduceAdd]
    rewrite [hB, h18, hF64]
    omega_using [hX, hL0]
  rw [hYv₁, ecx₁] at V₂
  rw [mem₁] at O₂ V₂
  have V₂' : val32 s₂.mem base (acc + 64) 18 =
      val32 s.mem base (acc + 64) 18 + 512 * val32 s.mem base acc 16 := V₂
  have hb₂ := hb₁.of_keeps K₂ (by decide)
  have ecx₂ : (s₂.gpr .ecx).toNat = 512 := by rw [K₂.1 _ (by decide)]; exact ecx₁
  have hY₂ := ysOk_acc hb₂ (d := acc + 64) (acc := acc + 128) (len := 4 * 2 + 8) (N := 2) (by omega_arith)
    (Or.inl (by omega_arith))
  have hYv₂ : yVal (fun j => s₂.mem.readW (off base (acc + 64 + 4 * j)) 32) 2 =
      val32 s₂.mem base (acc + 64) 2 := yVal_val32 _ _ _ _
  have d18 : val32 s₂.mem base (acc + 64) 18 = val32 s₂.mem base (acc + 64) 2 + F *
      (val32 s₂.mem base (acc + 72) 14 + D * val32 s₂.mem base (acc + 128) 2) := by
    rw [show 18 = 2 + (14 + 2) from rfl, val32_split _ _ 2 (14 + 2) hF, val32_split _ _ 14 2 hD,
      show acc + 64 + 4 * 2 = acc + 72 by omega_arith, show acc + 72 + 4 * 14 = acc + 128 by omega_arith]
  have d4 : val32 s₂.mem base (acc + 128) 4 = val32 s₂.mem base (acc + 128) 2 +
      F * val32 s₂.mem base (acc + 136) 2 := by
    rw [show 4 = 2 + 2 from rfl, val32_split _ _ 2 2 hF, show acc + 128 + 4 * 2 = acc + 136 by omega_arith]
  have z136₂ : val32 s₂.mem base (acc + 136) 2 = 0 := by
    rw [O₂.val32 (Or.inr (by omega_arith)) (by omega_arith)]; exact z136
  rw [z136₂, Nat.mul_zero, Nat.add_zero] at d4
  have hL1 : val32 s₂.mem base (acc + 64) 2 < F := hF ▸ val32_lt s₂.mem base (acc + 64) 2
  have hG : val32 s₂.mem base (acc + 128) 2 < 262656 := by
    refine Nat.lt_of_mul_lt_mul_left (a := E) ?_
    have h := d18
    rw [Nat.mul_add, ← Nat.mul_assoc, hFD] at h
    omega_using [h, V₂', hX, hL0]
  refine WP.mono (rowG_ok hb₂ (by decide) hY₂ (by omega_arith) ?_) fun u ⟨O₃, V₃, K₃⟩ => ?_
  · rewrite [hYv₂, ecx₂]
    simp only [Nat.reduceAdd]
    rewrite [d4, h4]
    rw [hF64] at hL1
    omega_using [hG, hL1]
  rw [hYv₂, ecx₂] at V₃
  have V₃' : val32 u.mem base (acc + 128) 4 =
      val32 s₂.mem base (acc + 128) 4 + 512 * val32 s₂.mem base (acc + 64) 2 := V₃
  generalize hB4 : (2 : Nat) ^ (32 * 4) = B4
  have dR : val32 u.mem base (acc + 72) 19 = val32 u.mem base (acc + 72) 14 + D *
      (val32 u.mem base (acc + 128) 4 + B4 * val32 u.mem base (acc + 144) 1) := by
    rw [show 19 = 14 + (4 + 1) from rfl, val32_split _ _ 14 (4 + 1) hD, val32_split _ _ 4 1 hB4,
      show acc + 72 + 4 * 14 = acc + 128 by omega_arith, show acc + 128 + 4 * 4 = acc + 144 by omega_arith]
  have tM : val32 u.mem base (acc + 72) 14 = val32 s₂.mem base (acc + 72) 14 :=
    O₃.val32 (Or.inl (by omega_arith)) (by omega_arith)
  have t144 : val32 u.mem base (acc + 144) 1 = 0 := by
    rw [O₃.val32 (Or.inr (by omega_arith)) (by omega_arith),
      O₂.val32 (Or.inr (by omega_arith)) (by omega_arith)]
    exact z144
  have hR : val32 u.mem base (acc + 72) 19 = val32 s₂.mem base (acc + 72) 14 + D *
      (val32 s₂.mem base (acc + 128) 2 + 512 * val32 s₂.mem base (acc + 64) 2) := by
    rw [dR, tM, t144, V₃', d4]
    simp only [Nat.mul_zero, Nat.add_zero]
  obtain ⟨heq, hlt⟩ := p521_fold_arith (p := p521Prime) hFD hp1 (by rw [hF64]; decide) hL0 hL1 d37.symm
    (V₂'.symm.trans d18) hR hA
  refine ⟨(O₂.mono (by omega_arith) (by omega_arith)).trans (O₃.mono (by omega_arith) (by omega_arith)),
    k₁.trans ((K₂.mono (by decide)).trans (K₃.mono (by decide))), hlt,
    ⟨val32 s.mem base acc 16 + E * val32 s₂.mem base (acc + 64) 2, ?_⟩⟩
  rewrite [h18]
  exact heq

/-- The squares' sum reads only the operand. -/
theorem sqDiag_congr {m m' : Mem} {pa : Nat} : ∀ n,
    (∀ j < n, w32 m' base (pa + 4 * j) = w32 m base (pa + 4 * j)) →
    sqDiag m' base pa n = sqDiag m base pa n
  | 0, _ => rfl
  | n + 1, h => by
    rw [sqDiag, sqDiag, sqDiag_congr n fun j hj => h j (by omega_arith), h n (by omega_arith)]

/-- P-521's square: the accumulator's words from 18 hold `T < 2p` with
`2⁵⁷⁶ T ≡ A²`, as the rows leave them. -/
theorem p521Square_ok (hb : Bx s base 8192) {a : Nat} (hp : Ptr s .esi a) (ha : a + 4 * (2 * 9) ≤ own 9)
    (hA : val32 s.mem base a (2 * 9) < p521Prime) :
    WP isa (.block p521Square) s fun u =>
      Outside base (own 9) (24 * 9 + 4) s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx] s u ∧
      val32 u.mem base (own 9 + 4 * (2 * 9)) (2 * 9 + 1) < 2 * p521Prime ∧
      ∃ U, 2 ^ (32 * (2 * 9)) * val32 u.mem base (own 9 + 4 * (2 * 9)) (2 * 9 + 1) =
        val32 s.mem base a (2 * 9) * val32 s.mem base a (2 * 9) + U * p521Prime := by
  have hn := hb.nowrap
  have ho : own 9 = 3520 := rfl
  rewrite [ho, show 2 * 9 = 18 from rfl, show 4 * 18 = 72 from rfl, show 18 + 1 = 19 from rfl,
    show 24 * 9 + 4 = 220 from rfl]
  rw [ho, show 2 * 9 = 18 from rfl] at ha
  rw [show 2 * 9 = 18 from rfl] at hA
  -- the powers of two, named
  have hp1 := p521_succ
  have hE0 := Nat.two_pow_pos (32 * 16)
  have h17 := pow32_succ 16
  simp only [Nat.reduceAdd] at h17
  have h34 := pow32_add 17 17
  simp only [Nat.reduceAdd] at h34
  generalize hE : (2 : Nat) ^ (32 * 16) = E at hp1 h17 hE0
  generalize hP17 : (2 : Nat) ^ (32 * 17) = P17 at h17 h34
  generalize hP34 : (2 : Nat) ^ (32 * 34) = P34 at h34
  -- the operand's top word is zero
  have a18 : val32 s.mem base a 18 = val32 s.mem base a 17 := by
    have h : val32 s.mem base a 18 = val32 s.mem base a 17 + P17 * w32 s.mem base (a + 4 * 17) :=
      hP17 ▸ val32_succ s.mem base a 17
    rw [h17] at h
    rw [h] at hA ⊢
    rcases Nat.eq_zero_or_pos (w32 s.mem base (a + 4 * 17)) with hz | hz
    · rw [hz, Nat.mul_zero, Nat.add_zero]
    · have := Nat.le_mul_of_pos_right (2 ^ 32 * E) hz
      omega_using [hA, hp1, this, hE0]
  have hA17 : val32 s.mem base a 17 < P17 := hP17 ▸ val32_lt s.mem base a 17
  have hAA : val32 s.mem base a 17 * val32 s.mem base a 17 < P34 := by
    rw [h34]
    exact Nat.mul_lt_mul_of_lt_of_lt hA17 hA17
  simp only [p521Square, ho, List.append_assoc]
  refine WP.block_append (WP.mono (zeroWords_ok hb (acc := 3520) (n := 37) (by omega_arith))
    fun s₁ ⟨O₁, Z₁, K₁⟩ => ?_)
  have hb₁ := hb.of_keeps K₁ (by decide)
  have hp₁ : Ptr s₁ .esi a := hp.of_keeps K₁ (by decide) (by decide)
  refine WP.block_append (WP.mono (sqRows_ok (size := 8192) (pa := a) (acc := 3520) (by omega_arith)
    (by omega_arith) 16 hb₁ hp₁ (Nat.le_refl _) Z₁) fun s₂ ⟨O₂, K₂, V₂, Z₂⟩ => ?_)
  have Z₂' : val32 s₂.mem base 3656 3 = 0 := Z₂
  have hb₂ := hb₁.of_keeps K₂ (by decide)
  have hp₂ : Ptr s₂ .esi a := hp₁.of_keeps K₂ (by decide) (by decide)
  have O₁' : Outside base 3520 148 s.mem s₁.mem := O₁
  have O₂' : Outside base 3520 148 s₁.mem s₂.mem := O₂
  have A₁ : val32 s₁.mem base a 17 = val32 s.mem base a 17 :=
    O₁'.val32 (Or.inl (by omega_arith)) (by omega_arith)
  have id := sq_identity s₁.mem base a 16
  rw [A₁] at id
  have s37 : ∀ m : Mem, val32 m base 3520 37 = val32 m base 3520 34 + P34 * val32 m base 3656 3 :=
    fun m => by rw [show 37 = 34 + 3 from rfl, val32_split _ _ 34 3 hP34]
  have C₂ : val32 s₂.mem base 3520 34 = sqCross s₁.mem base a 16 := by
    rw [← V₂, s37, Z₂', Nat.mul_zero, Nat.add_zero]
  simp only [dblWords, List.cons_append, List.nil_append]
  refine wp_movS rfl fun s₃ u₃ _ => ?_
  refine wp_movS rfl fun s₄ u₄ _ => ?_
  have k₄ : Keeps [.eax, .ebx, .ecx, .edx] s₂ s₄ := (u₃.keeps.mono (by decide)).trans (u₄.keeps.mono (by decide))
  have hb₄ := hb₂.of_keeps k₄ (by decide)
  have mem₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  have ecx₄ : (s₄.gpr .ecx).toNat = 1 := by rw [u₄.other _ (by decide), u₃.gpr]; rfl
  have ebx₄ : (s₄.gpr .ebx).toNat = 0 := by rw [u₄.gpr]; rfl
  refine WP.block_append (WP.mono (dblSteps_ok (acc := 3520) 34 hb₄ ecx₄ (by omega_arith))
    fun s₅ ⟨O₅, V₅, K₅⟩ => ?_)
  rewrite [hP34, mem₄, ebx₄, Nat.add_zero, C₂] at V₅
  rw [mem₄] at O₅
  have D₅ : val32 s₅.mem base 3520 34 = 2 * sqCross s₁.mem base a 16 :=
    no_carry V₅ (by omega_using [id, hAA])
  refine wp_movS rfl fun s₆ u₆ _ => ?_
  have k₆ : Keeps [.eax, .ebx, .ecx, .edx] s₂ s₆ :=
    k₄.trans ((K₅.mono (by decide)).trans (u₆.keeps.mono (by decide)))
  have hb₆ := hb₂.of_keeps k₆ (by decide)
  have hp₆ : Ptr s₆ .esi a := hp₂.of_keeps k₆ (by decide) (by decide)
  have mem₆ : s₆.mem = s₅.mem := u₆.mem
  have ebx₆ : (s₆.gpr .ebx).toNat = 0 := by rw [u₆.gpr]; rfl
  have O₅' : Outside base 3520 148 s₂.mem s₅.mem := O₅.mono (Nat.le_refl _) (by omega_arith)
  refine WP.block_append (WP.mono (diagSteps_ok (pa := a) (acc := 3520) 17 hb₆ hp₆ (by omega_arith)
    (by omega_arith)) fun s₇ ⟨O₇, V₇, K₇⟩ => ?_)
  rewrite [show 64 * 17 = 32 * 34 from rfl, show 2 * 17 = 34 from rfl, hP34, mem₆] at V₇
  rw [mem₆] at O₇
  have O₇' : Outside base 3520 148 s₅.mem s₇.mem := O₇.mono (Nat.le_refl _) (by omega_arith)
  have dg : sqDiag s₅.mem base a 17 = sqDiag s₁.mem base a 17 :=
    sqDiag_congr 17 fun j hj => (O₂'.trans O₅').w32 (Or.inl (by omega_arith)) (by omega_arith)
  have V₇' : val32 s₇.mem base 3520 34 + P34 * (s₇.gpr .ebx).toNat =
      val32 s.mem base a 17 * val32 s.mem base a 17 := by
    rw [V₇, D₅, ebx₆, dg, Nat.add_zero]
    exact id
  have P₇ := no_carry V₇' hAA
  have T₇ : val32 s₇.mem base 3656 3 = 0 := by
    rw [O₇.val32 (Or.inr (by omega_arith)) (by omega_arith),
      O₅.val32 (Or.inr (by omega_arith)) (by omega_arith)]
    exact Z₂'
  have hb₇ := hb₆.of_keeps K₇ (by decide)
  refine WP.mono (p521Fold_ok hb₇ (acc := 3520) (A := val32 s.mem base a 17) (by omega_arith)
    (by rw [s37, T₇, Nat.mul_zero, Nat.add_zero]; exact P₇) (a18 ▸ hA)) fun u ⟨O, K, hlt, ⟨U, hU⟩⟩ => ?_
  refine ⟨?_, (K₁.mono (by decide)).trans (K₂.trans (k₆.trans (K₇.trans K))), hlt, ⟨U, ?_⟩⟩
  · exact ((O₁'.trans (O₂'.trans (O₅'.trans (O₇'.trans O)))).mono (Nat.le_refl _) (by omega_arith))
  · rewrite [a18]; exact hU

end VG.Proof.Weierstrass.X86.Mont

end

/-! # Selecting the square from public operand pointers -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Mont
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

theorem square_pointer_eq {s : State} {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (pa : Ptr s .edi a) (pb : Ptr s .esi b) (he : (s.gpr .edi - s.gpr .esi == 0) = true) : a = b := by
  have h : s.gpr .edi - s.gpr .esi = 0 := by simpa only [beq_iff_eq] using he
  have h' := BitVec.sub_eq_iff_eq_add.mp h
  have hz : ∀ x : BitVec 32, (0 : BitVec 32) + x = x := BitVec.zero_add
  rw [hz, pa, pb] at h'
  have h'' := congrArg (fun x : BitVec 32 => x - s.gpr .ebp) h'
  rw [BitVec.add_comm (s.gpr .ebp), BitVec.add_sub_cancel,
    BitVec.add_comm (s.gpr .ebp), BitVec.add_sub_cancel] at h''
  have hnat := congrArg BitVec.toNat h''
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hnat

/-! ## The product by columns

The columns of the product and of the reduction as sums (`colAt`), their
values put together (`num_colAt`), and the code's columns: `lowCols_ok`,
`cols_ok70` for the rest, and the product and the square (`colsMul_ok`,
`colsSquare_ok`). -/

section

open VG.Impl.X25519.X86 (Term)
open VG.Proof.X25519.X86 (v wv wd acc colv tval treads num num_succ num_congr num_add sub Keep Ctx)

/-- `h 0 + … + h (n - 1)`. -/
def sumTo (h : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo h n + h n

theorem sumTo_congr {f g : Nat → Nat} : ∀ {n : Nat}, (∀ i < n, f i = g i) → sumTo f n = sumTo g n
  | 0, _ => rfl
  | n + 1, h => by
    rw [sumTo, sumTo, sumTo_congr fun i hi => h i (by omega_using [hi]), h n (by omega_using [])]

theorem sumTo_zero {f : Nat → Nat} {n : Nat} : ∀ m, (∀ i, n ≤ i → f i = 0) → sumTo f (n + m) = sumTo f n
  | 0, _ => rfl
  | m + 1, h => by
    rw [← Nat.add_assoc, sumTo, sumTo_zero m h, h _ (by omega_using []), Nat.add_zero]

theorem sumTo_add (f g : Nat → Nat) : ∀ n, sumTo (fun i => f i + g i) n = sumTo f n + sumTo g n
  | 0 => rfl
  | n + 1 => by rw [sumTo, sumTo, sumTo, sumTo_add f g n]; omega_using []

theorem sumTo_low (h : Nat → Nat) : ∀ n, sumTo h (n + 1) = h 0 + sumTo (fun i => h (i + 1)) n
  | 0 => by simp only [sumTo]; omega_using []
  | n + 1 => by rw [sumTo, sumTo_low h n, sumTo]; omega_using []

theorem sumTo_rev (h : Nat → Nat) : ∀ n, sumTo h (n + 1) = sumTo (fun i => h (n - i)) (n + 1)
  | 0 => rfl
  | n + 1 => by
    rw [sumTo, sumTo_rev h n, sumTo_low (fun i => h (n + 1 - i)), Nat.sub_zero, Nat.add_comm]
    refine congrArg (h (n + 1) + ·) (sumTo_congr fun i _ => ?_)
    rw [Nat.add_sub_add_right]

theorem sumTo_le {h : Nat → Nat} {B : Nat} : ∀ n, (∀ i, h i ≤ B) → sumTo h n ≤ n * B
  | 0, _ => Nat.zero_le _
  | n + 1, hB => by
    have h1 := sumTo_le n hB; have h2 := hB n
    rw [sumTo, Nat.succ_mul]; omega_using [h1, h2]

/-- Column `c` of the product of the numbers of `N` words `f` and `g`. -/
def colAt (f g : Nat → Nat) (N c : Nat) : Nat :=
  sumTo (fun i => if i < N ∧ c - i < N then f i * g (c - i) else 0) (c + 1)

/-- The columns, summed by rows instead. -/
theorem colAt_rows (f g : Nat → Nat) (N c : Nat) :
    colAt f g N c = sumTo (fun i => if i ≤ c ∧ c - i < N then f i * g (c - i) else 0) N := by
  have e1 := sumTo_zero (f := fun i => if i < N ∧ i ≤ c ∧ c - i < N then f i * g (c - i) else 0) (n := c + 1) N
    fun i hi => ite_eq_right (by omega_using [hi])
  have e2 := sumTo_zero (f := fun i => if i < N ∧ i ≤ c ∧ c - i < N then f i * g (c - i) else 0) (n := N) (c + 1)
    fun i hi => ite_eq_right (by omega_using [hi])
  rw [Nat.add_comm] at e2
  rw [e1] at e2
  rw [colAt]
  refine Eq.trans (sumTo_congr fun i hi => ?_) (e2.trans (sumTo_congr fun i hi => ?_))
  · simp only [Nat.lt_succ_iff.mp hi, true_and]
  · simp only [hi, true_and]

theorem colAt_le {f g : Nat → Nat} (hf : ∀ i, f i < 2 ^ 32) (hg : ∀ i, g i < 2 ^ 32) (N c : Nat) :
    colAt f g N c ≤ N * 2 ^ 64 := by
  rw [colAt_rows]
  refine sumTo_le N fun i => ?_
  split
  · have h := Nat.mul_le_mul (Nat.le_of_lt (hf i)) (Nat.le_of_lt (hg (c - i)))
    rw [← Nat.pow_add] at h
    exact h
  · exact Nat.zero_le _

/-- A window of a number's words: `g` from word `n`. -/
theorem num_window (g : Nat → Nat) (N n : Nat) : ∀ M,
    num (fun c => if n ≤ c ∧ c - n < N then g (c - n) else 0) M = (2 ^ 32) ^ n * num g (min N (M - n))
  | 0 => by simp [num]
  | M + 1 => by
    rw [num_succ, num_window g N n M]
    by_cases h : n ≤ M ∧ M - n < N
    · have e1 : min N (M - n) = M - n := by omega_using [h]
      have e2 : min N (M + 1 - n) = (M - n) + 1 := by omega_using [h]
      rw [ite_eq_left h, e1, e2, num_succ, Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add,
        Nat.add_sub_cancel' h.1]
    · have e : min N (M - n) = min N (M + 1 - n) := by omega_using [h]
      rw [ite_eq_right h, e, Nat.mul_zero, Nat.add_zero]

/-- The columns of a product, put together. -/
theorem num_colAt (f g : Nat → Nat) (N : Nat) :
    num (colAt f g N) (2 * N) = num f N * num g N := by
  have row : ∀ n ≤ N, num (fun c => sumTo (fun i => if i ≤ c ∧ c - i < N then f i * g (c - i) else 0) n) (2 * N) =
      num f n * num g N := by
    intro n
    induction n with
    | zero =>
      intro _
      simp only [sumTo, num, Nat.zero_mul]
      generalize 2 * N = M
      induction M with
      | zero => rfl
      | succ M ih => rw [num_succ, ih]; rfl
    | succ n ih =>
      intro hn
      have e : ∀ c, (if n ≤ c ∧ c - n < N then f n * g (c - n) else 0) =
          f n * (if n ≤ c ∧ c - n < N then g (c - n) else 0) := fun c => by
        split
        · rfl
        · rw [Nat.mul_zero]
      have hm : min N (2 * N - n) = N := by omega_using [hn]
      simp only [sumTo, e]
      rw [num_add, ih (by omega_using [hn]), VG.Proof.X25519.X86.num_mul, num_window, hm, num_succ, Nat.add_mul,
        Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_left_comm]
  rw [← row N (Nat.le_refl _)]
  exact num_congr fun c _ => colAt_rows f g N c

theorem num_split (f : Nat → Nat) (n : Nat) : ∀ k,
    num f (n + k) = num f n + (2 ^ 32) ^ n * num (fun j => f (n + j)) k
  | 0 => by simp [num]
  | k + 1 => by
    rw [← Nat.add_assoc, num_succ, num_split f n k, num_succ, Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add,
      Nat.add_assoc]

theorem colv_append (m : Mem) (x : BitVec 32) (as bs : List Term) :
    colv m x (as ++ bs) = colv m x as + colv m x bs := by
  simp only [colv, List.map_append, List.sum_append_nat]

theorem colv_filterMap (m : Mem) (x : BitVec 32) (f : Nat → Option Term) : ∀ n,
    colv m x ((List.range n).filterMap f) = sumTo (fun i => ((f i).map (tval m x)).getD 0) n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.filterMap_append, colv_append, colv_filterMap m x f n, sumTo]
    refine congrArg _ ?_
    cases h : f n with
    | none => simp [h, colv]
    | some t => simp [h, colv]

theorem mulTerms_colv (m : Mem) (x : BitVec 32) (A B N c : Nat) :
    colv m x (mulTerms A B N c) = colAt (fun i => wv m x (A + 4 * i)) (fun i => wv m x (B + 4 * i)) N c := by
  rw [mulTerms, colv_filterMap, colAt]
  refine sumTo_congr fun i _ => ?_
  split <;> rfl

theorem sqTerms_colv (m : Mem) (x : BitVec 32) (A N c : Nat) :
    colv m x (sqTerms A N c) = colAt (fun i => wv m x (A + 4 * i)) (fun i => wv m x (A + 4 * i)) N c := by
  have hf : ∀ i, ((if c - i < N ∧ 2 * i ≤ c then
        some (if 2 * i = c then Term.mulM (A + 4 * i) (A + 4 * i) else .mulM2 (A + 4 * i) (A + 4 * (c - i)))
      else none).map (tval m x)).getD 0 =
      if c - i < N ∧ 2 * i ≤ c then (if 2 * i = c then 1 else 2) * (wv m x (A + 4 * i) * wv m x (A + 4 * (c - i)))
      else 0 := by
    intro i
    by_cases h1 : c - i < N ∧ 2 * i ≤ c
    · rw [ite_eq_left h1, ite_eq_left h1]
      by_cases h2 : 2 * i = c
      · have : c - i = i := by omega_using [h2]
        rw [ite_eq_left h2, ite_eq_left h2, this, Nat.one_mul]; rfl
      · rw [ite_eq_right h2, ite_eq_right h2]; rfl
    · rw [ite_eq_right h1, ite_eq_right h1]; rfl
  rw [sqTerms, colv_filterMap, colAt, sumTo_congr fun i _ => hf i]
  generalize wv m x = w
  generalize hF : (fun i => _) = f
  generalize hG : (fun i => _) = g
  have key : ∀ i, i < c + 1 → f i + f (c - i) = g i + g (c - i) := by
    intro i hi
    have hi' : i ≤ c := by omega_using [hi]
    subst hF hG
    simp only [Nat.sub_sub_self hi', Nat.mul_comm (w (A + 4 * (c - i)))]
    generalize w (A + 4 * i) * w (A + 4 * (c - i)) = P
    by_cases hN : i < N ∧ c - i < N
    · rw [ite_eq_left hN, ite_eq_left hN.symm]
      simp only [hN, true_and]
      rcases Nat.lt_trichotomy (2 * i) c with h | h | h
      · rw [ite_eq_left (Nat.le_of_lt h), ite_eq_right (Nat.ne_of_lt h), ite_eq_right (by omega_using [h, hi'])]
        omega_using []
      · rw [ite_eq_left (Nat.le_of_eq h), ite_eq_left h, ite_eq_left (by omega_using [h]), ite_eq_left (by omega_using [h])]
        omega_using []
      · rw [ite_eq_right (by omega_using [h]), ite_eq_left (by omega_using [h]), ite_eq_right (by omega_using [h, hi'])]
        omega_using []
    · rw [ite_eq_right (fun h => hN (by omega_using [h, hi'])), ite_eq_right (fun h => hN (by omega_using [h, hi'])),
        ite_eq_right hN, ite_eq_right (fun h => hN h.symm)]
  have e1 := sumTo_rev f c
  have e2 := sumTo_rev g c
  have e3 := sumTo_add f (fun i => f (c - i)) (c + 1)
  have e4 := sumTo_add g (fun i => g (c - i)) (c + 1)
  have e5 := sumTo_congr key
  omega_using [e1, e2, e3, e4, e5]

theorem redTerms_colv (m : Mem) (x : BitVec 32) (Q M N c : Nat) :
    colv m x (redTerms Q M N c) +
        (if c < N then wv m x (Q + 4 * c) * (mw M 0).toNat else 0) =
      colAt (fun i => wv m x (Q + 4 * i)) (fun i => (mw M i).toNat) N c := by
  rw [redTerms, colv_filterMap, colAt, sumTo, Nat.sub_self]
  congr 1
  · refine sumTo_congr fun i _ => ?_
    by_cases h : i < N ∧ c - i < N
    · by_cases hz : mw M (c - i) = 0
      · simp only [h, hz, ne_eq, not_true_eq_false, and_false, ite_false, ite_true, Option.map_none, Option.getD_none,
          and_self]
        rfl
      · simp only [h, hz, ne_eq, not_false_eq_true, ite_true, Option.map_some, Option.getD_some,
          and_self, tval]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ⟨h'.1, h'.2.1⟩)]
      rfl
  · by_cases h : c < N
    · rw [ite_eq_left h, ite_eq_left ⟨h, by omega_using [h]⟩]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.1)]

/-- The digit `b m'` of the low word `b` clears it. -/
theorem digit_zero {R A b i m : Nat} (hs : A % R = b % R) (hm : (m * i + 1) % R = 0) :
    (A + b * i % R * (m % R)) % R = 0 := by
  have h : (b + b * i % R * (m % R)) % R = (b * (m * i + 1)) % R := by
    rw [Nat.add_mod, ← Nat.mul_mod, ← Nat.add_mod]
    refine congrArg (· % R) ?_
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm i m, Nat.add_comm]
  rw [Nat.add_mod, hs, ← Nat.add_mod, h, Nat.mul_mod, hm, Nat.mul_zero, Nat.zero_mod]

theorem mw_zero (m : Nat) : (mw m 0).toNat = m % 2 ^ 32 := by
  simp only [mw, Nat.mul_zero, Nat.shiftRight_zero, BitVec.toNat_ofNat]

theorem mul_le32 (a b : BitVec 32) : a.toNat * b.toNat ≤ 2 ^ 64 := by
  have h := Nat.mul_le_mul (Nat.le_of_lt a.isLt) (Nat.le_of_lt b.isLt)
  rw [← Nat.pow_add] at h
  exact h

/-- The digit's store, its product by `m_0`, and the shift. -/
theorem colShift_ok {W : Nat} {cl : Bool} {x : BitVec 32} {s : State} (hc : Ctx W x s cl) {m o : Nat}
    {q : BitVec 32} (hq : s.gpr .eax = q) (ho : o + 4 ≤ 4096) (ha : acc s < 2 ^ 72)
    (hz : (acc s + q.toNat * (mw m 0).toNat) % 2 ^ 32 = 0) :
    WP isa (.block (.store (Impl.X25519.X86.sc o) .eax :: (Impl.X25519.X86.accMul (.imm (mw m 0)) ++
        ([.mov .ebx (.reg .ecx), .mov .ecx (.reg .ebp), .mov .ebp (.imm 0)] : List Instr)))) s
      fun u => Keep s u ∧ Frame [sub x o 4] s.mem u.mem ∧
        2 ^ 32 * acc u = acc s + wv u.mem x o * (mw m 0).toNat := by
  refine wp_stm hc.edi (hc.inW4 ho (by decide)) fun s₁ u₁ => ?_
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.accMul_ok (s := s₁) (src := .imm (mw m 0)) rfl)
    fun s₂ ⟨a₂, k₂, m₂⟩ => ?_)
  refine wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_movi fun s₅ u₅ => WP.block_nil ?_
  have k₁ : Keep s s₁ := ⟨by rw [u₁.gpr], by rw [u₁.gpr], by rw [u₁.gpr], u₁.rd, u₁.wr⟩
  have acc₁ : acc s₁ = acc s := by simp only [acc, v, u₁.gpr]
  have eax₁ : v s₁ .eax = q.toNat := by simp only [v, u₁.gpr, hq]
  have hmul := mul_le32 q (mw m 0)
  have acc₂ : acc s₂ = acc s + q.toNat * (mw m 0).toNat := by
    rw [a₂ (by rw [acc₁, eax₁]; omega_using [hmul, ha]), acc₁, eax₁]
  have memu : s₅.mem = s.mem.writeW (addr x o) q := by rw [u₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem, hq]
  have wq : wv s₅.mem x o = q.toNat := by rw [memu, wv, VG.Proof.X25519.X86.wd_write_self]
  refine ⟨k₁.trans (k₂.trans ((VG.Proof.X25519.X86.updKeep u₃).trans
    ((VG.Proof.X25519.X86.updKeep u₄).trans (VG.Proof.X25519.X86.updKeep u₅)))), ?_, ?_⟩
  · rw [memu]
    exact VG.Proof.X25519.X86.frame_write1 (Frame.refl _ _) hc.fit4 ho (Nat.le_refl _) (Nat.le_refl _) _
  · rw [wq, ← acc₂]
    rw [← acc₂] at hz
    have h2 : acc s₅ = acc s₂ / 2 ^ 32 := by
      simp only [acc, v, u₅.gpr, u₅.other .ebx (by decide), u₅.other .ecx (by decide), u₄.gpr,
        u₄.other .ebx (by decide), u₃.gpr, u₃.other .ebp (by decide), VG.Proof.X25519.X86.toNat_zero32]
      have := (s₂.gpr .ebx).isLt
      omega_using [this]
    rw [h2]
    exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hz)

theorem colDigit_ok {W : Nat} {cl : Bool} {x : BitVec 32} {s : State} (hc : Ctx W x s cl) {k m o : Nat}
    (hM : MulOk k m) (ho : o + 4 ≤ 4096) (ha : acc s < 2 ^ 72) :
    WP isa (.block (colDigit k m o)) s fun u => Keep s u ∧ Frame [sub x o 4] s.mem u.mem ∧
      2 ^ 32 * acc u = acc s + wv u.mem x o * (mw m 0).toNat := by
  have hs : acc s % 2 ^ 32 = v s .ebx % 2 ^ 32 := by
    simp only [acc, Nat.add_assoc]
    rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 from rfl, Nat.mul_assoc, ← Nat.mul_add, Nat.add_mul_mod_self_left]
  have hz := digit_zero hs (minv32_mod hM)
  rw [← mw_zero] at hz
  have tail : ∀ {t : State} {q : BitVec 32}, t.gpr .eax = q → Keep s t → t.mem = s.mem → acc t = acc s →
      q.toNat = v s .ebx * (minv32 (mod k m)).toNat % 2 ^ 32 →
      WP isa (.block (.store (Impl.X25519.X86.sc o) .eax :: (Impl.X25519.X86.accMul (.imm (mw m 0)) ++
        ([.mov .ebx (.reg .ecx), .mov .ecx (.reg .ebp), .mov .ebp (.imm 0)] : List Instr)))) t
        fun u => Keep s u ∧ Frame [sub x o 4] s.mem u.mem ∧
          2 ^ 32 * acc u = acc s + wv u.mem x o * (mw m 0).toNat := by
    intro t q hq kt mt at_ hv
    refine WP.mono (colShift_ok (kt.ctx hc) hq ho (by rw [at_]; exact ha) (by rw [at_, hv]; exact hz))
      fun u ⟨K, F, E⟩ => ⟨kt.trans K, ?_, ?_⟩
    · rw [← mt]; exact F
    · rw [← at_]; exact E
  unfold colDigit
  refine wp_mov fun t₁ r₁ => ?_
  split
  next h =>
    rw [List.nil_append]
    refine tail r₁.gpr (VG.Proof.X25519.X86.updKeep r₁) r₁.mem (VG.Proof.X25519.X86.updAcc r₁) ?_
    rw [h]
    change _ = v s .ebx * 1 % 2 ^ 32
    rw [Nat.mul_one, Nat.mod_eq_of_lt (s.gpr .ebx).isLt]
  next _ =>
    simp only [List.cons_append, List.nil_append]
    refine wp_movi fun t₂ r₂ => wp_mul fun t₃ m₃ => ?_
    have k₃ : Keep t₂ t₃ := ⟨m₃.other _ (by decide) (by decide), m₃.other _ (by decide) (by decide),
      m₃.other _ (by decide) (by decide), m₃.rd, m₃.wr⟩
    refine tail m₃.eax ((VG.Proof.X25519.X86.updKeep r₁).trans ((VG.Proof.X25519.X86.updKeep r₂).trans k₃))
      (by rw [m₃.mem, r₂.mem, r₁.mem]) ?_ ?_
    · rw [← VG.Proof.X25519.X86.updAcc r₁]
      simp only [acc, v, m₃.other .ebx (by decide) (by decide), m₃.other .ecx (by decide) (by decide),
        m₃.other .ebp (by decide) (by decide), r₂.other .ebx (by decide), r₂.other .ecx (by decide),
        r₂.other .ebp (by decide)]
    · rw [BitVec.toNat_ofNat, r₂.other .eax (by decide), r₁.gpr, r₂.gpr]

theorem colAt_congr {f f' g : Nat → Nat} {N c : Nat} (h : ∀ i ≤ c, f i = f' i) : colAt f g N c = colAt f' g N c :=
  sumTo_congr fun i hi => by rw [h i (Nat.lt_succ_iff.mp hi)]

theorem redTerms_reads {Q m N c : Nat} {t : Term} (ht : t ∈ redTerms Q m N c) {d : Nat} (hd : d ∈ treads t) :
    ∃ i, i < c ∧ i < N ∧ c - i < N ∧ d = Q + 4 * i := by
  simp only [redTerms, List.mem_filterMap, List.mem_range] at ht
  obtain ⟨i, hi, h⟩ := ht
  split at h
  next hc =>
    cases h
    simp only [treads, List.mem_singleton] at hd
    exact ⟨i, hi, hc.1, hc.2.1, hd⟩
  next => cases h

theorem wv_lt32 (m : Mem) (x : BitVec 32) (d : Nat) : wv m x d < 2 ^ 32 := (wd m x d).isLt

/-- What the columns need of the product's terms: their reads, away from the
digits at `Q`, and their values, the columns of the product of `f` and `g`. -/
structure TermsOk (mem : Mem) (x : BitVec 32) (Q N : Nat) (ts : Nat → List Term) (f g : Nat → Nat) : Prop where
  reads : ∀ c, ∀ t ∈ ts c, ∀ d ∈ treads t, d + 4 ≤ 4096 ∧ (d + 4 ≤ Q ∨ Q + 4 * N ≤ d)
  val : ∀ c, colv mem x (ts c) = colAt f g N c
  hf : ∀ i, f i < 2 ^ 32
  hg : ∀ i, g i < 2 ^ 32

/-- The word at `[Q + 4 i]` of `mem`, and the modulus's words. -/
abbrev qw (mem : Mem) (x : BitVec 32) (Q i : Nat) : Nat := wv mem x (Q + 4 * i)
abbrev mn (m i : Nat) : Nat := (mw m i).toNat

theorem colAt_red_le (mem : Mem) (x : BitVec 32) (Q m N c : Nat) :
    colAt (qw mem x Q) (mn m) N c ≤ N * 2 ^ 64 :=
  colAt_le (fun _ => wv_lt32 _ _ _) (fun i => (mw m i).isLt) N c

theorem low_arith {P A₁ A₂ A₃ q V C R S : Nat} (h3 : 2 ^ 32 * A₃ = A₂ + q) (h2 : A₂ = A₁ + (V + R))
    (hC : R + q = C) (h1 : P * A₁ = S) : P * 2 ^ 32 * A₃ = S + P * (V + C) := by
  rw [Nat.mul_assoc, h3, h2, ← hC, ← h1, ← Nat.mul_add]
  congr 1
  omega_using []

theorem lowCols_ok {W : Nat} {cl : Bool} {x : BitVec 32} {s : State} (hc : Ctx W x s cl) {k m Q : Nat}
    (hM : MulOk k m) (hk : k ≤ 9) (hQ : Q + 4 * (2 * k) ≤ 4096) {ts : Nat → List Term} {f g : Nat → Nat}
    (hT : TermsOk s.mem x Q (2 * k) ts f g) (h0 : acc s = 0) : ∀ n, n ≤ 2 * k →
    WP isa (.block (lowCols k m Q ts n)) s fun u => Keep s u ∧ Frame [sub x Q (4 * n)] s.mem u.mem ∧
      acc u < 2 ^ 40 ∧
      (2 ^ 32) ^ n * acc u = num (fun c => colAt f g (2 * k) c + colAt (qw u.mem x Q) (mn m) (2 * k) c) n
  | 0, _ => WP.block_nil ⟨Keep.refl _, Frame.refl _ _, by rw [h0]; decide, by rw [h0]; rfl⟩
  | n + 1, hn => by
    have hfit := hc.fit4
    rw [lowCols]
    refine WP.block_append (WP.mono (lowCols_ok hc hM hk hQ hT h0 n (by omega_using [hn]))
      fun s₁ ⟨k₁, f₁, b₁, e₁⟩ => ?_)
    have hV : colv s₁.mem x (ts n) = colAt f g (2 * k) n := by
      rw [← hT.val n]
      exact VG.Proof.X25519.X86.colv_congr fun t ht d hd => by
        have h := hT.reads n t ht d hd
        exact VG.Proof.X25519.X86.wd_frame1 f₁ hfit (by omega_using [hQ, hn]) h.1 (by omega_using [h, hn])
    have hr : ∀ t ∈ ts n ++ redTerms Q m (2 * k) n, ∀ d ∈ treads t, d + 4 ≤ 4096 := by
      intro t ht d hd
      rcases List.mem_append.mp ht with ht | ht
      · exact (hT.reads n t ht d hd).1
      · obtain ⟨i, _, hi, _, rfl⟩ := redTerms_reads ht hd
        omega_using [hi, hQ]
    refine WP.block_append (WP.mono (VG.Proof.X25519.X86.terms_ok (k₁.ctx hc) _ hr) fun s₂ ⟨a₂, k₂, m₂⟩ => ?_)
    have hVle := colAt_le hT.hf hT.hg (2 * k) n
    have hRle : colv s₁.mem x (redTerms Q m (2 * k) n) ≤ 2 * k * 2 ^ 64 :=
      Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_of_eq (redTerms_colv s₁.mem x Q m (2 * k) n))
        (colAt_red_le s₁.mem x Q m (2 * k) n))
    rw [colv_append, hV] at a₂
    have e₂ := a₂ (by omega_using [hVle, hRle, b₁, hk])
    refine WP.mono (colDigit_ok (k₂.ctx (k₁.ctx hc)) hM (o := Q + 4 * n) (by omega_using [hQ, hn])
      (by rw [e₂]; omega_using [hVle, hRle, b₁, hk])) fun s₃ ⟨k₃, f₃, e₃⟩ => ?_
    rw [m₂] at f₃
    have hq : ∀ i < n, qw s₃.mem x Q i = qw s₁.mem x Q i := fun i hi => congrArg BitVec.toNat
      (VG.Proof.X25519.X86.wd_frame1 f₃ hfit (by omega_using [hQ, hn]) (by omega_using [hQ, hn, hi]) (by omega_using [hi]))
    have hR : colv s₃.mem x (redTerms Q m (2 * k) n) = colv s₁.mem x (redTerms Q m (2 * k) n) :=
      VG.Proof.X25519.X86.colv_congr fun t ht d hd => by
        obtain ⟨i, hi, hi', _, rfl⟩ := redTerms_reads ht hd
        exact VG.Proof.X25519.X86.wd_frame1 f₃ hfit (by omega_using [hQ, hn]) (by omega_using [hQ, hi'])
          (by omega_using [hi])
    have hC := redTerms_colv s₃.mem x Q m (2 * k) n
    rw [ite_eq_left (show n < 2 * k by omega_using [hn]), hR] at hC
    have hCle := colAt_red_le s₃.mem x Q m (2 * k) n
    refine ⟨k₁.trans (k₂.trans k₃), ?_, ?_, ?_⟩
    · exact (VG.Proof.X25519.X86.frameWiden f₁ hfit (Nat.le_refl _) (by omega_using []) (by omega_using [hQ, hn])).trans
        (VG.Proof.X25519.X86.frameWiden f₃ hfit (by omega_using []) (by omega_using []) (by omega_using [hQ, hn]))
    · rw [e₂] at e₃
      change _ + wv s₃.mem x (Q + 4 * n) * _ = colAt (qw s₃.mem x Q) (mn m) (2 * k) n at hC
      omega_using [e₃, hC, hCle, hVle, b₁, hk]
    · rw [num_succ, Nat.pow_succ (2 ^ 32) n]
      have hnum : num (fun c => colAt f g (2 * k) c + colAt (qw s₃.mem x Q) (mn m) (2 * k) c) n =
          num (fun c => colAt f g (2 * k) c + colAt (qw s₁.mem x Q) (mn m) (2 * k) c) n :=
        num_congr fun c hc' => congrArg _ (colAt_congr fun i hi => hq i (by omega_using [hi, hc']))
      rw [hnum]
      exact low_arith e₃ e₂ hC e₁

theorem highCols_ok {W : Nat} {cl : Bool} {x : BitVec 32} {s : State} (hc : Ctx W x s cl) {k m Q : Nat}
    (hk : k ≤ 9) (hQ : Q + 4 * (2 * k) ≤ 4096) {ts : Nat → List Term} {f g : Nat → Nat}
    (hT : TermsOk s.mem x Q (2 * k) ts f g) (ha : acc s < 2 ^ 40) :
    WP isa (.block (highCols k m Q ts)) s fun u => Keep s u ∧ Frame [sub x Q (4 * (2 * k))] s.mem u.mem ∧
      num (qw u.mem x Q) (2 * k) + (2 ^ 32) ^ (2 * k) * acc u =
        acc s + num (fun j => colAt f g (2 * k) (2 * k + j) + colAt (qw s.mem x Q) (mn m) (2 * k) (2 * k + j)) (2 * k) := by
  have hV : ∀ j, colv s.mem x (ts (2 * k + j) ++ redTerms Q m (2 * k) (2 * k + j)) =
      colAt f g (2 * k) (2 * k + j) + colAt (qw s.mem x Q) (mn m) (2 * k) (2 * k + j) := fun j => by
    have h := redTerms_colv s.mem x Q m (2 * k) (2 * k + j)
    rw [ite_eq_right (by omega_using []), Nat.add_zero] at h
    rw [colv_append, hT.val, h]
  unfold highCols
  refine WP.mono (VG.Proof.X25519.X86.cols_ok70 hc _ (2 * k) hQ ?_ ?_ ha) fun u ⟨K, F, E, _⟩ => ⟨K, F, ?_⟩
  · intro j hj t ht d hd
    rcases List.mem_append.mp ht with ht | ht
    · have h := hT.reads _ t ht d hd
      exact ⟨h.1, by omega_using [h, hj]⟩
    · obtain ⟨i, _, hi, hi', rfl⟩ := redTerms_reads ht hd
      exact ⟨by omega_using [hi, hQ], by omega_using [hi']⟩
  · intro j _
    rw [hV]
    have h1 := colAt_le hT.hf hT.hg (2 * k) (2 * k + j)
    have h2 := colAt_red_le s.mem x Q m (2 * k) (2 * k + j)
    omega_using [h1, h2, hk]
  · simp only [hV] at E
    exact E

theorem num_mn (m : Nat) : ∀ n, num (mn m) n = m % 2 ^ (32 * n)
  | 0 => by simp only [num, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
  | n + 1 => by
    have h := yVal_mw m (n + 1)
    rw [yVal, yVal_mw m n] at h
    rw [num_succ, num_mn m n, ← Nat.pow_mul]
    exact h

/-! P-256's columns: those of the digits and `p + 1`. -/

/-- The words of `p + 1` that are not zero: words 3 and 6 are 1 and word 7 is
`2³² - 1`. -/
def pVal (f : Nat → Nat) (c : Nat) : Nat :=
  (if 7 ≤ c ∧ c < 15 then f (c - 7) * (2 ^ 32 - 1) else 0) +
    ((if 3 ≤ c ∧ c < 11 then f (c - 3) else 0) + (if 6 ≤ c ∧ c < 14 then f (c - 6) else 0))

theorem colAt_pVal (f g : Nat → Nat) (h0 : g 0 = 0) (h1 : g 1 = 0) (h2 : g 2 = 0) (h3 : g 3 = 1) (h4 : g 4 = 0)
    (h5 : g 5 = 0) (h6 : g 6 = 1) (h7 : g 7 = 2 ^ 32 - 1) : ∀ c < 16, colAt f g 8 c = pVal f c := by
  intro c hc
  match c, hc with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _
  | 15, _ =>
    simp only [colAt_rows, sumTo, pVal, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceSub, and_true, and_false,
      ite_true, ite_false, h0, h1, h2, h3, h4, h5, h6, h7, Nat.mul_zero, Nat.mul_one, Nat.zero_add,
      Nat.add_zero] <;> omega_using []
  | n + 16, h => exact absurd h (by omega_using [])

theorem colAt_p (f : Nat → Nat) : ∀ c < 16, colAt f (mn (p256Prime + 1)) 8 c = pVal f c :=
  colAt_pVal f _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem pVal_congr {f f' : Nat → Nat} {c : Nat} (h3 : 3 ≤ c → c < 11 → f (c - 3) = f' (c - 3))
    (h6 : 6 ≤ c → c < 14 → f (c - 6) = f' (c - 6)) (h7 : 7 ≤ c → c < 15 → f (c - 7) = f' (c - 7)) :
    pVal f c = pVal f' c := by
  have a (a b : Prop) [Decidable (a ∧ b)] (x y : Nat) (h : a → b → x = y) :
      (if a ∧ b then x else 0) = if a ∧ b then y else 0 := by
    split
    next h' => exact h h'.1 h'.2
    next => rfl
  simp only [pVal]
  rw [a _ _ _ _ h3, a _ _ _ _ h6, a _ _ _ _ fun h h' => congrArg (· * _) (h7 h h')]

theorem pVal_le (f : Nat → Nat) (hf : ∀ i, f i < 2 ^ 32) (c : Nat) : pVal f c ≤ 2 ^ 64 := by
  have h3 := hf (c - 3); have h6 := hf (c - 6); have h7 := hf (c - 7)
  simp only [pVal]
  split <;> split <;> split <;> omega_using [h3, h6, h7]

/-- `edx:eax += [d]` for each `d`. -/
theorem sideAdds_ok {W : Nat} {cl : Bool} {x : BitVec 32} : ∀ {s : State} (_ : Ctx W x s cl) (ds : List Nat),
    (∀ d ∈ ds, d + 4 ≤ 4096) → v s .eax + 2 ^ 32 * v s .edx + (ds.map (wv s.mem x)).sum < 2 ^ 64 →
    WP isa (.block (ds.flatMap fun d =>
        ([.alu .add .eax (.mem (Impl.X25519.X86.sc d)), .alu .adc .edx (.imm 0)] : List Instr))) s fun u =>
      v u .eax + 2 ^ 32 * v u .edx = v s .eax + 2 ^ 32 * v s .edx + (ds.map (wv s.mem x)).sum ∧ Keep s u ∧
        u.mem = s.mem ∧ acc u = acc s
  | s, _, [], _, _ => WP.block_nil ⟨by simp, Keep.refl _, rfl, rfl⟩
  | s, hc, d :: ds, hd, hlt => by
    rw [List.flatMap_cons, List.cons_append, List.cons_append, List.nil_append]
    refine wp_addS (VG.Proof.X25519.X86.readSrc_sc hc (hd d List.mem_cons_self)) fun s₁ u₁ c₁ => ?_
    refine wp_adcS rfl c₁ fun s₂ u₂ _ => ?_
    have k₂ : Keep s s₂ := (VG.Proof.X25519.X86.updKeep u₁).trans (VG.Proof.X25519.X86.updKeep u₂)
    have m₂ : s₂.mem = s.mem := u₂.mem.trans u₁.mem
    simp only [List.map_cons, List.sum_cons] at hlt ⊢
    have e₂ : v s₂ .eax + 2 ^ 32 * v s₂ .edx = v s .eax + 2 ^ 32 * v s .edx + wv s.mem x d := by
      have ha := (s.gpr .eax).isLt; have hb := (s.gpr .edx).isLt; have hw := (wd s.mem x d).isLt
      simp only [v, wv] at hlt ⊢
      rw [u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.other _ (by decide), add3_toNat, BitVec.toNat_add,
        VG.Proof.X25519.X86.toNat_zero32]
      by_cases h : 2 ^ 32 ≤ (s.gpr .eax).toNat + (wd s.mem x d).toNat <;>
        simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
        omega_using [ha, hb, hw, hlt, h]
    refine WP.mono (sideAdds_ok (k₂.ctx hc) ds (fun d' h => hd d' (List.mem_cons_of_mem _ h))
      (by rw [e₂, m₂]; omega_using [hlt])) fun u ⟨e, k, m, a⟩ => ⟨?_, k₂.trans k, m.trans m₂, a.trans ?_⟩
    · rw [e, e₂, m₂]; omega_using []
    · simp only [acc, v, u₂.other .ebx (by decide), u₂.other .ecx (by decide), u₂.other .ebp (by decide),
        u₁.other .ebx (by decide), u₁.other .ecx (by decide), u₁.other .ebp (by decide)]

/-- `ebx:ecx:ebp += edx:eax`. -/
theorem accSide_ok {s : State} (hlt : acc s + (v s .eax + 2 ^ 32 * v s .edx) < 2 ^ 96) :
    WP isa (.block [.alu .add .ebx (.reg .eax), .alu .adc .ecx (.reg .edx), .alu .adc .ebp (.imm 0)]) s fun u =>
      acc u = acc s + (v s .eax + 2 ^ 32 * v s .edx) ∧ Keep s u ∧ u.mem = s.mem := by
  refine wp_addS rfl fun s₁ u₁ c₁ => wp_adcS rfl c₁ fun s₂ u₂ c₂ => wp_adcS rfl c₂ fun s₃ u₃ _ => WP.block_nil
    ⟨?_, (VG.Proof.X25519.X86.updKeep u₁).trans ((VG.Proof.X25519.X86.updKeep u₂).trans
      (VG.Proof.X25519.X86.updKeep u₃)), by rw [u₃.mem, u₂.mem, u₁.mem]⟩
  have ha := (s.gpr .ebx).isLt; have hb := (s.gpr .ecx).isLt; have hc := (s.gpr .ebp).isLt
  have hl := (s.gpr .eax).isLt; have hh := (s.gpr .edx).isLt
  simp only [acc, v] at hlt ⊢
  rw [u₃.other .ebx (by decide), u₃.other .ecx (by decide), u₂.other .ebx (by decide), u₁.gpr, u₂.gpr, u₃.gpr,
    u₂.other .ebp (by decide), u₁.other .ebp (by decide), u₁.other .ecx (by decide), u₁.other .edx (by decide),
    add3_toNat, add3_toNat, BitVec.toNat_add, VG.Proof.X25519.X86.toNat_zero32]
  by_cases h₁ : 2 ^ 32 ≤ (s.gpr .ebx).toNat + (s.gpr .eax).toNat <;>
    simp only [h₁, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
    [by_cases h₂ : 2 ^ 32 ≤ (s.gpr .ecx).toNat + (s.gpr .edx).toNat + 1;
      by_cases h₂ : 2 ^ 32 ≤ (s.gpr .ecx).toNat + (s.gpr .edx).toNat + 0] <;>
    simp only [h₂, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
    omega_using [ha, hb, hc, hl, hh, hlt, h₁, h₂]

theorem pAdds_sum (mem : Mem) (x : BitVec 32) (Q c : Nat) : ((pAdds Q c).map (wv mem x)).sum =
    (if 3 ≤ c ∧ c < 11 then qw mem x Q (c - 3) else 0) + (if 6 ≤ c ∧ c < 14 then qw mem x Q (c - 6) else 0) := by
  simp only [pAdds]
  split <;> split <;> simp [qw]

theorem pAdds_reads {Q c d : Nat} (hd : d ∈ pAdds Q c) : d + 4 ≤ Q + 32 := by
  simp only [pAdds, List.mem_append] at hd
  rcases hd with hd | hd <;> split at hd
  next h => rw [List.mem_singleton.mp hd]; omega_using [h]
  next => exact absurd hd List.not_mem_nil
  next h => rw [List.mem_singleton.mp hd]; omega_using [h]
  next => exact absurd hd List.not_mem_nil

/-- `0 - q` and `q` less its borrow are `(2³² - 1) q`. -/
theorem max_digit (q : BitVec 32) : (0 - q).toNat + 2 ^ 32 * (q - 0 - (BitVec.ofBool
    (decide ((0 : BitVec 32).toNat < q.toNat))).setWidth 32).toNat = q.toNat * (2 ^ 32 - 1) := by
  have hq := q.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_sub, VG.Proof.X25519.X86.ofBool_toNat,
    VG.Proof.X25519.X86.toNat_zero32]
  by_cases h0 : 0 < q.toNat <;> simp only [h0, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
    omega_using [h0, hq]

/-- `ebx:ecx:ebp +=` the column of the digits and `p + 1`. -/
theorem pRed_ok {W : Nat} {cl : Bool} {x : BitVec 32} {s : State} (hc : Ctx W x s cl) {Q c : Nat}
    (hQ : Q + 32 ≤ 4096) (ha : acc s < 2 ^ 72) :
    WP isa (.block (pRed Q c)) s fun u =>
      acc u = acc s + pVal (qw s.mem x Q) c ∧ Keep s u ∧ u.mem = s.mem := by
  have hr : ∀ d ∈ pAdds Q c, d + 4 ≤ 4096 := fun d hd => by have := pAdds_reads hd; omega_using [hQ, this]
  have hs := pAdds_sum s.mem x Q c
  unfold pRed
  split
  next h =>
    simp only [List.cons_append, List.nil_append]
    refine wp_movi fun s₁ u₁ => ?_
    refine wp_ldm (u₁.other .edi (by decide) |>.trans hc.edi)
      (by rw [u₁.rd, u₁.wr]; exact hc.inRW4 (d := Q + 4 * (c - 7)) (by omega_using [hQ, h]) (by decide)) fun s₂ u₂ => ?_
    refine wp_subS rfl fun s₃ u₃ c₃ => wp_sbbS rfl c₃ fun s₄ u₄ _ => ?_
    have k₄ : Keep s s₄ := (VG.Proof.X25519.X86.updKeep u₁).trans ((VG.Proof.X25519.X86.updKeep u₂).trans
      ((VG.Proof.X25519.X86.updKeep u₃).trans (VG.Proof.X25519.X86.updKeep u₄)))
    have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    have a₄ : acc s₄ = acc s := by
      simp only [acc, v, u₄.other .ebx (by decide), u₄.other .ecx (by decide), u₄.other .ebp (by decide),
        u₃.other .ebx (by decide), u₃.other .ecx (by decide), u₃.other .ebp (by decide),
        u₂.other .ebx (by decide), u₂.other .ecx (by decide), u₂.other .ebp (by decide),
        u₁.other .ebx (by decide), u₁.other .ecx (by decide), u₁.other .ebp (by decide)]
    have hq := wv_lt32 s.mem x (Q + 4 * (c - 7))
    have e₄ : v s₄ .eax + 2 ^ 32 * v s₄ .edx = qw s.mem x Q (c - 7) * (2 ^ 32 - 1) := by
      rw [v, v, u₄.other .eax (by decide), u₄.gpr, u₃.gpr, u₃.other .edx (by decide), u₂.gpr,
        u₂.other .eax (by decide), u₁.gpr, u₁.mem]
      exact max_digit _
    have hq3 := wv_lt32 s.mem x (Q + 4 * (c - 3))
    have hq6 := wv_lt32 s.mem x (Q + 4 * (c - 6))
    have hsum : qw s.mem x Q (c - 7) * (2 ^ 32 - 1) + ((pAdds Q c).map (wv s.mem x)).sum < 2 ^ 64 := by
      rw [hs]
      simp only [qw]
      split <;> split <;> omega_using [hq, hq3, hq6]
    refine WP.block_append (WP.mono (sideAdds_ok (k₄.ctx hc) (pAdds Q c) hr (by rw [e₄, m₄]; exact hsum))
      fun s₅ ⟨e₅, k₅, m₅, a₅⟩ => ?_)
    rw [e₄, m₄] at e₅
    refine WP.mono (accSide_ok (by rw [a₅, a₄, e₅]; omega_using [ha, hsum])) fun u ⟨e, k, m⟩ =>
      ⟨?_, k₄.trans (k₅.trans k), m.trans (m₅.trans m₄)⟩
    rw [e, a₅, a₄, e₅, hs, pVal, ite_eq_left h]
  next h =>
    have hco : ((pAdds Q c).flatMap fun d => Impl.X25519.X86.accAdd (.mem (Impl.X25519.X86.sc d))) =
        ((pAdds Q c).map Term.addM).flatMap Term.code := by
      rw [List.flatMap_map]; rfl
    have hcv : colv s.mem x ((pAdds Q c).map Term.addM) = ((pAdds Q c).map (wv s.mem x)).sum := by
      rw [colv, List.map_map]; rfl
    rw [hco]
    refine WP.mono (VG.Proof.X25519.X86.terms_ok hc _ fun t ht d hd => ?_) fun u ⟨e, k, m⟩ => ⟨?_, k, m⟩
    · obtain ⟨d', hd', rfl⟩ := List.mem_map.mp ht
      rw [List.mem_singleton.mp hd]
      exact hr d' hd'
    · have hle := pVal_le (qw s.mem x Q) (fun i => wv_lt32 _ _ _) c
      rw [pVal, ite_eq_right h, Nat.zero_add] at hle ⊢
      rw [e (by rw [hcv, hs]; omega_using [ha, hle]), hcv, hs]

/-- A column of the product and the digits. -/
theorem pCol_ok {W : Nat} {cl : Bool} {x : BitVec 32} {s : State} (hc : Ctx W x s cl) {Q o c : Nat}
    (hQ : Q + 32 ≤ 4096) (ho : o + 4 ≤ 4096) {ts : Nat → List Term} {f g : Nat → Nat}
    (hT : TermsOk s.mem x Q 8 ts f g) (ha : acc s < 2 ^ 40) :
    WP isa (.block (pCol Q ts o c)) s fun u => Keep s u ∧ Frame [sub x o 4] s.mem u.mem ∧ acc u < 2 ^ 40 ∧
      wv u.mem x o + 2 ^ 32 * acc u = acc s + (colAt f g 8 c + pVal (qw s.mem x Q) c) := by
  have hV := hT.val c
  have hVle := colAt_le hT.hf hT.hg 8 c
  have hPle := pVal_le (qw s.mem x Q) (fun i => wv_lt32 _ _ _) c
  unfold pCol
  refine WP.block_append (WP.mono (VG.Proof.X25519.X86.terms_ok hc (ts c) fun t ht d hd => (hT.reads c t ht d hd).1)
    fun s₁ ⟨a₁, k₁, m₁⟩ => ?_)
  rw [hV] at a₁
  have e₁ := a₁ (by omega_using [ha, hVle])
  refine WP.block_append (WP.mono (pRed_ok (k₁.ctx hc) (Q := Q) (c := c) hQ (by rw [e₁]; omega_using [ha, hVle]))
    fun s₂ ⟨e₂, k₂, m₂⟩ => ?_)
  rw [m₁, e₁] at e₂
  have hc₂ := k₂.ctx (k₁.ctx hc)
  refine WP.mono (VG.Proof.X25519.X86.colEnd_ok hc₂ ho) fun s₃ ⟨k₃, m₃, e₃⟩ =>
    ⟨k₁.trans (k₂.trans k₃), ?_, ?_, ?_⟩
  · rw [m₃, m₂, m₁]
    exact VG.Proof.X25519.X86.frame_write1 (Frame.refl _ _) hc.fit4 ho (Nat.le_refl _) (Nat.le_refl _) _
  · rw [e₃, e₂]; omega_using [ha, hVle, hPle]
  · rw [m₃, wv, VG.Proof.X25519.X86.wd_write_self, e₃, ← Nat.add_assoc (acc s), ← e₂]
    have := (s₂.gpr .ebx).isLt
    simp only [acc, v]
    omega_using [this]

theorem TermsOk.frame {mem mem' : Mem} {x : BitVec 32} {Q N : Nat} {ts : Nat → List Term} {f g : Nat → Nat}
    (hT : TermsOk mem x Q N ts f g) (hx : x.toNat + 4096 ≤ 2 ^ 32) (hQ : Q + 4 * N ≤ 4096)
    (hF : Frame [sub x Q (4 * N)] mem mem') : TermsOk mem' x Q N ts f g :=
  ⟨hT.reads, fun c => by
    rw [← hT.val c]
    exact VG.Proof.X25519.X86.colv_congr fun t ht d hd =>
      VG.Proof.X25519.X86.wd_frame1 hF hx hQ (hT.reads c t ht d hd).1 (hT.reads c t ht d hd).2, hT.hf, hT.hg⟩

theorem pLow_ok {W : Nat} {cl : Bool} {x : BitVec 32} {s : State} (hc : Ctx W x s cl) {Q : Nat}
    (hQ : Q + 32 ≤ 4096) {ts : Nat → List Term} {f g : Nat → Nat} (hT : TermsOk s.mem x Q 8 ts f g)
    (h0 : acc s = 0) : ∀ n, n ≤ 8 →
    WP isa (.block (pLow Q ts n)) s fun u => Keep s u ∧ Frame [sub x Q (4 * n)] s.mem u.mem ∧ acc u < 2 ^ 40 ∧
      num (qw u.mem x Q) n + (2 ^ 32) ^ n * acc u = num (fun c => colAt f g 8 c + pVal (qw u.mem x Q) c) n
  | 0, _ => WP.block_nil ⟨Keep.refl _, Frame.refl _ _, by rw [h0]; decide, by rw [h0]; rfl⟩
  | n + 1, hn => by
    have hfit := hc.fit4
    rw [pLow]
    refine WP.block_append (WP.mono (pLow_ok hc hQ hT h0 n (by omega_using [hn])) fun s₁ ⟨k₁, f₁, b₁, e₁⟩ => ?_)
    have hT₁ := hT.frame hfit (by omega_using [hQ]) (VG.Proof.X25519.X86.frameWiden f₁ hfit (Nat.le_refl _)
      (by omega_using [hn]) (by omega_using [hQ]))
    refine WP.mono (pCol_ok (k₁.ctx hc) hQ (o := Q + 4 * n) (by omega_using [hQ, hn]) hT₁ b₁)
      fun s₂ ⟨k₂, f₂, b₂, e₂⟩ => ⟨k₁.trans k₂, ?_, b₂, ?_⟩
    · exact (VG.Proof.X25519.X86.frameWiden f₁ hfit (Nat.le_refl _) (by omega_using []) (by omega_using [hQ, hn])).trans
        (VG.Proof.X25519.X86.frameWiden f₂ hfit (by omega_using []) (by omega_using []) (by omega_using [hQ, hn]))
    · have hq : ∀ i < n, qw s₂.mem x Q i = qw s₁.mem x Q i := fun i hi => congrArg BitVec.toNat
        (VG.Proof.X25519.X86.wd_frame1 f₂ hfit (by omega_using [hQ, hn]) (by omega_using [hQ, hn, hi])
          (by omega_using [hi]))
      have hP : ∀ c ≤ n, pVal (qw s₂.mem x Q) c = pVal (qw s₁.mem x Q) c := fun c hc' =>
        pVal_congr (fun h _ => hq _ (by omega_using [h, hc'])) (fun h _ => hq _ (by omega_using [h, hc']))
          fun h _ => hq _ (by omega_using [h, hc'])
      rw [num_succ, num_succ, num_congr fun c hc' => hq c hc', Nat.pow_succ (2 ^ 32) n,
        num_congr (f := fun c => colAt f g 8 c + pVal (qw s₂.mem x Q) c)
          (g := fun c => colAt f g 8 c + pVal (qw s₁.mem x Q) c)
          (fun c hc' => congrArg _ (hP c (Nat.le_of_lt hc'))), ← e₁, hP n (Nat.le_refl _), Nat.add_assoc,
        Nat.mul_assoc, ← Nat.mul_add, Nat.add_assoc, ← Nat.mul_add, ← e₂]

theorem pHigh_ok {W : Nat} {cl : Bool} {x : BitVec 32} {s : State} (hc : Ctx W x s cl) {Q : Nat}
    (hQ : Q + 32 ≤ 4096) {ts : Nat → List Term} {f g : Nat → Nat} (hT : TermsOk s.mem x Q 8 ts f g)
    (ha : acc s < 2 ^ 40) : ∀ n, n ≤ 8 →
    WP isa (.block (pHigh Q ts n)) s fun u => Keep s u ∧ Frame [sub x Q (4 * n)] s.mem u.mem ∧ acc u < 2 ^ 40 ∧
      num (qw u.mem x Q) n + (2 ^ 32) ^ n * acc u =
        acc s + num (fun j => colAt f g 8 (8 + j) + pVal (qw s.mem x Q) (8 + j)) n
  | 0, _ => WP.block_nil ⟨Keep.refl _, Frame.refl _ _, ha, by simp [num]⟩
  | n + 1, hn => by
    have hfit := hc.fit4
    rw [pHigh]
    refine WP.block_append (WP.mono (pHigh_ok hc hQ hT ha n (by omega_using [hn])) fun s₁ ⟨k₁, f₁, b₁, e₁⟩ => ?_)
    have hT₁ := hT.frame hfit (by omega_using [hQ]) (VG.Proof.X25519.X86.frameWiden f₁ hfit (Nat.le_refl _)
      (by omega_using [hn]) (by omega_using [hQ]))
    refine WP.mono (pCol_ok (k₁.ctx hc) hQ (o := Q + 4 * n) (c := 8 + n) (by omega_using [hQ, hn]) hT₁ b₁)
      fun s₂ ⟨k₂, f₂, b₂, e₂⟩ => ⟨k₁.trans k₂, ?_, b₂, ?_⟩
    · exact (VG.Proof.X25519.X86.frameWiden f₁ hfit (Nat.le_refl _) (by omega_using []) (by omega_using [hQ, hn])).trans
        (VG.Proof.X25519.X86.frameWiden f₂ hfit (by omega_using []) (by omega_using []) (by omega_using [hQ, hn]))
    · have hq : ∀ i < n, qw s₂.mem x Q i = qw s₁.mem x Q i := fun i hi => congrArg BitVec.toNat
        (VG.Proof.X25519.X86.wd_frame1 f₂ hfit (by omega_using [hQ, hn]) (by omega_using [hQ, hn, hi])
          (by omega_using [hi]))
      have hq' : ∀ i, n < i → i < 8 → qw s₁.mem x Q i = qw s.mem x Q i := fun i hi hi' => congrArg BitVec.toNat
        (VG.Proof.X25519.X86.wd_frame1 f₁ hfit (by omega_using [hQ, hn]) (by omega_using [hQ, hi'])
          (by omega_using [hi]))
      have hP : pVal (qw s₁.mem x Q) (8 + n) = pVal (qw s.mem x Q) (8 + n) :=
        pVal_congr (fun h h' => hq' _ (by omega_using [h]) (by omega_using [h'])) (fun h h' => hq' _ (by omega_using [h])
          (by omega_using [h'])) fun h h' => hq' _ (by omega_using [h]) (by omega_using [h'])
      rw [hP] at e₂
      rw [num_succ, num_succ, num_congr fun c hc' => hq c hc', Nat.pow_succ (2 ^ 32) n, Nat.add_assoc, Nat.mul_assoc,
        ← Nat.mul_add, e₂, Nat.mul_add, ← Nat.add_assoc, e₁, Nat.add_assoc]

theorem p_cols_arith {P A₁ R A₂ L H FG U p : Nat} (h1 : U + P * A₁ = L) (h2 : R + P * A₂ = A₁ + H)
    (hs : L + P * H = FG + U * (p + 1)) : P * (R + P * A₂) = FG + U * p := by
  rw [h2, Nat.mul_add]
  rw [Nat.mul_add, Nat.mul_one] at hs
  omega_using [h1, hs]

theorem cols_arith {P A₁ R A₂ L H FG QM : Nat} (h1 : P * A₁ = L) (h2 : R + P * A₂ = A₁ + H)
    (hs : L + P * H = FG + QM) : P * (R + P * A₂) = FG + QM := by
  rw [h2, Nat.mul_add, h1, hs]

theorem cols_lt {P F G U m X : Nat} (h : P * X = F * G + U * m) (hF : F < P) (hG : G < m) (hU : U < P) :
    X < 2 * m := by
  have hP : 0 < P := Nat.lt_of_le_of_lt (Nat.zero_le _) hF
  have h1 : F * G ≤ P * G := Nat.mul_le_mul_right _ (Nat.le_of_lt hF)
  have h2 : U * m ≤ P * m := Nat.mul_le_mul_right _ (Nat.le_of_lt hU)
  have h3 : P * G < P * m := Nat.mul_lt_mul_of_pos_left hG hP
  refine Nat.lt_of_mul_lt_mul_left (a := P) ?_
  rw [h, Nat.mul_left_comm]
  omega_using [h1, h2, h3]

theorem own_le {k : Nat} (hk : k ≤ 9) : own k + 64 * k = 4096 := by
  simp only [own, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes]; omega_using [hk]

/-- The columns: the `2k` words of the result at `[Q]`, with the carry in the
accumulator. -/
theorem allCols_ok {W : Nat} {cl : Bool} {x : BitVec 32} {s : State} (hc : Ctx W x s cl) {k m Q : Nat}
    (hM : MulOk k m) (hk : k ≤ 9) (hQ : Q + 4 * (2 * k) ≤ 4096) {ts : Nat → List Term} {f g : Nat → Nat}
    (hT : TermsOk s.mem x Q (2 * k) ts f g) (h0 : acc s = 0) :
    WP isa (.block (allCols k m Q ts)) s fun u => Keep s u ∧ Frame [sub x Q (4 * (2 * k))] s.mem u.mem ∧
      ∃ U, U < (2 ^ 32) ^ (2 * k) ∧
        (2 ^ 32) ^ (2 * k) * (num (qw u.mem x Q) (2 * k) + (2 ^ 32) ^ (2 * k) * acc u) =
          num f (2 * k) * num g (2 * k) + U * m := by
  have hfit := hc.fit4
  unfold allCols
  split
  next hp =>
    simp only [p256Field, Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    simp only [Nat.reduceMul] at hT hQ ⊢
    refine WP.block_append (WP.mono (pLow_ok hc hQ hT h0 8 (Nat.le_refl _)) fun s₁ ⟨k₁, f₁, b₁, e₁⟩ => ?_)
    refine WP.mono (pHigh_ok (k₁.ctx hc) hQ (hT.frame hfit hQ f₁) b₁ 8 (Nat.le_refl _))
      fun u ⟨k₂, f₂, _, e₂⟩ => ⟨k₁.trans k₂, f₁.trans f₂, num (qw s₁.mem x Q) 8,
        VG.Proof.X25519.X86.num_lt fun i _ => wv_lt32 _ _ _, ?_⟩
    have hsum : num (fun c => colAt f g 8 c + pVal (qw s₁.mem x Q) c) (8 + 8) =
        num f 8 * num g 8 + num (qw s₁.mem x Q) 8 * (p256Prime + 1) := by
      rw [num_add, ← num_congr fun c hc' => colAt_p (qw s₁.mem x Q) c hc', num_colAt f g 8,
        num_colAt (qw s₁.mem x Q) (mn (p256Prime + 1)) 8, num_mn]
      rfl
    rw [num_split] at hsum
    exact p_cols_arith e₁ e₂ hsum
  next =>
    refine WP.block_append (WP.mono (lowCols_ok (f := f) (g := g) hc hM hk hQ hT h0 (2 * k) (Nat.le_refl _))
      fun s₁ ⟨k₁, f₁, b₁, e₁⟩ => ?_)
    refine WP.mono (highCols_ok (k₁.ctx hc) (m := m) hk hQ (hT.frame hfit hQ f₁) b₁)
      fun u ⟨k₂, f₂, e₂⟩ => ⟨k₁.trans k₂, f₁.trans f₂, num (qw s₁.mem x Q) (2 * k),
        VG.Proof.X25519.X86.num_lt fun i _ => wv_lt32 _ _ _, ?_⟩
    have hsum : num (fun c => colAt f g (2 * k) c + colAt (qw s₁.mem x Q) (mn m) (2 * k) c) (2 * (2 * k)) =
        num f (2 * k) * num g (2 * k) + num (qw s₁.mem x Q) (2 * k) * m := by
      rw [num_add, num_colAt, num_colAt, num_mn, Nat.mod_eq_of_lt (by rw [← Nat.mul_assoc]; exact hM.m_lt)]
    rw [Nat.two_mul (2 * k), num_split] at hsum
    exact cols_arith e₁ e₂ hsum

theorem montCols_ok {s : State} {base : Addr} (hb : Bx s base 8192) {k m : Nat} (hM : MulOk k m) (hk : k ≤ 9)
    {ts : Nat → List Term} {f g : Nat → Nat}
    (hT : TermsOk s.mem (s.gpr .ebp) (own k + 4 * (2 * k)) (2 * k) ts f g) (hg : num g (2 * k) < m) :
    WP isa (.block (montCols k m ts)) s fun u =>
      Outside base (own k + 4 * (2 * k)) (8 * k + 4) s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .edi] s u ∧
      val32 u.mem base (own k + 4 * (2 * k)) (2 * k + 1) < 2 * m ∧
      ∃ U, 2 ^ (32 * (2 * k)) * val32 u.mem base (own k + 4 * (2 * k)) (2 * k + 1) =
        num f (2 * k) * num g (2 * k) + U * m := by
  have hn := hb.nowrap
  have hown := own_le hk
  have hk0 := hM.k0
  have hx := hb.ebp_toNat
  generalize hQ : own k + 4 * (2 * k) = Q at hT ⊢
  have hQ' : Q + 4 * (2 * k) + 4 ≤ 4096 := by omega_using [hQ, hown, hk0]
  unfold montCols
  rw [hQ]
  refine wp_mov fun s₁ u₁ => ?_
  have hc₁ : Ctx 8192 (s.gpr .ebp) s₁ false :=
    ⟨u₁.gpr, by rw [hx]; exact hn, by
      change (⟨(s.gpr .ebp).setWidth 64, 8192⟩ : Region) ∈ s₁.wr
      rw [u₁.wr, hb.ebp]; exact hb.wr, by decide, nofun⟩
  refine WP.block_append (WP.mono VG.Proof.X25519.X86.zeroAcc_ok fun s₂ ⟨k₂, m₂, a₂⟩ => ?_)
  have mem₂ : s₂.mem = s.mem := m₂.trans u₁.mem
  refine WP.block_append (WP.mono (allCols_ok (f := f) (g := g) (k₂.ctx hc₁) hM hk (by omega_using [hQ'])
    (by rw [mem₂]; exact hT) a₂) fun s₄ ⟨k₄, f₄, U, hUlt, hres⟩ => ?_)
  have hc₄ := k₄.ctx (k₂.ctx hc₁)
  have hfit := hc₁.fit4
  refine wp_stm hc₄.edi (hc₄.inW4 (d := own k + 16 * k) (by omega_using [hQ, hQ']) (by decide)) fun s₅ u₅ => ?_
  refine wp_mov fun u u₆ => WP.block_nil ?_
  have hFlt := VG.Proof.X25519.X86.num_lt (n := 2 * k) fun i _ => hT.hf i
  have hlt := cols_lt hres hFlt hg hUlt
  have hm2 : m < (2 ^ 32) ^ (2 * k) := by rw [← Nat.pow_mul, ← Nat.mul_assoc]; exact hM.m_lt
  -- The carry is the accumulator's low word.
  have hacc : acc s₄ = v s₄ .ebx := by
    have h2 : acc s₄ < 2 := by
      refine Nat.lt_of_mul_lt_mul_left (a := (2 ^ 32) ^ (2 * k)) ?_
      generalize (2 ^ 32) ^ (2 * k) = P at hlt hm2 ⊢
      omega_using [hlt, hm2]
    simp only [acc] at h2 ⊢
    omega_using [h2]
  rw [hacc] at hres hlt
  have hQk : own k + 16 * k = Q + 4 * (2 * k) := by omega_using [hQ]
  rw [hQk] at u₅
  have f₅ : Frame [sub (s.gpr .ebp) (Q + 4 * (2 * k)) 4] s₄.mem s₅.mem := by
    rw [u₅.mem]
    exact VG.Proof.X25519.X86.frame_write1 (Frame.refl _ _) hfit (by omega_using [hQ']) (Nat.le_refl _) (Nat.le_refl _) _
  have hF : Frame [sub (s.gpr .ebp) Q (8 * k + 4)] s.mem s₅.mem := by
    rw [← mem₂]
    exact (VG.Proof.X25519.X86.frameWiden f₄ hfit (Nat.le_refl _) (by omega_using []) (by omega_using [hQ'])).trans
      (VG.Proof.X25519.X86.frameWiden f₅ hfit (by omega_using []) (by omega_using []) (by omega_using [hQ']))
  have hval : val32 u.mem base Q (2 * k + 1) =
      num (qw s₄.mem (s.gpr .ebp) Q) (2 * k) + (2 ^ 32) ^ (2 * k) * v s₄ .ebx := by
    have h := square_num_eq u.mem (x := s.gpr .ebp) (o := Q) (2 * k + 1) (by omega_using [hx, hn, hQ'])
    rw [hb.ebp] at h
    rw [← h, num_succ, u₆.mem]
    refine congr (congrArg _ (num_congr fun i hi => ?_)) ?_
    · exact congrArg BitVec.toNat (VG.Proof.X25519.X86.wd_frame1 f₅ hfit (by omega_using [hQ'])
        (by omega_using [hQ', hi]) (by omega_using [hi]))
    · rw [u₅.mem, wv, VG.Proof.X25519.X86.wd_write_self]
  have K₁₄ : Keep s₁ s₄ := k₂.trans k₄
  have edi₅ : s₅.gpr .edi = s.gpr .ebp := by rw [u₅.gpr, K₁₄.edi, u₁.gpr]
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, U, ?_⟩
  · rw [u₆.mem, ← hb.ebp]
    exact square_frame_outside (by omega_using [hx, hn, hQ']) (by omega_using []) hF
  · intro r hr
    cases r <;> simp at hr
    · rw [u₆.other _ (by decide), u₅.gpr, K₁₄.esp, u₁.other _ (by decide)]
    · rw [u₆.gpr, edi₅]
    · rw [u₆.other _ (by decide), u₅.gpr, K₁₄.esi, u₁.other _ (by decide)]
  · rw [u₆.rd, u₅.rd, K₁₄.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, K₁₄.wr, u₁.wr]
  · rw [hval]; exact hlt
  · rw [hval, Nat.pow_mul]; exact hres

theorem mulTerms_ok {mem : Mem} {x : BitVec 32} {A B N Q : Nat} (hA : A + 4 * N ≤ Q) (hB : Q + 4 * N ≤ B)
    (hB' : B + 4 * N ≤ 4096) : TermsOk mem x Q N (mulTerms A B N) (qw mem x A) (qw mem x B) := by
  refine ⟨fun c t ht d hd => ?_, fun c => mulTerms_colv _ _ _ _ _ _, fun _ => wv_lt32 _ _ _, fun _ => wv_lt32 _ _ _⟩
  simp only [mulTerms, List.mem_filterMap] at ht
  obtain ⟨i, -, h⟩ := ht
  split at h
  next hc =>
    cases h
    simp only [treads, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> constructor <;> omega_using [hc, hA, hB, hB']
  next => cases h

theorem sqTerms_ok {mem : Mem} {x : BitVec 32} {A N Q : Nat} (hA : A + 4 * N ≤ Q) (hQ : Q ≤ 4096) :
    TermsOk mem x Q N (sqTerms A N) (qw mem x A) (qw mem x A) := by
  refine ⟨fun c t ht d hd => ?_, fun c => sqTerms_colv _ _ _ _ _, fun _ => wv_lt32 _ _ _, fun _ => wv_lt32 _ _ _⟩
  simp only [sqTerms, List.mem_filterMap] at ht
  obtain ⟨i, -, h⟩ := ht
  split at h
  next hc =>
    cases h
    have hd' : d = A + 4 * i ∨ d = A + 4 * (c - i) := by
      split at hd <;> simp only [treads, List.mem_cons, List.not_mem_nil, or_false] at hd <;> omega_using [hd]
    rcases hd' with rfl | rfl <;> constructor <;> omega_using [hc, hA, hQ]
  next => cases h

theorem colsMul_ok {s : State} {base : Addr} {k m pa pb : Nat} (hb : Bx s base 8192)
    (hM : MulOk k m) (hk : k ≤ 9) (hpa : Ptr s .edi pa) (hpb : Ptr s .esi pb)
    (hL : MulLayB k 8192 pa pb (own k)) (hB : val32 s.mem base pb (2 * k) < m) :
    WP isa (.block (colsMul k m)) s fun u =>
      Outside base (own k) (24 * k + 4) s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .edi] s u ∧
      val32 u.mem base (own k + 4 * (2 * k)) (2 * k + 1) < 2 * m ∧
      ∃ U, 2 ^ (32 * (2 * k)) * val32 u.mem base (own k + 4 * (2 * k)) (2 * k + 1) =
        val32 s.mem base pa (2 * k) * val32 s.mem base pb (2 * k) + U * m := by
  have hn := hb.nowrap
  have hown := own_le hk
  have hk0 := hM.k0
  have hLa := hL.pa; have hLb := hL.pb
  have htmp : tmpAt k = own k + 16 * k + 4 := by simp only [tmpAt]; omega_using []
  unfold colsMul
  refine WP.block_append (WP.mono (copyWords_ok hb hpa (by decide) (N := 2 * k) (d := own k) hLa (by omega_using [hown])
    (2 * k) (Nat.le_refl _)) fun s₁ ⟨O₁, K₁, V₁⟩ => ?_)
  have hb₁ := hb.of_keeps K₁ (by decide)
  refine WP.block_append (WP.mono (copyWords_ok hb₁ (hpb.of_keeps K₁ (by decide) (by decide)) (by decide) (N := 2 * k)
    (d := tmpAt k) (by omega_using [hLb, htmp]) (by omega_using [hown, htmp]) (2 * k) (Nat.le_refl _))
    fun s₂ ⟨O₂, K₂, V₂⟩ => ?_)
  have hb₂ := hb₁.of_keeps K₂ (by decide)
  have ex := hb₂.ebp_toNat
  have hval : ∀ o, o + 4 * (2 * k) ≤ 4096 → num (qw s₂.mem (s₂.gpr .ebp) o) (2 * k) = val32 s₂.mem base o (2 * k) :=
    fun o ho => by rw [← hb₂.ebp]; exact square_num_eq _ _ (by omega_using [ex, hn, ho])
  have hA₂ : val32 s₂.mem base (own k) (2 * k) = val32 s.mem base pa (2 * k) := by
    rw [O₂.val32 (by omega_using [htmp]) (by omega_using [hown, hn]), square_val_congr _ V₁]
  have hB₂ : val32 s₂.mem base (tmpAt k) (2 * k) = val32 s.mem base pb (2 * k) := by
    rw [square_val_congr _ V₂, O₁.val32 (by omega_using [hLb]) (by omega_using [hown, hn, hLb])]
  have hT : TermsOk s₂.mem (s₂.gpr .ebp) (own k + 4 * (2 * k)) (2 * k) (mulTerms (own k) (tmpAt k) (2 * k))
      (qw s₂.mem (s₂.gpr .ebp) (own k)) (qw s₂.mem (s₂.gpr .ebp) (tmpAt k)) :=
    mulTerms_ok (Nat.le_refl _) (by omega_using [htmp]) (by omega_using [htmp, hown, hk0])
  refine WP.mono (montCols_ok hb₂ hM hk hT (by rw [hval (tmpAt k) (by omega_using [htmp, hown, hk0]), hB₂]; exact hB))
    fun u ⟨O, K, H, U, E⟩ => ⟨?_, ?_, H, U, ?_⟩
  · have o₁ : Outside base (own k) (24 * k + 4) s.mem s₁.mem := O₁.mono (Nat.le_refl _) (by omega_using [])
    have o₂ : Outside base (own k) (24 * k + 4) s₁.mem s₂.mem := O₂.mono (by omega_using [htmp]) (by omega_using [htmp])
    exact (o₁.trans o₂).trans (O.mono (by omega_using []) (by omega_using []))
  · exact ((K₁.trans K₂).mono (by decide)).trans K
  · rw [E, hval (own k) (by omega_using [hown]), hval (tmpAt k) (by omega_using [htmp, hown, hk0]), hA₂, hB₂]

theorem colsSquare_ok {s : State} {base : Addr} {k m pa : Nat} (hb : Bx s base 8192)
    (hM : MulOk k m) (hk : k ≤ 9) (hpa : Ptr s .edi pa) (hLa : pa + 4 * (2 * k) ≤ own k)
    (hB : val32 s.mem base pa (2 * k) < m) :
    WP isa (.block (colsSquare k m)) s fun u =>
      Outside base (own k) (24 * k + 4) s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .edi] s u ∧
      val32 u.mem base (own k + 4 * (2 * k)) (2 * k + 1) < 2 * m ∧
      ∃ U, 2 ^ (32 * (2 * k)) * val32 u.mem base (own k + 4 * (2 * k)) (2 * k + 1) =
        val32 s.mem base pa (2 * k) * val32 s.mem base pa (2 * k) + U * m := by
  have hn := hb.nowrap
  have hown := own_le hk
  unfold colsSquare
  refine WP.block_append (WP.mono (copyWords_ok hb hpa (by decide) (N := 2 * k) (d := own k) hLa (by omega_using [hown])
    (2 * k) (Nat.le_refl _)) fun s₁ ⟨O₁, K₁, V₁⟩ => ?_)
  have hb₁ := hb.of_keeps K₁ (by decide)
  have ex := hb₁.ebp_toNat
  have hval : num (qw s₁.mem (s₁.gpr .ebp) (own k)) (2 * k) = val32 s.mem base pa (2 * k) := by
    rw [← square_val_congr _ V₁, ← hb₁.ebp]
    exact square_num_eq _ _ (by omega_using [ex, hn, hown])
  have hT : TermsOk s₁.mem (s₁.gpr .ebp) (own k + 4 * (2 * k)) (2 * k) (sqTerms (own k) (2 * k))
      (qw s₁.mem (s₁.gpr .ebp) (own k)) (qw s₁.mem (s₁.gpr .ebp) (own k)) :=
    sqTerms_ok (Nat.le_refl _) (by omega_using [hown])
  refine WP.mono (montCols_ok hb₁ hM hk hT (by rw [hval]; exact hB)) fun u ⟨O, K, H, U, E⟩ => ⟨?_, ?_, H, U, ?_⟩
  · have o₁ : Outside base (own k) (24 * k + 4) s.mem s₁.mem := O₁.mono (Nat.le_refl _) (by omega_using [])
    exact o₁.trans (O.mono (by omega_using []) (by omega_using []))
  · exact (K₁.mono (by decide)).trans K
  · rw [E, hval]

end

theorem mulBody_ok {s : State} {base : Addr} {k m pa pb : Nat} (hb : Bx s base 8192)
    (hM : MulOk k m) (hpa : Ptr s .edi pa) (hpb : Ptr s .esi pb)
    (hL : MulLayB k 8192 pa pb (own k)) (hB : val32 s.mem base pb (2 * k) < m) :
    WP isa (mulBody k m) s fun u =>
      Outside base (own k) (24 * k + 4) s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .edi] s u ∧
      val32 u.mem base (own k + 4 * (2 * k)) (2 * k + 1) < 2 * m ∧
      ∃ U, 2 ^ (32 * (2 * k)) * val32 u.mem base (own k + 4 * (2 * k)) (2 * k + 1) =
        val32 s.mem base pa (2 * k) * val32 s.mem base pb (2 * k) + U * m := by
  have hk := hM.k0
  have general : WP isa (.block (rowsF k m (2 * k))) s fun u =>
      Outside base (own k) (24 * k + 4) s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .edi] s u ∧
      val32 u.mem base (own k + 4 * (2 * k)) (2 * k + 1) < 2 * m ∧
      ∃ U, 2 ^ (32 * (2 * k)) * val32 u.mem base (own k + 4 * (2 * k)) (2 * k + 1) =
        val32 s.mem base pa (2 * k) * val32 s.mem base pb (2 * k) + U * m :=
    WP.mono (rowsF_ok hb hM hpa hpb hL hB (2 * k) (by omega_using [hk]) (by omega_using []))
      fun _ ⟨O, K, H, E⟩ => ⟨O.mono (by omega_using []) (by omega_using []), K.mono (by decide), H, E⟩
  unfold mulBody
  split
  next he =>
    obtain ⟨rfl, hm5⟩ := he
    refine WP.seq (wp_cmp fun t R _ Z => ?_)
    apply WP.block_nil
    refine WP.ite (s.gpr .edi - s.gpr .esi == 0) Z (fun h => ?_) (fun _ => ?_)
    · rewrite [hm5] at hB ⊢
      have hpaFit := hL.pa; have hpbFit := hL.pb
      have ho : own 9 = 3520 := rfl
      have hab := square_pointer_eq (by omega_using [hpaFit, ho] : pa < 2 ^ 32)
        (by omega_using [hpbFit, ho] : pb < 2 ^ 32) hpa hpb h
      subst pa
      have K := R.keeps []
      refine WP.mono (p521Square_ok (hb.of_keeps K (by decide))
        (hpb.of_keeps K (by decide) (by decide)) hpbFit (by rw [R.mem]; exact hB))
        fun u ⟨O, K', H, E⟩ => ?_
      rewrite [R.mem] at O E
      exact ⟨O, (K.mono (by decide)).trans (K'.mono (by decide)), H, E⟩
    · have K := R.keeps []
      refine WP.mono (rowsF_ok (hb.of_keeps K (by decide)) hM
        (hpa.of_keeps K (by decide) (by decide)) (hpb.of_keeps K (by decide) (by decide)) hL
        (by rw [R.mem]; exact hB) (2 * 9) (by decide) (by decide)) fun u ⟨O, K', H, E⟩ => ?_
      rewrite [R.mem] at O E
      exact ⟨O.mono (by omega_using []) (by omega_using []), (K.mono (by decide)).widen K' (by decide), H, E⟩
  next _ =>
    split
    next hk9 =>
      refine WP.seq (wp_cmp fun t R _ Z => ?_)
      apply WP.block_nil
      have K := R.keeps []
      have hbt := hb.of_keeps K (by decide)
      have hpat : Ptr t .edi pa := hpa.of_keeps K (by decide) (by decide)
      refine WP.ite (s.gpr .edi - s.gpr .esi == 0) Z (fun h => ?_) (fun _ => ?_)
      · have hpaFit := hL.pa; have hpbFit := hL.pb
        have ho := own_le hk9.2
        have hab := square_pointer_eq (by omega_using [hpaFit, ho] : pa < 2 ^ 32)
          (by omega_using [hpbFit, ho] : pb < 2 ^ 32) hpa hpb h
        subst pa
        refine WP.mono (colsSquare_ok hbt hM hk9.2 hpat hpbFit (by rw [R.mem]; exact hB))
          fun u ⟨O, K', H, E⟩ => ?_
        rw [R.mem] at O E
        exact ⟨O, (K.mono (by decide)).trans K', H, E⟩
      · refine WP.mono (colsMul_ok hbt hM hk9.2 hpat (hpb.of_keeps K (by decide) (by decide)) hL
          (by rw [R.mem]; exact hB)) fun u ⟨O, K', H, E⟩ => ?_
        rw [R.mem] at O E
        exact ⟨O, (K.mono (by decide)).trans K', H, E⟩
    next _ => exact general

end VG.Proof.Weierstrass.X86.Mont
