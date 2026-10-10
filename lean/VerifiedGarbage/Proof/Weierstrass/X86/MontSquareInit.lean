import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Proof.Weierstrass.X86.MontBase
import VerifiedGarbage.Impl.Weierstrass.X86.Mont

/-! ## `MontSquareColumns` -/

section

/-!
# Full-width squaring columns for x86 P-256 Montgomery arithmetic

Reuse the existing x86 Comba kernel, without X25519's modular folding.
The input lies above the sixteen output words in the Montgomery workspace.
-/

namespace VG.Proof.Weierstrass.X86.Mont

open VG VG.X86 VG.Impl.X25519.X86 VG.Proof.X25519.X86

theorem square_col_bound (s : State) (x : BitVec 32) (a k : Nat) (hk : k < 16) :
    colv s.mem x (sqrTerms a k) < 2 ^ 68 := by
  have hl : (sqrTerms a k).length ≤ 5 := by
    simp only [sqrTerms, List.length_append, List.length_map]
    have := (by decide : ∀ k < 16, ((List.range 8).filter fun i => 2 * i < k && k - i < 8).length ≤ 4) k hk
    split <;> simp only [List.length_cons, List.length_nil] <;> omega_using [this]
  have h1 := colv_le_len (m := s.mem) (x := x) (B := 2 ^ 65) (ts := sqrTerms a k) fun t ht => by
    simp only [sqrTerms, List.mem_append, List.mem_map] at ht
    rcases ht with ⟨i, -, rfl⟩ | ht
    · have := wv_mul_le s.mem x (a + 4 * i) (a + 4 * (k - i))
      simp only [tval]; omega_using [this]
    · split at ht
      · simp only [List.mem_singleton] at ht
        subst ht
        have := wv_mul_le s.mem x (a + 4 * (k / 2)) (a + 4 * (k / 2))
        simp only [tval]; omega_using [this]
      · exact absurd ht List.not_mem_nil
  have h2 := Nat.mul_le_mul_right (2 ^ 65) hl
  omega_using [h1, h2]

theorem square_col_sum (s : State) (x : BitVec 32) (a : Nat) :
    num (fun k => colv s.mem x (sqrTerms a k)) 16 = fe s.mem x a * fe s.mem x a := by
  have hcol : ∀ k, colv s.mem x (sqrTerms a k) = ((((List.range 8).filter fun i => 2 * i < k && k - i < 8).map
      fun i => 2 * (wv s.mem x (a + 4 * i) * wv s.mem x (a + 4 * (k - i)))) ++
      if k % 2 == 0 && k < 16 then [wv s.mem x (a + 4 * (k / 2)) * wv s.mem x (a + 4 * (k / 2))]
      else []).sum := fun k => by
    unfold colv sqrTerms
    rw [List.map_append, List.map_map]
    split <;> rfl
  simp only [hcol]
  exact sqr_identity (fun i => wv s.mem x (a + 4 * i))

/-- Full 512-bit square, with no carry beyond the output. -/
theorem square_columns_ok {W : Nat} {c : Bool} {x : BitVec 32} {s : State}
    (hc : Ctx W x s c) {o a : Nat} (ha : a + 32 ≤ 4096) (hoa : o + 64 ≤ a) :
    WP isa (.block (zeroAcc ++ cols o 16 (sqrTerms a))) s fun u =>
      Keep s u ∧ Frame [sub x o 64] s.mem u.mem ∧
      num (fun k => wv u.mem x (o + 4 * k)) 16 = fe s.mem x a * fe s.mem x a ∧ acc u = 0 := by
  refine WP.block_append (WP.mono zeroAcc_ok fun t ⟨K, M, Z⟩ => ?_)
  refine WP.mono (cols_ok (K.ctx hc) (sqrTerms a) 16 (by omega) ?_
    (fun k hk => square_col_bound t x a k hk) (by rw [Z]; decide)) fun u ⟨K', F, E, _⟩ => ?_
  · intro k hk term ht d hd
    simp only [sqrTerms, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
      Bool.and_eq_true, decide_eq_true_eq] at ht
    rcases ht with ⟨i, ⟨hi, -, hki⟩, rfl⟩ | ht
    · simp only [treads, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl <;> constructor <;> omega
    · split at ht
      · simp only [List.mem_singleton] at ht
        subst term
        simp only [treads, List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl <;> constructor <;> omega
      · exact absurd ht List.not_mem_nil
  · rw [Z, Nat.zero_add, square_col_sum, M] at E
    have hA := fe_lt s.mem x a
    have hAA := Nat.mul_lt_mul_of_lt_of_lt hA hA
    have hpow : (2 ^ 32 : Nat) ^ 16 = 2 ^ 256 * 2 ^ 256 := by decide
    rw [hpow] at E
    have hz : acc u = 0 := by omega
    refine ⟨K.trans K', ?_, ?_, hz⟩
    · simpa only [M] using F
    · simpa only [hz, Nat.mul_zero, Nat.add_zero] using E

end VG.Proof.Weierstrass.X86.Mont

end

/-! ## `MontSquareCopy` -/

section

/-! # Copying a square's operand into the existing Montgomery temporary area -/
namespace VG.Proof.Weierstrass.X86.Mont
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

variable {s : State} {base : Addr}

theorem squareCopy_ok (hb : Bx s base 8192) {a : Nat} (hp : Ptr s .esi a)
    (ha : a + 32 ≤ own 4) : ∀ j, j ≤ 8 →
    WP isa (.block (squareCopy j)) s fun u =>
      Outside base (tmpAt 4) (4 * j) s.mem u.mem ∧ Keeps [.eax] s u ∧
      ∀ i < j, w32 u.mem base (tmpAt 4 + 4 * i) = w32 s.mem base (a + 4 * i)
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, Keeps.refl _ _, by omega⟩
  | j + 1, hj => by
    have hn := hb.nowrap
    have htmp : tmpAt 4 = 3908 := rfl
    have hown : own 4 = 3840 := rfl
    rw [squareCopy]
    refine WP.block_append (WP.mono (squareCopy_ok hb hp ha j (by omega)) fun t ⟨O, K, V⟩ => ?_)
    have hbt := hb.of_keeps K (by decide)
    have hpt := hp.of_keeps K (by decide) (by decide)
    refine wp_movS (readSrc_ptr hbt hpt (d := 4 * j) (by omega)) fun v R _ => ?_
    have hbv := hbt.of_keeps R.keeps (by decide)
    refine wp_storeS (hbv.ea (d := tmpAt 4 + 4 * j) (by omega)) (hbv.write (n := 4) (by omega))
      fun u M => WP.block_nil ?_
    have hm : u.mem = t.mem.writeW (off base (tmpAt 4 + 4 * j))
        (t.mem.readW (off base (a + 4 * j)) 32) := by rw [M.mem, R.mem, R.gpr]
    have U := writeW32_outside t.mem base (d := tmpAt 4 + 4 * j)
      (t.mem.readW (off base (a + 4 * j)) 32) (by omega)
    rw [← hm] at U
    refine ⟨(O.mono (Nat.le_refl _) (by omega)).trans (U.mono (by omega) (by omega)),
      (K.trans R.keeps).trans (M.keeps _), ?_⟩
    intro i hi
    by_cases hij : i = j
    · subst i
      rw [hm, w32_write_self]
      exact O.w32 (by omega) (by omega)
    · rw [U.w32 (by omega) (by omega)]
      exact V i (by omega)

end VG.Proof.Weierstrass.X86.Mont

end

/-! ## `MontSquareProduct` -/

section

/-! # The Comba square in the Montgomery callee's workspace -/
namespace VG.Proof.Weierstrass.X86.Mont
open VG VG.X86 VG.X86.Wp VG.Impl.Weierstrass.X86.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

theorem square_wv_eq (m : Mem) {x : BitVec 32} {d : Nat} (hd : x.toNat + d < 2 ^ 32) :
    VG.Proof.X25519.X86.wv m x d = w32 m (x.setWidth 64) d := by
  simp only [VG.Proof.X25519.X86.wv, VG.Proof.X25519.X86.wd, w32, addr_eq hd, off]

theorem square_num_eq (m : Mem) {x : BitVec 32} {o : Nat} : ∀ n,
    x.toNat + o + 4 * n ≤ 2 ^ 32 →
    VG.Proof.X25519.X86.num (fun j => VG.Proof.X25519.X86.wv m x (o + 4 * j)) n = val32 m (x.setWidth 64) o n
  | 0, _ => rfl
  | n + 1, hn => by
    rw [VG.Proof.X25519.X86.num_succ, square_num_eq m n (by omega), val32_succ,
      square_wv_eq m (by omega), ← Nat.pow_mul]

theorem square_frame_outside {m m' : Mem} {x : BitVec 32} {o n : Nat}
    (hx : x.toNat + o + n ≤ 2 ^ 32) (hn : 0 < n)
    (F : Frame [VG.Proof.X25519.X86.sub x o n] m m') : Outside (x.setWidth 64) o n m m' := by
  intro y hy
  apply F y
  intro r hr
  rw [List.mem_singleton.mp hr]
  simp only [VG.Proof.X25519.X86.sub, addr_eq (by omega : x.toNat + o < 2 ^ 32)]
  change ¬ ((y - (x.setWidth 64 + BitVec.ofNat 64 o)).toNat + 1 ≤ n)
  have h := (Offset.lt_iff y (x.setWidth 64) (d := o) (n := n) (by omega)).mp
  simp only [ofs] at hy
  intro h'
  have := h (by omega)
  omega

/-- The copied input is squared exactly; the saved registers and input
buffer remain outside the written product. `ebp` is restored to the base. -/
theorem squareProduct_ok {s : State} {x : BitVec 32} (hc : VG.Proof.X25519.X86.Ctx 8192 x s false) :
    WP isa (.block squareProductBase) s fun u =>
      Bx u (x.setWidth 64) 8192 ∧ VG.Proof.X25519.X86.Keep s u ∧
      Outside (x.setWidth 64) (own 4) 64 s.mem u.mem ∧
      val32 u.mem (x.setWidth 64) (own 4) 16 =
        val32 s.mem (x.setWidth 64) (tmpAt 4) 8 * val32 s.mem (x.setWidth 64) (tmpAt 4) 8 ∧
      u.gpr .ebx = 0 := by
  unfold squareProductBase
  refine WP.block_append (WP.mono (square_columns_ok hc (o := own 4) (a := tmpAt 4)
    (by decide) (by decide)) fun t ⟨K, F, V, Z⟩ => ?_)
  refine wp_movS rfl fun u R _ => WP.block_nil ?_
  have hx := hc.fit
  have hx' : (x.setWidth 64).toNat = x.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]
  have E : u.gpr .ebp = x := by rw [R.gpr, K.edi, hc.edi]
  have W : u.wr = s.wr := R.wr.trans K.wr
  refine ⟨⟨by rw [E], by rw [W]; exact hc.wr, by rw [hx']; exact hx⟩,
    ⟨(R.other _ (by decide)).trans K.esi, (R.other _ (by decide)).trans K.edi,
      (R.other _ (by decide)).trans K.esp, R.rd.trans K.rd, W⟩, ?_, ?_, ?_⟩
  · rw [R.mem]
    exact square_frame_outside (by change x.toNat + 3840 + 64 ≤ 2 ^ 32; omega) (by decide) F
  · rw [R.mem]
    simp only [VG.Proof.X25519.X86.fe] at V
    rw [square_num_eq _ 16 (by change x.toNat + 3840 + 4 * 16 ≤ 2 ^ 32; omega),
      square_num_eq _ 8 (by change x.toNat + 3908 + 4 * 8 ≤ 2 ^ 32; omega)] at V
    exact V
  · rw [R.other _ (by decide)]
    apply BitVec.eq_of_toNat_eq
    change (t.gpr .ebx).toNat = 0
    simp only [VG.Proof.X25519.X86.acc, VG.Proof.X25519.X86.v] at Z
    omega

end VG.Proof.Weierstrass.X86.Mont

end

/-! ## `MontSquareInit` -/

section

/-! # Full-product initialization for the callable x86 P-256 square -/
namespace VG.Proof.Weierstrass.X86.Mont
open VG VG.X86 VG.X86.Wp VG.Impl.Weierstrass.X86.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

/-- Equal words at different offsets represent equal numbers. -/
theorem square_val_congr {m m' : Mem} {base : Addr} {d d' : Nat} : ∀ n,
    (∀ i < n, w32 m' base (d' + 4 * i) = w32 m base (d + 4 * i)) →
    val32 m' base d' n = val32 m base d n
  | 0, _ => rfl
  | n + 1, h => by
    rw [val32_succ, val32_succ, square_val_congr n (fun i hi => h i (by omega)), h n (by omega)]

theorem square_zero_top {mem : Mem} {base : Addr} {o n : Nat}
    (hz : w32 mem base (o + 4 * n) = 0) : val32 mem base o (n + 1) = val32 mem base o n := by
  rw [val32_succ, hz, Nat.mul_zero, Nat.add_zero]

theorem squareInit_ok {s : State} {base : Addr} {a : Nat} (hb : Bx s base 8192)
    (hp : Ptr s .esi a) (ha : a + 32 ≤ own 4) :
    WP isa (.block squareInit) s fun u =>
      Outside base (own 4) 100 s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .edi] s u ∧
      val32 u.mem base (own 4) 17 = val32 s.mem base a 8 * val32 s.mem base a 8 := by
  have hn := hb.nowrap
  have hown : own 4 = 3840 := rfl
  have htmp : tmpAt 4 = 3908 := rfl
  simp only [squareInit, List.append_assoc]
  refine WP.block_append (WP.mono (squareCopy_ok hb hp ha 8 (by decide)) fun t ⟨O, K, V⟩ => ?_)
  have V' := square_val_congr 8 V
  simp only [List.cons_append, List.nil_append]
  refine wp_movS rfl fun v R _ => ?_
  have hv : v.mem = t.mem := R.mem
  have he : v.gpr .edi = s.gpr .ebp := by rw [R.gpr, K.1 _ (by decide)]
  have hc : VG.Proof.X25519.X86.Ctx 8192 (s.gpr .ebp) v false :=
    ⟨he, by rw [hb.ebp_toNat]; exact hn,
      by change (⟨(s.gpr .ebp).setWidth 64, 8192⟩ : Region) ∈ v.wr
         rw [R.wr, K.2.2, hb.ebp]; exact hb.wr, by decide, nofun⟩
  refine WP.block_append (WP.mono (squareProduct_ok hc) fun w ⟨hbw, K', O', V'', Z⟩ => ?_)
  rw [hb.ebp] at hbw O' V''
  rw [hv, V'] at V''
  refine wp_storeS (hbw.ea (d := own 4 + 64) (by omega)) (hbw.write (n := 4) (by omega))
    fun u M => WP.block_nil ?_
  have hm : u.mem = w.mem.writeW (off base (own 4 + 64)) (0 : BitVec 32) := by rw [M.mem, Z]
  have O'' := writeW32_outside w.mem base (d := own 4 + 64) (0 : BitVec 32) (by omega)
  rw [← hm] at O''
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hv] at O'
    exact ((O.mono (by omega) (by omega)).trans (O'.mono (by omega) (by omega))).trans
      (O''.mono (by omega) (by omega))
  · intro r hr
    have hwE : w.gpr .ebp = s.gpr .ebp := by
      apply BitVec.eq_of_toNat_eq
      exact hbw.ebp_toNat.trans hb.ebp_toNat.symm
    cases r <;> simp at hr
    · rw [M.gpr, K'.esp, R.other _ (by decide), K.1 _ (by decide)]
    · rw [M.gpr, hwE]
    · rw [M.gpr, K'.esi, R.other _ (by decide), K.1 _ (by decide)]
  · rw [M.rd, K'.rd, R.rd, K.2.1]
  · rw [M.wr, K'.wr, R.wr, K.2.2]
  · have hz : w32 u.mem base (own 4 + 4 * 16) = 0 := by rw [hm, w32_write_self]; rfl
    rw [square_zero_top hz, O''.val32 (by omega) (by omega)]
    exact V''


end VG.Proof.Weierstrass.X86.Mont

end
