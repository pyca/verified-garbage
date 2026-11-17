module

import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Weierstrass.X86.MontRow
import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
import VerifiedGarbage.Proof.Mont.X86.Loop
import VerifiedGarbage.Proof.Mont.X86.RedRow
import VerifiedGarbage.Proof.Mont.X86.Row
public import VerifiedGarbage.Proof.Weierstrass.X86.MontBase
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareRed
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareArithmetic
import VerifiedGarbage.Proof.X25519.X86.Arith
public import VerifiedGarbage.Proof.X25519.X86.Column
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Weierstrass.X86.MontSquareBody`, which this module and modules that import it used -/

section

/-! ### `Weierstrass.X86.MontSquareInit`, which this module and modules that import it used -/

section

/-! ## `MontSquareColumns` -/

@[expose] public section

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
  refine WP.mono (cols_ok (K.ctx hc) (sqrTerms a) 16 (by omega_using [ha, hoa]) ?_
    (fun k hk => square_col_bound t x a k hk) (by rw [Z]; decide)) fun u ⟨K', F, E, _⟩ => ?_
  · intro k hk term ht d hd
    simp only [sqrTerms, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
      Bool.and_eq_true, decide_eq_true_eq] at ht
    rcases ht with ⟨i, ⟨hi, -, hki⟩, rfl⟩ | ht
    · simp only [treads, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl <;> constructor <;> omega_arith
    · split at ht
      · simp only [List.mem_singleton] at ht
        subst term
        simp only [treads, List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl <;> constructor <;> omega_arith
      · exact absurd ht List.not_mem_nil
  · rw [Z, Nat.zero_add, square_col_sum, M] at E
    have hA := fe_lt s.mem x a
    have hAA := Nat.mul_lt_mul_of_lt_of_lt hA hA
    have hpow : (2 ^ 32 : Nat) ^ 16 = 2 ^ 256 * 2 ^ 256 := by decide
    rw [hpow] at E
    have hz : acc u = 0 := by omega_using [E, hAA]
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
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, Keeps.refl _ _, by omega_using []⟩
  | j + 1, hj => by
    have hn := hb.nowrap
    have htmp : tmpAt 4 = 3908 := rfl
    have hown : own 4 = 3840 := rfl
    rw [squareCopy]
    refine WP.block_append (WP.mono (squareCopy_ok hb hp ha j (by omega_using [hj])) fun t ⟨O, K, V⟩ => ?_)
    have hbt := hb.of_keeps K (by decide)
    have hpt := hp.of_keeps K (by decide) (by decide)
    refine wp_movS (readSrc_ptr hbt hpt (d := 4 * j) (by omega_using [ha, hj, hown])) fun v R _ => ?_
    have hbv := hbt.of_keeps R.keeps (by decide)
    refine wp_storeS (hbv.ea (d := tmpAt 4 + 4 * j) (by omega_using [hj, htmp])) (hbv.write (n := 4) (by omega_using [hj, htmp]))
      fun u M => WP.block_nil ?_
    have hm : u.mem = t.mem.writeW (off base (tmpAt 4 + 4 * j))
        (t.mem.readW (off base (a + 4 * j)) 32) := by rw [M.mem, R.mem, R.gpr]
    have U := writeW32_outside t.mem base (d := tmpAt 4 + 4 * j)
      (t.mem.readW (off base (a + 4 * j)) 32) (by omega_using [hj, htmp])
    rw [← hm] at U
    refine ⟨(O.mono (Nat.le_refl _) (by omega_using [])).trans (U.mono (by omega_using []) (by omega_using [])),
      (K.trans R.keeps).trans (M.keeps _), ?_⟩
    intro i hi
    by_cases hij : i = j
    · subst i
      rw [hm, w32_write_self]
      exact O.w32 (by omega_using [ha, hj, htmp, hown]) (by omega_using [ha, hj, hown])
    · rw [U.w32 (by omega_using [hij]) (by omega_using [hj, htmp, hi])]
      exact V i (by omega_using [hi, hij])

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
    exact square_frame_outside (by change x.toNat + 3840 + 64 ≤ 2 ^ 32; omega_using [hx]) (by decide) F
  · rw [R.mem]
    simp only [VG.Proof.X25519.X86.fe] at V
    rw [square_num_eq _ 16 (by change x.toNat + 3840 + 4 * 16 ≤ 2 ^ 32; omega_using [hx]),
      square_num_eq _ 8 (by change x.toNat + 3908 + 4 * 8 ≤ 2 ^ 32; omega_using [hx])] at V
    exact V
  · rw [R.other _ (by decide)]
    apply BitVec.eq_of_toNat_eq
    change (t.gpr .ebx).toNat = 0
    simp only [VG.Proof.X25519.X86.acc, VG.Proof.X25519.X86.v] at Z
    omega_using [Z]

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
    rw [val32_succ, val32_succ, square_val_congr n (fun i hi => h i (by omega_using [hi])), h n (by omega_using [])]

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
  refine wp_storeS (hbw.ea (d := own 4 + 64) (by omega_using [hown])) (hbw.write (n := 4) (by omega_using [hown]))
    fun u M => WP.block_nil ?_
  have hm : u.mem = w.mem.writeW (off base (own 4 + 64)) (0 : BitVec 32) := by rw [M.mem, Z]
  have O'' := writeW32_outside w.mem base (d := own 4 + 64) (0 : BitVec 32) (by omega_using [hown])
  rw [← hm] at O''
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hv] at O'
    exact ((O.mono (by omega_using [hown, htmp]) (by omega_using [hown, htmp])).trans (O'.mono (by omega_using []) (by omega_using []))).trans
      (O''.mono (by omega_using []) (by omega_using []))
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
    rw [square_zero_top hz, O''.val32 (by omega_using []) (by omega_using [hown])]
    exact V''


end VG.Proof.Weierstrass.X86.Mont

end

end

end

/-! ## `MontSquareRound` -/

@[expose] public section

section

/-! # A REDC round on a completed x86 P-256 product -/
namespace VG.Proof.Weierstrass.X86.Mont
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

theorem squareRound_ok {s : State} {base : Addr} (hb : Bx s base 8192)
    {i : Nat} (hi : i < 8)
    (hlt : val32 s.mem base (own 4 + 4 * i) (17 - i) + (2 ^ 32 - 1) * p256Prime < 2 ^ (32 * (17 - i))) :
    WP isa (.block (squareRound i)) s fun u =>
      Outside base (own 4) 68 s.mem u.mem ∧ Keeps [.eax, .ecx] s u ∧
      ∃ q, q < 2 ^ 32 ∧
        2 ^ 32 * val32 u.mem base (own 4 + 4 * (i + 1)) (16 - i) =
          val32 s.mem base (own 4 + 4 * i) (17 - i) + q * p256Prime := by
  have hn := hb.nowrap
  have ho : own 4 = 3840 := rfl
  simp only [squareRound, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_bp hb (d := own 4 + 4 * i) (by omega_using [hi, ho])) fun t R _ => ?_
  have hbt := hb.of_keeps R.keeps (by decide)
  have hq : (t.gpr .ecx).toNat = w32 s.mem base (own 4 + 4 * i) := by rw [R.gpr]
  have hqB := (t.gpr .ecx).isLt
  have hqp : (t.gpr .ecx).toNat * p256Prime ≤ (2 ^ 32 - 1) * p256Prime :=
    Nat.mul_le_mul_right _ (by omega_using [])
  refine WP.mono (squareRed_ok hbt (w := own 4 + 4 * i) (extra := 7 - i) (by omega_using [])
    (by omega_using [hi, ho]) (by rw [R.mem]; exact hq) ?_) fun u ⟨O, V, K⟩ => ?_
  · rw [R.mem, show 10 + (7 - i) = 17 - i by omega_using [hi]]
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hqp _) hlt
  · refine ⟨?_, (R.keeps.mono (by decide)).widen K (by decide), (t.gpr .ecx).toNat, hqB, ?_⟩
    · rw [R.mem] at O
      exact O.mono (by omega_using []) (by omega_using [hi])
    · rw [R.mem, show 10 + (7 - i) = 17 - i by omega_using [hi]] at V
      have he : 17 - i = (16 - i) + 1 := by omega_using [hi]
      rw [he, val32, val32] at V
      have hlow := (u.mem.readW (off base (own 4 + 4 * i)) 32).isLt
      rw [← hq] at V
      have heq : own 4 + 4 * (i + 1) = own 4 + 4 * i + 4 := by omega_using []
      rw [heq, he, val32, ← hq]
      simp only [p256Prime, w32] at V ⊢
      omega_using [V, hlow]

end VG.Proof.Weierstrass.X86.Mont

end

/-! ## `MontSquareLoop` -/

section

/-! # Eight REDC rounds after full-width x86 P-256 squaring -/
namespace VG.Proof.Weierstrass.X86.Mont
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

def SquareInv (base : Addr) (T i : Nat) (mem : Mem) : Prop :=
  val32 mem base (own 4 + 4 * i) (17 - i) < 2 ^ (32 * (16 - i)) + p256Prime ∧
  ∃ U, U < 2 ^ (32 * i) ∧
    2 ^ (32 * i) * val32 mem base (own 4 + 4 * i) (17 - i) = T + U * p256Prime

theorem squareRounds_ok {s : State} {base : Addr} {T : Nat} (hb : Bx s base 8192)
    (hI : SquareInv base T 0 s.mem) : ∀ r, r ≤ 8 →
    WP isa (.block (squareRounds r)) s fun u =>
      Outside base (own 4) 68 s.mem u.mem ∧ Keeps [.eax, .ecx] s u ∧ SquareInv base T r u.mem
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, Keeps.refl _ _, hI⟩
  | r + 1, hr => by
    rw [squareRounds]
    refine WP.block_append (WP.mono (squareRounds_ok hb hI r (by omega_using [hr])) fun t ⟨O, K, H, U, hU, E⟩ => ?_)
    have hbt := hb.of_keeps K (by decide)
    refine WP.mono (squareRound_ok hbt (by omega_using [hr]) (square_round_room (by omega_using [hr]) H))
      fun u ⟨O', K', q, hq, E'⟩ => ⟨O.trans O', K.trans K', ?_, ?_⟩
    · have h := square_round_bound (by omega_using [hr] : r < 8) hq H E'
      rwa [show 17 - (r + 1) = 16 - r by omega_using []]
    · have h := square_round_multiple hq hU E E'
      rwa [show 17 - (r + 1) = 16 - r by omega_using []]

/-- The final nine words are below `2p` and congruent to the square times `R⁻¹`. -/
theorem squareReduce_ok {s : State} {base : Addr} {a : Nat} (hb : Bx s base 8192)
    (ha : a < p256Prime) (hT : val32 s.mem base (own 4) 17 = a * a) :
    WP isa (.block (squareRounds 8)) s fun u =>
      Outside base (own 4) 68 s.mem u.mem ∧ Keeps [.eax, .ecx] s u ∧
      val32 u.mem base (own 4 + 32) 9 < 2 * p256Prime ∧
      ∃ U, 2 ^ 256 * val32 u.mem base (own 4 + 32) 9 = a * a + U * p256Prime := by
  have hp : p256Prime < 2 ^ 256 := by decide
  have haa := Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_trans ha hp) (Nat.lt_trans ha hp)
  have hI : SquareInv base (a * a) 0 s.mem := by
    simp only [SquareInv, Nat.mul_zero, Nat.add_zero, Nat.sub_zero, Nat.pow_zero, Nat.one_mul, hT]
    refine ⟨?_, 0, by decide, by simp⟩
    omega_using [haa]
  refine WP.mono (squareRounds_ok hb hI 8 (by decide)) fun u ⟨O, K, _, U, hU, E⟩ =>
    ⟨O, K, square_final_bound ha hU E, U, E⟩

end VG.Proof.Weierstrass.X86.Mont

end

/-! ## `MontSquareBody` -/

section

/-! # The x86 P-256 square before its common final subtraction -/
namespace VG.Proof.Weierstrass.X86.Mont
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

theorem squareBody_ok {s : State} {base : Addr} {a : Nat} (hb : Bx s base 8192)
    (hp : Ptr s .esi a) (ha : a + 32 ≤ own 4) (hA : val32 s.mem base a 8 < p256Prime) :
    WP isa (.block squareBody) s fun u =>
      Outside base (own 4) 100 s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .edi] s u ∧
      val32 u.mem base (own 4 + 32) 9 < 2 * p256Prime ∧
      ∃ U, 2 ^ 256 * val32 u.mem base (own 4 + 32) 9 =
        val32 s.mem base a 8 * val32 s.mem base a 8 + U * p256Prime := by
  unfold squareBody
  refine WP.block_append (WP.mono (squareInit_ok hb hp ha) fun t ⟨O, K, V⟩ => ?_)
  refine WP.mono (squareReduce_ok (hb.of_keeps K (by decide)) hA V) fun u ⟨O', K', H, E⟩ =>
    ⟨O.trans (O'.mono (by omega_using []) (by omega_using [])), K.widen K' (by decide), H, E⟩

end VG.Proof.Weierstrass.X86.Mont

end

end

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

theorem mod_ok (k m : Nat) : (mod k m).ok m = true := by
  simp only [Mod.ok, mod, Option.all_none, Bool.not_false, Bool.true_or, Bool.and_true]
  exact p256RedChoice_ok k m

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

/-- The window `+= q m`, `q` in `ecx`, for `q = t₀ m'` (which P-256's sparse
reduction needs). -/
theorem redRowI_ok (hb : Bx s base size) {k m acc : Nat} (hM : MulOk k m)
    (hacc : acc + 4 * (2 * k) + 8 ≤ size)
    (hq : minv32 (mod k m) = 1 → (s.gpr .ecx).toNat = w32 s.mem base acc)
    (hlt : val32 s.mem base acc (2 * k + 2) + (s.gpr .ecx).toNat * m < 2 ^ (32 * (2 * k + 2))) :
    WP isa (.block (redRowI (mod k m) m acc)) s fun u =>
      Outside base acc (4 * (2 * k) + 8) s.mem u.mem ∧
      val32 u.mem base acc (2 * k + 2) = val32 s.mem base acc (2 * k + 2) + (s.gpr .ecx).toNat * m ∧
      Keeps [.eax, .ebx, .edx] s u := by
  have hk := hM.k0
  have hm2 : m < 2 ^ (32 * (2 * k)) := by rw [← Nat.mul_assoc]; exact hM.m_lt
  unfold redRowI
  split
  next he =>
    obtain ⟨hn, hm', hi⟩ := p256RedEnabled_ok (mod_ok k m) he
    have hk4 : k = 4 := hn
    subst hk4
    rw [hm'] at hlt ⊢
    simp only [Nat.reduceMul, Nat.reduceAdd] at hlt hacc ⊢
    unfold p256Prime at hlt ⊢
    exact WP.mono (p256RedB_ok hb rfl hacc (hq hi) hlt) fun u ⟨O, V, K⟩ => ⟨O, V, K.mono (by decide)⟩
  next _ =>
    rw [words_mod]
    refine WP.mono (rowG_ok hb (by omega_arith) (ysOk_m m) hacc ?_) fun u ⟨O, V, K⟩ => ⟨O, ?_, K⟩
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

/-! # Selecting the x86 P-256 square from public operand pointers -/

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
    obtain ⟨rfl, rfl⟩ := he
    refine WP.seq (wp_cmp fun t R _ Z => ?_)
    apply WP.block_nil
    refine WP.ite (s.gpr .edi - s.gpr .esi == 0) Z (fun h => ?_) (fun _ => ?_)
    · have hpaFit := hL.pa; have hpbFit := hL.pb
      have ho : own 4 = 3840 := rfl
      have hab := square_pointer_eq (by omega_using [hpaFit, ho] : pa < 2 ^ 32) (by omega_using [hpbFit, ho] : pb < 2 ^ 32) hpa hpb h
      subst pa
      have K := R.keeps []
      refine WP.mono (squareBody_ok (hb.of_keeps K (by decide))
        (hpb.of_keeps K (by decide) (by decide)) hpbFit (by rw [R.mem]; exact hB))
        fun u ⟨O, K', H, E⟩ => ?_
      rw [R.mem] at O E
      exact ⟨O, (K.mono (by decide)).trans K', H, E⟩
    · have K := R.keeps []
      refine WP.mono (rowsF_ok (hb.of_keeps K (by decide)) hM
        (hpa.of_keeps K (by decide) (by decide)) (hpb.of_keeps K (by decide) (by decide)) hL
        (by rw [R.mem]; exact hB) 8 (by decide) (by decide)) fun u ⟨O, K', H, E⟩ => ?_
      rw [R.mem] at O E
      exact ⟨O.mono (by omega_using []) (by omega_using []), (K.mono (by decide)).widen K' (by decide), H, E⟩
  next _ => exact general

end VG.Proof.Weierstrass.X86.Mont
