module

public import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
import VerifiedGarbage.Proof.MlKem.Encode
public import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.MlKem.X86_64.Compress
public import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
public import VerifiedGarbage.Proof.MlKem.Bits
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Impl.MlKem.X86_64.Compress
meta import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
meta import VerifiedGarbage.Proof.MlKem.Bits
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.Framework.Range

/-! ### `MlKem.X86_64.Groups`, which only this module used -/

section

/-!
# ML-KEM on x86-64: segments of groups of values and their bytes

The pieces of the compressions (`vg_mlkem_compress_encode`,
`vg_mlkem1024_compress_encode`, …) that move a segment of a group between
values and bytes, for any width `d ≤ 11`: values `o, …, o + c - 1` of the
group accumulated in `r10` from the last (`ceAcc_ok`, the number whose
base-`2ᵈ` digits they are), bytes stored from `r10` (`ceSt_ok`); bytes `o, …,
o + b - 1` loaded into `r10` from the last (`ddLd_ok`, the number whose bytes
they are), and values taken from the bottom of `r10` (`ddVals_ok`). A segment
is a chunk of the number of the group (`chunk_eq`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

/-! ## Chunks of a number -/

/-- Bits `s + p … s + p + m - 1` of the number whose digits are `c` digits
of `L` from digit `o`: those of the number of `L` from bit `w·o + s + p`. -/
theorem chunk_eq {w : Nat} {L : List Nat} (hL : ∀ a ∈ L, a < 2 ^ w) (o c s p m : Nat) (hp : s + p + m ≤ w * c) :
    digits w ((L.drop o).take c) / 2 ^ s / 2 ^ p % 2 ^ m = digits w L / 2 ^ (w * o + s + p) % 2 ^ m := by
  have hd := digits_div hL o
  have hm := digits_mod (L := L.drop o) (fun a ha => hL a (List.mem_of_mem_drop ha)) c
  rw [← hm, Nat.div_div_eq_div_mul, ← Nat.pow_add, mod_pow_div_mod _ (show s + p + m ≤ w * c by omega_arith), ← hd,
    Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_assoc]

/-! ## Bytes written in two parts -/

theorem off_add' (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem Written.append {m m₁ m₂ : Mem} {o : Addr} {a c : Nat} {v₁ v₂ : Nat → Byte} (h₁ : Written m m₁ o a v₁)
    (h₂ : Written m₁ m₂ (o + BitVec.ofNat 64 a) c v₂) (hac : a + c < 2 ^ 64) :
    Written m m₂ o (a + c) fun j => if j < a then v₁ j else v₂ (j - a) := by
  intro x
  rw [h₂ x, h₁ x]
  have e : (x - (o + BitVec.ofNat 64 a)) = (x - o) - BitVec.ofNat 64 a := by bv_omega
  have hA : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat]; omega_arith
  generalize x - o = y at e ⊢
  rw [e]
  by_cases hx : y.toNat < a
  · have : ¬ (y - BitVec.ofNat 64 a).toNat < c := by
      have := y.isLt
      rw [BitVec.toNat_sub, hA]
      rw [show 2 ^ 64 - a + y.toNat = 2 ^ 64 - (a - y.toNat) by omega_arith, Nat.mod_eq_of_lt (by omega_arith)]
      omega_arith
    rw [ifn this, ifp hx, ifp (show y.toNat < a + c by omega_arith)]
    dsimp only
    rw [ifp hx]
  · have e2 : (y - BitVec.ofNat 64 a).toNat = y.toNat - a := by
      have := y.isLt
      rw [BitVec.toNat_sub, hA, show 2 ^ 64 - a + y.toNat = 2 ^ 64 + (y.toNat - a) by omega_arith, Nat.add_mod_left,
        Nat.mod_eq_of_lt (by omega_arith)]
    rw [e2, ifn hx]
    by_cases hc : y.toNat - a < c
    · rw [ifp hc, ifp (show y.toNat < a + c by omega_arith)]
      dsimp only
      rw [ifn hx]
    · rw [ifn hc, ifn (by omega_arith)]

/-! ## Compressing -/

theorem r10zero_ok (s : State) :
    WP isa (.block [.mov32 .r10 (.imm 0)]) s fun s' => (s'.gpr .r10 = 0 ∧ s'.mem = s.mem) ∧
      Keep [.r10] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

/-- `Compress_d` of `a`, as the code computes it with the multiplier `M` and
the rounding constant `r`. -/
def ceV (r d : Nat) (a : BitVec 32) (M : BitVec 64) : BitVec 64 :=
  BitVec.setWidth 64 (BitVec.setWidth 32 ((BitVec.ofNat 64 ((BitVec.setWidth 64 a).toNat * M.toNat) +
    BitVec.ofNat 64 r) >>> 19) &&& BitVec.ofNat 32 (2 ^ d - 1))

theorem ceV_toNat {r d : Nat} (hd : d ≤ 11) {a : BitVec 32} {M : BitVec 64}
    (h : a.toNat * M.toNat + r < 2 ^ 30) :
    (ceV r d a M).toNat = (a.toNat * M.toNat + r) / 2 ^ 19 % 2 ^ d := by
  have hp : 2 ^ d ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) hd
  have hm : (BitVec.ofNat 32 (2 ^ d - 1)).toNat = 2 ^ d - 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have h1 : (BitVec.ofNat 64 ((BitVec.setWidth 64 a).toNat * M.toNat)).toNat = a.toNat * M.toNat := by
    rw [BitVec.toNat_ofNat, toNat_setWidth64, Nat.mod_eq_of_lt (by omega_arith)]
  have h2 : (BitVec.ofNat 64 ((BitVec.setWidth 64 a).toNat * M.toNat) + BitVec.ofNat 64 r).toNat =
      a.toNat * M.toNat + r := by
    rw [BitVec.toNat_add, h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := r) (by omega_arith)]; omega_arith
  have h3 : ((BitVec.ofNat 64 ((BitVec.setWidth 64 a).toNat * M.toNat) + BitVec.ofNat 64 r) >>> 19).toNat =
      (a.toNat * M.toNat + r) / 2 ^ 19 := by rw [shr_toNat, h2]
  rw [ceV, toNat_setWidth64, BitVec.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod,
    toNat_setWidth32_64 (by rw [h3]; omega_arith), h3]

theorem ceCoef_ok (r d j : Nat) (hr : r < 2 ^ 31) (hd1 : 1 ≤ d) (hd : d ≤ 11) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 4) :
    WP isa (.block (ceCoef r d j)) s fun s' =>
      (s'.gpr .r10 = (s.gpr .r10).rotateRight (64 - d) +
          ceV r d (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32) (s.gpr .r9) ∧
        s'.mem = s.mem) ∧ Keep [.rax, .rdx, .r10] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold ceCoef
  xrun [hin, show 1 ≤ 64 - d by omega_arith, show 64 - d ≤ 63 by omega_arith, ceV, sx_ofNat hr]

theorem digits_range_succ (d : Nat) (V : Nat → Nat) (t : Nat) :
    digits d ((List.range (t + 1)).map V) = V 0 + 2 ^ d * digits d ((List.range t).map fun u => V (u + 1)) := by
  rw [List.range_succ_eq_map, List.map_cons, digits_cons, List.map_map]
  rfl

theorem digits_map_lt {d : Nat} {V : Nat → Nat} {t : Nat} (h : ∀ u < t, V u < 2 ^ d) :
    digits d ((List.range t).map V) < 2 ^ (d * t) := by
  have := digits_lt (w := d) (L := (List.range t).map V) (by
    intro a ha
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
    exact h u (List.mem_range.mp hu))
  simpa using this

/-- The `c` compressed values `o, …, o + c - 1` of a group, from the last, into `r10`. -/
theorem ceAcc_ok {r d o c : Nat} (hrr : r < 2 ^ 31) (hd1 : 1 ≤ d) (hd : d ≤ 11) (hdc : d * c ≤ 60) (s : State)
    (hin : ∀ j < c, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (4 * (o + j))) 4) (V : Nat → Nat)
    (hV : ∀ j < c, (ceV r d (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * (o + j))) 32) (s.gpr .r9)).toNat = V j)
    (hVlt : ∀ j < c, V j < 2 ^ d) :
    WP isa (.block (ceAcc r d o c)) s fun s' =>
      (s'.gpr .r10).toNat = digits d ((List.range c).map V) ∧ s'.mem = s.mem ∧
        Keep [.rax, .rdx, .r10] s s' := by
  unfold ceAcc
  rw [WP.block_append_iff]
  refine WP.mono (r10zero_ok s) fun s₀ ⟨⟨h0, hm0⟩, k0⟩ => ?_
  have hdi0 : s₀.gpr .rdi = s.gpr .rdi := k0.gpr (by decide)
  have h90 : s₀.gpr .r9 = s.gpr .r9 := k0.gpr (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun t s' => Keep [.rax, .rdx, .r10] s₀ s' ∧ s'.mem = s.mem ∧
    (s'.gpr .r10).toNat = digits d ((List.range t).map fun u => V (c - t + u)))
    (fun t s' ht ⟨hk, hm, hr⟩ => ?_) c (Nat.le_refl _) s₀ ⟨Keep.refl _ _, hm0, by rw [h0]; rfl⟩)
    fun s' ⟨hk, hm, hr⟩ => ⟨by rw [hr]; simp, hm, (k0.trans hk).mono (by decide)⟩
  have hdi : s'.gpr .rdi = s.gpr .rdi := by rw [hk.gpr (by decide), hdi0]
  have h9 : s'.gpr .r9 = s.gpr .r9 := by rw [hk.gpr (by decide), h90]
  refine WP.mono (ceCoef_ok r d (o + (c - 1 - t)) hrr hd1 hd s' (by
      rw [hk.2.1, hk.2.2, k0.2.1, k0.2.2, hdi]; exact hin _ (by omega_arith)))
    fun s'' ⟨⟨h10, hm'⟩, hk'⟩ => ⟨(hk.trans hk').mono (by decide), hm'.trans hm, ?_⟩
  have hdt : d * t + d ≤ 60 := by
    have := Nat.mul_le_mul_left d (show t + 1 ≤ c by omega_arith); rw [Nat.mul_succ] at this; omega_arith
  have hacc : digits d ((List.range t).map fun u => V (c - t + u)) < 2 ^ (d * t) :=
    digits_map_lt fun u hu => hVlt _ (by omega_arith)
  have hlt : 2 ^ (d * t) * 2 ^ d ≤ 2 ^ 60 := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) hdt
  have hv := hVlt (c - 1 - t) (by omega_arith)
  have hA : digits d ((List.range t).map fun u => V (c - t + u)) * 2 ^ d < 2 ^ 60 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hacc (Nat.two_pow_pos d)) hlt
  have hpd : 2 ^ d ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) hd
  rw [h10, BitVec.toNat_add, rotr_toNat _ (by omega_arith) (by
      rw [hr]; exact Nat.lt_of_lt_of_le hacc (Nat.pow_le_pow_right (by decide) (by omega_arith))),
    hr, hdi, hm, h9, hV _ (by omega_arith), digits_range_succ, show 64 - (64 - d) = d by omega_arith,
    show c - (t + 1) + 0 = c - 1 - t by omega_arith]
  have e : (fun u => V (c - (t + 1) + (u + 1))) = fun u => V (c - t + u) := by
    funext u; congr 1; omega_arith
  rw [e, Nat.mod_eq_of_lt (by omega_arith), Nat.add_comm, Nat.mul_comm]

theorem ceStore_ok (k : Nat) (s : State) (hout : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 k) 1) :
    WP isa (.block (ceStore k)) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .r8 + BitVec.ofNat 64 k) (BitVec.setWidth 8 (s.gpr .r10)) ∧
        s'.gpr .r10 = s.gpr .r10 >>> 8) ∧ Keep [.r10] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold ceStore
  xrun [hout]

/-- The `nb` low bytes of `r10` stored at `r8 + k0`. -/
theorem ceSt_ok {k0 nb : Nat} (hb : nb ≤ 8) (s : State)
    (hout : ∀ k < nb, InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 (k0 + k)) 1) :
    WP isa (.block (ceSt k0 nb)) s fun s' =>
      Written s.mem s'.mem (s.gpr .r8 + BitVec.ofNat 64 k0) nb
          (fun k => BitVec.ofNat 8 ((s.gpr .r10).toNat / 2 ^ (8 * k))) ∧
        Keep [.r10] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun k s' => Keep [.r10] s s' ∧
    (s'.gpr .r10).toNat = (s.gpr .r10).toNat / 2 ^ (8 * k) ∧
    Written s.mem s'.mem (s.gpr .r8 + BitVec.ofNat 64 k0) k (fun t => BitVec.ofNat 8 ((s.gpr .r10).toNat / 2 ^ (8 * t))))
    (fun k s' hk ⟨hkp, hr, hw⟩ => ?_) nb (Nat.le_refl _) s ⟨Keep.refl _ _, by simp, Written.nil _ _ _⟩)
    fun s' ⟨hkp, _, hw⟩ => ⟨hw, hkp⟩
  have h8 : s'.gpr .r8 = s.gpr .r8 := hkp.gpr (by decide)
  refine WP.mono (ceStore_ok (k0 + k) s' (by rw [hkp.2.2, h8]; exact hout k hk))
    fun s'' ⟨⟨hm, h10⟩, hk'⟩ => ⟨(hkp.trans hk').mono (by decide), ?_, ?_⟩
  · rw [h10, shr_toNat, hr, Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ]
  · rw [hm, h8, ← off_add']
    refine (hw.snoc (by omega_arith) _).congr fun t ht => ?_
    by_cases e : t = k
    · subst e; rw [ifp rfl, b8_eq64, hr]
    · rw [ifn e]

/-! ## Decompressing -/

theorem ddByte_ok (k : Nat) (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 k) 1) :
    WP isa (.block (ddByte k)) s fun s' =>
      (s'.gpr .r10 = (s.gpr .r10).rotateRight 56 + BitVec.setWidth 64 (s.mem (s.gpr .rdi + BitVec.ofNat 64 k)) ∧
        s'.mem = s.mem) ∧ Keep [.rax, .r10] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold ddByte
  xrun [hin]

/-- Bytes `o, …, o + b - 1` of a group, from the last, into `r10`. -/
theorem ddLd_ok {o b : Nat} (hb : b ≤ 7) (s : State)
    (hin : ∀ k < b, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (o + k)) 1) :
    WP isa (.block (ddLd o b)) s fun s' =>
      (s'.gpr .r10).toNat = digits 8 ((List.range b).map fun k => (s.mem (s.gpr .rdi + BitVec.ofNat 64 (o + k))).toNat) ∧
        s'.mem = s.mem ∧ Keep [.rax, .r10] s s' := by
  unfold ddLd
  rw [WP.block_append_iff]
  refine WP.mono (r10zero_ok s) fun s₀ ⟨⟨h0, hm0⟩, k0⟩ => ?_
  have hdi0 : s₀.gpr .rdi = s.gpr .rdi := k0.gpr (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun t s' => Keep [.rax, .r10] s₀ s' ∧ s'.mem = s.mem ∧
    (s'.gpr .r10).toNat = digits 8 ((List.range t).map fun u =>
      (s.mem (s.gpr .rdi + BitVec.ofNat 64 (o + (b - t + u)))).toNat))
    (fun t s' ht ⟨hk, hm, hr⟩ => ?_) b (Nat.le_refl _) s₀ ⟨Keep.refl _ _, hm0, by rw [h0]; rfl⟩)
    fun s' ⟨hk, hm, hr⟩ => ⟨by rw [hr]; simp, hm, (k0.trans hk).mono (by decide)⟩
  have hdi : s'.gpr .rdi = s.gpr .rdi := by rw [hk.gpr (by decide), hdi0]
  refine WP.mono (ddByte_ok (o + (b - 1 - t)) s' (by
      rw [hk.2.1, hk.2.2, k0.2.1, k0.2.2, hdi]; exact hin _ (by omega_arith)))
    fun s'' ⟨⟨h10, hm'⟩, hk'⟩ => ⟨(hk.trans hk').mono (by decide), hm'.trans hm, ?_⟩
  have hacc : digits 8 ((List.range t).map fun u =>
      (s.mem (s.gpr .rdi + BitVec.ofNat 64 (o + (b - t + u)))).toNat) < 2 ^ (8 * t) :=
    digits_map_lt fun u _ => BitVec.isLt _
  have hv := (s.mem (s.gpr .rdi + BitVec.ofNat 64 (o + (b - 1 - t)))).isLt
  rw [h10, BitVec.toNat_add, rotr_toNat _ (by decide) (by
      rw [hr]; exact Nat.lt_of_lt_of_le hacc (Nat.pow_le_pow_right (by decide) (by omega_arith))), hr, hdi, hm,
    toNat_setWidth64_8, digits_range_succ, show 64 - 56 = 8 by rfl, show b - (t + 1) + 0 = b - 1 - t by omega_arith]
  have e : (fun u => (s.mem (s.gpr .rdi + BitVec.ofNat 64 (o + (b - (t + 1) + (u + 1))))).toNat) =
      fun u => (s.mem (s.gpr .rdi + BitVec.ofNat 64 (o + (b - t + u)))).toNat := by
    funext u; rw [show b - (t + 1) + (u + 1) = b - t + u by omega_arith]
  have hA : digits 8 ((List.range t).map fun u =>
      (s.mem (s.gpr .rdi + BitVec.ofNat 64 (o + (b - t + u)))).toNat) * 2 ^ 8 < 2 ^ 56 := by
    have := Nat.mul_lt_mul_of_pos_right hacc (show 0 < 2 ^ 8 by decide)
    have h' : 2 ^ (8 * t) * 2 ^ 8 ≤ 2 ^ 56 := by
      rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega_arith)
    omega_arith
  rw [e]
  have h64 : digits 8 ((List.range t).map fun u => (s.mem (s.gpr .rdi + BitVec.ofNat 64 (o + (b - t + u)))).toNat) *
      2 ^ 8 + (s.mem (s.gpr .rdi + BitVec.ofNat 64 (o + (b - 1 - t)))).toNat < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_of_lt_of_le hA (Nat.le_of_lt_succ hv)) (by decide)
  rw [Nat.mod_eq_of_lt h64, Nat.add_comm, Nat.mul_comm]

/-- The word `ddCoef` stores, from the accumulator `a`, with `q` in `r9`. -/
def ddW (d : Nat) (a M : BitVec 64) : BitVec 32 :=
  BitVec.setWidth 32 ((BitVec.ofNat 64 ((BitVec.setWidth 64 (BitVec.setWidth 32 a &&&
    BitVec.ofNat 32 (2 ^ d - 1))).toNat * M.toNat) + BitVec.ofNat 64 (2 ^ (d - 1))) >>> d)

theorem ddW_toNat {d : Nat} (hd1 : 1 ≤ d) (hd : d ≤ 11) (a : BitVec 64) {M : BitVec 64} (hM : M.toNat = 3329) :
    (ddW d a M).toNat = (3329 * (a.toNat % 2 ^ d) + 2 ^ (d - 1)) / 2 ^ d := by
  have hp : 2 ^ d ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) hd
  have hp' : 2 ^ (d - 1) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) (by omega_arith)
  have hm : (BitVec.ofNat 32 (2 ^ d - 1)).toNat = 2 ^ d - 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have hy : (BitVec.setWidth 64 (BitVec.setWidth 32 a &&& BitVec.ofNat 32 (2 ^ d - 1))).toNat = a.toNat % 2 ^ d := by
    rw [toNat_setWidth64, BitVec.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth,
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega_arith))]
  have hyl : a.toNat % 2 ^ d < 2 ^ 11 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos d)) hp
  generalize a.toNat % 2 ^ d = y at hy hyl ⊢
  have e1 : (BitVec.ofNat 64 ((BitVec.setWidth 64 (BitVec.setWidth 32 a &&& BitVec.ofNat 32 (2 ^ d - 1))).toNat *
      M.toNat)).toNat = 3329 * y := by
    rw [BitVec.toNat_ofNat, hy, hM, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  have e2 : (BitVec.ofNat 64 (2 ^ (d - 1))).toNat = 2 ^ (d - 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have h2 : (BitVec.ofNat 64 ((BitVec.setWidth 64 (BitVec.setWidth 32 a &&& BitVec.ofNat 32 (2 ^ d - 1))).toNat *
      M.toNat) + BitVec.ofNat 64 (2 ^ (d - 1))).toNat = 3329 * y + 2 ^ (d - 1) := by
    rw [BitVec.toNat_add, e1, e2, Nat.mod_eq_of_lt (by omega_arith)]
  have h3 : (3329 * y + 2 ^ (d - 1)) / 2 ^ d < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_arith)
  rw [ddW, toNat_setWidth32_64 (by rw [shr_toNat, h2]; exact h3), shr_toNat, h2]

theorem ddCoef_ok (d j : Nat) (hd1 : 1 ≤ d) (hd : d ≤ 11) (s : State)
    (hout : InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 4) :
    WP isa (.block (ddCoef d j)) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) (ddW d (s.gpr .r10) (s.gpr .r9)) ∧
        s'.gpr .r10 = s.gpr .r10 >>> d) ∧ Keep [.rax, .rdx, .r10] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold ddCoef
  xrun [hout, show 1 ≤ d by omega_arith, show d ≤ 63 by omega_arith, ddW,
    sx_ofNat (show 2 ^ (d - 1) < 2 ^ 31 from Nat.pow_lt_pow_right (by decide) (by omega_arith))]

/-- The low `c` values of `r10`, decompressed, to `rsi + 4o`, …. -/
theorem ddVals_ok {d o c : Nat} (hd1 : 1 ≤ d) (hd : d ≤ 11) (hc : c ≤ 8) (s : State)
    (hout : ∀ j < c, InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * (o + j))) 4) :
    WP isa (.block (ddVals d o c)) s fun s' =>
      (∀ j < c, s'.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * (o + j))) 32 =
        ddW d (s.gpr .r10 >>> (d * j)) (s.gpr .r9)) ∧
      Frame [⟨s.gpr .rsi + BitVec.ofNat 64 (4 * o), 4 * c⟩] s.mem s'.mem ∧ Keep [.rax, .rdx, .r10] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.rax, .rdx, .r10] s s' ∧
    s'.gpr .r10 = s.gpr .r10 >>> (d * j) ∧ Frame [⟨s.gpr .rsi + BitVec.ofNat 64 (4 * o), 4 * c⟩] s.mem s'.mem ∧
    ∀ t < j, s'.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * (o + t))) 32 = ddW d (s.gpr .r10 >>> (d * t)) (s.gpr .r9))
    (fun j s' hj ⟨hk, hr, hf, hw⟩ => ?_) c (Nat.le_refl _) s
    ⟨Keep.refl _ _, by simp, Frame.refl _ _, fun _ h => absurd h (by omega_arith)⟩)
    fun s' ⟨hk, _, hf, hw⟩ => ⟨hw, hf, hk⟩
  have hsi : s'.gpr .rsi = s.gpr .rsi := hk.gpr (by decide)
  have h9 : s'.gpr .r9 = s.gpr .r9 := hk.gpr (by decide)
  refine WP.mono (ddCoef_ok d (o + j) hd1 hd s' (by rw [hk.2.2, hsi]; exact hout j hj))
    fun s'' ⟨⟨hm, h10⟩, hk'⟩ => ⟨(hk.trans hk').mono (by decide), ?_, ?_, fun t ht => ?_⟩
  · rw [h10, hr, ← BitVec.shiftRight_add, Nat.mul_succ]
  · rw [hm, hsi, Nat.mul_add, ← off_add']
    exact hf.writeW (List.mem_singleton_self _) _ (contains_offset' (by omega_arith) (by omega_arith))
  · rw [hm, hsi, hr, h9]
    by_cases e : t = j
    · subst e; rw [Mem.readW_writeW_self32]
    · rw [Mem.readW_writeW_sep ?_ (by decide), hw t (by omega_arith)]
      intro x h₁ h₂
      simp only [Nat.reduceDiv] at h₁ h₂
      have : t < j ∨ j < t := by omega_arith
      rcases this with h | h <;> bv_omega

end VG.Proof.MlKem.X86_64

end

end

/-!
# ML-KEM on x86-64: compression (`vg_mlkem_compress_encode`, `vg_mlkem1024_compress_encode`)

The loop over the groups is proven once, for any widths, group of `c`
coefficients and `b` bytes, multiplier and rounding constant, from what the
code of a group does (`CE.loop_ok`), given the facts it needs (`CE.GrpIn`):
a group whose code accumulates its `c` values and stores its `b` bytes
(`CE.grp_ok`), as for every width of `vg_mlkem_compress_encode`, or one in
segments (`vg_mlkem1024_compress_encode`). `vg_mlkem_compress_encode` is
proven by its three cases.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace CE

section
variable (s₀ : State)
abbrev fP : Addr := s₀.gpr .rdi
abbrev oP : Addr := s₀.gpr .rdx
abbrev F : Poly := polyAt s₀.mem (fP s₀)
end

/-- After `i` groups of `c` coefficients and `b` bytes, with the multiplier `M` in `r9`. -/
structure Inv (s₀ : State) (d c b M : Nat) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = fP s₀ + BitVec.ofNat 64 (4 * c * i)
  r8 : s.gpr .r8 = oP s₀ + BitVec.ofNat 64 (b * i)
  r9 : (s.gpr .r9).toNat = M
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨oP s₀, 32 * d⟩] s₀.mem s.mem
  done : ∀ k < b * i, s.mem (oP s₀ + BitVec.ofNat 64 k) = (compressEncode d (F s₀))[k]!

theorem tail_ok (c b : Nat) (hc : 4 * c < 2 ^ 31) (hb : b < 2 ^ 31) (s : State) :
    WP isa (.block [.alu .add .rdi (.imm (BitVec.ofNat 32 (4 * c))), .alu .add .r8 (.imm (BitVec.ofNat 32 b)),
      .alu .sub .rcx (.imm 1)]) s fun s' =>
      (s'.gpr .rdi = s.gpr .rdi + BitVec.ofNat 64 (4 * c) ∧ s'.gpr .r8 = s.gpr .r8 + BitVec.ofNat 64 b ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.mem = s.mem) ∧
      Keep [.rdi, .r8, .rcx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [sx_ofNat hc, sx_ofNat hb]

theorem lenEq {ws : List Nat} {s₀ : State} (hp : (compressEncodeWK ws).pre s₀) {d : Nat} (hdd : dArg s₀ .rsi = d) :
    (s₀.gpr .rcx).toNat = 32 * d := by rw [hp.2.2.2.2.2.2.1, hdd]

/-- What the code of group `i` needs: its coefficients readable, their
compressed values (with the multiplier in `r9` and the rounding constant
`r`), its bytes writable, apart. -/
structure GrpIn (r d c b : Nat) (F : Poly) (i : Nat) (s : State) : Prop where
  rd : ∀ j < c, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 4
  v : ∀ j < c, (ceV r d (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32) (s.gpr .r9)).toNat =
    compress d F[c * i + j]!
  wr : ∀ k < b, InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 k) 1
  dj : Region.Disjoint ⟨s.gpr .rdi, 4 * c⟩ ⟨s.gpr .r8, b⟩

/-- What the code of group `i` does: its `b` bytes of the encoding. -/
abbrev GrpOut (d b : Nat) (F : Poly) (i : Nat) (s s' : State) : Prop :=
  Written s.mem s'.mem (s.gpr .r8) b (fun k => (compressEncode d F)[b * i + k]!) ∧ Keep [.rax, .rdx, .r10] s s'

section
variable {ws : List Nat} {s₀ : State} (hp : (compressEncodeWK ws).pre s₀) {r d c b M : Nat}
  (hd11 : 1 ≤ d ∧ d ≤ 11) (hc0 : 0 < c) (hc8 : c ≤ 8) (hb : b ≤ 11) (hbN : b * (256 / c) = 32 * d)
  (hcN : c * (256 / c) = 256) (hdd : dArg s₀ .rsi = d)
  (hcomp : ∀ x : Zq, x.val * M + r < 2 ^ 30 ∧ compress d x = (x.val * M + r) / 2 ^ 19 % 2 ^ d)
include hp hd11 hc0 hc8 hb hbN hcN hdd

omit hd11 hc0 hc8 hb hbN hcN in
theorem coeff {m : Mem} (hf : Frame [⟨oP s₀, 32 * d⟩] s₀.mem m) {k : Nat} (hk : k < 256) :
    coeffAt m (fP s₀) k = coeffAt s₀.mem (fP s₀) k :=
  coeffAt_congr (bytes_frame hf (by
    have := hp.2.2.1; rw [lenEq hp hdd] at this; simpa using this) (by decide)) hk

include hcomp in
theorem step {grp : List Instr}
    (hgrp : ∀ i < 256 / c, ∀ s, GrpIn r d c b (F s₀) i s → WP isa (.block grp) s (GrpOut d b (F s₀) i s))
    {i : Nat} (hi : i < 256 / c) {s : State} (hI : Inv s₀ d c b M i s) :
    WP isa (.block (grp ++ ceTail c b)) s fun s' => Inv s₀ d c b M (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have hci : c * i + c ≤ 256 := by
    have := Nat.mul_le_mul_left c (show i + 1 ≤ 256 / c by omega_arith); rw [Nat.mul_succ] at this; omega_arith
  have hbi : b * i + b ≤ 32 * d := by
    have := Nat.mul_le_mul_left b (show i + 1 ≤ 256 / c by omega_arith); rw [Nat.mul_succ] at this; omega_arith
  have hrd : s.rd ++ s.wr = [pR (fP s₀), ⟨oP s₀, 32 * d⟩] := by
    rw [hI.rd, hI.wr, hp.1, hp.2.1, lenEq hp hdd]; rfl
  have hwr : s.wr = [⟨oP s₀, 32 * d⟩] := by rw [hI.wr, hp.2.1, lenEq hp hdd]
  have ha : ∀ j < c, s.gpr .rdi + BitVec.ofNat 64 (4 * j) = coeffAddr (fP s₀) (c * i + j) := fun j _ => by
    rw [hI.rdi, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; rw [Nat.mul_add, Nat.mul_assoc]
  have hdj : Region.Disjoint (pR (fP s₀)) ⟨oP s₀, 32 * d⟩ := by
    have := hp.2.2.1; rw [lenEq hp hdd] at this; exact this
  rw [WP.block_append_iff]
  refine WP.mono (hgrp i hi s ⟨fun j hj => ?_, fun j hj => ?_, fun k hk => ?_, ?_⟩) fun s₁ ⟨w₁, k₁⟩ => ?_
  · rw [ha j hj, hrd]; exact ⟨_, by simp, coeff_contains _ (show c * i + j < 256 by omega_arith)⟩
  · have hr : Reduced s₀.mem (fP s₀) := hp.2.2.2.2.2.2.2
    have hk : c * i + j < 256 := by omega_arith
    rw [ha j hj, ← coeffAt_eq, coeff hp hdd hI.frame hk]
    have harg := (hcomp (F s₀)[c * i + j]!).1
    rw [polyAt_val hr hk] at harg
    rw [ceV_toNat hd11.2 (by rw [hI.r9]; exact harg), hI.r9, (hcomp _).2, polyAt_val hr hk]
  · rw [hwr, hI.r8, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨_, List.mem_singleton_self _, contains_offset' (by omega_arith) (by omega_arith)⟩
  · rw [hI.rdi, hI.r8]
    exact (hdj.sub_left (sub_offset' (by rw [Nat.mul_assoc]; omega_arith) (by decide))).sub_right
      (sub_offset' (by omega_arith) (by omega_arith))
  refine WP.mono (tail_ok c b (by omega_arith) (by omega_arith) s₁) fun s₂ ⟨⟨di₂, r8₂, cx₂, z₂, m₂⟩, k₂⟩ => ⟨?_, ?_, ?_⟩
  rotate_left
  · rw [cx₂, k₁.gpr (by decide)]
  · rw [z₂, k₁.gpr (by decide)]
  have hw : Written s.mem s₂.mem (oP s₀ + BitVec.ofNat 64 (b * i)) b
      fun k => (compressEncode d (F s₀))[b * i + k]! := by
    rw [m₂, ← hI.r8]; exact w₁
  obtain ⟨hf', hd'⟩ := Written.step hI.frame hI.done hw hbi (by omega_arith)
  refine ⟨?_, ?_, ?_, ?_, ?_, hf', fun k hk => hd' k (by rw [Nat.mul_succ] at hk; omega_arith)⟩
  · rw [di₂, k₁.gpr (by decide), hI.rdi]; exact ptr_step _ i (4 * c)
  · rw [r8₂, k₁.gpr (by decide), hI.r8]; exact ptr_step _ i b
  · rw [k₂.gpr (by decide), k₁.gpr (by decide), hI.r9]
  · rw [k₂.2.1, k₁.2.1, hI.rd]
  · rw [k₂.2.2, k₁.2.2, hI.wr]

include hcomp in
/-- The loop over the groups, each `grp`, with the multiplier `M`, from a
state with `f` in `rdi` and `out` in `r8`. -/
theorem loop_ok {grp : List Instr}
    (hgrp : ∀ i < 256 / c, ∀ s, GrpIn r d c b (F s₀) i s → WP isa (.block grp) s (GrpOut d b (F s₀) i s))
    (hM : M < 2 ^ 31) {s : State} (hdi : s.gpr .rdi = fP s₀) (h8 : s.gpr .r8 = oP s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa (ceLoopW M (256 / c) (grp ++ ceTail c b)) s fun s' =>
      bytesAt s'.mem (oP s₀) (32 * d) = compressEncode d (F s₀) ∧ Frame [⟨oP s₀, 32 * d⟩] s₀.mem s'.mem := by
  refine WP.seq (WP.mono (WP.keep [.r9] (Q := fun s' => s'.gpr .r9 = BitVec.ofNat 64 M ∧ s'.mem = s.mem)
    (by xrun [sx_ofNat hM]) (by rfl)) fun s₁ ⟨⟨h9, m₁⟩, k₁⟩ => ?_)
  have hN : 0 < 256 / c ∧ 256 / c ≤ 256 := ⟨Nat.div_pos (by omega_arith) hc0, Nat.div_le_self _ _⟩
  refine WP.mono (wp_counted (N := 256 / c) (v := BitVec.ofNat 32 (256 / c))
    (by rw [BitVec.toNat_ofNat]; omega_arith) (by omega_arith) (Inv s₀ d c b M)
    (fun s₂ m₂ k₂ => ⟨?_, ?_, ?_, ?_, ?_, ?_, fun k hk => absurd hk (by omega_arith)⟩)
    fun i hi s hI => step hp hd11 hc0 hc8 hb hbN hcN hdd hcomp hgrp hi hI) fun s' hI => ⟨?_, hI.frame⟩
  · rw [k₂.gpr (by decide), k₁.gpr (by decide), hdi]; simp
  · rw [k₂.gpr (by decide), k₁.gpr (by decide), h8]; simp
  · rw [k₂.gpr (by decide), h9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  · rw [k₂.2.1, k₁.2.1, hrd]
  · rw [k₂.2.2, k₁.2.2, hwr]
  · rw [m₂, m₁, hm]; exact Frame.refl _ _
  · exact bytesAt_eq! (compressEncode_length _ _) fun k hk => hI.done k (by omega_arith)

end

/-- A group whose code accumulates its `c` values and stores its `b` bytes
(`d · c = 8 · b`). -/
theorem grp_ok {r d c b : Nat} (hr : r < 2 ^ 31) (hd11 : 1 ≤ d ∧ d ≤ 11) (hdc : d * c = 8 * b) (hb : b ≤ 7)
    (F : Poly) {i : Nat} (hci : c * i + c ≤ 256) (hbi : b * i + b ≤ 32 * d) {s : State} (h : GrpIn r d c b F i s) :
    WP isa (.block (ceAcc r d 0 c ++ ceSt 0 b)) s (GrpOut d b F i s) := by
  rw [WP.block_append_iff]
  refine WP.mono (ceAcc_ok (o := 0) (c := c) hr hd11.1 hd11.2 (by omega_arith) s
    (fun j hj => by rw [Nat.zero_add]; exact h.rd j hj) (fun j => compress d F[c * i + (0 + j)]!)
    (fun j hj => by rw [Nat.zero_add]; exact h.v j hj) (fun _ _ => compress_lt d _)) fun s₁ ⟨r₁, m₁, k₁⟩ => ?_
  refine WP.mono (ceSt_ok (k0 := 0) (nb := b) (by omega_arith) s₁ (fun k hk => by
      rw [k₁.2.2, k₁.gpr (by decide), Nat.zero_add]; exact h.wr k hk)) fun s₂ ⟨w₂, k₂⟩ =>
    ⟨?_, (k₁.trans k₂).mono (by decide)⟩
  rw [k₁.gpr (by decide), add_ofNat_zero, m₁, r₁] at w₂
  refine w₂.congr fun k hk => ?_
  rw [Spec.MlKem.compressEncode, byteEncode_group (c := c) (by omega_arith) hdc (map_toList_lt _ (compress_lt d)) hk
    (by omega_arith), take_drop_eq _ 0 (by rw [map_toList_length]; omega_arith)]
  congr 3
  apply List.map_congr_left
  intro j hj
  rw [map_toList_getD _ _ (show c * i + j < 256 by have := List.mem_range.mp hj; omega_arith), Nat.zero_add]

end CE

/-- `x - k` is zero exactly when `x = k`. -/
theorem sub_beq_zero32 (x k : BitVec 32) : (x - k == 0) = decide (x = k) := by
  by_cases h : x = k
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e; apply h; bv_omega

theorem cePrologue_ok (s₀ : State) :
    WP isa (.block [.mov32 .rsi (.reg .rsi), .mov .r8 (.reg .rdx), .alu32 .cmp .rsi (.imm 1)]) s₀ fun s =>
      (s.gpr .rsi = BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.gpr .rsi)) ∧ s.gpr .r8 = s₀.gpr .rdx ∧
        s.zf = some (BitVec.setWidth 32 (s₀.gpr .rsi) - 1 == 0) ∧ s.mem = s₀.mem) ∧ Keep [.rsi, .r8] s₀ s := by
  refine WP.keep _ ?_ (by decide)
  xrun

theorem cmp32_ok (r : Reg) (k : BitVec 32) (s : State) :
    WP isa (.block [.alu32 .cmp r (.imm k)]) s fun s' =>
      (s'.zf = some (BitVec.setWidth 32 (s.gpr r) - k == 0) ∧ s'.mem = s.mem) ∧ Keep [r] s s' := by
  refine WP.keep _ ?_ (by cases r <;> rfl)
  xrun

theorem ce_wp {s₀ : State} (hp : compressEncodeK.pre s₀) :
    WP isa Impl.MlKem.X86_64.compressEncode s₀ fun s' =>
      bytesAt s'.mem (s₀.gpr .rdx) (s₀.gpr .rcx).toNat = compressEncode (dArg s₀ .rsi) (CE.F s₀) ∧
        Frame [⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩] s₀.mem s'.mem := by
  have hd := hp.2.2.2.2.2.1
  rw [CE.lenEq hp rfl]
  unfold Impl.MlKem.X86_64.compressEncode
  refine WP.seq (WP.mono (cePrologue_ok s₀) fun s₁ ⟨⟨si₁, r8₁, z₁, m₁⟩, k₁⟩ => ?_)
  have di₁ : s₁.gpr .rdi = s₀.gpr .rdi := k₁.gpr (by decide)
  have go : ∀ {d c b : Nat}, d ∈ compressWidths → d * c = 8 * b → b ≤ 5 → 0 < c → c ≤ 8 →
      b * (256 / c) = 32 * d → c * (256 / c) = 256 → dArg s₀ .rsi = d → ∀ s : State,
      s.gpr .rdi = s₀.gpr .rdi → s.gpr .r8 = s₀.gpr .rdx → s.rd = s₀.rd → s.wr = s₀.wr → s.mem = s₀.mem →
      WP isa (ceLoop d c b) s fun s' =>
        bytesAt s'.mem (s₀.gpr .rdx) (32 * dArg s₀ .rsi) = compressEncode (dArg s₀ .rsi) (CE.F s₀) ∧
          Frame [⟨s₀.gpr .rdx, 32 * dArg s₀ .rsi⟩] s₀.mem s'.mem := by
    intro d c b hd hdc hb hc0 hc hbN hcN hdd s h1 h2 h3 h4 h5
    have hd11 : 1 ≤ d ∧ d ≤ 11 := by rcases mem_compressWidths hd with rfl | rfl | rfl <;> decide
    rw [hdd]
    exact CE.loop_ok hp hd11 hc0 hc (by omega_arith) hbN hcN hdd (M := ceMul d) (r := 262080)
      (fun x => ⟨compress_arg_lt hd x, compress_eq hd x⟩)
      (fun i hi s hs => CE.grp_ok (by decide) hd11 hdc (by omega_arith) _
        (by have := Nat.mul_le_mul_left c (show i + 1 ≤ 256 / c by omega_arith); rw [Nat.mul_succ] at this; omega_arith)
        (by have := Nat.mul_le_mul_left b (show i + 1 ≤ 256 / c by omega_arith); rw [Nat.mul_succ] at this; omega_arith) hs)
      (by rw [ceMul]; split <;> [decide; split <;> decide]) h1 h2 h3 h4 h5
  refine WP.ite (M := isa) _ (show isa.eval .e s₁ = _ from z₁) (fun h => ?_) (fun h => ?_)
  · rw [sub_beq_zero32, decide_eq_true_eq] at h
    exact go (d := 1) (c := 8) (b := 1) (by rw [← (show dArg s₀ .rsi = 1 by simp only [dArg, h]; rfl)]; exact hd)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simp only [dArg, h]; rfl) s₁ di₁ r8₁ k₁.2.1 k₁.2.2 m₁
  · rw [sub_beq_zero32, decide_eq_false_iff_not] at h
    refine WP.seq (WP.mono (cmp32_ok .rsi 4 s₁) fun s₂ ⟨⟨z₂, m₂⟩, k₂⟩ => ?_)
    rw [si₁, BitVec.setWidth_32_64_32] at z₂
    refine WP.ite (M := isa) _ (show isa.eval .e s₂ = _ from z₂) (fun h' => ?_) (fun h' => ?_)
    · rw [sub_beq_zero32, decide_eq_true_eq] at h'
      exact go (d := 4) (c := 2) (b := 1) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simp only [dArg, h']; rfl) s₂ (by rw [k₂.gpr (by decide), di₁])
        (by rw [k₂.gpr (by decide), r8₁]) (by rw [k₂.2.1, k₁.2.1]) (by rw [k₂.2.2, k₁.2.2]) (by rw [m₂, m₁])
    · rw [sub_beq_zero32, decide_eq_false_iff_not] at h'
      have h10 : dArg s₀ .rsi = 10 := by
        rcases mem_compressWidths hd with e | e | e
        · exact absurd (BitVec.eq_of_toNat_eq (e.trans rfl)) h
        · exact absurd (BitVec.eq_of_toNat_eq (e.trans rfl)) h'
        · exact e
      exact go (d := 10) (c := 4) (b := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        h10 s₂ (by rw [k₂.gpr (by decide), di₁])
        (by rw [k₂.gpr (by decide), r8₁]) (by rw [k₂.2.1, k₁.2.1]) (by rw [k₂.2.2, k₁.2.2]) (by rw [m₂, m₁])

theorem compressEncode_correct (s : State) (hs : compressEncodeK.pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.compressEncode s t s' ∧ abiPreserved s s' ∧
      compressEncodeK.post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := Impl.MlKem.X86_64.compressEncode)
    [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10] (ce_wp hs) (by decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

theorem compressEncode_ct :
    ConstantTime isa compressEncodeK.pre compressEncodeK.pub Impl.MlKem.X86_64.compressEncode :=
  VG.Taint.constantTime (A := taint) (regsLo [.rdi, .rdx, .rcx, .rsp] [.rsi])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1])
      fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact hp.2.2.2.2)
    (by taint_decide)

end VG.Proof.MlKem.X86_64
