import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Impl.MlKem.X86_64.Compress
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Spec.MlKem.Poly
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Impl.MlKem.X86_64.Sample
import VerifiedGarbage.Proof.Sha3.Scratch

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.Bytes`. -/
section

/-!
# ML-KEM on x86-64: values and bytes

* shifts left by rotating a value whose top bits are zero (`rotr_toNat`),
  logical shifts right, and the byte a `store8` stores (`b8_eq`);
* `Written m m' o c v`: `m'` is `m` with the `c` bytes at `o` replaced by
  `v 0, …, v (c - 1)`, built one byte store at a time
  (`Written.first`, `Written.snoc`), and how a loop that writes its output
  `c` bytes at a time extends what it has written (`Written.extend`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

/-! ## Values -/

/-- Rotating right by `r` a value less than `2ʳ` shifts it left by `w - r`. -/
theorem rotr_toNat {w r : Nat} (x : BitVec w) (hr : r < w) (hx : x.toNat < 2 ^ r) :
    (x.rotateRight r).toNat = x.toNat * 2 ^ (w - r) := by
  rw [BitVec.toNat_rotateRight, Nat.mod_eq_of_lt hr, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hx,
    Nat.zero_or, Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  calc x.toNat * 2 ^ (w - r) < 2 ^ r * 2 ^ (w - r) := Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos _)
    _ = 2 ^ w := by rw [← Nat.pow_add]; congr 1; omega

theorem shr_toNat {w : Nat} (x : BitVec w) (n : Nat) : (x >>> n).toNat = x.toNat / 2 ^ n := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- The byte a `store8` stores of a 32-bit value. -/
theorem b8_eq (x : BitVec 32) : BitVec.setWidth 8 (BitVec.setWidth 64 x) = BitVec.ofNat 8 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- The byte a `store8` stores of a 64-bit value. -/
theorem b8_eq64 (x : BitVec 64) : BitVec.setWidth 8 x = BitVec.ofNat 8 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

theorem toNat_setWidth64 (x : BitVec 32) : (BitVec.setWidth 64 x).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]; omega

theorem toNat_setWidth64_8 (x : BitVec 8) : (BitVec.setWidth 64 x).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]; omega

theorem toNat_setWidth32_8 (x : BitVec 8) : (BitVec.setWidth 32 x).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]; omega

theorem toNat_setWidth32_64 {x : BitVec 64} (h : x.toNat < 2 ^ 32) : (BitVec.setWidth 32 x).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]; omega

/-! ## Regions -/

theorem contains_offset' {base : Addr} {len off n : Nat} (h : off + n ≤ len) (hl : len < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := by
  simp only [Region.Contains]
  rw [show base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  exact h

theorem sub_offset' {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (hl : len' < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := by
  intro a ha
  simp only [Region.Contains] at *
  have e : a - base = (a - (base + BitVec.ofNat 64 off)) + BitVec.ofNat 64 off := by bv_omega
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- Two ranges at offsets of the same pointer, one below the other. -/
theorem off_disj {p : Addr} {a n b m : Nat} (h : a + n ≤ b) (hb : b + m < 2 ^ 64) :
    Region.Disjoint ⟨p + BitVec.ofNat 64 a, n⟩ ⟨p + BitVec.ofNat 64 b, m⟩ := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  bv_omega

/-! ## Bytes written -/

/-- `m'` is `m` with the `c` bytes at `o` replaced by `v 0, …, v (c - 1)`. -/
def Written (m m' : Mem) (o : Addr) (c : Nat) (v : Nat → Byte) : Prop :=
  ∀ x, m' x = if (x - o).toNat < c then v (x - o).toNat else m x

theorem Written.nil (m : Mem) (o : Addr) (v : Nat → Byte) : VG.Proof.MlKem.X86_64.Written m m o 0 v := fun x => by
  rw [ifn (Nat.not_lt_zero _)]

theorem Written.first (m : Mem) (o : Addr) (b : Byte) : VG.Proof.MlKem.X86_64.Written m (m.writeW o b) o 1 fun _ => b := by
  intro x
  rw [VG.WriteBytes.writeW8_apply]
  by_cases h : x = o
  · subst h; simp
  · have : (x - o).toNat ≠ 0 := fun e => h (by bv_omega)
    simp only [h, ↓reduceIte]
    rw [ifn (by omega)]

theorem Written.snoc {m m' : Mem} {o : Addr} {c : Nat} {v : Nat → Byte} (h : VG.Proof.MlKem.X86_64.Written m m' o c v)
    (hc : c + 1 < 2 ^ 64) (b : Byte) :
    VG.Proof.MlKem.X86_64.Written m (m'.writeW (o + BitVec.ofNat 64 c) b) o (c + 1) fun j => if j = c then b else v j := by
  intro x
  rw [VG.WriteBytes.writeW8_apply, h x]
  by_cases hx : x = o + BitVec.ofNat 64 c
  · subst hx
    have : (o + BitVec.ofNat 64 c - o).toNat = c := by
      rw [show o + BitVec.ofNat 64 c - o = BitVec.ofNat 64 c by bv_omega, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
    simp [this]
  · have : (x - o).toNat ≠ c := fun e => hx (by bv_omega)
    simp only [hx, ↓reduceIte, this]
    by_cases hl : (x - o).toNat < c
    · rw [ifp hl, ifp (by omega)]
    · rw [ifn hl, ifn (by omega)]

/-- Writing `c` bytes within the region `R`. -/
theorem Written.frame {m m' : Mem} {o : Addr} {c : Nat} {v : Nat → Byte} (h : VG.Proof.MlKem.X86_64.Written m m' o c v)
    {R : Region} (hR : R.Contains o c) : Frame [R] m m' := by
  intro x hx
  rw [h x]
  split
  · rename_i hlt
    exact absurd (hR.byte hlt) (hx R (List.mem_singleton_self _))
  · rfl

theorem Written.congr {m m' : Mem} {o : Addr} {c : Nat} {v v' : Nat → Byte} (h : VG.Proof.MlKem.X86_64.Written m m' o c v)
    (hv : ∀ j < c, v j = v' j) : VG.Proof.MlKem.X86_64.Written m m' o c v' := by
  intro x
  rw [h x]
  split
  · rename_i hl; exact hv _ hl
  · rfl

/-- A loop that has written the first `a` bytes of its output, `val 0, …,
val (a - 1)`, then writes the next `c`. -/
theorem Written.extend {m m' : Mem} {out : Addr} {a c : Nat} {val : Nat → Byte}
    (hd : ∀ k < a, m (out + BitVec.ofNat 64 k) = val k)
    (hw : VG.Proof.MlKem.X86_64.Written m m' (out + BitVec.ofNat 64 a) c fun j => val (a + j)) (hlen : a + c < 2 ^ 64) :
    ∀ k < a + c, m' (out + BitVec.ofNat 64 k) = val k := by
  intro k hk
  rw [hw]
  by_cases h : k < a
  · have : ¬ (out + BitVec.ofNat 64 k - (out + BitVec.ofNat 64 a)).toNat < c := by
      rw [show out + BitVec.ofNat 64 k - (out + BitVec.ofNat 64 a) =
        BitVec.ofNat 64 k - BitVec.ofNat 64 a by bv_omega]
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega
    rw [ifn this, hd k h]
  · have e : (out + BitVec.ofNat 64 k - (out + BitVec.ofNat 64 a)).toNat = k - a := by
      rw [show out + BitVec.ofNat 64 k - (out + BitVec.ofNat 64 a) = BitVec.ofNat 64 (k - a) by
        rw [show k = a + (k - a) by omega, BitVec.ofNat_add]; bv_omega]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [e, ifp (by omega)]
    exact congrArg val (by omega)

/-- The loop's output so far, and the frame, one step further. -/
theorem Written.step {m₀ m m' : Mem} {out : Addr} {a c len : Nat} {val : Nat → Byte}
    (hf : Frame [⟨out, len⟩] m₀ m) (hd : ∀ k < a, m (out + BitVec.ofNat 64 k) = val k)
    (hw : VG.Proof.MlKem.X86_64.Written m m' (out + BitVec.ofNat 64 a) c fun j => val (a + j)) (hac : a + c ≤ len)
    (hlen : len < 2 ^ 64) :
    Frame [⟨out, len⟩] m₀ m' ∧ ∀ k < a + c, m' (out + BitVec.ofNat 64 k) = val k := by
  refine ⟨hf.trans (hw.frame ?_), Written.extend hd hw (by omega)⟩
  simp only [Region.Contains]
  rw [show out + BitVec.ofNat 64 a - out = BitVec.ofNat 64 a by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  exact hac

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.Groups`. -/
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

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

/-! ## Chunks of a number -/

/-- Bits `s + p … s + p + m - 1` of the number whose digits are `c` digits
of `L` from digit `o`: those of the number of `L` from bit `w·o + s + p`. -/
theorem chunk_eq {w : Nat} {L : List Nat} (hL : ∀ a ∈ L, a < 2 ^ w) (o c s p m : Nat) (hp : s + p + m ≤ w * c) :
    digits w ((L.drop o).take c) / 2 ^ s / 2 ^ p % 2 ^ m = digits w L / 2 ^ (w * o + s + p) % 2 ^ m := by
  have hd := digits_div hL o
  have hm := digits_mod (L := L.drop o) (fun a ha => hL a (List.mem_of_mem_drop ha)) c
  rw [← hm, Nat.div_div_eq_div_mul, ← Nat.pow_add, mod_pow_div_mod _ (show s + p + m ≤ w * c by omega), ← hd,
    Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_assoc]

/-! ## Bytes written in two parts -/

theorem off_add' (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem Written.append {m m₁ m₂ : Mem} {o : Addr} {a c : Nat} {v₁ v₂ : Nat → Byte} (h₁ : VG.Proof.MlKem.X86_64.Written m m₁ o a v₁)
    (h₂ : VG.Proof.MlKem.X86_64.Written m₁ m₂ (o + BitVec.ofNat 64 a) c v₂) (hac : a + c < 2 ^ 64) :
    VG.Proof.MlKem.X86_64.Written m m₂ o (a + c) fun j => if j < a then v₁ j else v₂ (j - a) := by
  intro x
  rw [h₂ x, h₁ x]
  have e : (x - (o + BitVec.ofNat 64 a)) = (x - o) - BitVec.ofNat 64 a := by bv_omega
  have hA : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat]; omega
  generalize x - o = y at e ⊢
  rw [e]
  by_cases hx : y.toNat < a
  · have : ¬ (y - BitVec.ofNat 64 a).toNat < c := by
      have := y.isLt
      rw [BitVec.toNat_sub, hA]
      rw [show 2 ^ 64 - a + y.toNat = 2 ^ 64 - (a - y.toNat) by omega, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [ifn this, ifp hx, ifp (show y.toNat < a + c by omega)]
    dsimp only
    rw [ifp hx]
  · have e2 : (y - BitVec.ofNat 64 a).toNat = y.toNat - a := by
      have := y.isLt
      rw [BitVec.toNat_sub, hA, show 2 ^ 64 - a + y.toNat = 2 ^ 64 + (y.toNat - a) by omega, Nat.add_mod_left,
        Nat.mod_eq_of_lt (by omega)]
    rw [e2, ifn hx]
    by_cases hc : y.toNat - a < c
    · rw [ifp hc, ifp (show y.toNat < a + c by omega)]
      dsimp only
      rw [ifn hx]
    · rw [ifn hc, ifn (by omega)]

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
    (VG.Proof.MlKem.X86_64.ceV r d a M).toNat = (a.toNat * M.toNat + r) / 2 ^ 19 % 2 ^ d := by
  have hp : 2 ^ d ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) hd
  have hm : (BitVec.ofNat 32 (2 ^ d - 1)).toNat = 2 ^ d - 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 : (BitVec.ofNat 64 ((BitVec.setWidth 64 a).toNat * M.toNat)).toNat = a.toNat * M.toNat := by
    rw [BitVec.toNat_ofNat, VG.Proof.MlKem.X86_64.toNat_setWidth64, Nat.mod_eq_of_lt (by omega)]
  have h2 : (BitVec.ofNat 64 ((BitVec.setWidth 64 a).toNat * M.toNat) + BitVec.ofNat 64 r).toNat =
      a.toNat * M.toNat + r := by
    rw [BitVec.toNat_add, h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := r) (by omega)]; omega
  have h3 : ((BitVec.ofNat 64 ((BitVec.setWidth 64 a).toNat * M.toNat) + BitVec.ofNat 64 r) >>> 19).toNat =
      (a.toNat * M.toNat + r) / 2 ^ 19 := by rw [VG.Proof.MlKem.X86_64.shr_toNat, h2]
  rw [VG.Proof.MlKem.X86_64.ceV, VG.Proof.MlKem.X86_64.toNat_setWidth64, BitVec.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod,
    VG.Proof.MlKem.X86_64.toNat_setWidth32_64 (by rw [h3]; omega), h3]

theorem ceCoef_ok (r d j : Nat) (hr : r < 2 ^ 31) (hd1 : 1 ≤ d) (hd : d ≤ 11) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 4) :
    WP isa (.block (ceCoef r d j)) s fun s' =>
      (s'.gpr .r10 = (s.gpr .r10).rotateRight (64 - d) +
          VG.Proof.MlKem.X86_64.ceV r d (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32) (s.gpr .r9) ∧
        s'.mem = s.mem) ∧ Keep [.rax, .rdx, .r10] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold ceCoef
  xrun [hin, show 1 ≤ 64 - d by omega, show 64 - d ≤ 63 by omega, VG.Proof.MlKem.X86_64.ceV, sx_ofNat hr]

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
    (hV : ∀ j < c, (VG.Proof.MlKem.X86_64.ceV r d (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * (o + j))) 32) (s.gpr .r9)).toNat = V j)
    (hVlt : ∀ j < c, V j < 2 ^ d) :
    WP isa (.block (ceAcc r d o c)) s fun s' =>
      (s'.gpr .r10).toNat = digits d ((List.range c).map V) ∧ s'.mem = s.mem ∧
        Keep [.rax, .rdx, .r10] s s' := by
  unfold ceAcc
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.r10zero_ok s) fun s₀ ⟨⟨h0, hm0⟩, k0⟩ => ?_
  have hdi0 : s₀.gpr .rdi = s.gpr .rdi := k0.gpr (by decide)
  have h90 : s₀.gpr .r9 = s.gpr .r9 := k0.gpr (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun t s' => Keep [.rax, .rdx, .r10] s₀ s' ∧ s'.mem = s.mem ∧
    (s'.gpr .r10).toNat = digits d ((List.range t).map fun u => V (c - t + u)))
    (fun t s' ht ⟨hk, hm, hr⟩ => ?_) c (Nat.le_refl _) s₀ ⟨Keep.refl _ _, hm0, by rw [h0]; rfl⟩)
    fun s' ⟨hk, hm, hr⟩ => ⟨by rw [hr]; simp, hm, (k0.trans hk).mono (by decide)⟩
  have hdi : s'.gpr .rdi = s.gpr .rdi := by rw [hk.gpr (by decide), hdi0]
  have h9 : s'.gpr .r9 = s.gpr .r9 := by rw [hk.gpr (by decide), h90]
  refine WP.mono (VG.Proof.MlKem.X86_64.ceCoef_ok r d (o + (c - 1 - t)) hrr hd1 hd s' (by
      rw [hk.2.1, hk.2.2, k0.2.1, k0.2.2, hdi]; exact hin _ (by omega)))
    fun s'' ⟨⟨h10, hm'⟩, hk'⟩ => ⟨(hk.trans hk').mono (by decide), hm'.trans hm, ?_⟩
  have hdt : d * t + d ≤ 60 := by
    have := Nat.mul_le_mul_left d (show t + 1 ≤ c by omega); rw [Nat.mul_succ] at this; omega
  have hacc : digits d ((List.range t).map fun u => V (c - t + u)) < 2 ^ (d * t) :=
    VG.Proof.MlKem.X86_64.digits_map_lt fun u hu => hVlt _ (by omega)
  have hlt : 2 ^ (d * t) * 2 ^ d ≤ 2 ^ 60 := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) hdt
  have hv := hVlt (c - 1 - t) (by omega)
  have hA : digits d ((List.range t).map fun u => V (c - t + u)) * 2 ^ d < 2 ^ 60 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hacc (Nat.two_pow_pos d)) hlt
  have hpd : 2 ^ d ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) hd
  rw [h10, BitVec.toNat_add, VG.Proof.MlKem.X86_64.rotr_toNat _ (by omega) (by
      rw [hr]; exact Nat.lt_of_lt_of_le hacc (Nat.pow_le_pow_right (by decide) (by omega))),
    hr, hdi, hm, h9, hV _ (by omega), VG.Proof.MlKem.X86_64.digits_range_succ, show 64 - (64 - d) = d by omega,
    show c - (t + 1) + 0 = c - 1 - t by omega]
  have e : (fun u => V (c - (t + 1) + (u + 1))) = fun u => V (c - t + u) := by
    funext u; congr 1; omega
  rw [e, Nat.mod_eq_of_lt (by omega), Nat.add_comm, Nat.mul_comm]

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
      VG.Proof.MlKem.X86_64.Written s.mem s'.mem (s.gpr .r8 + BitVec.ofNat 64 k0) nb
          (fun k => BitVec.ofNat 8 ((s.gpr .r10).toNat / 2 ^ (8 * k))) ∧
        Keep [.r10] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun k s' => Keep [.r10] s s' ∧
    (s'.gpr .r10).toNat = (s.gpr .r10).toNat / 2 ^ (8 * k) ∧
    VG.Proof.MlKem.X86_64.Written s.mem s'.mem (s.gpr .r8 + BitVec.ofNat 64 k0) k (fun t => BitVec.ofNat 8 ((s.gpr .r10).toNat / 2 ^ (8 * t))))
    (fun k s' hk ⟨hkp, hr, hw⟩ => ?_) nb (Nat.le_refl _) s ⟨Keep.refl _ _, by simp, Written.nil _ _ _⟩)
    fun s' ⟨hkp, _, hw⟩ => ⟨hw, hkp⟩
  have h8 : s'.gpr .r8 = s.gpr .r8 := hkp.gpr (by decide)
  refine WP.mono (VG.Proof.MlKem.X86_64.ceStore_ok (k0 + k) s' (by rw [hkp.2.2, h8]; exact hout k hk))
    fun s'' ⟨⟨hm, h10⟩, hk'⟩ => ⟨(hkp.trans hk').mono (by decide), ?_, ?_⟩
  · rw [h10, VG.Proof.MlKem.X86_64.shr_toNat, hr, Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ]
  · rw [hm, h8, ← VG.Proof.MlKem.X86_64.off_add']
    refine (hw.snoc (by omega) _).congr fun t ht => ?_
    by_cases e : t = k
    · subst e; rw [ifp rfl, VG.Proof.MlKem.X86_64.b8_eq64, hr]
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
  refine WP.mono (VG.Proof.MlKem.X86_64.r10zero_ok s) fun s₀ ⟨⟨h0, hm0⟩, k0⟩ => ?_
  have hdi0 : s₀.gpr .rdi = s.gpr .rdi := k0.gpr (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun t s' => Keep [.rax, .r10] s₀ s' ∧ s'.mem = s.mem ∧
    (s'.gpr .r10).toNat = digits 8 ((List.range t).map fun u =>
      (s.mem (s.gpr .rdi + BitVec.ofNat 64 (o + (b - t + u)))).toNat))
    (fun t s' ht ⟨hk, hm, hr⟩ => ?_) b (Nat.le_refl _) s₀ ⟨Keep.refl _ _, hm0, by rw [h0]; rfl⟩)
    fun s' ⟨hk, hm, hr⟩ => ⟨by rw [hr]; simp, hm, (k0.trans hk).mono (by decide)⟩
  have hdi : s'.gpr .rdi = s.gpr .rdi := by rw [hk.gpr (by decide), hdi0]
  refine WP.mono (VG.Proof.MlKem.X86_64.ddByte_ok (o + (b - 1 - t)) s' (by
      rw [hk.2.1, hk.2.2, k0.2.1, k0.2.2, hdi]; exact hin _ (by omega)))
    fun s'' ⟨⟨h10, hm'⟩, hk'⟩ => ⟨(hk.trans hk').mono (by decide), hm'.trans hm, ?_⟩
  have hacc : digits 8 ((List.range t).map fun u =>
      (s.mem (s.gpr .rdi + BitVec.ofNat 64 (o + (b - t + u)))).toNat) < 2 ^ (8 * t) :=
    VG.Proof.MlKem.X86_64.digits_map_lt fun u _ => BitVec.isLt _
  have hv := (s.mem (s.gpr .rdi + BitVec.ofNat 64 (o + (b - 1 - t)))).isLt
  rw [h10, BitVec.toNat_add, VG.Proof.MlKem.X86_64.rotr_toNat _ (by decide) (by
      rw [hr]; exact Nat.lt_of_lt_of_le hacc (Nat.pow_le_pow_right (by decide) (by omega))), hr, hdi, hm,
    VG.Proof.MlKem.X86_64.toNat_setWidth64_8, VG.Proof.MlKem.X86_64.digits_range_succ, show 64 - 56 = 8 by rfl, show b - (t + 1) + 0 = b - 1 - t by omega]
  have e : (fun u => (s.mem (s.gpr .rdi + BitVec.ofNat 64 (o + (b - (t + 1) + (u + 1))))).toNat) =
      fun u => (s.mem (s.gpr .rdi + BitVec.ofNat 64 (o + (b - t + u)))).toNat := by
    funext u; rw [show b - (t + 1) + (u + 1) = b - t + u by omega]
  have hA : digits 8 ((List.range t).map fun u =>
      (s.mem (s.gpr .rdi + BitVec.ofNat 64 (o + (b - t + u)))).toNat) * 2 ^ 8 < 2 ^ 56 := by
    have := Nat.mul_lt_mul_of_pos_right hacc (show 0 < 2 ^ 8 by decide)
    have h' : 2 ^ (8 * t) * 2 ^ 8 ≤ 2 ^ 56 := by
      rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
    omega
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
    (VG.Proof.MlKem.X86_64.ddW d a M).toNat = (3329 * (a.toNat % 2 ^ d) + 2 ^ (d - 1)) / 2 ^ d := by
  have hp : 2 ^ d ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) hd
  have hp' : 2 ^ (d - 1) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) (by omega)
  have hm : (BitVec.ofNat 32 (2 ^ d - 1)).toNat = 2 ^ d - 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hy : (BitVec.setWidth 64 (BitVec.setWidth 32 a &&& BitVec.ofNat 32 (2 ^ d - 1))).toNat = a.toNat % 2 ^ d := by
    rw [VG.Proof.MlKem.X86_64.toNat_setWidth64, BitVec.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth,
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  have hyl : a.toNat % 2 ^ d < 2 ^ 11 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos d)) hp
  generalize a.toNat % 2 ^ d = y at hy hyl ⊢
  have e1 : (BitVec.ofNat 64 ((BitVec.setWidth 64 (BitVec.setWidth 32 a &&& BitVec.ofNat 32 (2 ^ d - 1))).toNat *
      M.toNat)).toNat = 3329 * y := by
    rw [BitVec.toNat_ofNat, hy, hM, Nat.mod_eq_of_lt (by omega)]; omega
  have e2 : (BitVec.ofNat 64 (2 ^ (d - 1))).toNat = 2 ^ (d - 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2 : (BitVec.ofNat 64 ((BitVec.setWidth 64 (BitVec.setWidth 32 a &&& BitVec.ofNat 32 (2 ^ d - 1))).toNat *
      M.toNat) + BitVec.ofNat 64 (2 ^ (d - 1))).toNat = 3329 * y + 2 ^ (d - 1) := by
    rw [BitVec.toNat_add, e1, e2, Nat.mod_eq_of_lt (by omega)]
  have h3 : (3329 * y + 2 ^ (d - 1)) / 2 ^ d < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  rw [VG.Proof.MlKem.X86_64.ddW, VG.Proof.MlKem.X86_64.toNat_setWidth32_64 (by rw [VG.Proof.MlKem.X86_64.shr_toNat, h2]; exact h3), VG.Proof.MlKem.X86_64.shr_toNat, h2]

theorem ddCoef_ok (d j : Nat) (hd1 : 1 ≤ d) (hd : d ≤ 11) (s : State)
    (hout : InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 4) :
    WP isa (.block (ddCoef d j)) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) (VG.Proof.MlKem.X86_64.ddW d (s.gpr .r10) (s.gpr .r9)) ∧
        s'.gpr .r10 = s.gpr .r10 >>> d) ∧ Keep [.rax, .rdx, .r10] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold ddCoef
  xrun [hout, show 1 ≤ d by omega, show d ≤ 63 by omega, VG.Proof.MlKem.X86_64.ddW,
    sx_ofNat (show 2 ^ (d - 1) < 2 ^ 31 from Nat.pow_lt_pow_right (by decide) (by omega))]

/-- The low `c` values of `r10`, decompressed, to `rsi + 4o`, …. -/
theorem ddVals_ok {d o c : Nat} (hd1 : 1 ≤ d) (hd : d ≤ 11) (hc : c ≤ 8) (s : State)
    (hout : ∀ j < c, InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * (o + j))) 4) :
    WP isa (.block (ddVals d o c)) s fun s' =>
      (∀ j < c, s'.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * (o + j))) 32 =
        VG.Proof.MlKem.X86_64.ddW d (s.gpr .r10 >>> (d * j)) (s.gpr .r9)) ∧
      Frame [⟨s.gpr .rsi + BitVec.ofNat 64 (4 * o), 4 * c⟩] s.mem s'.mem ∧ Keep [.rax, .rdx, .r10] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.rax, .rdx, .r10] s s' ∧
    s'.gpr .r10 = s.gpr .r10 >>> (d * j) ∧ Frame [⟨s.gpr .rsi + BitVec.ofNat 64 (4 * o), 4 * c⟩] s.mem s'.mem ∧
    ∀ t < j, s'.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * (o + t))) 32 = VG.Proof.MlKem.X86_64.ddW d (s.gpr .r10 >>> (d * t)) (s.gpr .r9))
    (fun j s' hj ⟨hk, hr, hf, hw⟩ => ?_) c (Nat.le_refl _) s
    ⟨Keep.refl _ _, by simp, Frame.refl _ _, fun _ h => absurd h (by omega)⟩)
    fun s' ⟨hk, _, hf, hw⟩ => ⟨hw, hf, hk⟩
  have hsi : s'.gpr .rsi = s.gpr .rsi := hk.gpr (by decide)
  have h9 : s'.gpr .r9 = s.gpr .r9 := hk.gpr (by decide)
  refine WP.mono (VG.Proof.MlKem.X86_64.ddCoef_ok d (o + j) hd1 hd s' (by rw [hk.2.2, hsi]; exact hout j hj))
    fun s'' ⟨⟨hm, h10⟩, hk'⟩ => ⟨(hk.trans hk').mono (by decide), ?_, ?_, fun t ht => ?_⟩
  · rw [h10, hr, ← BitVec.shiftRight_add, Nat.mul_succ]
  · rw [hm, hsi, Nat.mul_add, ← VG.Proof.MlKem.X86_64.off_add']
    exact hf.writeW (List.mem_singleton_self _) _ (VG.Proof.MlKem.X86_64.contains_offset' (by omega) (by omega))
  · rw [hm, hsi, hr, h9]
    by_cases e : t = j
    · subst e; rw [Mem.readW_writeW_self32]
    · rw [Mem.readW_writeW_sep ?_ (by decide), hw t (by omega)]
      intro x h₁ h₂
      simp only [Nat.reduceDiv] at h₁ h₂
      have : t < j ∨ j < t := by omega
      rcases this with h | h <;> bv_omega

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.Contracts`. -/
section

/-!
# ML-KEM on x86-64: the contracts the proofs are written against

For each function, a contract with the facts of its shared contract
(`Spec/MlKem/Poly.lean`, `Spec/MlKem/Contract.lean`) spelled out for x86-64:
the arguments in their registers, the permitted regions, their disjointness,
and the postcondition. The proofs are written against these, and callers use
them (`WP.call`); `Verified.of_correct` moves a proof to the shared contract,
which implies it (`sig_implies`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64
open VG.Spec.MlKem

/-- The return address. -/
abbrev retR (s : State) : Region := ⟨s.gpr .rsp, 8⟩

/-- A polynomial, at `p`. -/
abbrev pR (p : Addr) : Region := ⟨p, 1024⟩

/-- `vg_mlkem_add(f = rdi, g = rsi)` and `vg_mlkem_sub(f = rdi, g = rsi)`:
`f` becomes `t f g`. -/
def accK (t : Poly → Poly → Poly) : Contract isa where
  pre s :=
    s.rd = [VG.Proof.MlKem.X86_64.pR (s.gpr .rsi)] ∧ s.wr = [VG.Proof.MlKem.X86_64.pR (s.gpr .rdi)] ∧
    (VG.Proof.MlKem.X86_64.pR (s.gpr .rdi)).Disjoint (VG.Proof.MlKem.X86_64.pR (s.gpr .rsi)) ∧ (VG.Proof.MlKem.X86_64.retR s).Disjoint (VG.Proof.MlKem.X86_64.pR (s.gpr .rdi)) ∧
    (VG.Proof.MlKem.X86_64.retR s).Disjoint (VG.Proof.MlKem.X86_64.pR (s.gpr .rsi)) ∧ Reduced s.mem (s.gpr .rdi) ∧ Reduced s.mem (s.gpr .rsi)
  post s s' := PolyIs s'.mem (s.gpr .rdi) (t (polyAt s.mem (s.gpr .rdi)) (polyAt s.mem (s.gpr .rsi)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_mlkem_encode12(f = rdi, out = rsi)`. -/
def encode12K : Contract isa where
  pre s :=
    s.rd = [VG.Proof.MlKem.X86_64.pR (s.gpr .rdi)] ∧ s.wr = [⟨s.gpr .rsi, 384⟩] ∧
    (VG.Proof.MlKem.X86_64.pR (s.gpr .rdi)).Disjoint ⟨s.gpr .rsi, 384⟩ ∧ (VG.Proof.MlKem.X86_64.retR s).Disjoint (VG.Proof.MlKem.X86_64.pR (s.gpr .rdi)) ∧
    (VG.Proof.MlKem.X86_64.retR s).Disjoint ⟨s.gpr .rsi, 384⟩ ∧ Reduced s.mem (s.gpr .rdi)
  post s s' := Spec.Sha3.bytesAt s'.mem (s.gpr .rsi) 384 = encode12 (polyAt s.mem (s.gpr .rdi))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_mlkem_decode12(b = rdi, f = rsi)`. -/
def decode12K : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 384⟩] ∧ s.wr = [VG.Proof.MlKem.X86_64.pR (s.gpr .rsi)] ∧
    Region.Disjoint ⟨s.gpr .rdi, 384⟩ (VG.Proof.MlKem.X86_64.pR (s.gpr .rsi)) ∧ (VG.Proof.MlKem.X86_64.retR s).Disjoint ⟨s.gpr .rdi, 384⟩ ∧
    (VG.Proof.MlKem.X86_64.retR s).Disjoint (VG.Proof.MlKem.X86_64.pR (s.gpr .rsi))
  post s s' := PolyIs s'.mem (s.gpr .rsi) (decode12 (Spec.Sha3.bytesAt s.mem (s.gpr .rdi) 384))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_mlkem_cbd2(b = rdi, f = rsi)`. -/
def cbd2K : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 128⟩] ∧ s.wr = [VG.Proof.MlKem.X86_64.pR (s.gpr .rsi)] ∧
    Region.Disjoint ⟨s.gpr .rdi, 128⟩ (VG.Proof.MlKem.X86_64.pR (s.gpr .rsi)) ∧ (VG.Proof.MlKem.X86_64.retR s).Disjoint ⟨s.gpr .rdi, 128⟩ ∧
    (VG.Proof.MlKem.X86_64.retR s).Disjoint (VG.Proof.MlKem.X86_64.pR (s.gpr .rsi))
  post s s' := PolyIs s'.mem (s.gpr .rsi) (samplePolyCBD 2 (Spec.Sha3.bytesAt s.mem (s.gpr .rdi) 128))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- The width `d`, a `u32` argument in `r`. -/
abbrev dArg (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-- `vg_mlkem_compress_encode(f = rdi, d = esi, out = rdx, len = rcx)`, or
another compression of the same signature for the widths `ws`
(`vg_mlkem1024_compress_encode`). -/
def compressEncodeWK (ws : List Nat) : Contract isa where
  pre s :=
    s.rd = [VG.Proof.MlKem.X86_64.pR (s.gpr .rdi)] ∧ s.wr = [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] ∧
    (VG.Proof.MlKem.X86_64.pR (s.gpr .rdi)).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ ∧ (VG.Proof.MlKem.X86_64.retR s).Disjoint (VG.Proof.MlKem.X86_64.pR (s.gpr .rdi)) ∧
    (VG.Proof.MlKem.X86_64.retR s).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ ∧ VG.Proof.MlKem.X86_64.dArg s .rsi ∈ ws ∧
    (s.gpr .rcx).toNat = 32 * VG.Proof.MlKem.X86_64.dArg s .rsi ∧ Reduced s.mem (s.gpr .rdi)
  post s s' := Spec.Sha3.bytesAt s'.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
    VG.Spec.MlKem.compressEncode (VG.Proof.MlKem.X86_64.dArg s .rsi) (polyAt s.mem (s.gpr .rdi))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ (s₁.gpr .rsi).setWidth 32 = (s₂.gpr .rsi).setWidth 32

abbrev compressEncodeK : Contract isa := VG.Proof.MlKem.X86_64.compressEncodeWK compressWidths

/-- `vg_mlkem_decode_decompress(b = rdi, len = rsi, d = edx, f = rcx)`, or
another decompression of the same signature for the widths `ws`
(`vg_mlkem1024_decode_decompress`). -/
def decodeDecompressWK (ws : List Nat) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩] ∧ s.wr = [VG.Proof.MlKem.X86_64.pR (s.gpr .rcx)] ∧
    Region.Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ (VG.Proof.MlKem.X86_64.pR (s.gpr .rcx)) ∧
    (VG.Proof.MlKem.X86_64.retR s).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ ∧ (VG.Proof.MlKem.X86_64.retR s).Disjoint (VG.Proof.MlKem.X86_64.pR (s.gpr .rcx)) ∧
    VG.Proof.MlKem.X86_64.dArg s .rdx ∈ ws ∧ (s.gpr .rsi).toNat = 32 * VG.Proof.MlKem.X86_64.dArg s .rdx
  post s s' := PolyIs s'.mem (s.gpr .rcx)
    (VG.Spec.MlKem.decodeDecompress (VG.Proof.MlKem.X86_64.dArg s .rdx) (Spec.Sha3.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32

abbrev decodeDecompressK : Contract isa := VG.Proof.MlKem.X86_64.decodeDecompressWK compressWidths

/-! ## Constant time -/

/-- The taint in which the registers `rs` are public, and the low halves of
`los` (public 32-bit arguments). -/
def regsLo (rs los : List Reg) : X86_64.Taint.T :=
  { regs := RegSet.ofList rs, flags := false, lo := RegSet.ofList los }

theorem agree_regsLo {rs los : List Reg} {s₁ s₂ : State} (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hl : ∀ r ∈ los, (s₁.gpr r).setWidth 32 = (s₂.gpr r).setWidth 32) :
    X86_64.Taint.Agree (VG.Proof.MlKem.X86_64.regsLo rs los) s₁ s₂ where
  rf := ⟨fun r hr => h r (RegSet.mem_ofList.mp hr), fun h => by cases h⟩
  wr h := absurd rfl h
  wf₁ := ⟨fun h => absurd rfl h, fun _ h => by cases h⟩
  wf₂ := ⟨fun h => absurd rfl h, fun _ h => by cases h⟩
  ok _ h := by cases h
  slots _ h := by cases h
  lo r hr := hl r (RegSet.mem_ofList.mp hr)

/-! ## Satisfiability -/

theorem read_zero (a : Addr) : ∀ n, Mem.read (fun _ => 0) a n = 0
  | 0 => rfl
  | n + 1 => by
    rw [Mem.read, VG.Proof.MlKem.X86_64.read_zero (a + 1) n]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_append]
    have (w : Nat) : (0 : BitVec w).toNat = 0 := BitVec.toNat_zero
    rw [this, this, this]
    rfl

/-- In memory of zeros, every polynomial is reduced. -/
theorem reduced_zero (p : Addr) : Reduced (fun _ => 0) p := fun _ _ => by
  simp only [coeffAt, Mem.readW, VG.Proof.MlKem.X86_64.read_zero]
  decide

/-- `sig_implies`, whose satisfiability witness may need `Reduced` of the
memory of zeros. -/
syntax "mlkem_implies " "[" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " using " term : tactic
macro_rules
  | `(tactic| mlkem_implies [$ls,*] [$ws,*] using $w) => `(tactic| exact
      { pre := by sig_implies_pre [$ls,*]
        post := by sig_implies_post [$ls,*]
        pub := by sig_implies_pub [$ls,*]
        sat := by
          refine ⟨$w, ?_⟩
          sig_pre [$ls,*]
          and_intros
          all_goals first
            | rfl
            | decide
            | exact Region.disjoint_of_sep (by decide)
            | exact reduced_zero _
            | (intro a h₁ h₂
               set_option linter.unusedSimpArgs false in
               simp only [Region.Contains, $ws,*] at h₁ h₂
               bv_omega) })

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode`. -/
section

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

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem ceMul_eq : ceMul = compressMul := rfl

namespace CE

section
variable (s₀ : State)
abbrev fP : Addr := s₀.gpr .rdi
abbrev oP : Addr := s₀.gpr .rdx
abbrev F : Poly := polyAt s₀.mem (VG.Proof.MlKem.X86_64.CE.fP s₀)
end

/-- After `i` groups of `c` coefficients and `b` bytes, with the multiplier `M` in `r9`. -/
structure Inv (s₀ : State) (d c b M : Nat) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = VG.Proof.MlKem.X86_64.CE.fP s₀ + BitVec.ofNat 64 (4 * c * i)
  r8 : s.gpr .r8 = VG.Proof.MlKem.X86_64.CE.oP s₀ + BitVec.ofNat 64 (b * i)
  r9 : (s.gpr .r9).toNat = M
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨VG.Proof.MlKem.X86_64.CE.oP s₀, 32 * d⟩] s₀.mem s.mem
  done : ∀ k < b * i, s.mem (VG.Proof.MlKem.X86_64.CE.oP s₀ + BitVec.ofNat 64 k) = (compressEncode d (VG.Proof.MlKem.X86_64.CE.F s₀))[k]!

theorem tail_ok (c b : Nat) (hc : 4 * c < 2 ^ 31) (hb : b < 2 ^ 31) (s : State) :
    WP isa (.block [.alu .add .rdi (.imm (BitVec.ofNat 32 (4 * c))), .alu .add .r8 (.imm (BitVec.ofNat 32 b)),
      .alu .sub .rcx (.imm 1)]) s fun s' =>
      (s'.gpr .rdi = s.gpr .rdi + BitVec.ofNat 64 (4 * c) ∧ s'.gpr .r8 = s.gpr .r8 + BitVec.ofNat 64 b ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.mem = s.mem) ∧
      Keep [.rdi, .r8, .rcx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [sx_ofNat hc, sx_ofNat hb]

theorem lenEq {ws : List Nat} {s₀ : State} (hp : (VG.Proof.MlKem.X86_64.compressEncodeWK ws).pre s₀) {d : Nat} (hdd : VG.Proof.MlKem.X86_64.dArg s₀ .rsi = d) :
    (s₀.gpr .rcx).toNat = 32 * d := by rw [hp.2.2.2.2.2.2.1, hdd]

/-- What the code of group `i` needs: its coefficients readable, their
compressed values (with the multiplier in `r9` and the rounding constant
`r`), its bytes writable, apart. -/
structure GrpIn (r d c b : Nat) (F : Poly) (i : Nat) (s : State) : Prop where
  rd : ∀ j < c, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 4
  v : ∀ j < c, (VG.Proof.MlKem.X86_64.ceV r d (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32) (s.gpr .r9)).toNat =
    compress d F[c * i + j]!
  wr : ∀ k < b, InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 k) 1
  dj : Region.Disjoint ⟨s.gpr .rdi, 4 * c⟩ ⟨s.gpr .r8, b⟩

/-- What the code of group `i` does: its `b` bytes of the encoding. -/
abbrev GrpOut (d b : Nat) (F : Poly) (i : Nat) (s s' : State) : Prop :=
  VG.Proof.MlKem.X86_64.Written s.mem s'.mem (s.gpr .r8) b (fun k => (compressEncode d F)[b * i + k]!) ∧ Keep [.rax, .rdx, .r10] s s'

section
variable {ws : List Nat} {s₀ : State} (hp : (VG.Proof.MlKem.X86_64.compressEncodeWK ws).pre s₀) {r d c b M : Nat}
  (hd11 : 1 ≤ d ∧ d ≤ 11) (hc0 : 0 < c) (hc8 : c ≤ 8) (hb : b ≤ 11) (hbN : b * (256 / c) = 32 * d)
  (hcN : c * (256 / c) = 256) (hdd : VG.Proof.MlKem.X86_64.dArg s₀ .rsi = d)
  (hcomp : ∀ x : Zq, x.val * M + r < 2 ^ 30 ∧ compress d x = (x.val * M + r) / 2 ^ 19 % 2 ^ d)
include hp hd11 hc0 hc8 hb hbN hcN hdd

omit hd11 hc0 hc8 hb hbN hcN in
theorem coeff {m : Mem} (hf : Frame [⟨VG.Proof.MlKem.X86_64.CE.oP s₀, 32 * d⟩] s₀.mem m) {k : Nat} (hk : k < 256) :
    coeffAt m (VG.Proof.MlKem.X86_64.CE.fP s₀) k = coeffAt s₀.mem (VG.Proof.MlKem.X86_64.CE.fP s₀) k :=
  coeffAt_congr (bytes_frame hf (by
    have := hp.2.2.1; rw [VG.Proof.MlKem.X86_64.CE.lenEq hp hdd] at this; simpa using this) (by decide)) hk

include hcomp in
theorem step {grp : List Instr}
    (hgrp : ∀ i < 256 / c, ∀ s, VG.Proof.MlKem.X86_64.CE.GrpIn r d c b (VG.Proof.MlKem.X86_64.CE.F s₀) i s → WP isa (.block grp) s (VG.Proof.MlKem.X86_64.CE.GrpOut d b (VG.Proof.MlKem.X86_64.CE.F s₀) i s))
    {i : Nat} (hi : i < 256 / c) {s : State} (hI : VG.Proof.MlKem.X86_64.CE.Inv s₀ d c b M i s) :
    WP isa (.block (grp ++ ceTail c b)) s fun s' => VG.Proof.MlKem.X86_64.CE.Inv s₀ d c b M (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have hci : c * i + c ≤ 256 := by
    have := Nat.mul_le_mul_left c (show i + 1 ≤ 256 / c by omega); rw [Nat.mul_succ] at this; omega
  have hbi : b * i + b ≤ 32 * d := by
    have := Nat.mul_le_mul_left b (show i + 1 ≤ 256 / c by omega); rw [Nat.mul_succ] at this; omega
  have hrd : s.rd ++ s.wr = [VG.Proof.MlKem.X86_64.pR (VG.Proof.MlKem.X86_64.CE.fP s₀), ⟨VG.Proof.MlKem.X86_64.CE.oP s₀, 32 * d⟩] := by
    rw [hI.rd, hI.wr, hp.1, hp.2.1, VG.Proof.MlKem.X86_64.CE.lenEq hp hdd]; rfl
  have hwr : s.wr = [⟨VG.Proof.MlKem.X86_64.CE.oP s₀, 32 * d⟩] := by rw [hI.wr, hp.2.1, VG.Proof.MlKem.X86_64.CE.lenEq hp hdd]
  have ha : ∀ j < c, s.gpr .rdi + BitVec.ofNat 64 (4 * j) = coeffAddr (VG.Proof.MlKem.X86_64.CE.fP s₀) (c * i + j) := fun j _ => by
    rw [hI.rdi, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; rw [Nat.mul_add, Nat.mul_assoc]
  have hdj : Region.Disjoint (VG.Proof.MlKem.X86_64.pR (VG.Proof.MlKem.X86_64.CE.fP s₀)) ⟨VG.Proof.MlKem.X86_64.CE.oP s₀, 32 * d⟩ := by
    have := hp.2.2.1; rw [VG.Proof.MlKem.X86_64.CE.lenEq hp hdd] at this; exact this
  rw [WP.block_append_iff]
  refine WP.mono (hgrp i hi s ⟨fun j hj => ?_, fun j hj => ?_, fun k hk => ?_, ?_⟩) fun s₁ ⟨w₁, k₁⟩ => ?_
  · rw [ha j hj, hrd]; exact ⟨_, by simp, coeff_contains _ (show c * i + j < 256 by omega)⟩
  · have hr : Reduced s₀.mem (VG.Proof.MlKem.X86_64.CE.fP s₀) := hp.2.2.2.2.2.2.2
    have hk : c * i + j < 256 := by omega
    rw [ha j hj, ← coeffAt_eq, VG.Proof.MlKem.X86_64.CE.coeff hp hdd hI.frame hk]
    have harg := (hcomp (VG.Proof.MlKem.X86_64.CE.F s₀)[c * i + j]!).1
    rw [polyAt_val hr hk] at harg
    rw [VG.Proof.MlKem.X86_64.ceV_toNat hd11.2 (by rw [hI.r9]; exact harg), hI.r9, (hcomp _).2, polyAt_val hr hk]
  · rw [hwr, hI.r8, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨_, List.mem_singleton_self _, VG.Proof.MlKem.X86_64.contains_offset' (by omega) (by omega)⟩
  · rw [hI.rdi, hI.r8]
    exact (hdj.sub_left (VG.Proof.MlKem.X86_64.sub_offset' (by rw [Nat.mul_assoc]; omega) (by decide))).sub_right
      (VG.Proof.MlKem.X86_64.sub_offset' (by omega) (by omega))
  refine WP.mono (VG.Proof.MlKem.X86_64.CE.tail_ok c b (by omega) (by omega) s₁) fun s₂ ⟨⟨di₂, r8₂, cx₂, z₂, m₂⟩, k₂⟩ => ⟨?_, ?_, ?_⟩
  rotate_left
  · rw [cx₂, k₁.gpr (by decide)]
  · rw [z₂, k₁.gpr (by decide)]
  have hw : VG.Proof.MlKem.X86_64.Written s.mem s₂.mem (VG.Proof.MlKem.X86_64.CE.oP s₀ + BitVec.ofNat 64 (b * i)) b
      fun k => (compressEncode d (VG.Proof.MlKem.X86_64.CE.F s₀))[b * i + k]! := by
    rw [m₂, ← hI.r8]; exact w₁
  obtain ⟨hf', hd'⟩ := Written.step hI.frame hI.done hw hbi (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, hf', fun k hk => hd' k (by rw [Nat.mul_succ] at hk; omega)⟩
  · rw [di₂, k₁.gpr (by decide), hI.rdi]; exact ptr_step _ i (4 * c)
  · rw [r8₂, k₁.gpr (by decide), hI.r8]; exact ptr_step _ i b
  · rw [k₂.gpr (by decide), k₁.gpr (by decide), hI.r9]
  · rw [k₂.2.1, k₁.2.1, hI.rd]
  · rw [k₂.2.2, k₁.2.2, hI.wr]

include hcomp in
/-- The loop over the groups, each `grp`, with the multiplier `M`, from a
state with `f` in `rdi` and `out` in `r8`. -/
theorem loop_ok {grp : List Instr}
    (hgrp : ∀ i < 256 / c, ∀ s, VG.Proof.MlKem.X86_64.CE.GrpIn r d c b (VG.Proof.MlKem.X86_64.CE.F s₀) i s → WP isa (.block grp) s (VG.Proof.MlKem.X86_64.CE.GrpOut d b (VG.Proof.MlKem.X86_64.CE.F s₀) i s))
    (hM : M < 2 ^ 31) {s : State} (hdi : s.gpr .rdi = VG.Proof.MlKem.X86_64.CE.fP s₀) (h8 : s.gpr .r8 = VG.Proof.MlKem.X86_64.CE.oP s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa (ceLoopW M (256 / c) (grp ++ ceTail c b)) s fun s' =>
      bytesAt s'.mem (VG.Proof.MlKem.X86_64.CE.oP s₀) (32 * d) = compressEncode d (VG.Proof.MlKem.X86_64.CE.F s₀) ∧ Frame [⟨VG.Proof.MlKem.X86_64.CE.oP s₀, 32 * d⟩] s₀.mem s'.mem := by
  refine WP.seq (WP.mono (WP.keep [.r9] (Q := fun s' => s'.gpr .r9 = BitVec.ofNat 64 M ∧ s'.mem = s.mem)
    (by xrun [sx_ofNat hM]) (by rfl)) fun s₁ ⟨⟨h9, m₁⟩, k₁⟩ => ?_)
  have hN : 0 < 256 / c ∧ 256 / c ≤ 256 := ⟨Nat.div_pos (by omega) hc0, Nat.div_le_self _ _⟩
  refine WP.mono (wp_counted (N := 256 / c) (v := BitVec.ofNat 32 (256 / c))
    (by rw [BitVec.toNat_ofNat]; omega) (by omega) (VG.Proof.MlKem.X86_64.CE.Inv s₀ d c b M)
    (fun s₂ m₂ k₂ => ⟨?_, ?_, ?_, ?_, ?_, ?_, fun k hk => absurd hk (by omega)⟩)
    fun i hi s hI => VG.Proof.MlKem.X86_64.CE.step hp hd11 hc0 hc8 hb hbN hcN hdd hcomp hgrp hi hI) fun s' hI => ⟨?_, hI.frame⟩
  · rw [k₂.gpr (by decide), k₁.gpr (by decide), hdi]; simp
  · rw [k₂.gpr (by decide), k₁.gpr (by decide), h8]; simp
  · rw [k₂.gpr (by decide), h9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [k₂.2.1, k₁.2.1, hrd]
  · rw [k₂.2.2, k₁.2.2, hwr]
  · rw [m₂, m₁, hm]; exact Frame.refl _ _
  · exact bytesAt_eq! (compressEncode_length _ _) fun k hk => hI.done k (by omega)

end

/-- A group whose code accumulates its `c` values and stores its `b` bytes
(`d · c = 8 · b`). -/
theorem grp_ok {r d c b : Nat} (hr : r < 2 ^ 31) (hd11 : 1 ≤ d ∧ d ≤ 11) (hdc : d * c = 8 * b) (hb : b ≤ 7)
    (F : Poly) {i : Nat} (hci : c * i + c ≤ 256) (hbi : b * i + b ≤ 32 * d) {s : State} (h : VG.Proof.MlKem.X86_64.CE.GrpIn r d c b F i s) :
    WP isa (.block (ceAcc r d 0 c ++ ceSt 0 b)) s (VG.Proof.MlKem.X86_64.CE.GrpOut d b F i s) := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.ceAcc_ok (o := 0) (c := c) hr hd11.1 hd11.2 (by omega) s
    (fun j hj => by rw [Nat.zero_add]; exact h.rd j hj) (fun j => compress d F[c * i + (0 + j)]!)
    (fun j hj => by rw [Nat.zero_add]; exact h.v j hj) (fun _ _ => compress_lt d _)) fun s₁ ⟨r₁, m₁, k₁⟩ => ?_
  refine WP.mono (VG.Proof.MlKem.X86_64.ceSt_ok (k0 := 0) (nb := b) (by omega) s₁ (fun k hk => by
      rw [k₁.2.2, k₁.gpr (by decide), Nat.zero_add]; exact h.wr k hk)) fun s₂ ⟨w₂, k₂⟩ =>
    ⟨?_, (k₁.trans k₂).mono (by decide)⟩
  rw [k₁.gpr (by decide), add_ofNat_zero, m₁, r₁] at w₂
  refine w₂.congr fun k hk => ?_
  rw [Spec.MlKem.compressEncode, byteEncode_group (c := c) (by omega) hdc (map_toList_lt _ (compress_lt d)) hk
    (by omega), take_drop_eq _ 0 (by rw [map_toList_length]; omega)]
  congr 3
  apply List.map_congr_left
  intro j hj
  rw [map_toList_getD _ _ (show c * i + j < 256 by have := List.mem_range.mp hj; omega), Nat.zero_add]

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
      bytesAt s'.mem (s₀.gpr .rdx) (s₀.gpr .rcx).toNat = compressEncode (VG.Proof.MlKem.X86_64.dArg s₀ .rsi) (CE.F s₀) ∧
        Frame [⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩] s₀.mem s'.mem := by
  have hd := hp.2.2.2.2.2.1
  rw [CE.lenEq hp rfl]
  unfold Impl.MlKem.X86_64.compressEncode
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.cePrologue_ok s₀) fun s₁ ⟨⟨si₁, r8₁, z₁, m₁⟩, k₁⟩ => ?_)
  have di₁ : s₁.gpr .rdi = s₀.gpr .rdi := k₁.gpr (by decide)
  have go : ∀ {d c b : Nat}, d ∈ compressWidths → d * c = 8 * b → b ≤ 5 → 0 < c → c ≤ 8 →
      b * (256 / c) = 32 * d → c * (256 / c) = 256 → VG.Proof.MlKem.X86_64.dArg s₀ .rsi = d → ∀ s : State,
      s.gpr .rdi = s₀.gpr .rdi → s.gpr .r8 = s₀.gpr .rdx → s.rd = s₀.rd → s.wr = s₀.wr → s.mem = s₀.mem →
      WP isa (ceLoop d c b) s fun s' =>
        bytesAt s'.mem (s₀.gpr .rdx) (32 * VG.Proof.MlKem.X86_64.dArg s₀ .rsi) = compressEncode (VG.Proof.MlKem.X86_64.dArg s₀ .rsi) (CE.F s₀) ∧
          Frame [⟨s₀.gpr .rdx, 32 * VG.Proof.MlKem.X86_64.dArg s₀ .rsi⟩] s₀.mem s'.mem := by
    intro d c b hd hdc hb hc0 hc hbN hcN hdd s h1 h2 h3 h4 h5
    have hd11 : 1 ≤ d ∧ d ≤ 11 := by rcases mem_compressWidths hd with rfl | rfl | rfl <;> decide
    rw [hdd]
    exact CE.loop_ok hp hd11 hc0 hc (by omega) hbN hcN hdd (M := ceMul d) (r := 262080)
      (fun x => ⟨compress_arg_lt hd x, compress_eq hd x⟩)
      (fun i hi s hs => CE.grp_ok (by decide) hd11 hdc (by omega) _
        (by have := Nat.mul_le_mul_left c (show i + 1 ≤ 256 / c by omega); rw [Nat.mul_succ] at this; omega)
        (by have := Nat.mul_le_mul_left b (show i + 1 ≤ 256 / c by omega); rw [Nat.mul_succ] at this; omega) hs)
      (by rw [ceMul]; split <;> [decide; split <;> decide]) h1 h2 h3 h4 h5
  refine WP.ite (M := isa) _ (show isa.eval .e s₁ = _ from z₁) (fun h => ?_) (fun h => ?_)
  · rw [VG.Proof.MlKem.X86_64.sub_beq_zero32, decide_eq_true_eq] at h
    exact go (d := 1) (c := 8) (b := 1) (by rw [← (show VG.Proof.MlKem.X86_64.dArg s₀ .rsi = 1 by simp only [VG.Proof.MlKem.X86_64.dArg, h]; rfl)]; exact hd)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simp only [VG.Proof.MlKem.X86_64.dArg, h]; rfl) s₁ di₁ r8₁ k₁.2.1 k₁.2.2 m₁
  · rw [VG.Proof.MlKem.X86_64.sub_beq_zero32, decide_eq_false_iff_not] at h
    refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.cmp32_ok .rsi 4 s₁) fun s₂ ⟨⟨z₂, m₂⟩, k₂⟩ => ?_)
    rw [si₁, BitVec.setWidth_32_64_32] at z₂
    refine WP.ite (M := isa) _ (show isa.eval .e s₂ = _ from z₂) (fun h' => ?_) (fun h' => ?_)
    · rw [VG.Proof.MlKem.X86_64.sub_beq_zero32, decide_eq_true_eq] at h'
      exact go (d := 4) (c := 2) (b := 1) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simp only [VG.Proof.MlKem.X86_64.dArg, h']; rfl) s₂ (by rw [k₂.gpr (by decide), di₁])
        (by rw [k₂.gpr (by decide), r8₁]) (by rw [k₂.2.1, k₁.2.1]) (by rw [k₂.2.2, k₁.2.2]) (by rw [m₂, m₁])
    · rw [VG.Proof.MlKem.X86_64.sub_beq_zero32, decide_eq_false_iff_not] at h'
      have h10 : VG.Proof.MlKem.X86_64.dArg s₀ .rsi = 10 := by
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
    [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10] (VG.Proof.MlKem.X86_64.ce_wp hs) (by decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

theorem compressEncode_ct :
    ConstantTime isa compressEncodeK.pre compressEncodeK.pub Impl.MlKem.X86_64.compressEncode :=
  VG.Taint.constantTime (A := taint) (VG.Proof.MlKem.X86_64.regsLo [.rdi, .rdx, .rcx, .rsp] [.rsi])
    (fun _ _ _ _ hp => VG.Proof.MlKem.X86_64.agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1])
      fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact hp.2.2.2.2)
    (by taint_decide)

/-- A state satisfying the precondition. -/
def compressEncodeSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 1 | .rdx => 0x2000 | .rcx => 32 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 32⟩]

theorem compressEncode_verified :
    Verified X86_64.target Impl.MlKem.X86_64.compressEncode (Spec.MlKem.compressEncodeContract X86_64.abi) :=
  Verified.of_correct VG.Proof.MlKem.X86_64.compressEncode_correct VG.Proof.MlKem.X86_64.compressEncode_ct (by
    mlkem_implies [Spec.MlKem.compressEncodeContract, Spec.MlKem.compressEncodeSig, VG.Proof.MlKem.X86_64.compressEncodeK,
      X86_64.abi, X86_64.argRegs] [compressEncodeSat] using VG.Proof.MlKem.X86_64.compressEncodeSat)

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.Zero`. -/
section

/-!
# ML-KEM on x86-64: zeroing a Keccak state

`zeroSt b off` stores `rax` (zero) to the 25 lanes at `b + off`: the all-zero
state (`zeroSt_ok`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

theorem lane_sep (p : Addr) {i j : Nat} (hi : i < 25) (hj : j < 25) (h : i ≠ j) :
    Mem.Sep (p + BitVec.ofNat 64 (8 * i)) (64 / 8) (p + BitVec.ofNat 64 (8 * j)) (64 / 8) := by
  intro x hx hy
  simp only [Nat.reduceDiv] at hx hy
  bv_omega

theorem zeroStep_ok (b : Reg) (d : Nat) (s : State) (hw : InRegions s.wr (s.gpr b + BitVec.ofNat 64 d) 8) :
    WP isa (.block [.store (at_ b d) .rax]) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr b + BitVec.ofNat 64 d) (s.gpr .rax)) ∧ Keep [] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [hw]

/-- The lanes at `b + off`, zeroed. -/
theorem zeroSt_ok (b : Reg) (off : Nat) (s : State) (h0 : s.gpr .rax = 0)
    (hw : ∀ i < 25, InRegions s.wr (s.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block (zeroSt b off)) s fun s' =>
      Spec.Sha3.stateAt s'.mem (s.gpr b + BitVec.ofNat 64 off) = Spec.Sha3.zero ∧
        Frame [⟨s.gpr b + BitVec.ofNat 64 off, 200⟩] s.mem s'.mem ∧ Keep [] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun k s' => Keep [] s s' ∧
      Frame [⟨s.gpr b + BitVec.ofNat 64 off, 200⟩] s.mem s'.mem ∧
      ∀ j < k, s'.mem.readW (s.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 (8 * j)) 64 = 0)
    (fun k s' hk ⟨hk', hf, hz⟩ => ?_) 25 (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s' ⟨hk, hf, hz⟩ => ⟨?_, hf, hk⟩
  · have hb : s'.gpr b = s.gpr b := hk'.gpr (by simp)
    have ha : s'.gpr .rax = 0 := by rw [hk'.gpr (by simp), h0]
    have e : s.gpr b + BitVec.ofNat 64 (off + 8 * k) = s.gpr b + BitVec.ofNat 64 off + BitVec.ofNat 64 (8 * k) := by
      rw [BitVec.add_assoc, BitVec.ofNat_add]
    refine WP.mono (VG.Proof.MlKem.X86_64.zeroStep_ok b (off + 8 * k) s' (by rw [hk'.2.2, hb, e]; exact hw k hk))
      fun s'' ⟨hm, hk''⟩ => ⟨hk'.trans hk'', ?_, fun j hj => ?_⟩
    · rw [hm, hb, e]
      exact hf.writeW (List.mem_singleton_self _) _ (VG.Proof.MlKem.X86_64.contains_offset' (by omega) (by omega))
    · rw [hm, hb, e, ha]
      by_cases hjk : j = k
      · subst hjk; rw [Mem.readW_writeW_self64]
      · rw [Mem.readW_writeW_sep (VG.Proof.MlKem.X86_64.lane_sep _ (by omega) hk hjk) (by decide), hz j (by omega)]
  · apply Vector.ext
    intro i hi
    simp only [Spec.Sha3.stateAt, Spec.Sha3.zero, Vector.getElem_ofFn, Vector.getElem_replicate]
    exact hz i hi

end VG.Proof.MlKem.X86_64

end
