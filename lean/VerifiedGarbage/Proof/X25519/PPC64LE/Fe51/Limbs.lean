module
-- separate module: the five-limb field's proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Spec.X25519
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# X25519 on PPC64LE: numbers of five 51-bit limbs

The arithmetic of `Impl/X25519/PPC64LE/Fe51.lean`, on natural numbers: the
number of five limbs (`val5`), the columns of a product and of a square
(`mul_ident`, `sqr_ident`), their reduction to five limbs (`tail_val`), a
difference (`sub_val`), and four 64-bit words to and from five limbs
(`unpack_val`, `pack_val`).
-/

@[expose] public section

namespace VG.Proof.X25519.PPC64LE.Fe51

open VG.Spec.X25519 (P)

/-- The number of five limbs. -/
def val5 (f : Nat → Nat) : Nat := f 0 + 2 ^ 51 * f 1 + 2 ^ 102 * f 2 + 2 ^ 153 * f 3 + 2 ^ 204 * f 4

theorem val5_congr {f g : Nat → Nat} (h : ∀ k < 5, f k = g k) : val5 f = val5 g := by
  simp only [val5, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)]

/-- Five numbers as limbs. -/
def lim (x0 x1 x2 x3 x4 : Nat) (k : Nat) : Nat :=
  if k = 0 then x0 else if k = 1 then x1 else if k = 2 then x2 else if k = 3 then x3 else x4

theorem val5_lim (x0 x1 x2 x3 x4 : Nat) :
    val5 (lim x0 x1 x2 x3 x4) = x0 + 2 ^ 51 * x1 + 2 ^ 102 * x2 + 2 ^ 153 * x3 + 2 ^ 204 * x4 := rfl

/-- A number and a multiple of `p`. -/
theorem mod_of_add {x y k : Nat} (h : x = y + P * k) : x % P = y % P := by
  rw [h, Nat.add_mul_mod_self_left]

private theorem mul_ring (W a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Nat) :
    (a0 + W * a1 + W ^ 2 * a2 + W ^ 3 * a3 + W ^ 4 * a4) * (b0 + W * b1 + W ^ 2 * b2 + W ^ 3 * b3 + W ^ 4 * b4) +
      19 * ((a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1) + W * (a2 * b4 + a3 * b3 + a4 * b2) +
        W ^ 2 * (a3 * b4 + a4 * b3) + W ^ 3 * (a4 * b4)) =
    ((0 + a0 * b0 + a1 * (19 * b4) + a2 * (19 * b3) + a3 * (19 * b2) + a4 * (19 * b1)) +
      W * (0 + a0 * b1 + a1 * b0 + a2 * (19 * b4) + a3 * (19 * b3) + a4 * (19 * b2)) +
      W ^ 2 * (0 + a0 * b2 + a1 * b1 + a2 * b0 + a3 * (19 * b4) + a4 * (19 * b3)) +
      W ^ 3 * (0 + a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0 + a4 * (19 * b4)) +
      W ^ 4 * (0 + a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0)) +
    W ^ 5 * ((a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1) + W * (a2 * b4 + a3 * b3 + a4 * b2) +
        W ^ 2 * (a3 * b4 + a4 * b3) + W ^ 3 * (a4 * b4)) := by
  grind

/-- The columns of a product. -/
theorem mul_ident (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Nat) :
    ((0 + a0 * b0 + a1 * (19 * b4) + a2 * (19 * b3) + a3 * (19 * b2) + a4 * (19 * b1)) +
      2 ^ 51 * (0 + a0 * b1 + a1 * b0 + a2 * (19 * b4) + a3 * (19 * b3) + a4 * (19 * b2)) +
      2 ^ 102 * (0 + a0 * b2 + a1 * b1 + a2 * b0 + a3 * (19 * b4) + a4 * (19 * b3)) +
      2 ^ 153 * (0 + a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0 + a4 * (19 * b4)) +
      2 ^ 204 * (0 + a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0)) % P =
    (val5 (lim a0 a1 a2 a3 a4) * val5 (lim b0 b1 b2 b3 b4)) % P := by
  have h := mul_ring (2 ^ 51) a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  rw [val5_lim, val5_lim]
  simp only [← Nat.pow_mul, Nat.reduceMul] at h
  generalize (a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1) + 2 ^ 51 * (a2 * b4 + a3 * b3 + a4 * b2) +
        2 ^ 102 * (a3 * b4 + a4 * b3) + 2 ^ 153 * (a4 * b4) = K at h
  generalize (a0 + 2 ^ 51 * a1 + 2 ^ 102 * a2 + 2 ^ 153 * a3 + 2 ^ 204 * a4) *
    (b0 + 2 ^ 51 * b1 + 2 ^ 102 * b2 + 2 ^ 153 * b3 + 2 ^ 204 * b4) = AB at h ⊢
  refine (mod_of_add (k := K) ?_).symm
  simp only [P]
  omega_using [h]

private theorem sqr_ring (W a0 a1 a2 a3 a4 : Nat) :
    (a0 + W * a1 + W ^ 2 * a2 + W ^ 3 * a3 + W ^ 4 * a4) * (a0 + W * a1 + W ^ 2 * a2 + W ^ 3 * a3 + W ^ 4 * a4) +
      19 * ((2 * (a1 * a4) + 2 * (a2 * a3)) + W * (2 * (a2 * a4) + a3 * a3) +
        W ^ 2 * (2 * (a3 * a4)) + W ^ 3 * (a4 * a4)) =
    ((0 + a0 * a0 + 2 * (a1 * (19 * a4)) + 2 * (a2 * (19 * a3))) +
      W * (0 + 2 * (a0 * a1) + 2 * (a2 * (19 * a4)) + a3 * (19 * a3)) +
      W ^ 2 * (0 + 2 * (a0 * a2) + a1 * a1 + 2 * (a3 * (19 * a4))) +
      W ^ 3 * (0 + 2 * (a0 * a3) + 2 * (a1 * a2) + a4 * (19 * a4)) +
      W ^ 4 * (0 + 2 * (a0 * a4) + 2 * (a1 * a3) + a2 * a2)) +
    W ^ 5 * ((2 * (a1 * a4) + 2 * (a2 * a3)) + W * (2 * (a2 * a4) + a3 * a3) +
        W ^ 2 * (2 * (a3 * a4)) + W ^ 3 * (a4 * a4)) := by
  grind

/-- The columns of a square. -/
theorem sqr_ident (a0 a1 a2 a3 a4 : Nat) :
    ((0 + a0 * a0 + 2 * (a1 * (19 * a4)) + 2 * (a2 * (19 * a3))) +
      2 ^ 51 * (0 + 2 * (a0 * a1) + 2 * (a2 * (19 * a4)) + a3 * (19 * a3)) +
      2 ^ 102 * (0 + 2 * (a0 * a2) + a1 * a1 + 2 * (a3 * (19 * a4))) +
      2 ^ 153 * (0 + 2 * (a0 * a3) + 2 * (a1 * a2) + a4 * (19 * a4)) +
      2 ^ 204 * (0 + 2 * (a0 * a4) + 2 * (a1 * a3) + a2 * a2)) % P =
    (val5 (lim a0 a1 a2 a3 a4) * val5 (lim a0 a1 a2 a3 a4)) % P := by
  have h := sqr_ring (2 ^ 51) a0 a1 a2 a3 a4
  rw [val5_lim]
  simp only [← Nat.pow_mul, Nat.reduceMul] at h
  generalize (2 * (a1 * a4) + 2 * (a2 * a3)) + 2 ^ 51 * (2 * (a2 * a4) + a3 * a3) +
        2 ^ 102 * (2 * (a3 * a4)) + 2 ^ 153 * (a4 * a4) = K at h
  generalize (a0 + 2 ^ 51 * a1 + 2 ^ 102 * a2 + 2 ^ 153 * a3 + 2 ^ 204 * a4) *
    (a0 + 2 ^ 51 * a1 + 2 ^ 102 * a2 + 2 ^ 153 * a3 + 2 ^ 204 * a4) = AB at h ⊢
  refine (mod_of_add (k := K) ?_).symm
  simp only [P]
  omega_using [h]

/-- The limbs' product from the shifted registers' (`i + j = 13`). -/
theorem prod_div {x y a b i j : Nat} (hx : x = a * 2 ^ i) (hy : y = b * 2 ^ j) (hij : i + j = 13) :
    x * y / 2 ^ 13 = a * b := by
  subst hx hy
  rw [show a * 2 ^ i * (b * 2 ^ j) = a * b * 2 ^ 13 by rw [← hij, Nat.pow_add]; grind]
  exact Nat.mul_div_cancel _ (by decide)

/-- Twice the limbs' product (`i + j = 14`). -/
theorem prod_div2 {x y a b i j : Nat} (hx : x = a * 2 ^ i) (hy : y = b * 2 ^ j) (hij : i + j = 14) :
    x * y / 2 ^ 13 = 2 * (a * b) := by
  subst hx hy
  rw [show a * 2 ^ i * (b * 2 ^ j) = 2 * (a * b) * 2 ^ 13 by
    have : (2 : Nat) ^ i * 2 ^ j = 2 * 2 ^ 13 := by rw [← Nat.pow_add, hij]
    grind]
  exact Nat.mul_div_cancel _ (by decide)

/-- A product's two halves: `mulld`'s, shifted right by 13, and `mulhdu`'s. -/
theorem prod_halves (n : Nat) :
    n % 2 ^ 64 / 2 ^ 13 = n / 2 ^ 13 % 2 ^ 51 ∧ n / 2 ^ 64 = n / 2 ^ 13 / 2 ^ 51 := by
  omega_using []

/-- The reduction of the columns `L k + 2⁵¹ H k`: the limbs `r k` and their bounds. -/
theorem tail_val {L0 L1 L2 L3 L4 H0 H1 H2 H3 H4 T0 T1 T2 T3 T4 r0 r1 r2 r3 r4 : Nat}
    (hL0 : L0 < 2 ^ 54) (hL1 : L1 < 2 ^ 54) (hL2 : L2 < 2 ^ 54) (hL3 : L3 < 2 ^ 54) (hL4 : L4 < 2 ^ 54)
    (hH0 : H0 < 5 * 2 ^ 61) (hH1 : H1 < 5 * 2 ^ 61) (hH2 : H2 < 5 * 2 ^ 61) (hH3 : H3 < 5 * 2 ^ 61)
    (hH4 : H4 < 5 * 2 ^ 61)
    (hT0 : T0 = L0 + 19 * (H4 % 2 ^ 51)) (hT1 : T1 = L1 + H0 + 19 * (H4 / 2 ^ 51)) (hT2 : T2 = L2 + H1)
    (hT3 : T3 = L3 + H2) (hT4 : T4 = L4 + H3)
    (hr0 : r0 = T0 % 2 ^ 51 + 19 * (T4 / 2 ^ 51)) (hr1 : r1 = T1 % 2 ^ 51 + T0 / 2 ^ 51)
    (hr2 : r2 = T2 % 2 ^ 51 + T1 / 2 ^ 51) (hr3 : r3 = T3 % 2 ^ 51 + T2 / 2 ^ 51)
    (hr4 : r4 = T4 % 2 ^ 51 + T3 / 2 ^ 51) :
    val5 (lim r0 r1 r2 r3 r4) % P = ((L0 + 2 ^ 51 * H0) + 2 ^ 51 * (L1 + 2 ^ 51 * H1) +
      2 ^ 102 * (L2 + 2 ^ 51 * H2) + 2 ^ 153 * (L3 + 2 ^ 51 * H3) + 2 ^ 204 * (L4 + 2 ^ 51 * H4)) % P ∧
    r0 < 2 ^ 51 + 2 ^ 18 ∧ r1 < 2 ^ 51 + 2 ^ 18 ∧ r2 < 2 ^ 51 + 2 ^ 18 ∧ r3 < 2 ^ 51 + 2 ^ 18 ∧
    r4 < 2 ^ 51 + 2 ^ 18 := by
  refine ⟨(mod_of_add (k := H4 + T4 / 2 ^ 51) ?_).symm, by omega_arith, by omega_arith, by omega_arith,
    by omega_arith, by omega_arith⟩
  rw [val5_lim]
  simp only [P]
  omega_arith

/-- A difference, limb by limb, with the limbs of `2p` added. -/
theorem sub_val {a b d : Nat → Nat} (h0 : d 0 + b 0 = a 0 + (2 ^ 52 - 38))
    (hk : ∀ k, 0 < k → k < 5 → d k + b k = a k + (2 ^ 52 - 2)) :
    val5 d + val5 b = val5 a + P * 2 := by
  have h1 := hk 1 (by decide) (by decide); have h2 := hk 2 (by decide) (by decide)
  have h3 := hk 3 (by decide) (by decide); have h4 := hk 4 (by decide) (by decide)
  simp only [val5, P]
  omega_arith

/-- Four 64-bit words below `2²⁵⁵` as five limbs. -/
theorem unpack_val {w0 w1 w2 w3 l0 l1 l2 l3 l4 : Nat} (h0 : w0 < 2 ^ 64) (h1 : w1 < 2 ^ 64)
    (h2 : w2 < 2 ^ 64) (h3 : w3 < 2 ^ 63)
    (e0 : l0 = w0 % 2 ^ 51) (e1 : l1 = (w0 / 2 ^ 51 + w1 * 2 ^ 13 % 2 ^ 64) % 2 ^ 64 % 2 ^ 51)
    (e2 : l2 = (w1 / 2 ^ 38 + w2 * 2 ^ 26 % 2 ^ 64) % 2 ^ 64 % 2 ^ 51)
    (e3 : l3 = (w2 / 2 ^ 25 + w3 * 2 ^ 39 % 2 ^ 64) % 2 ^ 64 % 2 ^ 51) (e4 : l4 = w3 / 2 ^ 12) :
    val5 (lim l0 l1 l2 l3 l4) = w0 + 2 ^ 64 * (w1 + 2 ^ 64 * (w2 + 2 ^ 64 * w3)) ∧
    l0 < 2 ^ 51 ∧ l1 < 2 ^ 51 ∧ l2 < 2 ^ 51 ∧ l3 < 2 ^ 51 ∧ l4 < 2 ^ 51 := by
  refine ⟨?_, by omega_arith, by omega_arith, by omega_arith, by omega_arith, by omega_arith⟩
  rw [val5_lim]
  omega_arith

/-- Five limbs below `2⁵¹ + 2¹⁸` as four 64-bit words: the carries taken, limb after limb, then
the limbs' bits put together with a carry chain. -/
theorem pack_val {l0 l1 l2 l3 l4 t1 t2 t3 t4 n0 m1 m2 m3 m4 x u1 u2 u3 w0 w1 w2 w3 k0 k1 k2 k3 : Nat}
    (b0 : l0 < 2 ^ 51 + 2 ^ 18) (b1 : l1 < 2 ^ 51 + 2 ^ 18) (b2 : l2 < 2 ^ 51 + 2 ^ 18)
    (b3 : l3 < 2 ^ 51 + 2 ^ 18) (b4 : l4 < 2 ^ 51 + 2 ^ 18)
    (ht1 : t1 = l1 + l0 / 2 ^ 51) (ht2 : t2 = l2 + t1 / 2 ^ 51) (ht3 : t3 = l3 + t2 / 2 ^ 51)
    (ht4 : t4 = l4 + t3 / 2 ^ 51) (hn0 : n0 = l0 % 2 ^ 51 + 19 * (t4 / 2 ^ 51))
    (hm1 : m1 = t1 % 2 ^ 51) (hm2 : m2 = t2 % 2 ^ 51) (hm3 : m3 = t3 % 2 ^ 51) (hm4 : m4 = t4 % 2 ^ 51)
    (hx : x = m1 * 2 ^ 51 % 2 ^ 64) (hu1 : u1 = (m1 / 2 ^ 13 + m2 * 2 ^ 38 % 2 ^ 64) % 2 ^ 64)
    (hu2 : u2 = (m2 / 2 ^ 26 + m3 * 2 ^ 25 % 2 ^ 64) % 2 ^ 64) (hu3 : u3 = (m3 / 2 ^ 39 + m4 * 2 ^ 12 % 2 ^ 64) % 2 ^ 64)
    (e0 : w0 + 2 ^ 64 * k0 = n0 + x) (e1 : w1 + 2 ^ 64 * k1 = u1 + k0) (e2 : w2 + 2 ^ 64 * k2 = u2 + k1)
    (e3 : w3 + 2 ^ 64 * k3 = u3 + k2) :
    (w0 + 2 ^ 64 * (w1 + 2 ^ 64 * (w2 + 2 ^ 64 * w3))) % P = val5 (lim l0 l1 l2 l3 l4) % P := by
  have hA : l0 + 2 ^ 51 * l1 + 2 ^ 102 * l2 + 2 ^ 153 * l3 + 2 ^ 204 * l4 =
      l0 % 2 ^ 51 + 2 ^ 51 * m1 + 2 ^ 102 * m2 + 2 ^ 153 * m3 + 2 ^ 204 * m4 + 2 ^ 255 * (t4 / 2 ^ 51) := by
    omega_using [ht1, ht2, ht3, ht4, hm1, hm2, hm3, hm4]
  have c1 : m1 < 2 ^ 51 := by omega_using [hm1]
  have c2 : m2 < 2 ^ 51 := by omega_using [hm2]
  have c3 : m3 < 2 ^ 51 := by omega_using [hm3]
  have c4 : m4 < 2 ^ 51 := by omega_using [hm4]
  have hB : x + 2 ^ 64 * u1 + 2 ^ 128 * u2 + 2 ^ 192 * u3 =
      2 ^ 51 * m1 + 2 ^ 102 * m2 + 2 ^ 153 * m3 + 2 ^ 204 * m4 := by
    omega_using [hx, hu1, hu2, hu3, c1, c2, c3, c4]
  have hc : t4 / 2 ^ 51 ≤ 1 := by omega_using [ht1, ht2, ht3, ht4, b0, b1, b2, b3, b4]
  have hC : w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 + 2 ^ 192 * w3 + 2 ^ 256 * k3 =
      n0 + (x + 2 ^ 64 * u1 + 2 ^ 128 * u2 + 2 ^ 192 * u3) := by
    omega_using [e0, e1, e2, e3]
  have hk : k3 = 0 := by omega_using [hC, hB, hn0, hc, c1, c2, c3, c4]
  refine (mod_of_add (k := t4 / 2 ^ 51) ?_).symm
  rw [val5_lim]
  simp only [P]
  omega_using [hA, hB, hC, hk, hn0]

end VG.Proof.X25519.PPC64LE.Fe51
