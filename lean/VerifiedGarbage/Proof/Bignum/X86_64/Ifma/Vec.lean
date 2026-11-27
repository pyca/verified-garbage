module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.ZPre
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSA with AVX512_IFMA on x86-64, any size: the vector code

`vec` (`vec_ok`), with no MXCSR of its own (its dispatcher's
`vg_mcdt_enter` sets it: `CrtIfma.withVzu`), the exponentiations (with `X`
and `Y` into Montgomery form for `R = 2^(208 R)`, `expLoop_ok`), the last
of them `Y := Y Fin / R`: `Y ≡ x^e Fin`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off writeW_outside)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (wp_seqs_app ofs_off0 and_ffff_hi mont_into0 mont_into1 mont_out
  writeW32_outside se_ofNat cop2)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The vector code before its `vzeroupper`. -/
theorem vecBody_ok (hl : AmmOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {e : Nat → Nat}
    (hB : s.gpr .rbx = B)
    (hs : Scr s B (l.nl * l.D)) (ar : Ar l s.mem B M k) (hR : ∀ p < l.nl, Nat.Coprime (2 ^ (52 * l.S)) (M p))
    (gx : ∀ p < l.nl, Good l s.mem B M l.oX p) (gy : ∀ p < l.nl, Good l s.mem B M l.oY p)
    (gk : ∀ p < l.nl, Good l s.mem B M l.oK1 p) (gf : ∀ p < l.nl, Good l s.mem B M l.oFin p)
    (vx : Q → ∀ p < l.nl, val52 l s.mem B (l.D * p + l.oX) % M p = x p * 2 ^ l.cv % M p)
    (vy : Q → ∀ p < l.nl, val52 l s.mem B (l.D * p + l.oY) % M p = 1 * 2 ^ l.cv % M p)
    (vk : Q → ∀ p < l.nl, val52 l s.mem B (l.D * p + l.oK1) % M p = 2 ^ (104 * l.S - l.cv) % M p)
    (he : ∀ p < l.nl, e p < 2 ^ (8 * l.E)) (hd : ∀ p < l.nl, ∀ i < l.ND, dig l s.mem B p i = digit l (e p) i) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (expLoop l)) s fun s' =>
      (∀ p < l.nl, Good l s'.mem B M l.oY p ∧
        (Q → val52 l s'.mem B (l.D * p + l.oY) % M p =
          x p ^ e p * val52 l s.mem B (l.D * p + l.oFin) % M p)) ∧
      Outside B 0 (l.nl * l.D) s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr :=
  WP.mono (expLoop_ok hl ⟨hB, hs, ar, hR, gx, gy, gk, vx, vy, vk⟩ gf he hd)
    fun _ ⟨v, f, g, rd, wr, x⟩ => ⟨v, f.toOutside hl, fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 _ r12 =>
      g r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r12, rd, wr, x⟩

/-! ## Writes above both regions -/

section
variable {m m' : Mem} {B : Addr} {n : Nat} (hl : AmmOk l) (h : Outside B (l.nl * l.D) n m m')
include hl h

theorem hi_word {p c : Nat} (hp : p < l.nl) (hc : c + 8 ≤ l.D) : word m' B (l.D * p + c) = word m B (l.D * p + c) :=
  have := hl.D_bounds
  have hle := lane_end hl hp
  have h2 := nlD_le hl
  h.word (.inl (by rcases D_mulN hl hp with h | h <;> omega_using [hc, h, hle]))
    (by rcases D_mulN hl hp with h | h <;> omega_using [hc, this, h, hle, h2])

theorem hi_limb {p c : Nat} (hp : p < l.nl) (hc : c + l.NB ≤ l.D) {j : Nat} (hj : j < l.L) :
    limb l m' B (l.D * p + c) j = limb l m B (l.D * p + c) j := by
  have := off_ltN hl hj
  show (word m' B _).toNat = (word m B _).toNat
  rw [Nat.add_assoc, hi_word hl h hp (by omega_using [hc, this])]

theorem hi_val {p c : Nat} (hp : p < l.nl) (hc : c + l.NB ≤ l.D) :
    val52 l m' B (l.D * p + c) = val52 l m B (l.D * p + c) :=
  val52_of_limbs fun _ hj => hi_limb hl h hp hc hj

theorem Good.of_hi {M : Nat → Nat} {p c : Nat} (g : Good l m B M c p) (hp : p < l.nl) (hc : c + l.NB ≤ l.D) :
    Good l m' B M c p :=
  g.of_limbs fun _ hj => hi_limb hl h hp hc hj

theorem GoodS.of_hi {M : Nat → Nat} {p c : Nat} (g : GoodS l m B M c p) (hp : p < l.nl) (hc : c + l.NB ≤ l.D) :
    GoodS l m' B M c p :=
  ⟨fun j hj => by rw [hi_limb hl h hp hc hj]; exact g.lt j hj, by rw [hi_val hl h hp hc]; exact g.v⟩

theorem Ar0.of_hi {M k : Nat → Nat} (a : Ar0 l m B M k) : Ar0 l m' B M k := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have := hl.bounds
  refine ⟨fun p hp j hj => ?_, fun p hp => ?_, fun p hp t ht => ?_, a.klt, fun p hp => ?_, a.bnd⟩
  · rw [hi_limb hl h hp (by simp only [oM]; omega_using [o10]) hj]; exact a.mlt p hp j hj
  · rw [hi_val hl h hp (by simp only [oM]; omega_using [o10])]; exact a.mv p hp
  · rw [Nat.add_assoc, hi_word hl h hp (by omega_using [o1, o10, ht]), ← Nat.add_assoc]; exact a.kw p hp t ht
  · rw [hi_limb hl h hp (by simp only [oM]; omega_using [o10]) (by simp only [Lay.L]; omega_using [this])]; exact a.k0 p hp

theorem dig_of_hi {p i : Nat} (hp : p < l.nl) (hi : i < l.ND) : dig l m' B p i = dig l m B p i := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨d1, d2⟩ := lay_dAt hl hi
  have := hl.D_bounds
  exact congrArg (fun b : BitVec 8 => nibOf l i b.toNat) (h _ (.inl (by
    rw [ofs_off0 B (by rcases D_mulN hl hp with h | h <;> omega_using [d2, o7, o10, this, h])]
    have hle := lane_end hl hp
    rcases D_mulN hl hp with h | h <;> omega_using [d2, o7, o10, h, hle])))

end

/-- `withVzu`: a code `c` that keeps the regions' frame, then `vzeroupper`:
what it leaves of memory (`R`), with MXCSR as it was. -/
theorem withVzu_ok {s : State} {B : Addr} {c : Prog isa} {R : Mem → Prop}
    (hc : WP isa c s fun s₃ => R s₃.mem ∧ Outside B 0 (l.nl * l.D) s.mem s₃.mem ∧
        (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
          r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → s₃.gpr r = s.gpr r) ∧
        s₃.rd = s.rd ∧ s₃.wr = s.wr ∧ s₃.mxcsr = s.mxcsr) :
    WP isa (withVzu c) s fun s' =>
      R s'.mem ∧ Outside B 0 (l.nl * l.D + 8) s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr :=
  WP.seq (WP.mono hc fun _ ⟨v₃, O₃, g₃, rd₃, wr₃, x₃⟩ => by
    rw [WP.block_cons_iff]
    exact ⟨_, rfl, WP.block_nil ⟨v₃, O₃.mono (by omega_using []) (by omega_using []), g₃, rd₃, wr₃, x₃⟩⟩)

/-- The doublings of the layouts without `ammCoreZ`. -/
theorem dbls_eq (hl : AmmOk l) (hz : l.z = false) : 2 ^ (104 * l.S - 64 * l.W) = 2 ^ l.dbls * 2 ^ (64 * l.W) := by
  rw [← Nat.pow_add]; congr 1
  rcases hl with (rfl | rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd hz (by decide) | decide

/-- The vector code: `Y ≡ x^e Fin` for each prime, below twice the prime, from the region's numbers:
the modulus (odd, `W` words), the base and 1 times `R_X = 2^(64 W)`, and `2^dbls R_X`. -/
theorem vec_ok (hl : AmmOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {e : Nat → Nat}
    (hB : s.gpr .rbx = B)
    (hs : Scr s B (l.nl * l.D + 8)) (ar : Ar0 l s.mem B M k) (hodd : ∀ p < l.nl, M p % 2 = 1)
    (hMw : ∀ p < l.nl, M p < 2 ^ (64 * l.W))
    (gx : ∀ p < l.nl, GoodS l s.mem B M l.oX p) (gy : ∀ p < l.nl, GoodS l s.mem B M l.oY p)
    (gk : ∀ p < l.nl, GoodS l s.mem B M l.oK1 p) (gf : ∀ p < l.nl, GoodS l s.mem B M l.oFin p)
    (vx : Q → ∀ p < l.nl, val52 l s.mem B (l.D * p + l.oX) % M p = x p * 2 ^ (64 * l.W) % M p)
    (vy : Q → ∀ p < l.nl, val52 l s.mem B (l.D * p + l.oY) % M p = 1 * 2 ^ (64 * l.W) % M p)
    (vk : Q → ∀ p < l.nl, val52 l s.mem B (l.D * p + l.oK1) % M p = 2 ^ l.dbls * 2 ^ (64 * l.W) % M p)
    (he : ∀ p < l.nl, e p < 2 ^ (8 * l.E)) (hd : ∀ p < l.nl, ∀ i < l.ND, dig l s.mem B p i = digit l (e p) i) :
    WP isa (vec l) s fun s' =>
      (∀ p < l.nl, GoodS l s'.mem B M l.oY p ∧
        (Q → val52 l s'.mem B (l.D * p + l.oY) % M p =
          x p ^ e p * val52 l s.mem B (l.D * p + l.oFin) % M p)) ∧
      Outside B 0 (l.nl * l.D + 8) s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hs₂ : Scr s B (l.nl * l.D) := AmmSym.Scr.mono hs (by omega_using [])
  rcases hl.zcases with hz | hz
  · rw [show vec l = withVzu (VG.Impl.Bignum.X86_64.seqs (expLoop l)) by
      unfold vec; rw [hz, ite_eq_right (by decide)]]
    refine withVzu_ok (l := l) (R := fun m' => ∀ p < l.nl, GoodS l m' B M l.oY p ∧
      (Q → val52 l m' B (l.D * p + l.oY) % M p = x p ^ e p * val52 l s.mem B (l.D * p + l.oFin) % M p)) ?_
    have ge : ∀ p, M p ≤ gb l (M p) := fun p => Nat.le_of_eq (gb_eq hz _).symm
    refine WP.mono (vecBody_ok hl (Q := Q) (x := x) hB hs₂
      ⟨ar, fun h => absurd h (by rw [hz]; decide)⟩ (fun p hp => cop2 (hodd p hp) _)
      (fun p hp => (gx p hp).good (ge p)) (fun p hp => (gy p hp).good (ge p))
      (fun p hp => (gk p hp).good (ge p)) (fun p hp => (gf p hp).good (ge p))
      (fun hq p hp => by rw [cv_eq hz]; exact vx hq p hp) (fun hq p hp => by rw [cv_eq hz]; exact vy hq p hp)
      (fun hq p hp => by rw [cv_eq hz, dbls_eq hl hz]; exact vk hq p hp) he hd)
      fun s₃ ⟨v₃, rest⟩ => ⟨fun p hp => ⟨(v₃ p hp).1.strong hz, (v₃ p hp).2⟩, rest⟩
  · rw [show vec l = withVzu (.seq (VG.Impl.Bignum.X86_64.seqs (zPre l))
        (.seq (VG.Impl.Bignum.X86_64.seqs (expLoop l)) (zPost l))) by unfold vec; rw [hz.z, ite_eq_left rfl]]
    refine withVzu_ok (l := l) (R := fun m' => ∀ p < l.nl, GoodS l m' B M l.oY p ∧
      (Q → val52 l m' B (l.D * p + l.oY) % M p = x p ^ e p * val52 l s.mem B (l.D * p + l.oFin) % M p)) ?_
    exact zBody_ok hz (Q := Q) (x := x) hB hs₂ ar hodd hMw gx gy gk gf vx vy vk he hd

end VG.Proof.Bignum.X86_64.Ifma
