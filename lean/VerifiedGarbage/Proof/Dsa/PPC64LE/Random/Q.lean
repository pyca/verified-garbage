module

public import VerifiedGarbage.Proof.Dsa.RandomBytes
import VerifiedGarbage.Proof.Dsa.RandomEncoding
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Env
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Spec.Dsa.Random
import VerifiedGarbage.Proof.Dsa.DomainShape
import VerifiedGarbage.Proof.Dsa.RandomRange
import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.RsaPss
public import VerifiedGarbage.TCB.Mem
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Dsa.PPC64LE.Random.Copy`, which this module and modules that import it used -/

section

/-! ### `Dsa.PPC64LE.Random.Math`, which this module and modules that import it used -/

section

/-!
# DSA sampling on PPC64LE: the arithmetic of the registers

What the sampler's instructions compute, on 64-bit registers: the mask of
q's first significant octet (`smear_eq`, its bits smeared right), a masked
octet (`mask_byte`), the test of a short tape (`short_eq`), a step of the
borrow chain (`borrow_eq`), and the test of `q > 1` (`valid_eq`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Rnd

open VG

/-- The mask of the significant bits of a nonzero octet `n`. -/
abbrev maskOf (n : Nat) : Nat := 2 ^ (n.log2 + 1) - 1

/-- `x` with its bits smeared right, as the code computes it. -/
def smear (x : BitVec 64) : BitVec 64 :=
  ((x ||| x >>> 1) ||| (x ||| x >>> 1) >>> 2) ||| ((x ||| x >>> 1) ||| (x ||| x >>> 1) >>> 2) >>> 4

/-- The same on numbers. -/
def smearN (n : Nat) : Nat :=
  ((n ||| n >>> 1) ||| (n ||| n >>> 1) >>> 2) ||| ((n ||| n >>> 1) ||| (n ||| n >>> 1) >>> 2) >>> 4

theorem or_lt {a b : Nat} (ha : a < 256) (hb : b < 256) : a ||| b < 256 :=
  Nat.or_lt_two_pow (n := 8) ha hb

theorem shr_lt {a k : Nat} (ha : a < 256) : a >>> k < 256 := by
  rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha

theorem ofNat_or {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a ||| BitVec.ofNat 64 b = BitVec.ofNat 64 (a ||| b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (Nat.or_lt_two_pow ha hb)]

theorem ofNat_shr {a : Nat} (ha : a < 2 ^ 64) (k : Nat) :
    BitVec.ofNat 64 a >>> k = BitVec.ofNat 64 (a >>> k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

theorem smear_ofNat {n : Nat} (hn : n < 256) : smear (BitVec.ofNat 64 n) = BitVec.ofNat 64 (smearN n) := by
  have h1 : n ||| n >>> 1 < 256 := or_lt hn (shr_lt hn)
  have h2 : (n ||| n >>> 1) ||| (n ||| n >>> 1) >>> 2 < 256 := or_lt h1 (shr_lt h1)
  unfold smear smearN
  rw [ofNat_shr (by omega_using [hn]), ofNat_or (by omega_using [hn]) (by have := shr_lt (k := 1) hn; omega_using [this]),
    ofNat_shr (by omega_using [h1]), ofNat_or (by omega_using [h1]) (by have := shr_lt (k := 2) h1; omega_using [this]),
    ofNat_shr (by omega_using [h2]), ofNat_or (by omega_using [h2]) (by have := shr_lt (k := 4) h2; omega_using [this])]

theorem smearN_eq : ∀ n < 256, 0 < n → smearN n = maskOf n := by decide +kernel

/-- The mask of a nonzero octet. -/
theorem smear_eq {n : Nat} (hn : n < 256) (h0 : 0 < n) :
    smear (BitVec.ofNat 64 n) = BitVec.ofNat 64 (maskOf n) := by
  rw [smear_ofNat hn, smearN_eq n hn h0]

theorem maskOf_lt {n : Nat} (hn : n < 256) (h0 : 0 < n) : maskOf n < 256 := by
  have := (Nat.log2_lt (show n ≠ 0 by omega_using [h0])).mpr (show n < 2 ^ 8 by omega_using [hn])
  have : 2 ^ (n.log2 + 1) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega_using [this])
  have := Nat.two_pow_pos (n.log2 + 1)
  simp only [maskOf]; omega_arith

/-- An octet masked in a register, stored as an octet. -/
theorem mask_byte (b : Byte) {M : Nat} (hM : M < 256) :
    (BitVec.ofNat 64 b.toNat &&& BitVec.ofNat 64 M).setWidth 8 = b &&& BitVec.ofNat 8 M := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega_using []),
    Nat.mod_eq_of_lt (a := M) (by omega_using [hM]), Nat.mod_eq_of_lt (a := M) (by omega_using [hM]),
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left (by have := b.isLt; omega_using []))]

/-- An octet with all ones, stored as an octet. -/
theorem mask_byte_ff (b : Byte) : (BitVec.ofNat 64 b.toNat &&& BitVec.ofNat 64 255).setWidth 8 = b := by
  rw [mask_byte b (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 8) b.isLt

/-- The test of a short tape: 1 exactly when fewer than `w` octets are left. -/
theorem short_eq {x w : Nat} (hx : x < 2 ^ 64) (hw : w ≤ 32) :
    ((BitVec.ofNat 64 x >>> 63) ^^^ BitVec.ofNat 64 1) &&& ((BitVec.ofNat 64 x - BitVec.ofNat 64 w) >>> 63) =
      BitVec.ofNat 64 (if x < w then 1 else 0) := by
  have ha : BitVec.ofNat 64 x >>> 63 = BitVec.ofNat 64 (if x < 2 ^ 63 then 0 else 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.shiftRight_eq_div_pow]
    split
    · rw [Nat.div_eq_of_lt (by omega_arith)]; rfl
    · rw [show x / 2 ^ 63 = 1 by omega_arith]; rfl
  have hb : (BitVec.ofNat 64 x - BitVec.ofNat 64 w) >>> 63 =
      BitVec.ofNat 64 (if x < w then 1 else if x < 2 ^ 63 then 0 else if x - w < 2 ^ 63 then 0 else 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (a := w) (by omega_using [hw]), Nat.shiftRight_eq_div_pow]
    split
    · rw [show (2 ^ 64 - w + x) % 2 ^ 64 = 2 ^ 64 - w + x by omega_arith,
        show (2 ^ 64 - w + x) / 2 ^ 63 = 1 by omega_arith]; rfl
    · rw [show (2 ^ 64 - w + x) % 2 ^ 64 = x - w by omega_arith]
      split
      · rw [Nat.div_eq_of_lt (by omega_arith)]; rfl
      · split
        · rw [Nat.div_eq_of_lt (by omega_arith)]; rfl
        · rw [show (x - w) / 2 ^ 63 = 1 by omega_arith]; rfl
  rw [ha, hb]
  by_cases h1 : x < w
  · rw [ite_eq_left (show x < 2 ^ 63 by omega_using [hw, h1]), ite_eq_left h1, ite_eq_left h1]; rfl
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : x < 2 ^ 63
    · rw [ite_eq_left h2, ite_eq_left h2]; rfl
    · rw [ite_eq_right h2, ite_eq_right h2]; split <;> rfl

/-- A step of the borrow chain: the borrow out of `k − (q + b)`. -/
theorem borrow_eq {k q b : Nat} (hk : k < 256) (hq : q < 256) (hb : b ≤ 1) :
    (BitVec.ofNat 64 k - (BitVec.ofNat 64 q + BitVec.ofNat 64 b)) >>> 63 =
      BitVec.ofNat 64 (if k < q + b then 1 else 0) := by
  rw [← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := k) (by omega_using [hk]), Nat.mod_eq_of_lt (a := q + b) (by omega_using [hq, hb]), Nat.shiftRight_eq_div_pow]
  split
  · rw [show (2 ^ 64 - (q + b) + k) % 2 ^ 64 = 2 ^ 64 - (q + b) + k by omega_arith,
      show (2 ^ 64 - (q + b) + k) / 2 ^ 63 = 1 by omega_arith]
    rfl
  · rw [show (2 ^ 64 - (q + b) + k) % 2 ^ 64 = k - (q + b) by omega_arith, Nat.div_eq_of_lt (by omega_using [hk])]
    rfl

/-- `(0 − x) >> 63` for `x < 2⁶³`: whether `x` is not zero. -/
theorem nz_eq {x : Nat} (hx : x < 2 ^ 63) :
    (BitVec.ofNat 64 0 - BitVec.ofNat 64 x) >>> 63 = BitVec.ofNat 64 (if x = 0 then 0 else 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := x) (by omega_using [hx]), Nat.shiftRight_eq_div_pow]
  split
  · subst x; rfl
  · rw [show (2 ^ 64 - x + 0 % 2 ^ 64) % 2 ^ 64 = 2 ^ 64 - x by omega_arith,
      show (2 ^ 64 - x) / 2 ^ 63 = 1 by omega_arith]
    rfl

/-- The test of `q > 1` from its significant octets `w` and the first `t`:
`w ≠ 0`, and `w ≥ 2` or `t ≥ 2`. -/
theorem valid_eq {w t : Nat} (hw : w < 256) (ht : t < 256) :
    BitVec.ofNat 64 (if (w >>> 1 ||| t >>> 1) = 0 then 0 else 1) &&&
        BitVec.ofNat 64 (if w = 0 then 0 else 1) =
      BitVec.ofNat 64 (if w ≠ 0 ∧ (2 ≤ w ∨ 2 ≤ t) then 1 else 0) := by
  have e : (w >>> 1 ||| t >>> 1) = 0 ↔ w < 2 ∧ t < 2 := by
    rw [Nat.or_eq_zero_iff, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]; omega_using []
  generalize (w >>> 1 ||| t >>> 1) = z at e ⊢
  have e1 := e.mp
  have e2 := e.mpr
  split <;> split <;> split <;> first | rfl | (exfalso; omega_arith)

end VG.Proof.Dsa.PPC64LE.Rnd

end

end

/-!
# DSA sampling on PPC64LE: a draw into the nonce

`copy_ok`: `copy` copies the `W` octets of the tape from `used` to the
nonce's last `W` octets, the first masked by `M` (`cpy`), changing memory
there only, and adds `W` to `used`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Rnd

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random
open VG.Proof.Mont

/-- The registers `copy` writes. -/
def copyRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r25]

/-- The draw's octet `j` as the nonce gets it: the first masked. -/
def cpy (bs : List Byte) (M : Nat) (j : Nat) : Byte :=
  if j = 0 then bs.getD 0 0 &&& BitVec.ofNat 8 M else bs.getD j 0

/-- The frame's offset of the draw in the nonce. -/
abbrev SE.o (E : SE) : Nat := oNonce + (E.ql - E.W)

theorem copy_ok {E : SE} {R : List Byte} {s : State} {u : Nat} (hE : E.Ok) (h : SEnv E R s)
    (h25 : s.gpr .r25 = BitVec.ofNat 64 u) (hu : u + E.W ≤ E.rl) :
    WP isa copy s fun t =>
      (t.gpr .r25 = BitVec.ofNat 64 (u + E.W) ∧ Outside E.F E.o E.W s.mem t.mem ∧
        ∀ j < E.W, t.mem (off E.F (E.o + j)) = cpy (R.drop u) E.M j) ∧ Keep copyRegs s t := by
  have hf := hE.fnw
  have hW1 := hE.W1
  have hWq := hE.Wq
  have hql := hE.ql
  have hrn := hE.rnw
  have hM := hE.M
  simp only [frameBytes] at hf
  refine WP.keep copyRegs ?_ (by decide)
  unfold copy Precompute.countLoop
  have hi : WP isa (.block copyInit) s fun s₁ =>
      s₁.gpr .r3 = off E.rand u ∧ s₁.gpr .r4 = off E.F E.o ∧ s₁.gpr .r5 = BitVec.ofNat 64 E.W ∧
        s₁.gpr .r6 = BitVec.ofNat 64 E.M ∧ s₁.gpr .r25 = BitVec.ofNat 64 u ∧
        s₁.gpr .r28 = BitVec.ofNat 64 E.W ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    unfold copyInit
    prun [h.r23, h25, h.r21, h.r28, h.r29, h.sp, exec_addSp (show oNonce < 2 ^ 15 by decide), BitVec.add_zero]
    rw [VG.Offset.add_ofNat_sub _ (by simp only [oNonce]; omega_using [hWq])]
    rw [show oNonce + E.ql - E.W = oNonce + (E.ql - E.W) by omega_using [hWq]]
  refine WP.seq (WP.mono hi fun s₁ ⟨i3, i4, i5, i6, i25, i28, im, ird, iwr⟩ => ?_)
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r3 = off E.rand (u + i) ∧ t.gpr .r4 = off E.F (E.o + i) ∧
      t.gpr .r6 = BitVec.ofNat 64 (if i = 0 then E.M else 255) ∧ t.gpr .r25 = BitVec.ofNat 64 u ∧
      t.gpr .r28 = BitVec.ofNat 64 E.W ∧ Outside E.F E.o E.W s.mem t.mem ∧
      (∀ j < i, t.mem (off E.F (E.o + j)) = cpy (R.drop u) E.M j) ∧ t.rd = s.rd ∧ t.wr = s.wr
  refine WP.seq (WP.mono (wp_countdown (body := .block (copyByte ++ ([.subi .r5 .r5 1] : List Instr)))
    (cnt := .r5) (N := E.W) (by omega_using [hWq, hql]) (by omega_using [hW1]) Inv
    (fun i hi t ⟨t3, t4, t6, t25, t28, tout, tb, trd, twr⟩ _ => ?_)
    ⟨by rw [i3, Nat.add_zero], by rw [i4, Nat.add_zero], by rw [i6]; rfl, i25, i28, by rw [im]; exact Outside.refl _ _ _ _,
      fun _ h => absurd h (by omega_using []), ird, iwr⟩ i5) fun t ht => ?_)
  · have hrd : InRegions (t.rd ++ t.wr) (off E.rand (u + i)) 1 := by
      rw [trd, twr]; exact h.rr _ (by omega_using [hu, hi])
    have hwr : InRegions t.wr (off E.F (E.o + i)) 1 := by
      have := (h.nw.congr (twr.trans rfl)).st (d := E.ql - E.W + i) (n := 1) (by omega_using [hWq, hql, hi])
      rwa [off_off, show oNonce + (E.ql - E.W + i) = E.o + i by simp only [SE.o]; omega_using []] at this
    have hb : t.mem (off E.rand (u + i)) = R.getD (u + i) 0 := by
      rw [tout _ (outside_of_disj hE hE.dR (VG.Offset.contains_base _ (by omega_using [hu, hi]) (by omega_using [hu, hrn, hi])) (o := E.ql - E.W)
        (n := E.W) (by omega_using [hWq, hql])), h.byte (by omega_using [hu, hi])]
    generalize hv : (BitVec.ofNat 64 (t.mem (off E.rand (u + i))).toNat &&&
      BitVec.ofNat 64 (if i = 0 then E.M else 255)).setWidth 8 = v
    have hst : WP isa (.block (copyByte ++ ([.subi .r5 .r5 1] : List Instr))) t fun t' =>
        t'.gpr .r3 = off E.rand (u + i + 1) ∧ t'.gpr .r4 = off E.F (E.o + i + 1) ∧
          t'.gpr .r6 = BitVec.ofNat 64 255 ∧ t'.gpr .r5 = t.gpr .r5 - BitVec.ofNat 64 1 ∧
          t'.gpr .r25 = t.gpr .r25 ∧ t'.gpr .r28 = t.gpr .r28 ∧
          t'.mem = t.mem.write (off E.F (E.o + i)) 1 v ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
      unfold copyByte
      prun [t3, t4, t6, exec_lbz' (show Reg.r3 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
        exec_stb (show Reg.r4 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hrd, hwr, BitVec.add_zero,
        read_byte64, hv]
    have hw1 := write1_outside t.mem E.F (d := E.o + i) v (by simp only [SE.o, oNonce]; omega_using [hWq, hql, hi])
    refine WP.mono hst fun t' ⟨a3, a4, a6, a5, a25, a28, am, ard, awr⟩ => ⟨⟨by rw [a3, Nat.add_assoc],
      by rw [a4, Nat.add_assoc], ?_, a25.trans t25, a28.trans t28, ?_, ?_, ard.trans trd, awr.trans twr⟩, a5⟩
    · rw [a6, ite_eq_right (by omega_using [])]
    · rw [am]; exact tout.trans (hw1.mono (by omega_using []) (by omega_using [hi]))
    · intro j hj
      rw [am]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [hw1 _ (by rw [Mont.ofs_off0 E.F (by simp only [SE.o, oNonce]; omega_arith)]; omega_using [hj])]; exact tb j hj
      · have hd : ∀ k, (R.drop u).getD k 0 = R.getD (u + k) 0 := fun k => by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
        rw [write1_self, ← hv, hb, cpy, hd, hd]
        split
        · rename_i hj0; subst hj0
          exact mask_byte _ hM
        · rename_i hj0
          exact mask_byte_ff _
  · obtain ⟨-, -, -, t25, t28, tout, tb, -, -⟩ := ht
    prun [t25, t28, ← BitVec.ofNat_add]
    exact ⟨tout, tb⟩

end VG.Proof.Dsa.PPC64LE.Rnd

end

end

/-!
# DSA sampling on PPC64LE: the sampler's data of q

`SE.Q E qb`: the sampler's data are those of q's octets `qb`, for `q > 1`:
the width of a draw is `drawBytes q` (`Q.draw`), q's significant octets
decode to q (`Q.qs_val`), and a draw copied with its first octet masked
(`cpy`) decodes to the specification's candidate (`Q.cand`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Rnd

open VG
open VG.Proof.Dsa (significant qSigOf)

/-- `E` is the sampler's data for q's octets `qb`, and `q > 1`. -/
structure SE.Q (E : SE) (qb : List Byte) : Prop where
  len : qb.length = E.ql
  W : E.W = (significant qb).1
  M : E.M = maskOf (significant qb).2.toNat
  qs : E.qs = qSigOf qb
  gt : 1 < Spec.Dsa.decodeBE qb

theorem SE.Q.draw {E : SE} {qb : List Byte} (h : E.Q qb) :
    Spec.Dsa.Random.drawBytes (Spec.Dsa.decodeBE qb) = E.W := by
  rw [Dsa.random_drawBytes_scan, h.W]

theorem SE.Q.qs_val {E : SE} {qb : List Byte} (h : E.Q qb) :
    Spec.Dsa.decodeBE E.qs = Spec.Dsa.decodeBE qb := by
  rw [h.qs, qSigOf, Dsa.random_significant_drop]

theorem SE.Q.W_pos {E : SE} {qb : List Byte} (h : E.Q qb) : 0 < E.W := by
  have := (Dsa.random_valid_scan qb).mp h.gt
  rw [h.W]; omega_using [this]

/-- The draw as the nonce gets it. -/
abbrev cpyList (bs : List Byte) (M W : Nat) : List Byte := (List.range W).map (cpy bs M)

theorem cpyList_take (bs : List Byte) (M W : Nat) : cpyList (bs.take W) M W = cpyList bs M W := by
  simp only [cpyList, List.map_inj_left, List.mem_range]
  intro j hj
  simp only [cpy, List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hj]
  split
  · rename_i h0; subst h0; rw [ite_eq_left hj]
  · rfl

theorem cpyList_cons (b : Byte) (bs : List Byte) (M : Nat) :
    cpyList (b :: bs) M (bs.length + 1) = (b &&& BitVec.ofNat 8 M) :: bs := by
  apply List.ext_getElem
  · simp [cpyList]
  · intro i h₁ h₂
    simp only [cpyList, List.getElem_map, List.getElem_range, cpy]
    cases i with
    | zero => simp
    | succ i =>
      simp only [Nat.add_one_ne_zero, ite_false, List.getElem_cons_succ]
      simp only [List.length_cons] at h₂
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < bs.length by omega_using [h₂])]

/-- The copied draw decodes to the candidate. -/
theorem SE.Q.cand {E : SE} {qb : List Byte} (h : E.Q qb) {bs : List Byte} (hl : E.W ≤ bs.length) :
    Spec.Dsa.decodeBE (cpyList bs E.M E.W) = Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE qb) (bs.take E.W) := by
  have hW := h.W_pos
  rw [← cpyList_take]
  obtain ⟨b, rest, he⟩ : ∃ b rest, bs.take E.W = b :: rest := by
    cases hc : bs.take E.W with
    | nil =>
      have := congrArg List.length hc
      rw [List.length_take, Nat.min_eq_left hl, List.length_nil] at this; omega
    | cons b rest => exact ⟨b, rest, rfl⟩
  have hrl : rest.length + 1 = E.W := by
    have := congrArg List.length he
    rw [List.length_take, List.length_cons, Nat.min_eq_left hl] at this; omega_using [this]
  rw [he, ← hrl, cpyList_cons, Dsa.random_candidate_mask qb b rest (by rw [hrl, h.W]), h.M]

end VG.Proof.Dsa.PPC64LE.Rnd
