module

public import VerifiedGarbage.Impl.Dsa.RISCV64.Random
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Spec.Rsa.Contract
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Dsa.DomainShape
import VerifiedGarbage.Proof.Dsa.RandomRange
import VerifiedGarbage.Proof.Dsa.RandomEncoding
public import VerifiedGarbage.Proof.Dsa.RandomBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Spec.Dsa.Random
import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.RsaPss
public import VerifiedGarbage.TCB.Mem

/-! ### `Dsa.RISCV64.RndMath`, which this module and modules that import it used -/

section

/-!
# DSA sampling on RISC-V: the arithmetic of the registers

As on PPC64LE (`Proof/Dsa/PPC64LE/Random/Q.lean`).

What the sampler's instructions compute, on 64-bit registers: the mask of
q's first significant octet (`smear_eq`, its bits smeared right), a masked
octet (`mask_byte`), the test of a short tape (`short_eq`), a step of the
borrow chain (`borrow_eq`), and the test of `q > 1` (`valid_eq`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.Rnd

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

end VG.Proof.Dsa.RISCV64.Rnd

end

end

/-!
# DSA sampling on RISC-V: the sampler's state

As on PPC64LE (`Proof/Dsa/PPC64LE/Random/Env.lean` and `Q.lean`). `SE`:
what the sampler works with, all public: the frame's stack pointer `F` (the
nonce at `F + oNonce`), the tape (`rl` octets at `rand`), q's significant
octets (`W` of them at `qp`, `qs`), `p_len` and `q_len` (in `s2`) and the
mask `M` of the first one's bits. `SEnv E R s`: the registers hold them,
the nonce is writable, the tape and q readable, and memory holds the tape
`R` and `qs`. A change of memory in the nonce only keeps `SEnv`
(`SEnv.step`). `SE.Q`: `E` is the data of q's octets.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.Rnd

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Proof.Mont
open VG.Proof.Dsa (significant qSigOf)

/-- A run keeps the stack pointer. -/
theorem wp_sp {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun t => Q t ∧ t.sp = s.sp :=
  let ⟨tr, t, e, q⟩ := h
  ⟨tr, t, e, q, Exec.sp e⟩

/-- The lengths in `s2`. -/
abbrev lens (pl ql : Nat) : BitVec 64 := BitVec.ofNat 64 (pl + 65536 * ql)

theorem lenQ_eq {pl ql : Nat} (hp : pl < 65536) (hq : ql < 65536) :
    lens pl ql >>> 16 = BitVec.ofNat 64 ql := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show pl + 65536 * ql < 2 ^ 64 by omega_using [hp, hq]), Nat.mod_eq_of_lt (show ql < 2 ^ 64 by omega_using [hq])]
  omega_using [hp]

theorem lenP_eq {pl ql : Nat} (hp : pl < 65536) (hq : ql < 65536) :
    lens pl ql <<< 48 >>> 48 = BitVec.ofNat 64 pl := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show pl + 65536 * ql < 2 ^ 64 by omega_using [hp, hq]), Nat.mod_eq_of_lt (show pl < 2 ^ 64 by omega_using [hp])]
  simp only [Nat.reducePow]
  omega_using [hp]

/-- The sampler's public data. -/
structure SE where
  F : Addr
  rand : Addr
  rl : Nat
  qp : Addr
  pl : Nat
  ql : Nat
  W : Nat
  M : Nat
  qs : List Byte

/-- The nonce. -/
abbrev SE.N (E : SE) : Addr := off E.F oNonce

/-- The nonce's region. -/
abbrev SE.NR (E : SE) : Region := ⟨E.N, 32⟩

structure SE.Ok (E : SE) : Prop where
  pl : E.pl < 65536
  ql : E.ql ≤ 32
  W1 : 1 ≤ E.W
  Wq : E.W ≤ E.ql
  M : E.M < 256
  qs : E.qs.length = E.W
  rnw : E.rand.toNat + E.rl ≤ 2 ^ 64
  rl : E.rl < 2 ^ 64
  qnw : E.qp.toNat + E.W ≤ 2 ^ 64
  fnw : E.F.toNat + frameBytes ≤ 2 ^ 64
  fal : E.F.toNat % 8 = 0
  dR : (⟨E.rand, E.rl⟩ : Region).Disjoint E.NR
  dQ : (⟨E.qp, E.W⟩ : Region).Disjoint E.NR

/-- A state of the sampler, with the tape `R`. -/
structure SEnv (E : SE) (R : List Byte) (s : State) : Prop where
  sp : s.sp = E.F
  s2 : s.gpr .s2 = lens E.pl E.ql
  s3 : s.gpr .s3 = E.rand
  s4 : s.gpr .s4 = BitVec.ofNat 64 E.rl
  s7 : s.gpr .s7 = E.qp
  s8 : s.gpr .s8 = BitVec.ofNat 64 E.W
  s9 : s.gpr .s9 = BitVec.ofNat 64 E.M
  nw : Scr s E.N 32
  rr : ∀ i < E.rl, InRegions (s.rd ++ s.wr) (off E.rand i) 1
  qr : ∀ i < E.W, InRegions (s.rd ++ s.wr) (off E.qp i) 1
  R : Spec.Rsa.bytesAt s.mem E.rand E.rl = R
  Q : Spec.Rsa.bytesAt s.mem E.qp E.W = E.qs

/-- The registers `SEnv` fixes. -/
def envRegs : List Reg := [.s2, .s3, .s4, .s7, .s8, .s9]

/-- An address of a region apart from the nonce is not in the frame's
octets `[oNonce + o, oNonce + o + n)` within the nonce. -/
theorem outside_of_disj {E : SE} (hE : E.Ok) {r : Region} (hd : r.Disjoint E.NR) {x : Addr}
    (hx : r.Contains x 1) {o n : Nat} (hon : o + n ≤ 32) :
    ofs E.F x < oNonce + o ∨ oNonce + o + n ≤ ofs E.F x := by
  have hf := hE.fnw
  by_contra hc
  apply hd x hx
  simp only [Region.Contains, SE.N, off]
  rw [VG.Offset.toNat_sub_add x E.F (by simp only [oNonce]; omega_using [])]
  simp only [ofs, oNonce, frameBytes] at hc hf ⊢
  rw [show 2 ^ 64 - 32 + (x - E.F).toNat = (x - E.F).toNat - 32 + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega_using [])]
  omega

/-- The octets of a region apart from the nonce are kept by a change in it. -/
theorem bytes_kept {E : SE} (hE : E.Ok) {A : Addr} {k : Nat} (hd : (⟨A, k⟩ : Region).Disjoint E.NR)
    (hnw : A.toNat + k ≤ 2 ^ 64) {o n : Nat} (hon : o + n ≤ 32) {m m' : Mem}
    (ho : Outside E.F (oNonce + o) n m m') : Spec.Rsa.bytesAt m' A k = Spec.Rsa.bytesAt m A k := by
  simp only [Spec.Rsa.bytesAt, List.map_inj_left, List.mem_range]
  intro i hi
  refine ho _ (outside_of_disj hE hd ?_ hon)
  exact VG.Offset.contains_base A (by omega_using [hi]) (by omega_using [hnw, hi])

/-- `SEnv` after code that keeps its registers and the stack pointer and
changes memory in the nonce only. -/
theorem SEnv.step {E : SE} {R : List Byte} {s t : State} {rs : List Reg} (hE : E.Ok) (h : SEnv E R s)
    (k : Keep rs s t) (hsp : t.sp = s.sp) {o n : Nat} (hon : o + n ≤ 32)
    (ho : Outside E.F (oNonce + o) n s.mem t.mem)
    (hr : ∀ r ∈ envRegs, r ∉ rs := by decide) : SEnv E R t where
  sp := hsp.trans h.sp
  s2 := (k.gpr (hr _ (by decide))).trans h.s2
  s3 := (k.gpr (hr _ (by decide))).trans h.s3
  s4 := (k.gpr (hr _ (by decide))).trans h.s4
  s7 := (k.gpr (hr _ (by decide))).trans h.s7
  s8 := (k.gpr (hr _ (by decide))).trans h.s8
  s9 := (k.gpr (hr _ (by decide))).trans h.s9
  nw := h.nw.congr k.2.2
  rr := by rw [k.2.1, k.2.2]; exact h.rr
  qr := by rw [k.2.1, k.2.2]; exact h.qr
  R := (bytes_kept hE hE.dR hE.rnw hon ho).trans h.R
  Q := (bytes_kept hE hE.dQ hE.qnw hon ho).trans h.Q

/-- `SEnv` after code that keeps its registers, the stack pointer and memory. -/
theorem SEnv.stepM {E : SE} {R : List Byte} {s t : State} {rs : List Reg} (hE : E.Ok) (h : SEnv E R s)
    (k : Keep rs s t) (hsp : t.sp = s.sp) (hm : t.mem = s.mem)
    (hr : ∀ r ∈ envRegs, r ∉ rs := by decide) : SEnv E R t :=
  h.step hE k hsp (o := 0) (n := 0) (by omega_using []) (by rw [hm]; exact Outside.refl _ _ _ _) hr

/-- The tape's octet `i`. -/
theorem SEnv.byte {E : SE} {R : List Byte} {s : State} (h : SEnv E R s) {i : Nat} (hi : i < E.rl) :
    s.mem (off E.rand i) = R.getD i 0 := by
  rw [← h.R]
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hi]

/-- q's significant octet `i`. -/
theorem SEnv.qbyte {E : SE} {R : List Byte} {s : State} (h : SEnv E R s) {i : Nat} (hi : i < E.W) :
    s.mem (off E.qp i) = E.qs.getD i 0 := by
  rw [← h.Q]
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hi]

theorem SEnv.R_length {E : SE} {R : List Byte} {s : State} (h : SEnv E R s) : R.length = E.rl := by
  rw [← h.R, VG.Proof.Bignum.bytesAt_length]

theorem SEnv.lenQ {E : SE} {R : List Byte} {s : State} (hE : E.Ok) (h : SEnv E R s) :
    s.gpr .s2 >>> 16 = BitVec.ofNat 64 E.ql := by
  rw [h.s2]; exact lenQ_eq hE.pl (by have := hE.ql; omega_using [this])

/-! ## The data of q -/

/-- The draw's octet `j` as the nonce gets it: the first masked. -/
def cpy (bs : List Byte) (M : Nat) (j : Nat) : Byte :=
  if j = 0 then bs.getD 0 0 &&& BitVec.ofNat 8 M else bs.getD j 0

/-- The frame's offset of the draw in the nonce. -/
abbrev SE.o (E : SE) : Nat := oNonce + (E.ql - E.W)

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

end VG.Proof.Dsa.RISCV64.Rnd
