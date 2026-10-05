import VerifiedGarbage.Proof.Ecdsa.AArch64.Flags
import VerifiedGarbage.Proof.Weierstrass.AArch64.Ladder
import VerifiedGarbage.Proof.Weierstrass.AArch64.Chain
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
import VerifiedGarbage.Proof.Weierstrass.Law3
import VerifiedGarbage.Proof.Framework.AArch64.Spill

/-!
# ECDSA on AArch64: the curve, the arguments and the working space

What the proof of `Impl.Ecdsa.AArch64.Cfg.sign` needs of a curve (`CfgOk`)
and of its arguments (`Pre`), for any curve of `n` words, and the state
`setup` leaves (`SetupPost`), as on x86-64 (`Proof/Ecdsa/X86_64/Layout.lean`).

The working space is the `8192` bytes at `scratch`: the saved registers in
`[0, 56)`, the slots `c.sl i = 64 + 8 n i` of `n` words for `i < nslots`, and
the tables of bits `bitsAt n j` (`64 n` bytes each, `j < 3`), which are
slots `nslots + 8 j` to `nslots + 8 j + 7`. Every offset the scalar's table
(`j = 0`) is read at is below `4096`, as `ldrb` needs.
-/

namespace VG.Proof.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

/-- The size of the working space, in bytes. -/
abbrev size : Nat := 8192

/-- What the proof of the code needs of a curve: its field and order are odd
and fit in `n` words (`n < 10`: the multiplications accumulate in
`x8`–`x15`), `G` is on the curve, `p < 2n` (so `x mod n` is one conditional
subtraction), the Montgomery constants are right, encodings are `8 n`
bytes, a hash of `8 n` bytes is not truncated, `n ≥ 4` words, the inversion
modulo `p` sound (`InvSound`, which `p` prime gives) with its batches and
constants right (`InvOk`), and modulo `n` too or the chain of `n - 2` right
(`fastN`), `n` even (the comb's
selection moves an entry's words in pairs), and `a = -3` (the complete formulas are those for it). The group law needs
more (`Weierstrass.Law`, which a prime field and no point of order 2 give:
`Weierstrass.Good.law`), which only the proofs of the results take. -/
structure CfgOk (c : Cfg) : Prop where
  n0 : 0 < c.n
  n10 : c.n < 10
  onG : onCurve c.C (G c.C) = true
  p_odd : c.C.p % 2 = 1
  n_odd : c.C.n % 2 = 1
  p_lt : c.C.p < 2 ^ (64 * c.n)
  n_lt : c.C.n < 2 ^ (64 * c.n)
  p_ge : 3 ≤ c.C.p
  n_ge : 3 ≤ c.C.n
  p_lt_2n : c.C.p < 2 * c.C.n
  minv_p : (c.C.p * (BitVec.ofNat 64 (minv c.C.p)).toNat + 1) % 2 ^ 64 = 0
  minv_n : (c.C.n * (BitVec.ofNat 64 (minv c.C.n)).toNat + 1) % 2 ^ 64 = 0
  red_p : c.MP'.ok c.C.p = true
  red_n : c.MN'.ok c.C.n = true
  n2 : c.n % 2 = 0
  len : c.C.len = 8 * c.n
  hash : 64 * c.n ≤ Spec.Ecdsa.nBits c.C
  n4 : 4 ≤ c.n
  sound_p : InvSound c.C.p
  inv_p : InvOk c.invP c.C.p
  inv_n : c.fastN = true → InvSound c.C.n ∧ InvOk c.invN c.C.n
  chain_n : c.fastN = false → chainCheck (slide (c.C.n - 2)).1 (slide (c.C.n - 2)).2 (c.C.n - 2) = true
  am3 : AM3 c.C

/-- The comb's tables (`Cfg.combWords`) at `T`: readable, held, not
wrapping around, and apart from the working space at `base`. -/
structure TblPre (c : Cfg) (s : State) (T base : Addr) : Prop where
  rd : (⟨T, 8 * c.combWords.length⟩ : Region) ∈ s.rd
  held : ∀ i < c.combWords.length, s.mem.readW (T + BitVec.ofNat 64 (8 * i)) 64 = c.combWords.getD i 0
  fit : T.toNat + 8 * c.combWords.length ≤ 2 ^ 64
  sc : Region.Disjoint ⟨T, 8 * c.combWords.length⟩ ⟨base, size⟩

/-- The arguments: `out = x0` (`16 n` bytes), `d = x1`, `digest = x2`,
`k = x3` (`8 n` bytes each) and `scratch = x4`, and the comb's tables at
the static `c.tsym` (`Artifact.consts`), readable and writable as the
contract says and apart from each other as it says. -/
structure Pre (c : Cfg) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x1, 8 * c.n⟩, ⟨s.gpr .x2, 8 * c.n⟩, ⟨s.gpr .x3, 8 * c.n⟩,
    ⟨s.syms c.tsym, 8 * c.combWords.length⟩]
  wr : s.wr = [⟨s.gpr .x0, 16 * c.n⟩, ⟨s.gpr .x4, size⟩]
  out_sc : Region.Disjoint ⟨s.gpr .x0, 16 * c.n⟩ ⟨s.gpr .x4, size⟩
  out_d : Region.Disjoint ⟨s.gpr .x0, 16 * c.n⟩ ⟨s.gpr .x1, 8 * c.n⟩
  out_digest : Region.Disjoint ⟨s.gpr .x0, 16 * c.n⟩ ⟨s.gpr .x2, 8 * c.n⟩
  out_k : Region.Disjoint ⟨s.gpr .x0, 16 * c.n⟩ ⟨s.gpr .x3, 8 * c.n⟩
  d_sc : Region.Disjoint ⟨s.gpr .x1, 8 * c.n⟩ ⟨s.gpr .x4, size⟩
  digest_sc : Region.Disjoint ⟨s.gpr .x2, 8 * c.n⟩ ⟨s.gpr .x4, size⟩
  k_sc : Region.Disjoint ⟨s.gpr .x3, 8 * c.n⟩ ⟨s.gpr .x4, size⟩
  out_fit : (s.gpr .x0).toNat + 16 * c.n ≤ 2 ^ 64
  sc_fit : (s.gpr .x4).toNat + size ≤ 2 ^ 64
  tbl : TblPre c s (s.syms c.tsym) (s.gpr .x4)

/-- What `setup` needs of its arguments (`Pre` gives it, and so can the
arguments of other functions that run it): the working space `scratch = x4`
writable, and `k = x3`, `d = x1` and `digest = x2` (`8 n` bytes each)
readable and apart from it. -/
structure SetupPre (c : Cfg) (s : State) : Prop where
  wr : (⟨s.gpr .x4, size⟩ : Region) ∈ s.wr
  k_in : ∀ e, e + 8 ≤ 8 * c.n → InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 e) 8
  d_in : ∀ e, e + 8 ≤ 8 * c.n → InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 e) 8
  digest_in : ∀ e, e + 8 ≤ 8 * c.n → InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 e) 8
  d_sc : Region.Disjoint ⟨s.gpr .x1, 8 * c.n⟩ ⟨s.gpr .x4, size⟩
  digest_sc : Region.Disjoint ⟨s.gpr .x2, 8 * c.n⟩ ⟨s.gpr .x4, size⟩
  k_sc : Region.Disjoint ⟨s.gpr .x3, 8 * c.n⟩ ⟨s.gpr .x4, size⟩
  sc_fit : (s.gpr .x4).toNat + size ≤ 2 ^ 64

theorem Pre.setup {c : Cfg} {s : State} (hp : Pre c s) (h7 : c.n < 10) : SetupPre c s where
  wr := by rw [hp.wr]; simp
  k_in := inRegions_words (by rw [hp.rd]; simp) (by omega)
  d_in := inRegions_words (by rw [hp.rd]; simp) (by omega)
  digest_in := inRegions_words (by rw [hp.rd]; simp) (by omega)
  d_sc := hp.d_sc
  digest_sc := hp.digest_sc
  k_sc := hp.k_sc
  sc_fit := hp.sc_fit

/-- The number in slot `i`. -/
abbrev sv (c : Cfg) (base : Addr) (s : State) (i : Nat) : Nat := wordsVal s.mem base (c.sl i) c.n

/-- What `setup` leaves, from the state `s₀` at entry, with the working space
at `base = x4`: `x0 = base`, `out` in `x20`, `x19` and `x20` in `[0, 16)`,
`k`, `d` and the hash in their slots, the constants in theirs, and the flag
all ones; only `x0`, `x1`, `x5` and `x20` and the working space changed. -/
structure SetupPost (c : Cfg) (s₀ : State) (base : Addr) (s : State) : Prop where
  scr : Scr s base size
  x20 : s.gpr .x20 = s₀.gpr .x0
  keep : KeepRegs [.x0, .x1, .x5, .x20] s₀ s
  unch : Unch base [(0, size)] s₀.mem s.mem
  saved : Spill.Saved base s₀.gpr Cfg.saved s.mem
  k : sv c base s K = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x3) (8 * c.n))
  d : sv c base s D = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x1) (8 * c.n))
  e : sv c base s E = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (8 * c.n))
  consts : ∀ ix ∈ c.consts, sv c base s ix.1 = ix.2
  flag : word s.mem base (c.sl FLAG) = BitVec.allOnes 64

/-! ## Slots -/

theorem sl_eq (c : Cfg) (i : Nat) : c.sl i = 64 + 8 * c.n * i := rfl

theorem bitsAt_eq (c : Cfg) (j : Nat) : bitsAt c.n j = 64 + 8 * c.n * 45 + 64 * c.n * j := rfl

theorem sl_mod8 (c : Cfg) (i : Nat) : c.sl i % 8 = 0 := by
  rw [sl_eq, Nat.mul_assoc]; omega

theorem bitsAt_mod8 (c : Cfg) (j : Nat) : bitsAt c.n j % 8 = 0 := by
  rw [bitsAt_eq, Nat.mul_assoc 8, Nat.mul_assoc 64]; omega

/-- Slots `i < j` are apart. -/
theorem sl_lt (c : Cfg) {i j : Nat} (h : i < j) : c.sl i + 8 * c.n ≤ c.sl j := by
  rw [sl_eq, sl_eq]
  have := Nat.mul_le_mul_left (8 * c.n) h
  rw [Nat.mul_succ] at this
  omega

theorem sl_apart (c : Cfg) {i j : Nat} (h : i ≠ j) :
    c.sl i + 8 * c.n ≤ c.sl j ∨ c.sl j + 8 * c.n ≤ c.sl i := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact Or.inl (sl_lt c h)
  · exact Or.inr (sl_lt c h)

theorem sl_inj (c : Cfg) (hn : 0 < c.n) {i j : Nat} (h : c.sl i = c.sl j) : i = j := by
  by_contra hij
  have := sl_apart c hij
  omega

/-- Every slot is in the working space. -/
theorem sl_le (c : Cfg) (hn : c.n < 10) {i : Nat} (hi : i < 45) : c.sl i + 8 * c.n ≤ size := by
  rw [sl_eq]
  have := Nat.mul_le_mul_left (8 * c.n) hi
  rw [Nat.mul_succ] at this
  have : 8 * c.n * 45 ≤ 8 * 9 * 45 := Nat.mul_le_mul_right _ (by omega)
  show _ ≤ 8192
  omega

/-- Every table is in the working space. -/
theorem bitsAt_le (c : Cfg) (hn : c.n < 10) {j : Nat} (hj : j < 3) : bitsAt c.n j + 64 * c.n ≤ size := by
  rw [bitsAt_eq]
  have := Nat.mul_le_mul_left (64 * c.n) hj
  rw [Nat.mul_succ] at this
  have : 8 * c.n * 45 ≤ 8 * 9 * 45 := Nat.mul_le_mul_right _ (by omega)
  have : 64 * c.n * 3 ≤ 64 * 9 * 3 := Nat.mul_le_mul_right _ (by omega)
  show _ ≤ 8192
  omega

/-- The table of the scalar's bits is in the first `4096` bytes of the working
space, where `ldrb` reaches. -/
theorem bitsAt0_le (c : Cfg) (hn : c.n < 10) : bitsAt c.n 0 + 64 * c.n ≤ 4096 := by
  rw [bitsAt_eq]
  have : 8 * c.n * 45 ≤ 8 * 9 * 45 := Nat.mul_le_mul_right _ (by omega)
  omega

end VG.Proof.Ecdsa.AArch64
