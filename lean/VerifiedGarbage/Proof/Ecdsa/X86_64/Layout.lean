import VerifiedGarbage.Proof.Weierstrass.X86_64.Ladder
import VerifiedGarbage.Proof.Weierstrass.X86_64.Flags
import VerifiedGarbage.Proof.Weierstrass.X86_64.BytesLen
import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Proof.Weierstrass.CombW
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
import VerifiedGarbage.Proof.Weierstrass.Law3
import VerifiedGarbage.Proof.Weierstrass.Booth

/-!
# ECDSA on x86-64: the curve, the arguments and the working space

What the proof of `Impl.Ecdsa.X86_64.Cfg.sign` needs of a curve (`CfgOk`)
and of its arguments (`Pre`), for any curve of `n` words, and the state
`setup` leaves (`SetupPost`).

The working space is the `8192` bytes at `scratch`: the saved registers in
`[0, 48)`, the slots `c.sl i = 64 + 8 n i` of `n` words for `i < nslots`, and
the tables of bits `bitsAt n j` (`64 n` bytes each, `j < 3`, each followed
by a word that the comb's last digit may read).

A curve with a fixed-base comb (`Cfg.comb`) has its tables in a `static`
(`Cfg.combConsts`), which the calling convention gives
(`Abi.withConsts`): after the arguments in the regions the code may read, at
the static's address, holding the tables' words, and apart from what it may
write (`TblsHeld`).
-/

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

/-- The size of the working space, in bytes. -/
abbrev size : Nat := 8192

/-- What the proof needs of a curve's comb: digits of `w ≤ 8` bits, whose
`combJ` windows cover the scalar's `64 n` bits and at most a word more (the
word past its table of bits). That its tables are right (`CombTbls`) the
proofs of the results take with the group law. -/
structure CombOk (c : Cfg) (d : CombData) : Prop where
  w : 1 ≤ d.w ∧ d.w < 9
  cover : 64 * c.n ≤ d.w * c.combJ d.w ∧ d.w * c.combJ d.w ≤ 64 * c.n + 8

/-- The comb's tables, if the curve has one, are right (`CombOkW`, which a
curve's own facts prove, with its group law), and for the comb with Booth's
digits (`jac`) the curve's order is what it needs (`BoothOk`). -/
def CombTbls (c : Cfg) : Prop :=
  ∀ d, c.comb = some d → CombOkW c.C d.w (c.combJ d.w) d.tbl d.start ∧
    (d.jac = true → BoothOk c.C d.w (c.combJ d.w) (2 ^ (64 * c.n)))

/-- What the proof of the code needs of a curve: its field and order are odd
and fit in `n` words (`n < 10`, so that the slots and tables fit in the
working space), `G` is on the curve, `p < 2n` (so `x mod n` is one
conditional subtraction), the Montgomery constants (and the reduction's words
of `(p + 1) / 2⁶⁴` if `p ≡ -1 (mod 2⁶⁴)`, `red_p`) are right, encodings are
`len` bytes in `n` words (`8 (n - 1) < len ≤ 8 n`, at least one word), and
the bits of a hash of `len` bytes that are not `e`'s (`c.sh`, 0 unless `n`
has fewer than `8 len` bits) are fewer than 32, and for up to nine words
(from four) the inversion by divsteps modulo `p` sound with its batches and
constants right, and modulo `n` if `fastN`. The group law needs more (`Weierstrass.Law`, which a prime field
and no point of order 2 give: `Weierstrass.Good.law`), which only the proofs
of the results take. -/
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
  red_p : c.MP'.ok c.C.p = true
  minv_n : (c.C.n * (BitVec.ofNat 64 (minv c.C.n)).toNat + 1) % 2 ^ 64 = 0
  len8 : 8 ≤ c.C.len
  len_lo : 8 * c.n < c.C.len + 8
  len_hi : c.C.len ≤ 8 * c.n
  sh : c.sh < 32
  /-- The comb, if the curve has one. -/
  comb : ∀ d, c.comb = some d → CombOk c d
  /-- For up to nine words, the inversion by divsteps modulo `p` sound
  (`InvSound`, which a prime gives) with its batches and constants right
  (`InvOk`), and modulo `n` too if `fastN`. -/
  inv : c.n ≤ 9 → 4 ≤ c.n ∧ InvSound c.C.p ∧ InvOk c.invP c.C.p
  inv_n : c.fastN = true → c.n ≤ 9 → InvSound c.C.n ∧ InvOk c.invN c.C.n
  /-- `a = -3`, for the window method's formulas, and for up to six words an
  even number of them, for its selection of 16 bytes at a time. -/
  am3 : AM3 c.C
  even : c.n ≤ 6 → c.n % 2 = 0

/-- The comb's tables, if any, at the address of their static: held, not
wrapping around, and apart from the regions `wr`, as `Abi.withConsts`
says. -/
def TblsHeld (c : Cfg) (s : State) (wr : List Region) : Prop :=
  Abi.constsHeld s.mem (fun n => s.syms n) c.combConsts ∧
    ∀ t ∈ Abi.constRegions (fun n => s.syms n) c.combConsts, t.base.toNat + t.len ≤ 2 ^ 64 ∧
      ∀ r ∈ wr, t.Disjoint r

/-- The arguments: `out = rdi` (`2 len` bytes), `d = rsi`, `digest = rdx`,
`k = rcx` (`len` bytes each) and `scratch = r8`, readable and writable as
the contract says and apart from each other as it says, and the comb's
tables, if any. -/
structure Pre (c : Cfg) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .rsi, c.C.len⟩, ⟨s.gpr .rdx, c.C.len⟩, ⟨s.gpr .rcx, c.C.len⟩] ++
    Abi.constRegions (fun n => s.syms n) c.combConsts
  wr : s.wr = [⟨s.gpr .rdi, 2 * c.C.len⟩, ⟨s.gpr .r8, size⟩]
  out_sc : Region.Disjoint ⟨s.gpr .rdi, 2 * c.C.len⟩ ⟨s.gpr .r8, size⟩
  out_d : Region.Disjoint ⟨s.gpr .rdi, 2 * c.C.len⟩ ⟨s.gpr .rsi, c.C.len⟩
  out_digest : Region.Disjoint ⟨s.gpr .rdi, 2 * c.C.len⟩ ⟨s.gpr .rdx, c.C.len⟩
  out_k : Region.Disjoint ⟨s.gpr .rdi, 2 * c.C.len⟩ ⟨s.gpr .rcx, c.C.len⟩
  d_sc : Region.Disjoint ⟨s.gpr .rsi, c.C.len⟩ ⟨s.gpr .r8, size⟩
  digest_sc : Region.Disjoint ⟨s.gpr .rdx, c.C.len⟩ ⟨s.gpr .r8, size⟩
  k_sc : Region.Disjoint ⟨s.gpr .rcx, c.C.len⟩ ⟨s.gpr .r8, size⟩
  out_fit : (s.gpr .rdi).toNat + 2 * c.C.len ≤ 2 ^ 64
  sc_fit : (s.gpr .r8).toNat + size ≤ 2 ^ 64
  tbls : TblsHeld c s s.wr

/-- What `setup` needs of its arguments (`Pre` gives it, and so can the
arguments of other functions that run it): the working space `scratch = r8`
writable, and `k = rcx`, `d = rsi` and `digest = rdx` (`len` bytes each)
readable and apart from it. -/
structure SetupPre (c : Cfg) (s : State) : Prop where
  wr : (⟨s.gpr .r8, size⟩ : Region) ∈ s.wr
  k_in : ∀ e, e + 8 ≤ c.C.len → InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofNat 64 e) 8
  d_in : ∀ e, e + 8 ≤ c.C.len → InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 e) 8
  digest_in : ∀ e, e + 8 ≤ c.C.len → InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 e) 8
  d_sc : Region.Disjoint ⟨s.gpr .rsi, c.C.len⟩ ⟨s.gpr .r8, size⟩
  digest_sc : Region.Disjoint ⟨s.gpr .rdx, c.C.len⟩ ⟨s.gpr .r8, size⟩
  k_sc : Region.Disjoint ⟨s.gpr .rcx, c.C.len⟩ ⟨s.gpr .r8, size⟩
  sc_fit : (s.gpr .r8).toNat + size ≤ 2 ^ 64

theorem Pre.setup {c : Cfg} {s : State} (hp : Pre c s) : SetupPre c s where
  wr := by rw [hp.wr]; simp
  k_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.out_fit; omega)
  d_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.out_fit; omega)
  digest_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.out_fit; omega)
  d_sc := hp.d_sc
  digest_sc := hp.digest_sc
  k_sc := hp.k_sc
  sc_fit := hp.sc_fit

/-- The number in slot `i`. -/
abbrev sv (c : Cfg) (base : Addr) (s : State) (i : Nat) : Nat := wordsVal s.mem base (c.sl i) c.n

/-- The bits slot `i` is shifted right by when `setupWith hs` shifts slot
`hs`: `sh` for that slot, 0 for the others. -/
abbrev shAt (c : Cfg) (hs : Option Nat) (i : Nat) : Nat := if hs = some i then c.sh else 0

theorem shAt_none (c : Cfg) (i : Nat) : shAt c none i = 0 := rfl
theorem shAt_self (c : Cfg) (i : Nat) : shAt c (some i) i = c.sh := ite_eq_left_of_eq_true _ _ (eq_true rfl)
theorem shAt_E_D (c : Cfg) : shAt c (some E) D = 0 := rfl
theorem shAt_E_K (c : Cfg) : shAt c (some E) K = 0 := rfl
theorem shAt_D_E (c : Cfg) : shAt c (some D) E = 0 := rfl
theorem shAt_D_K (c : Cfg) : shAt c (some D) K = 0 := rfl

/-- What `setupWith hs` leaves, from the state `s₀` at entry, with the
working space at `base = r8`: `rdi = base`, `out` in `rsi`, the callee-saved
registers in `[0, 48)`, `k`, `d` and the hash in their slots (the one in
slot `hs` shifted right by `sh`), the constants in theirs, and the flag all
ones; only `rax`, `rdi`, `r14`, `rsi` and `rdx` and the working space
changed. -/
structure SetupPost (c : Cfg) (hs : Option Nat) (s₀ : State) (base : Addr) (s : State) : Prop where
  scr : Scr s base size
  rsi : s.gpr .rsi = s₀.gpr .rdi
  keep : KeepRegs [.rax, .rdi, .r14, .rsi, .rdx] s₀ s
  unch : Unch base [(0, size)] s₀.mem s.mem
  saved : Spill.Saved s.mem base s₀.gpr Cfg.saved
  k : sv c base s K = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rcx) c.C.len)
  d : sv c base s D = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rsi) c.C.len) >>> shAt c hs D
  e : sv c base s E = ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdx) c.C.len) >>> shAt c hs E
  consts : ∀ ix ∈ c.consts, sv c base s ix.1 = ix.2
  flag : word s.mem base (c.sl FLAG) = BitVec.allOnes 64

/-! ## Slots -/

theorem sl_eq (c : Cfg) (i : Nat) : c.sl i = 64 + 8 * c.n * i := rfl

theorem bitsAt_eq (c : Cfg) (j : Nat) : bitsAt c.n j = 64 + 8 * c.n * 45 + (64 * c.n + 8) * j := rfl

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

/-- Every slot and table is in the working space. -/
theorem sl_le (c : Cfg) (hn : c.n < 10) {i : Nat} (hi : i < 45) : c.sl i + 8 * c.n ≤ size := by
  rw [sl_eq]
  have := Nat.mul_le_mul_left (8 * c.n) hi
  rw [Nat.mul_succ] at this
  have : 8 * c.n * 45 ≤ 8 * 9 * 45 := Nat.mul_le_mul_right _ (by omega)
  show _ ≤ 8192
  omega

theorem bitsAt_le (c : Cfg) (hn : c.n < 10) {j : Nat} (hj : j < 3) : bitsAt c.n j + 64 * c.n ≤ size := by
  rw [bitsAt_eq]
  have := Nat.mul_le_mul_left (64 * c.n + 8) hj
  rw [Nat.mul_succ] at this
  show _ ≤ 8192
  omega

/-- The word past a table of bits is in the working space too. -/
theorem bitsAt_le_pad (c : Cfg) (hn : c.n < 10) {j : Nat} (hj : j < 3) :
    bitsAt c.n j + 64 * c.n + 8 ≤ size := by
  rw [bitsAt_eq]
  have := Nat.mul_le_mul_left (64 * c.n + 8) hj
  rw [Nat.mul_succ] at this
  show _ ≤ 8192
  omega

end VG.Proof.Ecdsa.X86_64
