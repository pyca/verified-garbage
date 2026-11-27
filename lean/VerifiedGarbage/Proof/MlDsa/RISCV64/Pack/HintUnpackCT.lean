module

public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.MlDsa.Pack.HintMem
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Proof.MlDsa.Pack.HintMem
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.MlDsa.Pack.Mem
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.Pack.Mem
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Common
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Inline
meta import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Pack.Hint
public import VerifiedGarbage.Proof.MlDsa.Pack.Hint2
import VerifiedGarbage.Proof.MlKem.RISCV64.Bytes
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Isa
meta import VerifiedGarbage.Impl.MlDsa.RISCV64.Pack.Hint
meta import VerifiedGarbage.Proof.MlDsa.Pack.Hint2
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Bytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.MlDsa.Contract
meta import VerifiedGarbage.Proof.Framework.RISCV64.Inline
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.TCB.RISCV64.Isa

/-! ### `MlDsa.RISCV64.Pack.HintPack`, which this module and modules that import it used -/

section

/-! ### `MlDsa.RISCV64.Pack.HintBase`, which this module and modules that import it used -/

section

/-!
# ML-DSA on RISC-V: what the proofs of `HintBitPack` and `HintBitUnpack` share

The 32-bit argument `omega`, zero-extended (`zext_eq`); the comparisons of
small numbers (`ltBit`: the sign bit of a 64-bit difference); the counter of
a loop that compares with 256; and the byte loads and stores, one
instruction at a time (`wp_lbz`, `wp_stb`, `lbu` and `sb` with PPC64LE's
arguments).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Pack.Hint

open VG VG.RISCV64
open VG.Spec.MlDsa

/-- The 32-bit argument in `r`. -/
abbrev w32 (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-- `omega` zero-extended, as `zextOmega` leaves it. -/
theorem zext_eq (x : BitVec 64) : x <<< 32 >>> 32 = BitVec.ofNat 64 (x.setWidth 32).toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, show 2 ^ 64 = 2 ^ 32 * 2 ^ 32 by decide,
    Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (by decide)]
  omega_using []

/-- The sign bit of `x - y`, for `x` and `y` less than `2⁶³`: whether `x < y`. -/
theorem ltBit_eq {x y : Nat} (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    (BitVec.ofNat 64 x - BitVec.ofNat 64 y) >>> 63 = BitVec.ofNat 64 (if x < y then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  split <;> omega_arith

/-- The counter of a loop over 256 coefficients: `j + 1 - 256`. -/
theorem cnt256 {j : Nat} (hj : j < 256) :
    (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 256 != 0) = decide (j + 1 ≠ 256) := by
  by_cases h : j + 1 = 256
  · rw [h]; rfl
  · rw [decide_eq_true h]
    simp only [bne_iff_ne, ne_eq]
    intro e
    apply h
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    simp at this
    omega_using [hj, this]

theorem ofNat_succ (x : Nat) : BitVec.ofNat 64 x + BitVec.ofNat 64 1 = BitVec.ofNat 64 (x + 1) := by
  rw [BitVec.ofNat_add_ofNat]

theorem ofNat_lt {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The low byte of a register holding a number. -/
theorem lowByte (x : Nat) : (BitVec.ofNat 64 x).setWidth 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide)]

/-- A byte, zero-extended, as a number. -/
theorem byte_ofNat (b : Byte) : b.setWidth 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, ofNat_lt (by have := b.isLt; omega_using []),
    Nat.mod_eq_of_lt (by have := b.isLt; omega_using [])]

/-- A word, zero-extended: zero exactly when the word is. -/
theorem word_w_zero (v : BitVec 32) : (v.setWidth 64 == 0) = (v == 0) := by
  by_cases h : v = 0
  · subst h; rfl
  · have : v.setWidth 64 ≠ 0 := fun e => h (by
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := v.isLt; omega_using [])] at this
      exact this)
    rw [beq_false_of_ne this, beq_false_of_ne h]

theorem eval_zero_w (s : State) (r : Reg) : isa.eval (.zero r) s = some (s.gpr r == 0) := rfl

/-- `beqz` of a register holding a number. -/
theorem eval_zero_ofNat (s : State) (r : Reg) {k : Nat} (hk : k < 2 ^ 64)
    (h : s.gpr r = BitVec.ofNat 64 k) : isa.eval (.zero r) s = some (decide (k = 0)) := by
  show some (s.gpr r == 0) = _
  rw [h, Option.some.injEq]
  by_cases e : k = 0
  · subst e; rfl
  · rw [decide_eq_false e]
    refine beq_false_of_ne fun h0 => e ?_
    have := congrArg BitVec.toNat h0
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `lbu`, with PPC64LE's arguments (`Proof/MlDsa/PPC64LE/Pack/HintBase.lean`). -/
theorem wp_lbz {t n : Reg} {off : Nat} {a : Addr} (_hn : n ≠ .t0) (ho : off < 2048)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Steps.Upd s s' t ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .b t n off :: is)) s Q :=
  Steps.wp_lbu ho ha hin k

/-- `sb`, with PPC64LE's arguments. -/
theorem wp_stb {t n : Reg} {off : Nat} {a : Addr} (_hn : n ≠ .t0) (ho : off < 2048)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Steps.Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .b t n off :: is)) s Q :=
  Steps.wp_sb ho ha hout k

end

/-- Code keeps the stack pointer. -/
theorem wp_sp {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.sp = s.sp := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.sp he⟩

/-- The parameters of the hint encodings. -/
theorem mem_hintParams' {ω k : Nat} (h : (ω, k) ∈ hintParams) : 4 ≤ k ∧ k ≤ 8 ∧ 55 ≤ ω ∧ ω ≤ 80 := by
  simp only [hintParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  omega_using [h]

end VG.Proof.MlDsa.RISCV64.Pack.Hint

end

end

/-!
# ML-DSA on RISC-V: `vg_mldsa_hint_bit_pack`, correct

As on AArch64 (`Proof/MlDsa/AArch64/Pack/HintPack.lean`), the code follows
the fold form of `HintBitPack` (`Proof/MlDsa/Pack/Hint.lean`) step by step:
the bytes of `y` are the array of the spec (`hpS`, `hpT`), and `t1` its
index, which stays below `ω` because it counts the 1s before the current
coefficient (`hpT_idx_lt`). Zeroing `y` (`zero_ok`) leaves the state the
loops start from (`ZPost`), from which constant time takes the runs
(`HintPackCT.lean`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Pack.Hint

open VG.RISCV64.Steps (Upd Mupd)
open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.RISCV64 (wp_loop_nz count_sub count_nz ptr_add byte_writeW8)
open VG.Proof.MlKem (bytesAt_writeW8 bytesAt_eq)
open VG.Proof.MlDsa.Pack

theorem _root_.VG.RISCV64.Steps.Upd.keepH {s s' : State} {d : Reg} {v : BitVec 64} (h : Upd s s' d v) : Keep [d] s s' :=
  ⟨fun r hr => h.other r fun e => hr (e ▸ List.mem_singleton_self _), h.rd, h.wr⟩

theorem _root_.VG.RISCV64.Steps.Mupd.keepH {s s' : State} {m : Mem} (h : Mupd s s' m) : Keep [] s s' :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr⟩

theorem add0 (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## The arguments -/

section
variable (s₀ : State)

/-- `h`, `ω`, `y` and `len`. -/
abbrev pH : Addr := s₀.gpr .a0
abbrev pω : Nat := w32 s₀ .a2
abbrev pY : Addr := s₀.gpr .a3
abbrev pLen : Nat := (s₀.gpr .a4).toNat
abbrev pk : Nat := pLen s₀ - pω s₀
abbrev hR : Region := ⟨pH s₀, (s₀.gpr .a1).toNat * 4⟩
abbrev yR : Region := ⟨pY s₀, pLen s₀⟩
/-- The hint. -/
abbrev pHint : List (Vector Bool n) := hintAt s₀.mem (pH s₀) (pk s₀)
abbrev pS (i : Nat) : Array Byte × Nat := hpS (pω s₀) (pk s₀) (pHint s₀) i
abbrev pT (i j : Nat) : Array Byte × Nat := hpT (pω s₀) (pk s₀) (pHint s₀) i j

end

/-- The precondition, as `sig_pre` states it. -/
structure PPre (s : State) : Prop where
  rd : s.rd = [hR s]
  wr : s.wr = [yR s]
  d_hy : (hR s).Disjoint (yR s)
  fitH : (pH s).toNat + (s.gpr .a1).toNat * 4 ≤ 2 ^ 64
  fitY : (pY s).toNat + pLen s ≤ 2 ^ 64
  par : (pω s, pk s) ∈ hintParams
  ωle : pω s ≤ pLen s
  hlen : (s.gpr .a1).toNat = 256 * pk s
  ones : hintOnes (pHint s) ≤ pω s
  al : (pH s).toNat % 4 = 0

theorem pfacts {s₀ : State} (hp : PPre s₀) :
    4 ≤ pk s₀ ∧ pk s₀ ≤ 8 ∧ 55 ≤ pω s₀ ∧ pω s₀ ≤ 80 ∧ pω s₀ + pk s₀ = pLen s₀ ∧ pLen s₀ ≤ 88 := by
  have := mem_hintParams' hp.par
  have := hp.ωle
  have e : pk s₀ = pLen s₀ - pω s₀ := rfl
  omega_arith

/-! ## Zeroing `y` -/

/-- What zeroing `y` leaves. -/
structure ZPost (s₀ s : State) : Prop where
  a0 : s.gpr .a0 = pH s₀
  a1 : s.gpr .a1 = BitVec.ofNat 64 (pk s₀)
  a2 : s.gpr .a2 = BitVec.ofNat 64 (pω s₀)
  a3 : s.gpr .a3 = pY s₀
  zero : ∀ t < pLen s₀, s.mem (pY s₀ + BitVec.ofNat 64 t) = 0
  frame : Frame [yR s₀] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The zeroing loop after `t` bytes, from `s₁`. -/
structure ZInv (s₀ s₁ : State) (t : Nat) (s : State) : Prop where
  a7 : s.gpr .a7 = pY s₀ + BitVec.ofNat 64 t
  a6 : s.gpr .a6 = BitVec.ofNat 64 (pLen s₀ - t)
  keep : Keep [.a6, .a7] s₁ s
  frame : Frame [yR s₀] s₀.mem s.mem
  zero : ∀ u < t, s.mem (pY s₀ + BitVec.ofNat 64 u) = 0

theorem zero_ok {s₀ : State} (hp : PPre s₀) : WP isa hbpZero s₀ (ZPost s₀) := by
  obtain ⟨hk4, -, -, -, hsum, hL88⟩ := pfacts hp
  have fY := hp.fitY
  unfold hbpZero zextOmega
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (Steps.wp_sll (by decide) fun s₁ o₁ => Steps.wp_srl (by decide) fun s₂ o₂ => Steps.wp_sub fun s₃ o₃ =>
    Steps.wp_addi (by decide) fun s₄ o₄ => Steps.wp_li (by decide) fun s₅ o₅ =>
    Steps.wp_addi (by decide) fun s₆ o₆ => WP.block_nil ?_)
  obtain k₅ := (((o₁.keepH.trans o₂.keepH).trans o₃.keepH).trans o₄.keepH).trans o₅.keepH
  obtain k₆ := k₅.trans o₆.keepH
  obtain m₆ : s₆.mem = s₀.mem := by rw [o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  obtain r5 : s₆.gpr .a2 = BitVec.ofNat 64 (pω s₀) := by
    rw [o₆.other _ (by decide), o₅.other _ (by decide), o₄.other _ (by decide), o₃.other _ (by decide), o₂.gpr,
      o₁.gpr, zext_eq]
  obtain r0 : s₆.gpr .t0 = 0 := by rw [o₆.other _ (by decide), o₅.gpr]; rfl
  obtain r4 : s₆.gpr .a1 = BitVec.ofNat 64 (pk s₀) := by
    rw [o₆.other _ (by decide), o₅.other _ (by decide), o₄.other _ (by decide), o₃.gpr,
      o₂.other _ (by decide), o₁.other _ (by decide), o₂.gpr, o₁.gpr, zext_eq]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, ofNat_lt (by omega_arith)]; exact hp.ωle), ofNat_lt (by omega_arith), ofNat_lt (by omega_arith)]
  obtain hwr : s₆.wr = [yR s₀] := by rw [k₆.2.2, hp.wr]
  refine WP.mono (wp_loop_nz (ZInv s₀ s₆) (N := pLen s₀) (by omega_arith) (fun t ht s h => ?_) (fun s h => h)
    ⟨by rw [o₆.gpr, k₅.gpr (r := .a3) (by decide), add0], ?_, Keep.refl _ _, by rw [m₆]; exact Frame.refl _ _,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s h => ?_
  · -- A byte.
    obtain hc : (yR s₀).Contains (pY s₀ + BitVec.ofNat 64 t) 1 := Offset.contains_base _ (by omega_arith) (by omega_arith)
    refine Steps.wp_sb (by decide) (by rw [h.a7, add0])
      (by rw [h.keep.2.2, hwr]; exact ⟨_, List.mem_singleton_self _, hc⟩) fun s₁ m₁ =>
      Steps.wp_addi (by decide) fun s₂ o₂ => Steps.wp_subi (by decide) fun s₃ o₃ => WP.block_nil ?_
    obtain c9 : s₃.gpr .a6 = BitVec.ofNat 64 (pLen s₀ - (t + 1)) := by
      rw [o₃.gpr, o₂.other _ (by decide), m₁.gpr, h.a6, count_sub ht]
    obtain m₃ : s₃.mem = s.mem.writeW (pY s₀ + BitVec.ofNat 64 t) ((s.gpr .t0).setWidth 8) := by
      rw [o₃.mem, o₂.mem, m₁.mem]
    refine ⟨⟨?_, c9, (h.keep.trans ((m₁.keepH.trans o₂.keepH).trans o₃.keepH)).mono (by decide), ?_, fun u hu => ?_⟩,
      by rw [c9]; exact count_nz ht (by omega_arith)⟩
    · rw [o₃.other _ (by decide), o₂.gpr, m₁.gpr, h.a7, ptr_add]
    · rw [m₃]; exact h.frame.writeW (List.mem_singleton_self _) _ hc
    · rw [m₃, byte_writeW8 _ _ (by omega_arith) (by omega_arith)]
      split
      · rw [h.keep.gpr (by decide), r0]; rfl
      · exact h.zero u (by omega_arith)
  · rw [o₆.other _ (by decide), o₅.other _ (by decide), o₄.gpr, add0, Nat.sub_zero, ofNat_toNat64,
      o₃.other _ (by decide), o₂.other _ (by decide), o₁.other _ (by decide)]
  · exact ⟨by rw [h.keep.gpr (by decide), k₆.gpr (by decide)], by rw [h.keep.gpr (by decide), r4],
      by rw [h.keep.gpr (by decide), r5], by rw [h.keep.gpr (by decide), k₆.gpr (by decide)], h.zero, h.frame,
      h.keep.2.1.trans k₆.2.1, h.keep.2.2.trans k₆.2.2⟩

/-! ## The polynomials -/

theorem pT_zero (s₀ : State) (i : Nat) : pT s₀ i 0 = pS s₀ i := hpT_zero _ _ _ i

theorem pS_succ (s₀ : State) (i : Nat) :
    pS s₀ (i + 1) = ((pT s₀ i 256).1.set! (pω s₀ + i) (BitVec.ofNat 8 (pT s₀ i 256).2), (pT s₀ i 256).2) :=
  hpS_succ _ _ _ i

/-- Before coefficient `j` of polynomial `i`. -/
structure CInv (s₀ : State) (i j : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = pH s₀ + BitVec.ofNat 64 (4 * (256 * i + j))
  a3 : s.gpr .a3 = pY s₀
  a6 : s.gpr .a6 = BitVec.ofNat 64 (pk s₀ - i)
  a7 : s.gpr .a7 = pY s₀ + BitVec.ofNat 64 (pω s₀ + i)
  t1 : s.gpr .t1 = BitVec.ofNat 64 (pT s₀ i j).2
  t2 : s.gpr .t2 = BitVec.ofNat 64 j
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [yR s₀] s₀.mem s.mem
  y : bytesAt s.mem (pY s₀) (pLen s₀) = (pT s₀ i j).1.toList

/-- The end of a coefficient: the pointer, `j` and the counter. -/
theorem coefTail_ok {s₀ : State} {i j : Nat} (hj : j < 256) {s : State}
    (r3 : s.gpr .a0 = pH s₀ + BitVec.ofNat 64 (4 * (256 * i + j))) (r6 : s.gpr .a3 = pY s₀)
    (r9 : s.gpr .a6 = BitVec.ofNat 64 (pk s₀ - i)) (r10 : s.gpr .a7 = pY s₀ + BitVec.ofNat 64 (pω s₀ + i))
    (r11 : s.gpr .t1 = BitVec.ofNat 64 (pT s₀ i (j + 1)).2) (r12 : s.gpr .t2 = BitVec.ofNat 64 j)
    (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) (frame : Frame [yR s₀] s₀.mem s.mem)
    (y : bytesAt s.mem (pY s₀) (pLen s₀) = (pT s₀ i (j + 1)).1.toList) :
    WP isa (.block [.addi .a0 .a0 4, .addi .t2 .t2 1, .addi .a5 .t2 (-256)]) s fun s' =>
      CInv s₀ i (j + 1) s' ∧ (s'.gpr .a5 != 0) = decide (j + 1 ≠ 256) :=
  Steps.wp_addi (by decide) fun s₁ o₁ => Steps.wp_addi (by decide) fun s₂ o₂ =>
    Steps.wp_subi (by decide) fun s₃ o₃ => WP.block_nil (by
      obtain k₃ := (o₁.keepH.trans o₂.keepH).trans o₃.keepH
      obtain c12' : s₂.gpr .t2 = BitVec.ofNat 64 (j + 1) := by
        rw [o₂.gpr, o₁.other _ (by decide), r12, ofNat_succ]
      obtain c12 : s₃.gpr .t2 = BitVec.ofNat 64 (j + 1) := by rw [o₃.other _ (by decide), c12']
      refine ⟨⟨?_, by rw [k₃.gpr (by decide), r6], by rw [k₃.gpr (by decide), r9], by rw [k₃.gpr (by decide), r10],
        by rw [k₃.gpr (by decide), r11], c12, by rw [k₃.2.1, rd], by rw [k₃.2.2, wr],
        by rw [o₃.mem, o₂.mem, o₁.mem]; exact frame, by rw [o₃.mem, o₂.mem, o₁.mem]; exact y⟩, ?_⟩
      · rw [o₃.other _ (by decide), o₂.other _ (by decide), o₁.gpr, r3, ptr_add,
          show 4 * (256 * i + j) + 4 = 4 * (256 * i + (j + 1)) by omega_arith]
      · rw [o₃.gpr, c12']; exact cnt256 hj)

/-- Coefficient `j` of polynomial `i`: if it is not 0, `y[index] ← j`. -/
theorem coef_ok {s₀ : State} (hp : PPre s₀) {i j : Nat} (hi : i < pk s₀) (hj : j < 256) {s : State}
    (hI : CInv s₀ i j s) :
    WP isa hbpCoef s fun s' => CInv s₀ i (j + 1) s' ∧ (s'.gpr .a5 != 0) = decide (j + 1 ≠ 256) := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := pfacts hp
  have fH := hp.fitH
  have fY := hp.fitY
  have hl := hp.hlen
  obtain hpos : 256 * i + j < 256 * pk s₀ := by omega_arith
  obtain hR' : (hR s₀).Contains (coeffAddr (pH s₀) (256 * i + j)) 4 := Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain hw : s.mem.readW (coeffAddr (pH s₀) (256 * i + j)) 32 = coeffAt s₀.mem (pH s₀) (256 * i + j) :=
    hI.frame.readW hR' (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.d_hy) (by decide)
  obtain hbit := hintAt_get (m := s₀.mem) (p := pH s₀) hi (show j < n from hj)
  obtain hT : pT s₀ i (j + 1) = hpStep ((pHint s₀).getD i noHint) (pT s₀ i j) j := hpT_succ _ _ _ i j
  unfold hbpCoef
  refine WP.seq (Steps.wp_lwu (a := coeffAddr (pH s₀) (256 * i + j)) (by decide) (by rw [hI.a0, add0])
    (VG.Proof.MlKem.RISCV64.align4_add hp.al _)
    (by rw [hI.rd, hI.wr, hp.rd]; exact ⟨_, .head _, hR'⟩) fun s₁ o₁ => WP.block_nil ?_)
  obtain hb : (s₁.gpr .a5 == 0) = !((pHint s₀).getD i noHint)[j]! := by
    rw [hbit, o₁.gpr, word_w_zero, hw, Bool.beq_eq_decide_eq]
    by_cases e : coeffAt s₀.mem (pH s₀) (256 * i + j) = 0 <;> simp [e]
  refine WP.seq (WP.ite _ (eval_zero_w s₁ .a5) (fun h0 => ?_) (fun h1 => ?_))
  · -- A 0.
    rw [hb, Bool.not_eq_true'] at h0
    obtain hT0 : pT s₀ i (j + 1) = pT s₀ i j := by rw [hT, hpStep, h0]; rfl
    refine WP.block_nil (coefTail_ok hj (by rw [o₁.other _ (by decide), hI.a0]) (by rw [o₁.other _ (by decide), hI.a3])
      (by rw [o₁.other _ (by decide), hI.a6]) (by rw [o₁.other _ (by decide), hI.a7])
      (by rw [o₁.other _ (by decide), hI.t1, hT0]) (by rw [o₁.other _ (by decide), hI.t2])
      (by rw [o₁.rd, hI.rd]) (by rw [o₁.wr, hI.wr]) (by rw [o₁.mem]; exact hI.frame) (by rw [o₁.mem, hI.y, hT0]))
  · -- A 1: `y[index] ← j`.
    rw [hb, Bool.not_eq_false'] at h1
    obtain hlt : (pT s₀ i j).2 < pω s₀ := hpT_idx_lt (hintAt_length _ _ _) hp.ones hi (show j < n from hj) h1
    obtain hc : (yR s₀).Contains (pY s₀ + BitVec.ofNat 64 (pT s₀ i j).2) 1 := Offset.contains_base _ (by omega_arith) (by omega_arith)
    refine Steps.wp_add fun s₂ o₂ => wp_stb (a := pY s₀ + BitVec.ofNat 64 (pT s₀ i j).2) (by decide) (by decide)
      (by rw [o₂.gpr, o₁.other _ (by decide), o₁.other _ (by decide), hI.a3, hI.t1, add0])
      (by rw [o₂.wr, o₁.wr, hI.wr, hp.wr]; exact ⟨_, .head _, hc⟩) fun s₃ m₃ =>
      Steps.wp_addi (by decide) fun s₄ o₄ => WP.block_nil ?_
    obtain k₄ := ((o₁.keepH.trans o₂.keepH).trans m₃.keepH).trans o₄.keepH
    obtain mem₄ : s₄.mem = s.mem.writeW (pY s₀ + BitVec.ofNat 64 (pT s₀ i j).2) (BitVec.ofNat 8 j) := by
      rw [o₄.mem, m₃.mem, o₂.mem, o₁.mem, o₂.other _ (by decide), o₁.other _ (by decide), hI.t2, lowByte]
    obtain hT1 : pT s₀ i (j + 1) = ((pT s₀ i j).1.set! (pT s₀ i j).2 (BitVec.ofNat 8 j), (pT s₀ i j).2 + 1) := by
      rw [hT, hpStep, h1]; rfl
    refine coefTail_ok hj (by rw [k₄.gpr (by decide), hI.a0]) (by rw [k₄.gpr (by decide), hI.a3])
      (by rw [k₄.gpr (by decide), hI.a6]) (by rw [k₄.gpr (by decide), hI.a7])
      (by rw [o₄.gpr, m₃.gpr, o₂.other _ (by decide), o₁.other _ (by decide), hI.t1, hT1, ofNat_succ])
      (by rw [k₄.gpr (by decide), hI.t2]) (by rw [k₄.2.1, hI.rd]) (by rw [k₄.2.2, hI.wr]) ?_ ?_
    · rw [mem₄]; exact hI.frame.writeW (List.mem_singleton_self _) _ hc
    · rw [mem₄, bytesAt_writeW8 _ _ (by omega_arith) (by omega_arith), hI.y, hT1]
      simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]

/-- Before polynomial `i`. -/
structure HPInv (s₀ : State) (i : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = pH s₀ + BitVec.ofNat 64 (4 * (256 * i))
  a3 : s.gpr .a3 = pY s₀
  a6 : s.gpr .a6 = BitVec.ofNat 64 (pk s₀ - i)
  a7 : s.gpr .a7 = pY s₀ + BitVec.ofNat 64 (pω s₀ + i)
  t1 : s.gpr .t1 = BitVec.ofNat 64 (pS s₀ i).2
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [yR s₀] s₀.mem s.mem
  y : bytesAt s.mem (pY s₀) (pLen s₀) = (pS s₀ i).1.toList

theorem poly_ok {s₀ : State} (hp : PPre s₀) {i : Nat} (hi : i < pk s₀) {s : State} (hP : HPInv s₀ i s) :
    WP isa hbpPoly s fun s' => HPInv s₀ (i + 1) s' ∧ (s'.gpr .a6 != 0) = decide (i + 1 ≠ pk s₀) := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := pfacts hp
  have fY := hp.fitY
  unfold hbpPoly
  refine WP.seq (Steps.wp_li (by decide) fun s₁ o₁ => WP.block_nil ?_)
  refine WP.seq (wp_loop_nz (CInv s₀ i) (N := 256) (by decide) (fun j hj s hI => coef_ok hp hi hj hI)
    (fun s h => ?_) ⟨by rw [o₁.other _ (by decide), hP.a0, Nat.add_zero], by rw [o₁.other _ (by decide), hP.a3],
      by rw [o₁.other _ (by decide), hP.a6], by rw [o₁.other _ (by decide), hP.a7],
      by rw [o₁.other _ (by decide), hP.t1, pT_zero], o₁.gpr, by rw [o₁.rd, hP.rd], by rw [o₁.wr, hP.wr],
      by rw [o₁.mem]; exact hP.frame, by rw [o₁.mem, hP.y, pT_zero]⟩)
  obtain hidx : (pT s₀ i 256).2 ≤ pω s₀ := hpT_idx_le (hintAt_length _ _ _) hp.ones hi
  obtain hc : (yR s₀).Contains (pY s₀ + BitVec.ofNat 64 (pω s₀ + i)) 1 := Offset.contains_base _ (by omega_arith) (by omega_arith)
  refine Steps.wp_sb (by decide) (by rw [h.a7, add0]) (by rw [h.wr, hp.wr]; exact ⟨_, .head _, hc⟩)
    fun s₂ m₂ => Steps.wp_addi (by decide) fun s₃ o₃ => Steps.wp_subi (by decide) fun s₄ o₄ => WP.block_nil ?_
  obtain k₄ := (m₂.keepH.trans o₃.keepH).trans o₄.keepH
  obtain c9 : s₄.gpr .a6 = BitVec.ofNat 64 (pk s₀ - (i + 1)) := by
    rw [o₄.gpr, o₃.other _ (by decide), m₂.gpr, h.a6, count_sub hi]
  obtain mem₄ : s₄.mem = s.mem.writeW (pY s₀ + BitVec.ofNat 64 (pω s₀ + i)) (BitVec.ofNat 8 (pT s₀ i 256).2) := by
    rw [o₄.mem, o₃.mem, m₂.mem, h.t1, lowByte]
  refine ⟨⟨?_, by rw [k₄.gpr (by decide), h.a3], c9, ?_, by rw [k₄.gpr (by decide), h.t1, pS_succ],
    by rw [k₄.2.1, h.rd], by rw [k₄.2.2, h.wr], ?_, ?_⟩, by rw [c9]; exact count_nz hi (by omega_arith)⟩
  · rw [k₄.gpr (by decide), h.a0, show 4 * (256 * i + 256) = 4 * (256 * (i + 1)) by omega_arith]
  · rw [o₄.other _ (by decide), o₃.gpr, m₂.gpr, h.a7, ptr_add, Nat.add_assoc]
  · rw [mem₄]; exact h.frame.writeW (List.mem_singleton_self _) _ hc
  · rw [mem₄, bytesAt_writeW8 _ _ (by omega_arith) (by omega_arith), h.y, pS_succ]
    simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]

theorem main_ok {s₀ : State} (hp : PPre s₀) {s : State} (hz : ZPost s₀ s) :
    WP isa hbpMain s fun s' =>
      bytesAt s'.mem (pY s₀) (pLen s₀) = hintBitPack (pω s₀) (pk s₀) (pHint s₀) ∧ Frame [yR s₀] s₀.mem s'.mem := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := pfacts hp
  unfold hbpMain
  refine WP.seq (Steps.wp_addi (by decide) fun s₁ o₁ => Steps.wp_add fun s₂ o₂ => Steps.wp_li (by decide) fun s₃ o₃ =>
    WP.block_nil ?_)
  obtain k₃ := (o₁.keepH.trans o₂.keepH).trans o₃.keepH
  refine wp_loop_nz (HPInv s₀) (N := pk s₀) (by omega_arith) (fun i hi s hP => poly_ok hp hi hP)
    (fun s hP => ⟨hP.y.trans (hintBitPack_hpS _ _ _).symm, hP.frame⟩)
    ⟨by rw [k₃.gpr (by decide), hz.a0]; exact (add0 _).symm, by rw [k₃.gpr (by decide), hz.a3],
      by rw [o₃.other _ (by decide), o₂.other _ (by decide), o₁.gpr, add0, hz.a1, Nat.sub_zero],
      by rw [o₃.other _ (by decide), o₂.gpr, o₁.other _ (by decide), o₁.other _ (by decide), hz.a3, hz.a2,
        Nat.add_zero],
      by rw [o₃.gpr]; rfl, by rw [k₃.2.1, hz.rd], by rw [k₃.2.2, hz.wr],
      by rw [o₃.mem, o₂.mem, o₁.mem]; exact hz.frame, ?_⟩
  rw [o₃.mem, o₂.mem, o₁.mem]
  show _ = (Array.replicate (pω s₀ + pk s₀) (0 : Byte)).toList
  rw [Array.toList_replicate, hsum]
  exact bytesAt_eq (by simp) fun t ht => by rw [hz.zero t ht]; simp

/-! ## The function -/

/-- The registers `hintBitPack` writes. -/
abbrev hbpRegs : List Reg := [.t0, .a0, .a1, .a2, .a5, .a6, .a7, .t1, .t2]

theorem correct {s₀ : State} (hp : PPre s₀) :
    WP isa Impl.MlDsa.RISCV64.Pack.hintBitPack s₀ fun s' =>
      bytesAt s'.mem (pY s₀) (pLen s₀) = hintBitPack (pω s₀) (pk s₀) (pHint s₀) ∧ Keep hbpRegs s₀ s' := by
  refine WP.keep hbpRegs (WP.seq (WP.mono (zero_ok hp) fun s hz => WP.mono (main_ok hp hz) fun _ h => h.1))
    (by decide +kernel)

end VG.Proof.MlDsa.RISCV64.Pack.Hint

end

end

/-! ### `MlDsa.RISCV64.Pack.HintCT`, which this module and modules that import it used -/

section

/-!
# Constant time of code that leaks memory both runs agree on (RISC-V)

The RISC-V counterpart of PPC64LE's `memTaint`
(`Proof/MlDsa/PPC64LE/Pack/HintCT.lean`), for `vg_mldsa_hint_bit_pack` and
`vg_mldsa_hint_bit_unpack`, which branch and index memory on their input,
which they load from memory.

The taint analysis (`Proof/Framework/RISCV64/Taint.lean`) treats memory as
secret. `memTaint` is one for code that runs with permissions only on memory
whose bytes two runs agree on (`MemEq`): every load it makes is then public,
and a store keeps the agreement if it stores a public value at a public
address. Neither function has a frame or calls.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Pack.Hint

open VG VG.RISCV64
open VG.RISCV64.Taint (T pub set)

/-- `m₁` and `m₂` agree on every byte of the regions `rs`. -/
def MemEq (rs : List Region) (m₁ m₂ : Mem) : Prop := ∀ x, InRegions rs x 1 → m₁ x = m₂ x

/-- The registers `τ` agree, and the permissions and the memory they permit. -/
def MAgree (τ : T) (s₁ s₂ : State) : Prop :=
  VG.RISCV64.Taint.Agree τ s₁ s₂ ∧ s₁.rd = s₂.rd ∧ s₁.wr = s₂.wr ∧ MemEq (s₁.rd ++ s₁.wr) s₁.mem s₂.mem

/-- Instructions that only write a general-purpose register. -/
def regOp : Instr → Bool
  | .add .. | .sub .. | .addw .. | .subw .. | .sltu .. | .mul .. | .mulhu .. | .logic .. | .addi ..
  | .addiw .. | .logicImm .. | .li .. | .lui .. | .shift .. | .shiftReg .. => true
  | _ => false

/-- Loads are public, stores must store public values; the other memory
instructions and frames are not analysed. -/
def mstep (τ : T) : Instr → Option T
  | .load _ t n _ => if pub τ n then some (set τ t true) else none
  | .store _ t n _ => if pub τ n && pub τ t then some τ else none
  | i => if regOp i then VG.RISCV64.Taint.step τ i else none

theorem exec_regOp {i : Instr} (hi : regOp i = true) {s s' : State} (h : exec i s = some s') :
    s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases i <;> simp [regOp] at hi
  case shift op sz d n sh =>
    cases sz <;> simp only [exec] at h <;> split at h <;>
      first | (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩) | (simp at h)
  case shiftReg op sz d n m =>
    cases sz <;> simp only [exec] at h <;>
      first | (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩) | (simp at h)
  all_goals simp only [exec] at h
  all_goals first
    | (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩)
    | (split at h <;> (try split at h) <;>
        first | (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩) | (simp at h))

theorem MemEq.read {rs : List Region} {m₁ m₂ : Mem} (h : MemEq rs m₁ m₂) {a : Addr} {n : Nat}
    (hi : InRegions rs a n) (hn : n < 2 ^ 64) : m₁.read a n = m₂.read a n := by
  obtain ⟨r, hr, hc⟩ := hi
  exact Mem.read_congr fun i hi' =>
    h _ ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat a (by omega_using [hn, hi'])]; exact hi')⟩

theorem MemEq.write {rs : List Region} {m₁ m₂ : Mem} (h : MemEq rs m₁ m₂) (a : Addr) (n : Nat)
    (v : BitVec (8 * n)) : MemEq rs (m₁.write a n v) (m₂.write a n v) := fun x hx => by
  simp only [Mem.write]
  split
  · rfl
  · exact h x hx

theorem regOp_sound {τ τ' : T} {i : Instr} (hr : regOp i = true) {s₁ s₂ s₁' s₂' : State}
    (ha : MAgree τ s₁ s₂) (hs : VG.RISCV64.Taint.step τ i = some τ') (e₁ : exec i s₁ = some s₁')
    (e₂ : exec i s₂ = some s₂') : addrs i s₁ = addrs i s₂ ∧ MAgree τ' s₁' s₂' := by
  obtain ⟨hadd, ht⟩ := VG.RISCV64.Taint.step_sound ha.1 hs e₁ e₂
  obtain ⟨m₁, r₁, w₁⟩ := exec_regOp hr e₁
  obtain ⟨m₂, r₂, w₂⟩ := exec_regOp hr e₂
  exact ⟨hadd, ht, by rw [r₁, r₂, ha.2.1], by rw [w₁, w₂, ha.2.2.1], by
    rw [m₁, m₂, r₁, w₁]; exact ha.2.2.2⟩

theorem addr_agree {τ : T} {s₁ s₂ : State} (ha : MAgree τ s₁ s₂) {n : Reg} (hn : pub τ n = true)
    (bytes off : Nat) {a₁ a₂ : Addr} (h₁ : addr s₁ bytes n off = some a₁)
    (h₂ : addr s₂ bytes n off = some a₂) : a₁ = a₂ := by
  simp only [addr] at h₁ h₂
  rw [ha.1.reg hn] at h₁
  split at h₁ <;> [rename_i hc; cases h₁]
  rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h₂
  exact (Option.some.inj h₁).symm.trans (Option.some.inj h₂)

theorem load_sound {τ : T} {s₁ s₂ : State} (ha : MAgree τ s₁ s₂) {n : Reg} (hn : pub τ n = true)
    (bytes off : Nat) {a₁ a₂ : Addr} (h₁ : addr s₁ bytes n off = some a₁)
    (h₂ : addr s₂ bytes n off = some a₂) {v₁ v₂ : BitVec (8 * bytes)}
    (l₁ : s₁.load a₁ bytes = some v₁) (l₂ : s₂.load a₂ bytes = some v₂) (hb : bytes < 2 ^ 64) :
    v₁ = v₂ := by
  have ea := addr_agree ha hn bytes off h₁ h₂
  subst ea
  simp only [State.load] at l₁ l₂
  split at l₁ <;> [rename_i hi; cases l₁]
  split at l₂ <;> [skip; cases l₂]
  cases l₁; cases l₂
  exact ha.2.2.2.read hi hb

theorem store_sound {τ : T} {s₁ s₂ : State} (ha : MAgree τ s₁ s₂) {n : Reg} (hn : pub τ n = true)
    (bytes off : Nat) {a₁ a₂ : Addr} (h₁ : addr s₁ bytes n off = some a₁)
    (h₂ : addr s₂ bytes n off = some a₂) {v : BitVec (8 * bytes)} {s₁' s₂' : State}
    (e₁ : s₁.store a₁ bytes v = some s₁') (e₂ : s₂.store a₂ bytes v = some s₂') :
    MAgree τ s₁' s₂' := by
  have ea := addr_agree ha hn bytes off h₁ h₂
  subst ea
  simp only [State.store] at e₁ e₂
  split at e₁ <;> [skip; cases e₁]
  split at e₂ <;> [skip; cases e₂]
  cases e₁; cases e₂
  exact ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.write _ _ _⟩

theorem mstep_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : MAgree τ s₁ s₂)
    (hs : mstep τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ MAgree τ' s₁' s₂' := by
  cases i with
  | load sz t n off =>
    simp only [mstep] at hs
    split at hs <;> [rename_i hn; cases hs]
    cases hs
    refine ⟨by simp [addrs, ha.1.reg hn], ?_⟩
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨a₁, h₁, v₁, l₁, rfl⟩ := e₁; obtain ⟨a₂, h₂, v₂, l₂, rfl⟩ := e₂
    have hv := load_sound ha hn _ off h₁ h₂ l₁ l₂ (by cases sz <;> decide)
    subst hv
    exact ⟨ha.1.write t fun _ => rfl, ha.2⟩
  | store sz t n off =>
    simp only [mstep] at hs
    split at hs <;> [rename_i hn; cases hs]
    cases hs
    simp only [Bool.and_eq_true] at hn
    refine ⟨by simp [addrs, ha.1.reg hn.1], ?_⟩
    simp only [exec, Option.bind_eq_some_iff] at e₁ e₂
    obtain ⟨a₁, h₁, e₁⟩ := e₁; obtain ⟨a₂, h₂, e₂⟩ := e₂
    rw [ha.1.reg hn.2] at e₁
    exact store_sound ha hn.1 _ off h₁ h₂ e₁ e₂
  | _ =>
    simp only [mstep] at hs
    split at hs <;> [rename_i hr; cases hs]
    exact regOp_sound hr ha hs e₁ e₂

/-- Taint tracking over memory both runs agree on, for RISC-V code without
calls or frames. -/
def memTaint : VG.Taint isa where
  T := VG.RISCV64.Taint.T
  Agree := MAgree
  step := mstep
  step_sound := mstep_sound
  condPub := VG.RISCV64.Taint.condPub
  cond_sound h hc := VG.RISCV64.Taint.cond_sound h.1 hc
  meet τ₁ τ₂ := τ₁.inter τ₂
  meet_left h := ⟨taint.meet_left h.1, h.2⟩
  meet_right h := ⟨taint.meet_right h.1, h.2⟩
  le τ σ := τ.subset σ
  le_sound hle h := ⟨taint.le_sound hle h.1, h.2⟩
  call _ := none
  call_sound _ hs _ _ := by cases hs
  ret _ := none
  ret_sound _ hs _ _ := by cases hs
  push _ _ := none
  push_sound _ hs _ _ := by cases hs
  pop _ _ := none
  pop_sound _ hs _ _ := by cases hs

end VG.Proof.MlDsa.RISCV64.Pack.Hint

end

end

/-! ### `MlDsa.RISCV64.Pack.HintUnpack`, which only this module used -/

section

/-!
# ML-DSA on RISC-V: `vg_mldsa_hint_bit_unpack`, the steps

As on 32-bit ARM (`Proof/MlDsa/Arm/Pack/HintUnpack.lean`), the code follows
the fold form of `HintBitUnpack` (`hintBitUnpack_eq`,
`Proof/MlDsa/Pack/Hint.lean`) step by step: while no check has failed, the
words of `h` are the hint of the spec (`HArr`) and `t1` its index; once one
has, `t1` is 256, which skips the rest (`SRel`). Here: the arguments,
zeroing `h`, one coefficient (`set_ok`, `next_ok`) and the coefficients of a
polynomial (`coefs_ok`); the polynomials, the trailing bytes and the return
value are in `HintUnpackMain.lean`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Pack.Hint.Unpack

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.RISCV64 (wp_loop_nz count_sub count_nz ptr_add)
open VG.Proof.MlKem (bytesAt_getD)
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.RISCV64.Pack.Hint (add0 ofNat_toNat64)

/-! ## The arguments -/

section
variable (s₀ : State)

/-- `y`, `len`, `ω`, `h` and `hlen`. -/
abbrev uY : Addr := s₀.gpr .a0
abbrev uLen : Nat := (s₀.gpr .a1).toNat
abbrev uω : Nat := w32 s₀ .a2
abbrev uH : Addr := s₀.gpr .a3
abbrev uk : Nat := uLen s₀ - uω s₀
abbrev uyR : Region := ⟨uY s₀, uLen s₀⟩
abbrev uhR : Region := ⟨uH s₀, (s₀.gpr .a4).toNat * 4⟩
/-- The bytes of `y`, as the spec reads them. -/
abbrev uYs : Array Byte := (bytesAt s₀.mem (uY s₀) (uLen s₀)).toArray

end

/-- The precondition, as `sig_pre` states it. -/
structure UPre (s : State) : Prop where
  rd : s.rd = [uyR s]
  wr : s.wr = [uhR s]
  d_yh : (uyR s).Disjoint (uhR s)
  fitY : (uY s).toNat + uLen s ≤ 2 ^ 64
  fitH : (uH s).toNat + (s.gpr .a4).toNat * 4 ≤ 2 ^ 64
  par : (uω s, uk s) ∈ hintParams
  ωle : uω s ≤ uLen s
  hlen : (s.gpr .a4).toNat = 256 * uk s
  al : (uH s).toNat % 4 = 0

theorem ufacts {s₀ : State} (hp : UPre s₀) :
    4 ≤ uk s₀ ∧ uk s₀ ≤ 8 ∧ 55 ≤ uω s₀ ∧ uω s₀ ≤ 80 ∧ uω s₀ + uk s₀ = uLen s₀ ∧ uLen s₀ ≤ 88 := by
  have := mem_hintParams' hp.par
  have := hp.ωle
  have e : uk s₀ = uLen s₀ - uω s₀ := rfl
  omega_arith

/-! ## Comparisons -/

/-- The register `ltBit` writes, as a condition. -/
theorem eval_lt_zero {s : State} {r : Reg} {a b : Nat} (h : s.gpr r = BitVec.ofNat 64 (if a < b then 1 else 0)) :
    isa.eval (.zero r) s = some (decide (b ≤ a)) := by
  show some (s.gpr r == 0) = _
  rw [h]
  split <;> simp <;> omega_arith

theorem eval_lt_nonzero {s : State} {r : Reg} {a b : Nat}
    (h : s.gpr r = BitVec.ofNat 64 (if a < b then 1 else 0)) :
    isa.eval (.nonzero r) s = some (decide (a < b)) := by
  show some (s.gpr r != 0) = _
  rw [h]
  split <;> simp <;> omega_arith

/-- A byte, as a word offset. -/
theorem shl2_byte (b : Byte) : b.setWidth 64 <<< 2 = BitVec.ofNat 64 (4 * b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, ofNat_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

theorem ptr_pred (p : Addr) {x : Nat} (h : 1 ≤ x) :
    p + BitVec.ofNat 64 x - BitVec.ofNat 64 1 = p + BitVec.ofNat 64 (x - 1) := by
  rw [show x = (x - 1) + 1 by omega_arith, ← ofNat_succ, ← BitVec.add_assoc, BitVec.add_sub_cancel,
    Nat.add_sub_cancel]

/-! ## The hint in memory -/

/-- The code's state is the spec's: a hint and its index, at most `ω`, or a
failed check, and 256 in `t1`. -/
def SRel (s₀ : State) : Option (Array (Vector Bool n) × Nat) → State → Prop
  | some (hA, idx), s => s.gpr .t1 = BitVec.ofNat 64 idx ∧ idx ≤ uω s₀ ∧ HArr s.mem (uH s₀) (uk s₀) hA
  | none, s => s.gpr .t1 = BitVec.ofNat 64 256

/-- What stays the same throughout the loops. -/
structure UCom (s₀ s : State) : Prop where
  a0 : s.gpr .a0 = uY s₀
  a2 : s.gpr .a2 = BitVec.ofNat 64 (uω s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [uhR s₀] s₀.mem s.mem

theorem UCom.of {s₀ s s' : State} (h : UCom s₀ s) {rs : List Reg} (hk : Keep rs s s') (h3 : Reg.a0 ∉ rs)
    (h5 : Reg.a2 ∉ rs) (hm : Frame [uhR s₀] s.mem s'.mem) : UCom s₀ s' :=
  ⟨(hk.gpr h3).trans h.a0, (hk.gpr h5).trans h.a2, hk.2.1.trans h.rd, hk.2.2.trans h.wr, h.frame.trans hm⟩

/-- Where the loops of polynomial `i` are, with the bound in `a5`. -/
structure PCom (s₀ : State) (i bound : Nat) (s : State) : Prop where
  com : UCom s₀ s
  a3 : s.gpr .a3 = uH s₀ + BitVec.ofNat 64 (1024 * i)
  a5 : s.gpr .a5 = BitVec.ofNat 64 bound

/-- The coefficient steps write only `t0`, `a6` and `t1`. -/
abbrev cRegs : List Reg := [.t0, .a6, .t1]

theorem PCom.of {s₀ s s' : State} {i bound : Nat} (h : PCom s₀ i bound s) (hk : Keep cRegs s s')
    (hm : Frame [uhR s₀] s.mem s'.mem) : PCom s₀ i bound s' :=
  ⟨h.com.of hk (by decide) (by decide) hm, (hk.gpr (by decide)).trans h.a3, (hk.gpr (by decide)).trans h.a5⟩

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- A byte of `y`, unchanged by the writes to `h`. -/
theorem yByte {s : State} (hc : UCom s₀ s) {t : Nat} (ht : t < uLen s₀) :
    s.mem (uY s₀ + BitVec.ofNat 64 t) = (uYs s₀).getD t 0 := by
  have fY := hp.fitY
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD, bytesAt_getD _ _ ht]
  refine hc.frame _ fun r hr hc' => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact hp.d_yh _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) hc'

theorem yIn {s : State} (hc : UCom s₀ s) {t : Nat} (ht : t < uLen s₀) :
    InRegions (s.rd ++ s.wr) (uY s₀ + BitVec.ofNat 64 t) 1 := by
  have fY := hp.fitY
  rw [hc.rd, hp.rd]; exact ⟨_, .head _, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

/-! ## Zeroing `h` -/

/-- What zeroing `h` leaves. -/
structure ZPost (s s' : State) : Prop where
  com : UCom s s'
  a3 : s'.gpr .a3 = uH s
  t1 : s'.gpr .t1 = 0
  t2 : s'.gpr .t2 = BitVec.ofNat 64 (uk s)
  zero : ∀ t < 256 * uk s, coeffAt s'.mem (uH s) t = 0

/-- The zeroing loop after `t` words, from `s₁`. -/
structure ZInv (s₀ s₁ : State) (t : Nat) (s : State) : Prop where
  a7 : s.gpr .a7 = uH s₀ + BitVec.ofNat 64 (4 * t)
  a6 : s.gpr .a6 = BitVec.ofNat 64 (256 * uk s₀ - t)
  keep : Keep [.a6, .a7] s₁ s
  frame : Frame [uhR s₀] s₀.mem s.mem
  zero : ∀ u < t, coeffAt s.mem (uH s₀) u = 0

omit hp in
theorem coeffAt_writeW_ne' (m : Mem) (p : Addr) {i j : Nat} (hi : i < 2048) (hj : j < 2048) (h : i ≠ j)
    (v : BitVec 32) : coeffAt (m.writeW (coeffAddr p j) v) p i = coeffAt m p i := by
  rw [coeffAt_eq, coeffAt_eq, Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]

theorem zero_ok : WP isa hbuZero s₀ (ZPost s₀) := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  have fH := hp.fitH
  have hl := hp.hlen
  unfold hbuZero zextOmega
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (Steps.wp_sll (by decide) fun s₁ o₁ => Steps.wp_srl (by decide) fun s₂ o₂ => Steps.wp_sub fun s₃ o₃ =>
    Steps.wp_addi (by decide) fun s₄ o₄ => Steps.wp_li (by decide) fun s₅ o₅ =>
    Steps.wp_addi (by decide) fun s₆ o₆ => WP.block_nil ?_)
  obtain k₅ := (((o₁.keepH.trans o₂.keepH).trans o₃.keepH).trans o₄.keepH).trans o₅.keepH
  obtain k₆ := k₅.trans o₆.keepH
  obtain m₆ : s₆.mem = s₀.mem := by rw [o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  obtain r5 : s₆.gpr .a2 = BitVec.ofNat 64 (uω s₀) := by
    rw [o₆.other _ (by decide), o₅.other _ (by decide), o₄.other _ (by decide), o₃.other _ (by decide), o₂.gpr,
      o₁.gpr, zext_eq]
  obtain r0 : s₆.gpr .t0 = 0 := by rw [o₆.other _ (by decide), o₅.gpr]; rfl
  obtain r12 : s₆.gpr .t2 = BitVec.ofNat 64 (uk s₀) := by
    rw [o₆.other _ (by decide), o₅.other _ (by decide), o₄.other _ (by decide), o₃.gpr,
      o₂.other _ (by decide), o₁.other _ (by decide), o₂.gpr, o₁.gpr, zext_eq]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, ofNat_lt (by omega_arith)]; exact hp.ωle), ofNat_lt (by omega_arith),
      ofNat_lt (by omega_arith)]
  obtain hwr : s₆.wr = [uhR s₀] := by rw [k₆.2.2, hp.wr]
  refine WP.seq (wp_loop_nz (ZInv s₀ s₆) (N := 256 * uk s₀) (by omega_arith) (fun t ht s h => ?_) (fun s h => ?_)
    ⟨by rw [o₆.gpr, k₅.gpr (r := .a3) (by decide), add0], ?_, Keep.refl _ _,
      by rw [m₆]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
  · -- A word.
    obtain hc : (uhR s₀).Contains (coeffAddr (uH s₀) t) 4 := Offset.contains_base _ (by omega_arith) (by omega_arith)
    refine Steps.wp_sw (by decide) (by rw [h.a7, add0]) (VG.Proof.MlKem.RISCV64.align4_add hp.al t)
      (by rw [h.keep.2.2, hwr]; exact ⟨_, List.mem_singleton_self _, hc⟩) fun s₁ m₁ =>
      Steps.wp_addi (by decide) fun s₂ o₂ => Steps.wp_subi (by decide) fun s₃ o₃ => WP.block_nil ?_
    obtain c9 : s₃.gpr .a6 = BitVec.ofNat 64 (256 * uk s₀ - (t + 1)) := by
      rw [o₃.gpr, o₂.other _ (by decide), m₁.gpr, h.a6, count_sub ht]
    obtain m₃ : s₃.mem = s.mem.writeW (coeffAddr (uH s₀) t) ((s.gpr .t0).setWidth 32) := by
      rw [o₃.mem, o₂.mem, m₁.mem]
    obtain z0 : (s.gpr .t0).setWidth 32 = 0 := by rw [h.keep.gpr (by decide), r0]; rfl
    refine ⟨⟨?_, c9, (h.keep.trans ((m₁.keepH.trans o₂.keepH).trans o₃.keepH)).mono (by decide), ?_,
      fun u hu => ?_⟩, by rw [c9]; exact count_nz ht (by omega_arith)⟩
    · rw [o₃.other _ (by decide), o₂.gpr, m₁.gpr, h.a7, ptr_add, Nat.mul_succ]
    · rw [m₃]; exact h.frame.writeW (List.mem_singleton_self _) _ hc
    · rw [m₃, z0]
      by_cases e : u = t
      · subst e; rw [coeffAt_eq, Mem.readW_writeW_self32]
      · rw [coeffAt_writeW_ne' _ _ (by omega_arith) (by omega_arith) e, h.zero u (by omega_arith)]
  · refine Steps.wp_li (by decide) fun s' o' => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, o'.gpr, ?_, ?_⟩
    · rw [o'.other _ (by decide), h.keep.gpr (by decide), k₆.gpr (by decide)]
    · rw [o'.other _ (by decide), h.keep.gpr (by decide), r5]
    · rw [o'.rd, h.keep.2.1, k₆.2.1]
    · rw [o'.wr, h.keep.2.2, k₆.2.2]
    · rw [o'.mem]; exact h.frame
    · rw [o'.other _ (by decide), h.keep.gpr (by decide), k₆.gpr (by decide)]
    · rw [o'.other _ (by decide), h.keep.gpr (by decide), r12]
    · rw [o'.mem]; exact h.zero

  · rw [o₆.other _ (by decide), o₅.other _ (by decide), o₄.gpr, add0, Nat.sub_zero, ← hl, ofNat_toNat64,
      o₃.other _ (by decide), o₂.other _ (by decide), o₁.other _ (by decide)]
/-! ## One coefficient -/

/-- The index of a state of the spec: 256 once a check failed. -/
def ixOf : Option (Array (Vector Bool n) × Nat) → Nat
  | some (_, idx) => idx
  | none => 256

/-- Setting coefficient `y[index]` of polynomial `i`. -/
theorem set_ok {i bound idx : Nat} (hi : i < uk s₀) (hidx : idx < uLen s₀) {hA : Array (Vector Bool n)}
    {s : State} (hP : PCom s₀ i bound s) (h11 : s.gpr .t1 = BitVec.ofNat 64 idx)
    (hh : HArr s.mem (uH s₀) (uk s₀) hA) :
    WP isa (.block hbuSet) s fun s' => PCom s₀ i bound s' ∧ Keep cRegs s s' ∧
      s'.gpr .t1 = BitVec.ofNat 64 (idx + 1) ∧
      HArr s'.mem (uH s₀) (uk s₀) (huSet i ((uYs s₀).getD idx 0).toNat hA) := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  have fH := hp.fitH
  have hl := hp.hlen
  obtain hb := ((uYs s₀).getD idx 0).isLt
  obtain hc : (uhR s₀).Contains (coeffAddr (uH s₀) (256 * i + ((uYs s₀).getD idx 0).toNat)) 4 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  unfold hbuSet
  refine Steps.wp_add fun s₁ o₁ => wp_lbz (a := uY s₀ + BitVec.ofNat 64 idx) (by decide) (by decide)
    (by rw [o₁.gpr, hP.com.a0, h11, add0]) (by rw [o₁.rd, o₁.wr]; exact yIn hp hP.com hidx) fun s₂ o₂ =>
    Steps.wp_sll (by decide) fun s₃ o₃ => Steps.wp_add fun s₄ o₄ => Steps.wp_li (by decide) fun s₅ o₅ =>
    Steps.wp_sw (a := coeffAddr (uH s₀) (256 * i + ((uYs s₀).getD idx 0).toNat)) (by decide) ?_
      (VG.Proof.MlKem.RISCV64.align4_add hp.al _) (by rw [o₅.wr, o₄.wr, o₃.wr, o₂.wr, o₁.wr, hP.com.wr, hp.wr]; exact ⟨_, .head _, hc⟩) fun s₆ m₆ =>
    Steps.wp_addi (by decide) fun s₇ o₇ => WP.block_nil ?_
  · rw [o₅.other _ (by decide), o₄.gpr, o₃.other _ (by decide), o₃.gpr, o₂.other _ (by decide),
      o₁.other _ (by decide), hP.a3, o₂.gpr, o₁.mem, yByte hp hP.com hidx, shl2_byte, add0, ptr_add]
    congr 2; omega_arith
  obtain k₇ := (((((o₁.keepH.trans o₂.keepH).trans o₃.keepH).trans o₄.keepH).trans o₅.keepH).trans m₆.keepH).trans
    o₇.keepH
  obtain mem₇ : s₇.mem = s.mem.writeW (coeffAddr (uH s₀) (256 * i + ((uYs s₀).getD idx 0).toNat)) (1 : BitVec 32) := by
    rw [o₇.mem, m₆.mem, o₅.gpr, o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]; rfl
  refine ⟨hP.of (k₇.mono (by decide)) (by rw [mem₇]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc),
    k₇.mono (by decide), ?_, by rw [mem₇]; exact harr_set hk8 hh hi hb⟩
  rw [o₇.gpr, m₆.gpr, o₅.other _ (by decide), o₄.other _ (by decide), o₃.other _ (by decide),
    o₂.other _ (by decide), o₁.other _ (by decide), h11, ofNat_succ]

omit hp in
/-- `r0 ← (index < bound)`. -/
theorem more_ok {i bound idx : Nat} (hb : bound < 256) (hidx : idx ≤ 256) {s : State}
    (hP : PCom s₀ i bound s) (h11 : s.gpr .t1 = BitVec.ofNat 64 idx) :
    WP isa (.block hbuMore) s fun s' => PCom s₀ i bound s' ∧ Keep cRegs s s' ∧ s'.mem = s.mem ∧
      s'.gpr .t1 = BitVec.ofNat 64 idx ∧ s'.gpr .t0 = BitVec.ofNat 64 (if idx < bound then 1 else 0) := by
  unfold hbuMore ltBit
  refine Steps.wp_sub fun s₁ o₁ => Steps.wp_srl (by decide) fun s₂ o₂ => WP.block_nil ?_
  obtain k₂ := o₁.keepH.trans o₂.keepH
  refine ⟨hP.of (k₂.mono (by decide)) (by rw [o₂.mem, o₁.mem]; exact Frame.refl _ _), k₂.mono (by decide),
    by rw [o₂.mem, o₁.mem], by rw [k₂.gpr (by decide), h11], ?_⟩
  rw [o₂.gpr, o₁.gpr, h11, hP.a5, ltBit_eq (by omega_arith) (by omega_arith)]

/-- A coefficient after the first: checked against the previous one. -/
theorem next_ok {i bound first idx : Nat} (hi : i < uk s₀) (hfi : first < idx) (hib : idx < bound)
    (hbω : bound ≤ uω s₀) {hA : Array (Vector Bool n)} {s : State} (hP : PCom s₀ i bound s)
    (h11 : s.gpr .t1 = BitVec.ofNat 64 idx) (hh : HArr s.mem (uH s₀) (uk s₀) hA) :
    WP isa hbuNext s fun s' => PCom s₀ i bound s' ∧ Keep cRegs s s' ∧
      SRel s₀ (huStep (uYs s₀) i first (hA, idx) 0) s' ∧
      s'.gpr .t0 = BitVec.ofNat 64 (if ixOf (huStep (uYs s₀) i first (hA, idx) 0) < bound then 1 else 0) := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  obtain hcb := ((uYs s₀).getD idx 0).isLt
  obtain hpb := ((uYs s₀).getD (idx - 1) 0).isLt
  unfold hbuNext ltBit
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (Steps.wp_add fun s₁ o₁ => wp_lbz (a := uY s₀ + BitVec.ofNat 64 idx) (by decide) (by decide)
    (by rw [o₁.gpr, hP.com.a0, h11, add0]) (by rw [o₁.rd, o₁.wr]; exact yIn hp hP.com (by omega_arith)) fun s₂ o₂ =>
    Steps.wp_subi (by decide) fun s₃ o₃ =>
    wp_lbz (a := uY s₀ + BitVec.ofNat 64 (idx - 1)) (by decide) (by decide)
      (by rw [o₃.gpr, o₂.other _ (by decide), o₁.gpr, hP.com.a0, h11, add0, ptr_pred _ (by omega_arith)])
      (by rw [o₃.rd, o₃.wr, o₂.rd, o₂.wr, o₁.rd, o₁.wr]; exact yIn hp hP.com (by omega_arith)) fun s₄ o₄ =>
    Steps.wp_sub fun s₅ o₅ => Steps.wp_srl (by decide) fun s₆ o₆ => WP.block_nil ?_)
  obtain k₆ := ((((o₁.keepH.trans o₂.keepH).trans o₃.keepH).trans o₄.keepH).trans o₅.keepH).trans o₆.keepH
  obtain m₆ : s₆.mem = s.mem := by rw [o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  obtain hP₆ : PCom s₀ i bound s₆ := hP.of (k₆.mono (by decide)) (by rw [m₆]; exact Frame.refl _ _)
  obtain r0 : s₆.gpr .t0 = BitVec.ofNat 64
      (if ((uYs s₀).getD (idx - 1) 0).toNat < ((uYs s₀).getD idx 0).toNat then 1 else 0) := by
    rw [o₆.gpr, o₅.gpr, o₄.gpr, o₄.other _ (by decide), o₃.other _ (by decide), o₂.gpr, o₃.mem, o₂.mem, o₁.mem,
      yByte hp hP.com (by omega_arith), yByte hp hP.com (by omega_arith), byte_ofNat, byte_ofNat,
      ltBit_eq (by omega_arith) (by omega_arith)]
  obtain h11₆ : s₆.gpr .t1 = BitVec.ofNat 64 idx := by rw [k₆.gpr (by decide), h11]
  refine WP.seq (WP.ite _ (eval_lt_zero r0) (fun hge => ?_) (fun hlt => ?_))
  · -- Not increasing: fail.
    obtain hge : ((uYs s₀).getD idx 0).toNat ≤ ((uYs s₀).getD (idx - 1) 0).toNat := of_decide_eq_true hge
    obtain hs : huStep (uYs s₀) i first (hA, idx) 0 = none := by
      simp only [huStep]; exact ite_eq_left_of_eq_true _ _ (eq_true ⟨hfi, hge⟩)
    rw [hs]
    refine Steps.wp_li (by decide) fun s₇ o₇ => WP.block_nil ?_
    obtain hP₇ : PCom s₀ i bound s₇ := hP₆.of (o₇.keepH.mono (by decide)) (by rw [o₇.mem]; exact Frame.refl _ _)
    refine WP.mono (more_ok (by omega_arith) (by decide) hP₇ o₇.gpr) fun s₈ ⟨hP₈, k₈, _, h11₈, r0₈⟩ =>
      ⟨hP₈, ((k₆.trans o₇.keepH).trans k₈).mono (by decide), h11₈, r0₈⟩
  · -- `y[index - 1] < y[index]`: set it.
    obtain hlt : ((uYs s₀).getD (idx - 1) 0).toNat < ((uYs s₀).getD idx 0).toNat := by
      have := of_decide_eq_false hlt; omega_arith
    obtain hs : huStep (uYs s₀) i first (hA, idx) 0 = some (huSet i ((uYs s₀).getD idx 0).toNat hA, idx + 1) := by
      simp only [huStep]; exact ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))
    rw [hs]
    refine WP.mono (set_ok hp hi (hA := hA) (by omega_arith) hP₆ h11₆ (by rw [m₆]; exact hh)) fun s₇ ⟨hP₇, k₇, h11₇, hh₇⟩ => ?_
    refine WP.mono (more_ok (by omega_arith) (by omega_arith) hP₇ h11₇) fun s₈ ⟨hP₈, k₈, m₈, h11₈, r0₈⟩ =>
      ⟨hP₈, ((k₆.trans k₇).trans k₈).mono (by decide), ⟨h11₈, by omega_arith, by rw [m₈]; exact hh₇⟩, r0₈⟩

/-! ## The coefficients of a polynomial -/

/-- The coefficients of polynomial `i`, from the index `first` up to `bound`. -/
theorem coefs_ok {i bound first : Nat} (hi : i < uk s₀) (hfb : first ≤ bound) (hbω : bound ≤ uω s₀)
    {hA : Array (Vector Bool n)} {s : State} (hP : PCom s₀ i bound s) (h11 : s.gpr .t1 = BitVec.ofNat 64 first)
    (hh : HArr s.mem (uH s₀) (uk s₀) hA) :
    WP isa hbuCoefs s fun s' => PCom s₀ i bound s' ∧ Keep cRegs s s' ∧
      SRel s₀ (optFold (huStep (uYs s₀) i first) (List.range (bound - first)) (hA, first)) s' := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  unfold hbuCoefs
  refine WP.seq (WP.mono (more_ok (by omega_arith) (by omega_arith) hP h11) fun s₁ ⟨hP₁, k₁, m₁, h11₁, r0₁⟩ => ?_)
  refine WP.ite _ (eval_lt_zero r0₁) (fun hge => ?_) (fun hlt => ?_)
  · -- `first = bound`: nothing.
    obtain e : bound - first = 0 := by have := of_decide_eq_true hge; omega_arith
    rw [e]
    exact WP.block_nil ⟨hP₁, k₁, h11₁, by omega_arith, by rw [m₁]; exact hh⟩
  obtain hlt : first < bound := by have := of_decide_eq_false hlt; omega_arith
  obtain F1 : optFold (huStep (uYs s₀) i first) (List.range 1) (hA, first) =
      some (huSet i ((uYs s₀).getD first 0).toNat hA, first + 1) := by
    simp only [List.range_one, optFold, huStep, gt_iff_lt, Nat.lt_irrefl, false_and, ↓reduceIte, Option.bind_some]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (set_ok hp hi (hA := hA) (by omega_arith) hP₁ h11₁ (by rw [m₁]; exact hh)) fun s₂ ⟨hP₂, k₂, h11₂, hh₂⟩ =>
    WP.mono (more_ok (by omega_arith) (by omega_arith) hP₂ h11₂) fun s₃ ⟨hP₃, k₃, m₃, h11₃, r0₃⟩ => ?_
  refine WP.ite _ (eval_lt_zero r0₃) (fun hge => ?_) (fun hlt' => ?_)
  · -- `first + 1 = bound`.
    obtain e : bound - first = 1 := by have := of_decide_eq_true hge; omega_arith
    rw [e, F1]
    exact WP.block_nil ⟨hP₃, ((k₁.trans k₂).trans k₃).mono (by decide), h11₃, by omega_arith, by rw [m₃]; exact hh₂⟩
  obtain hlt' : first + 1 < bound := by have := of_decide_eq_false hlt'; omega_arith
  -- The loop: after `t ≥ 1` coefficients, the state of the spec's fold.
  refine WP.loop (M := isa) (fun m s' => ∃ t, 1 ≤ t ∧ first + t < bound ∧ m = bound - first - t ∧
      ∃ hA' : Array (Vector Bool n), optFold (huStep (uYs s₀) i first) (List.range t) (hA, first) = some (hA', first + t) ∧
        PCom s₀ i bound s' ∧ Keep cRegs s s' ∧ s'.gpr .t1 = BitVec.ofNat 64 (first + t) ∧
        HArr s'.mem (uH s₀) (uk s₀) hA')
    (fun m s' ⟨t, ht1, htb, hm, hA', hF, hP', k', h11', hh'⟩ => ?_) _ s₃
    ⟨1, Nat.le_refl _, hlt', rfl, _, F1, hP₃, ((k₁.trans k₂).trans k₃).mono (by decide), h11₃, by rw [m₃]; exact hh₂⟩
  refine WP.mono (next_ok hp hi (first := first) (by omega_arith) htb hbω hP' h11' hh') fun s₄ ⟨hP₄, k₄, hS, r0₄⟩ => ?_
  obtain hF1 : optFold (huStep (uYs s₀) i first) (List.range (t + 1)) (hA, first) =
      huStep (uYs s₀) i first (hA', first + t) 0 := by
    rw [optFold_range_succ, hF]; rfl
  obtain k₄' : Keep cRegs s s₄ := (k'.trans k₄).mono (by decide)
  cases hst : huStep (uYs s₀) i first (hA', first + t) 0 with
  | none =>
    rw [hst] at hS r0₄
    refine .inl ⟨by rw [eval_lt_nonzero r0₄]; simp only [ixOf]; exact congrArg some (decide_eq_false (by omega_arith)),
      hP₄, k₄', ?_⟩
    rw [optFold_range_none _ (show t + 1 ≤ bound - first by omega_arith) (by rw [hF1, hst])]
    exact hS
  | some st =>
    obtain ⟨hA'', idx''⟩ := st
    obtain e := huStep_idx hst
    simp only at e
    rw [hst] at hS r0₄
    simp only [ixOf] at r0₄
    by_cases hc : idx'' < bound
    · exact .inr ⟨by rw [eval_lt_nonzero r0₄]; exact congrArg some (decide_eq_true hc), _, by omega_arith,
        t + 1, by omega_arith, by omega_arith, rfl, hA'', by rw [hF1, hst, e]; rfl, hP₄, k₄', by rw [hS.1, e]; rfl, hS.2.2⟩
    · refine .inl ⟨by rw [eval_lt_nonzero r0₄]; exact congrArg some (decide_eq_false hc), hP₄, k₄', ?_⟩
      rw [show bound - first = t + 1 by omega_arith, hF1, hst]
      exact hS

end

/-! ## The whole function

The polynomials (`upoly_ok`: one of them is `huPoly` of the spec, or nothing
once a check failed), the trailing bytes (`trail_ok`: `huTrail`), the return
value, and the whole function (`correct`), from the steps above.
-/

/-- The spec's state after `i` polynomials. -/
abbrev uSt (s₀ : State) (i : Nat) : Option (Array (Vector Bool n) × Nat) :=
  optFold (huPoly (uω s₀) (uYs s₀)) (List.range i) (Array.replicate (uk s₀) noHint, 0)

/-- Before polynomial `i`. -/
structure OInv (s₀ : State) (i : Nat) (s : State) : Prop where
  com : UCom s₀ s
  a3 : s.gpr .a3 = uH s₀ + BitVec.ofNat 64 (1024 * i)
  a7 : s.gpr .a7 = uY s₀ + BitVec.ofNat 64 (uω s₀ + i)
  t2 : s.gpr .t2 = BitVec.ofNat 64 (uk s₀ - i)
  st : SRel s₀ (uSt s₀ i) s

theorem fail_ok {s : State} :
    WP isa hbuFail s fun s' => Keep [.t1] s s' ∧ s'.mem = s.mem ∧ s'.gpr .t1 = BitVec.ofNat 64 256 :=
  Steps.wp_li (by decide) fun _ o => WP.block_nil ⟨o.keepH, o.mem, o.gpr⟩

/-- `ltBit t x y` of numbers. -/
theorem lt_ok {t x y : Reg} {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) {s : State}
    (hx : s.gpr x = BitVec.ofNat 64 a) (hy : s.gpr y = BitVec.ofNat 64 b) :
    WP isa (.block (ltBit t x y)) s fun s' => Keep [t] s s' ∧ s'.mem = s.mem ∧
      s'.gpr t = BitVec.ofNat 64 (if a < b then 1 else 0) := by
  unfold ltBit
  refine Steps.wp_sub fun s₁ o₁ => Steps.wp_srl (by decide) fun s₂ o₂ => WP.block_nil ⟨(o₁.keepH.trans o₂.keepH).mono (by simp),
    by rw [o₂.mem, o₁.mem], by rw [o₂.gpr, o₁.gpr, hx, hy, ltBit_eq ha hb]⟩

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- What a polynomial leaves before the pointers move on. -/
def PPost (s₀ : State) (i : Nat) (s s' : State) : Prop :=
  Keep [.t0, .a5, .a6, .t1] s s' ∧ UCom s₀ s' ∧ SRel s₀ (uSt s₀ (i + 1)) s'

omit hp in
theorem uSt_succ (i : Nat) : uSt s₀ (i + 1) = (uSt s₀ i).bind fun st => huPoly (uω s₀) (uYs s₀) st i :=
  optFold_range_succ _ _ _

/-- Polynomial `i`, unless a check failed. -/
theorem poly_ok {i : Nat} (hi : i < uk s₀) {s : State} (hI : OInv s₀ i s) :
    WP isa hbuPoly s (PPost s₀ i s) := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  have hS := hI.st
  obtain hsucc := uSt_succ (s₀ := s₀) i
  unfold hbuPoly
  cases hst : uSt s₀ i with
  | none =>
    rw [hst] at hS hsucc
    refine WP.seq (WP.mono (lt_ok (a := uω s₀) (b := 256) (by omega_arith) (by decide) hI.com.a2 hS)
      fun s₁ ⟨k₁, m₁, r0₁⟩ => ?_)
    refine WP.ite _ (eval_lt_zero r0₁) (fun h => absurd (of_decide_eq_true h) (by omega_arith)) fun _ =>
      WP.block_nil ⟨k₁.mono (by decide), hI.com.of k₁ (by decide) (by decide) (by rw [m₁]; exact Frame.refl _ _), ?_⟩
    rw [hsucc]; show s₁.gpr .t1 = _; rw [k₁.gpr (by decide), hS]
  | some st =>
    obtain ⟨hA, idx⟩ := st
    rw [hst] at hS hsucc
    obtain ⟨h11, hidx, hh⟩ := hS
    have hP : huPoly (uω s₀) (uYs s₀) (hA, idx) i = if ((uYs s₀).getD (uω s₀ + i) 0).toNat < idx ∨
        ((uYs s₀).getD (uω s₀ + i) 0).toNat > uω s₀ then none else
        optFold (huStep (uYs s₀) i idx) (List.range (((uYs s₀).getD (uω s₀ + i) 0).toNat - idx)) (hA, idx) := rfl
    simp only [Option.bind_some] at hsucc
    rw [hP] at hsucc
    refine WP.seq (WP.mono (lt_ok (a := uω s₀) (b := idx) (by omega_arith) (by omega_arith) hI.com.a2 h11)
      fun s₁ ⟨k₁, m₁, r0₁⟩ => ?_)
    refine WP.ite _ (eval_lt_zero r0₁) (fun _ => ?_) fun h => absurd (of_decide_eq_false h) (by omega_arith)
    obtain ⟨bound, hbound⟩ : ∃ b, ((uYs s₀).getD (uω s₀ + i) 0).toNat = b := ⟨_, rfl⟩
    rw [hbound] at hsucc
    obtain hb : bound < 256 := hbound ▸ ((uYs s₀).getD (uω s₀ + i) 0).isLt
    obtain hc₁ : UCom s₀ s₁ := hI.com.of k₁ (by decide) (by decide) (by rw [m₁]; exact Frame.refl _ _)
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine wp_lbz (a := uY s₀ + BitVec.ofNat 64 (uω s₀ + i)) (by decide) (by decide)
      (by rw [k₁.gpr (by decide), hI.a7, add0]) (yIn hp hc₁ (by omega_arith)) fun s₂ o₂ => WP.block_nil ?_
    obtain hc₂ : UCom s₀ s₂ := hc₁.of o₂.keepH (by decide) (by decide) (by rw [o₂.mem]; exact Frame.refl _ _)
    obtain r8 : s₂.gpr .a5 = BitVec.ofNat 64 bound := by rw [o₂.gpr, yByte hp hc₁ (by omega_arith), byte_ofNat, hbound]
    obtain h11₂ : s₂.gpr .t1 = BitVec.ofNat 64 idx := by rw [o₂.other _ (by decide), k₁.gpr (by decide), h11]
    refine WP.mono (lt_ok (by omega_arith) (by omega_arith) r8 h11₂) fun s₃ ⟨k₃, m₃, r0₃⟩ => ?_
    obtain k₃' : Keep [.t0, .a5, .a6, .t1] s s₃ := ((k₁.trans o₂.keepH).trans k₃).mono (by decide)
    obtain m₃' : s₃.mem = s.mem := by rw [m₃, o₂.mem, m₁]
    obtain hc₃ : UCom s₀ s₃ := hc₂.of k₃ (by decide) (by decide) (by rw [m₃]; exact Frame.refl _ _)
    obtain fail : ∀ {s'}, Keep [.t0, .t1] s₃ s' → s'.mem = s₃.mem → s'.gpr .t1 = BitVec.ofNat 64 256 →
        bound < idx ∨ bound > uω s₀ → PPost s₀ i s s' := fun k' m' h11' hc => by
      refine ⟨(k₃'.trans k').mono (by decide), hc₃.of k' (by decide) (by decide) (by rw [m']; exact Frame.refl _ _),
        ?_⟩
      rw [hsucc, ite_eq_left_of_eq_true _ _ (eq_true hc)]; exact h11'
    refine WP.ite _ (eval_lt_zero r0₃) (fun hge => ?_)
      fun hlt => WP.mono fail_ok fun s' ⟨k', m', h11'⟩ => fail (k'.mono (by decide)) m' h11' (.inl (by have := of_decide_eq_false hlt; omega_arith))
    obtain hge : idx ≤ bound := of_decide_eq_true hge
    refine WP.seq (WP.mono (lt_ok (a := uω s₀) (b := bound) (by omega_arith) (by omega_arith) hc₃.a2
      (by rw [k₃.gpr (by decide), r8])) fun s₄ ⟨k₄, m₄, r0₄⟩ => ?_)
    refine WP.ite _ (eval_lt_zero r0₄) (fun hle => ?_)
      fun hgt => WP.mono fail_ok fun s' ⟨k', m', h11'⟩ => fail (s' := s') ((k₄.trans k').mono (by decide))
        (by rw [m', m₄]) h11' (.inr (by have := of_decide_eq_false hgt; omega_arith))
    obtain hle : bound ≤ uω s₀ := of_decide_eq_true hle
    obtain hP₄ : PCom s₀ i bound s₄ := ⟨hc₃.of k₄ (by decide) (by decide) (by rw [m₄]; exact Frame.refl _ _),
      by rw [k₄.gpr (by decide), k₃.gpr (by decide), o₂.other _ (by decide), k₁.gpr (by decide), hI.a3],
      by rw [k₄.gpr (by decide), k₃.gpr (by decide), r8]⟩
    refine WP.mono (coefs_ok hp hi (hA := hA) hge hle hP₄ (by rw [k₄.gpr (by decide), k₃.gpr (by decide), h11₂])
      (by rw [m₄, m₃']; exact hh))
      fun s' ⟨hP', k', hS'⟩ => ⟨((k₃'.trans k₄).trans k').mono (by decide), hP'.com, ?_⟩
    rw [hsucc, ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]; exact hS'

omit hp in
theorem SRel.of {st : Option (Array (Vector Bool n) × Nat)} {s s' : State} (h : SRel s₀ st s)
    (h11 : s'.gpr .t1 = s.gpr .t1) (hm : s'.mem = s.mem) : SRel s₀ st s' := by
  cases st with
  | none => exact h11.trans h
  | some st => obtain ⟨hA, idx⟩ := st; exact ⟨h11.trans h.1, h.2.1, by rw [hm]; exact h.2.2⟩

/-- Polynomial `i`, and the pointers and the count moved on. -/
theorem upoly_ok {i : Nat} (hi : i < uk s₀) {s : State} (hI : OInv s₀ i s) :
    WP isa (.seq hbuPoly (.block [.addi .a7 .a7 1, .addi .a3 .a3 1024, .addi .t2 .t2 (-1)])) s fun s' =>
      OInv s₀ (i + 1) s' ∧ (s'.gpr .t2 != 0) = decide (i + 1 ≠ uk s₀) := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  refine WP.seq (WP.mono (poly_ok hp hi hI) fun s₁ ⟨k₁, hc₁, hS₁⟩ => ?_)
  refine Steps.wp_addi (by decide) fun s₂ o₂ => Steps.wp_addi (by decide) fun s₃ o₃ =>
    Steps.wp_subi (by decide) fun s₄ o₄ => WP.block_nil ?_
  obtain k₄ := (o₂.keepH.trans o₃.keepH).trans o₄.keepH
  obtain m₄ : s₄.mem = s₁.mem := by rw [o₄.mem, o₃.mem, o₂.mem]
  obtain c12 : s₄.gpr .t2 = BitVec.ofNat 64 (uk s₀ - (i + 1)) := by
    rw [o₄.gpr, o₃.other _ (by decide), o₂.other _ (by decide), k₁.gpr (by decide), hI.t2, count_sub hi]
  refine ⟨⟨hc₁.of k₄ (by decide) (by decide) (by rw [m₄]; exact Frame.refl _ _), ?_, ?_, c12,
    hS₁.of (k₄.gpr (by decide)) m₄⟩, by rw [c12]; exact count_nz hi (by omega_arith)⟩
  · rw [o₄.other _ (by decide), o₃.gpr, o₂.other _ (by decide), k₁.gpr (by decide), hI.a3, ptr_add, Nat.mul_succ]
  · rw [o₄.other _ (by decide), o₃.other _ (by decide), o₂.gpr, k₁.gpr (by decide), hI.a7, ptr_add,
      Nat.add_assoc]

/-- The polynomials, from the state after zeroing `h`. -/
theorem main_ok {s : State} (hz : ZPost s₀ s) : WP isa hbuMain s (OInv s₀ (uk s₀)) := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  unfold hbuMain
  refine WP.seq (Steps.wp_add fun s₁ o₁ => WP.block_nil ?_)
  refine wp_loop_nz (OInv s₀) (N := uk s₀) (by omega_arith) (fun i hi s hI => upoly_ok hp hi hI) (fun _ h => h)
    ⟨hz.com.of o₁.keepH (by decide) (by decide) (by rw [o₁.mem]; exact Frame.refl _ _),
      by rw [o₁.other _ (by decide), hz.a3, Nat.mul_zero]; exact (add0 _).symm,
      by rw [o₁.gpr, hz.com.a0, hz.com.a2, Nat.add_zero],
      by rw [o₁.other _ (by decide), hz.t2, Nat.sub_zero],
      ⟨by rw [o₁.other _ (by decide), hz.t1]; rfl, Nat.zero_le _, by rw [o₁.mem]; exact harr_zero hz.zero⟩⟩

/-! ## The bytes after the last index -/

/-- Once a check failed, nothing. -/
theorem trail_none {s : State} (hc : UCom s₀ s) (h11 : s.gpr .t1 = BitVec.ofNat 64 256) :
    WP isa hbuTrail s fun s' => UCom s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .t1 = BitVec.ofNat 64 256 := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  unfold hbuTrail
  refine WP.seq (WP.mono (lt_ok (by decide) (by omega_arith) h11 hc.a2) fun s₁ ⟨k₁, m₁, r0₁⟩ => ?_)
  refine WP.ite _ (eval_lt_zero r0₁) (fun _ => WP.block_nil ⟨hc.of k₁ (by decide) (by decide)
    (by rw [m₁]; exact Frame.refl _ _), m₁, by rw [k₁.gpr (by decide), h11]⟩)
    fun h => absurd (of_decide_eq_false h) (by omega_arith)

/-- The bytes from the index `idx` up to `ω` are zero, or the index becomes 256. -/
theorem trail_some {idx : Nat} (hidx : idx ≤ uω s₀) {s : State} (hc : UCom s₀ s)
    (h11 : s.gpr .t1 = BitVec.ofNat 64 idx) :
    WP isa hbuTrail s fun s' => UCom s₀ s' ∧ s'.mem = s.mem ∧
      s'.gpr .t1 = BitVec.ofNat 64
        (if (optFold (huTrail (uYs s₀)) (List.range' idx (uω s₀ - idx)) ()).isSome then uω s₀ else 256) := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  unfold hbuTrail
  refine WP.seq (WP.mono (lt_ok (by omega_arith) (by omega_arith) h11 hc.a2) fun s₁ ⟨k₁, m₁, r0₁⟩ => ?_)
  obtain hc₁ : UCom s₀ s₁ := hc.of k₁ (by decide) (by decide) (by rw [m₁]; exact Frame.refl _ _)
  refine WP.ite _ (eval_lt_zero r0₁) (fun hge => ?_) (fun hlt => ?_)
  · -- `idx = ω`: nothing.
    obtain e : uω s₀ - idx = 0 := by have := of_decide_eq_true hge; omega_arith
    refine WP.block_nil ⟨hc₁, m₁, ?_⟩
    rw [k₁.gpr (by decide), h11, e]
    simp only [List.range'_zero, optFold, Option.isSome_some, ↓reduceIte]
    congr 1; omega_arith
  obtain hlt : idx < uω s₀ := by have := of_decide_eq_false hlt; omega_arith
  refine WP.loop (M := isa) (fun m s' => ∃ u, m = uω s₀ - idx - u ∧ idx + u < uω s₀ ∧
      optFold (huTrail (uYs s₀)) (List.range' idx u) () = some () ∧ s'.gpr .t1 = BitVec.ofNat 64 (idx + u) ∧
      UCom s₀ s' ∧ s'.mem = s.mem)
    (fun m s' ⟨u, hm, hu, hF, h11', hc', hm'⟩ => ?_) _ s₁
    ⟨0, rfl, by omega_arith, rfl, by rw [k₁.gpr (by decide), h11]; rfl, hc₁, m₁⟩
  obtain hF1 : optFold (huTrail (uYs s₀)) (List.range' idx (u + 1)) () = huTrail (uYs s₀) () (idx + u) := by
    rw [optFold_range'_succ, hF]; rfl
  refine WP.seq (Steps.wp_add fun s₂ o₂ => wp_lbz (a := uY s₀ + BitVec.ofNat 64 (idx + u)) (by decide) (by decide)
    (by rw [o₂.gpr, hc'.a0, h11', add0]) (by rw [o₂.rd, o₂.wr]; exact yIn hp hc' (by omega_arith)) fun s₃ o₃ =>
    WP.block_nil ?_)
  obtain k₃ := o₂.keepH.trans o₃.keepH
  obtain m₃ : s₃.mem = s'.mem := by rw [o₃.mem, o₂.mem]
  obtain hc₃ : UCom s₀ s₃ := hc'.of k₃ (by decide) (by decide) (by rw [m₃]; exact Frame.refl _ _)
  obtain r9 : s₃.gpr .a6 = BitVec.ofNat 64 ((uYs s₀).getD (idx + u) 0).toNat := by
    rw [o₃.gpr, o₂.mem, yByte hp hc' (by omega_arith), byte_ofNat]
  obtain hyb := ((uYs s₀).getD (idx + u) 0).isLt
  refine WP.seq (WP.ite _ (eval_zero_ofNat s₃ .a6 (by omega_arith) r9) (fun hz => ?_) (fun hnz => ?_))
  · -- A zero byte: next.
    obtain hz : (uYs s₀).getD (idx + u) 0 = 0 := by
      apply BitVec.eq_of_toNat_eq; exact of_decide_eq_true hz
    obtain hF2 : optFold (huTrail (uYs s₀)) (List.range' idx (u + 1)) () = some () := by
      rw [hF1]; simp only [huTrail, hz, ne_eq, not_true_eq_false, ↓reduceIte]
    refine Steps.wp_addi (by decide) fun s₄ o₄ => WP.block_nil ?_
    obtain h11₄ : s₄.gpr .t1 = BitVec.ofNat 64 (idx + (u + 1)) := by
      rw [o₄.gpr, k₃.gpr (by decide), h11', ofNat_succ, Nat.add_assoc]
    obtain hc₄ : UCom s₀ s₄ := hc₃.of o₄.keepH (by decide) (by decide) (by rw [o₄.mem]; exact Frame.refl _ _)
    refine WP.mono (lt_ok (by omega_arith) (by omega_arith) h11₄ hc₄.a2) fun s₅ ⟨k₅, m₅, r0₅⟩ => ?_
    obtain hc₅ : UCom s₀ s₅ := hc₄.of k₅ (by decide) (by decide) (by rw [m₅]; exact Frame.refl _ _)
    obtain h11₅ : s₅.gpr .t1 = BitVec.ofNat 64 (idx + (u + 1)) := by rw [k₅.gpr (by decide), h11₄]
    obtain hm₅ : s₅.mem = s.mem := by rw [m₅, o₄.mem, m₃, hm']
    by_cases e : idx + (u + 1) < uω s₀
    · exact .inr ⟨by rw [eval_lt_nonzero r0₅]; exact congrArg some (decide_eq_true e), _, by omega_arith, u + 1, rfl, e,
        hF2, h11₅, hc₅, hm₅⟩
    · refine .inl ⟨by rw [eval_lt_nonzero r0₅]; exact congrArg some (decide_eq_false e), hc₅, hm₅, ?_⟩
      rw [show uω s₀ - idx = u + 1 by omega_arith, hF2, h11₅]
      simp only [Option.isSome_some, ↓reduceIte]
      congr 1; omega_arith
  · -- A nonzero byte: fail.
    obtain hnz : (uYs s₀).getD (idx + u) 0 ≠ 0 := fun e => by
      have := of_decide_eq_false hnz; rw [e] at this; exact this rfl
    obtain hn : optFold (huTrail (uYs s₀)) (List.range' idx (uω s₀ - idx)) () = none :=
      optFold_range'_none _ _ (show u + 1 ≤ uω s₀ - idx by omega_arith)
        (by rw [hF1, huTrail, ite_eq_left_of_eq_true _ _ (eq_true hnz)])
    refine WP.mono fail_ok fun s₄ ⟨k₄, m₄, h11₄⟩ => ?_
    obtain hc₄ : UCom s₀ s₄ := hc₃.of k₄ (by decide) (by decide) (by rw [m₄]; exact Frame.refl _ _)
    refine WP.mono (lt_ok (by decide) (by omega_arith) h11₄ hc₄.a2) fun s₅ ⟨k₅, m₅, r0₅⟩ => ?_
    refine .inl ⟨by rw [eval_lt_nonzero r0₅]; exact congrArg some (decide_eq_false (by omega_arith)),
      hc₄.of k₅ (by decide) (by decide) (by rw [m₅]; exact Frame.refl _ _), by rw [m₅, m₄, m₃, hm'], ?_⟩
    rw [k₅.gpr (by decide), h11₄, hn]
    rfl

/-! ## The return value -/

omit hp in
theorem ret_ok {x ω : Nat} (hx : x ≤ 256) (hω : ω ≤ 80) {s : State} (h11 : s.gpr .t1 = BitVec.ofNat 64 x)
    (h5 : s.gpr .a2 = BitVec.ofNat 64 ω) :
    WP isa (.block hbuRet) s fun s' => s'.mem = s.mem ∧
      (s'.gpr .a0).setWidth 32 = if x ≤ ω then 1 else 0 := by
  unfold hbuRet
  refine Steps.wp_sub fun s₁ o₁ => Steps.wp_srl (by decide) fun s₂ o₂ => Steps.wp_li (by decide) fun s₃ o₃ =>
    Steps.wp_sub fun s₄ o₄ => WP.block_nil ⟨by rw [o₄.mem, o₃.mem, o₂.mem, o₁.mem], ?_⟩
  rw [o₄.gpr, o₃.gpr, o₃.other _ (by decide), o₂.gpr, o₁.gpr, h5, h11, ltBit_eq (by omega_arith) (by omega_arith)]
  by_cases e : x ≤ ω
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)), ite_eq_left_of_eq_true _ _ (eq_true e)]; rfl
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith)), ite_eq_right_of_eq_false _ _ (eq_false e)]; rfl

/-! ## The function -/

/-- The registers `hintBitUnpack` writes. -/
abbrev hbuRegs : List Reg := [.t0, .a0, .a2, .a3, .a5, .a6, .a7, .t1, .t2]

/-- The postcondition, as `sig_post` states it. -/
def UPost (s₀ s' : State) : Prop :=
  match hintBitUnpack (uω s₀) (uk s₀) (bytesAt s₀.mem (uY s₀) (uLen s₀)) with
  | some hint => (s'.gpr .a0).setWidth 32 = 1 ∧ HintIs s'.mem (uH s₀) (uk s₀) hint
  | none => (s'.gpr .a0).setWidth 32 = 0

theorem correct : WP isa Impl.MlDsa.RISCV64.Pack.hintBitUnpack s₀ fun s' => UPost s₀ s' ∧ Keep hbuRegs s₀ s' := by
  obtain ⟨hk4, hk8, -, hω80, hsum, hL88⟩ := ufacts hp
  refine WP.keep hbuRegs ?_ (by decide +kernel)
  unfold Impl.MlDsa.RISCV64.Pack.hintBitUnpack
  refine WP.seq (WP.mono (zero_ok hp) fun s₁ hz => WP.seq (WP.mono (main_ok hp hz) fun s₂ hI => ?_))
  have hS := hI.st
  cases hst : uSt s₀ (uk s₀) with
  | none =>
    rw [hst] at hS
    have e : optFold (huPoly (uω s₀) (bytesAt s₀.mem (uY s₀) (uLen s₀)).toArray) (List.range (uk s₀))
        (Array.replicate (uk s₀) noHint, 0) = none := hst
    refine WP.seq (WP.mono (trail_none hp hI.com hS) fun s₃ ⟨hc₃, m₃, h11₃⟩ =>
      WP.mono (ret_ok (by decide) hω80 h11₃ hc₃.a2) fun s₄ ⟨_, r3₄⟩ => ?_)
    simp only [UPost, hintBitUnpack_eq, e]
    rw [r3₄, ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]
  | some st =>
    obtain ⟨hA, idx⟩ := st
    rw [hst] at hS
    obtain ⟨h11, hidx, hh⟩ := hS
    have e : optFold (huPoly (uω s₀) (bytesAt s₀.mem (uY s₀) (uLen s₀)).toArray) (List.range (uk s₀))
        (Array.replicate (uk s₀) noHint, 0) = some (hA, idx) := hst
    refine WP.seq (WP.mono (trail_some hp hidx hI.com h11) fun s₃ ⟨hc₃, m₃, h11₃⟩ =>
      WP.mono (ret_ok (by split <;> omega_arith) hω80 h11₃ hc₃.a2) fun s₄ ⟨m₄, r3₄⟩ => ?_)
    cases hT : optFold (huTrail (uYs s₀)) (List.range' idx (uω s₀ - idx)) () with
    | none =>
      have eT : optFold (huTrail (bytesAt s₀.mem (uY s₀) (uLen s₀)).toArray) (List.range' idx (uω s₀ - idx)) () =
        none := hT
      simp only [UPost, hintBitUnpack_eq, e, eT, Option.map_none]
      rw [hT] at r3₄
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at r3₄
      rw [r3₄, ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]
    | some u =>
      have eT : optFold (huTrail (bytesAt s₀.mem (uY s₀) (uLen s₀)).toArray) (List.range' idx (uω s₀ - idx)) () =
        some u := hT
      simp only [UPost, hintBitUnpack_eq, e, eT, Option.map_some]
      rw [hT] at r3₄
      simp only [Option.isSome_some, ↓reduceIte] at r3₄
      refine ⟨by rw [r3₄, ite_eq_left_of_eq_true _ _ (eq_true (Nat.le_refl _))], ?_⟩
      rw [m₄, m₃]
      exact harr_hintIs hh

end

end VG.Proof.MlDsa.RISCV64.Pack.Hint.Unpack

end

end

/-!
# ML-DSA on RISC-V: `vg_mldsa_hint_bit_unpack`, constant time and `Verified`

Constant time but for its input, as on AArch64: zeroing `h` leaks only the
pointers and `hlen` (the taint analysis), and leaves states that agree on
`k`, `ω`, the pointers and the index, and on all the memory the rest may
access (the input `y`, which the contract lets it leak, and `h`, zeroed);
`memTaint` proves the rest. `omega` is a `u32`, whose register's upper bits
the two runs need not agree on: the code zero-extends it before using it.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Pack.Hint.Unpack

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.RISCV64.Pack.Hint (MAgree memTaint wp_sp)

theorem pre_of {s : State} (h : (hintBitUnpackContract RISCV64.abi).pre s) : UPre s := by
  sig_pre [hintBitUnpackContract, hintBitUnpackSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- The public registers after zeroing `h`: `y`, `ω`, `h`, the index and `k`. -/
abbrev hbuTaint : VG.RISCV64.Taint.T := VG.RISCV64.Taint.ofRegs [.a0, .a2, .a3, .t1, .t2]

theorem ct : ConstantTime isa (hintBitUnpackContract RISCV64.abi).pre (hintBitUnpackContract RISCV64.abi).pub
    Impl.MlDsa.RISCV64.Pack.hintBitUnpack := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold Impl.MlDsa.RISCV64.Pack.hintBitUnpack
  refine RelCT.seq (R := MAgree hbuTaint) ?_
    (RelCT.taint (A := memTaint) hbuTaint (fun _ _ h => h) (by taint_decide))
  refine RelCT.mono (RelCT.wpDep (F := fun (s₀ s : State) => ZPost s₀ s ∧ s.sp = s₀.sp)
    (RelCT.taint (A := taint) (VG.RISCV64.Taint.ofRegs [.a3, .a4]) ?_ (by taint_decide))
    (fun x y ⟨hx, hy, _⟩ => ⟨wp_sp (zero_ok (pre_of hx)), wp_sp (zero_ok (pre_of hy))⟩)) (fun _ _ h => h) ?_
  · rintro a b ⟨_, _, hab⟩
    sig_pub [hintBitUnpackContract, hintBitUnpackSig, RISCV64.abi, RISCV64.argRegs] at hab
    obtain ⟨hsp, -, -, -, -, h6, h7⟩ := hab
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.RISCV64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h6
    · exact h7
  rintro x' y' ⟨_, x, y, ⟨hx, hy, hpb⟩, ⟨fx, spx⟩, ⟨fy, spy⟩⟩
  have px := pre_of hx
  have py := pre_of hy
  sig_pub [hintBitUnpackContract, hintBitUnpackSig, RISCV64.abi, RISCV64.argRegs] at hpb
  obtain ⟨hsp, hleak, p3, p4, p5, p6, p7⟩ := hpb
  have hω : uω x = uω y := by simp only [uω, w32, p5]
  have hrd : x'.rd = y'.rd := by rw [fx.com.rd, fy.com.rd, px.rd, py.rd]; simp only [uyR, uY, uLen, p3, p4]
  have hwr : x'.wr = y'.wr := by rw [fx.com.wr, fy.com.wr, px.wr, py.wr]; simp only [uhR, uH, p6, p7]
  refine ⟨⟨by rw [spx, spy, hsp], fun r hr => ?_⟩, hrd, hwr, fun a ha => ?_⟩
  · simp only [VG.RISCV64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [fx.com.a0, fy.com.a0]; simp only [uY, p3]
    · rw [fx.com.a2, fy.com.a2, hω]
    · rw [fx.a3, fy.a3]; simp only [uH, p6]
    · rw [fx.t1, fy.t1]
    · rw [fx.t2, fy.t2]; simp only [uk, uLen, p4, hω]
  · rw [fx.com.rd, fx.com.wr, px.rd, px.wr] at ha
    obtain ⟨r, hr, hc⟩ := ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · -- `y`: as on entry, where the runs agree.
      have hxy : ¬ (uhR x).Contains a 1 := fun hc' => px.d_yh a hc hc'
      rw [fx.com.frame a (fun r hr hc' => by simp only [List.mem_singleton] at hr; subst hr; exact hxy hc'),
        fy.com.frame a (fun r hr hc' => by
          simp only [List.mem_singleton] at hr; subst hr
          simp only [uhR, uH, ← p6, ← p7] at hc'
          exact hxy hc')]
      have hb : bytesAt x.mem (uY x) (uLen x) = bytesAt y.mem (uY y) (uLen y) := map_toNat_inj hleak
      have hlt : (a - uY x).toNat < uLen x := by simp only [Region.Contains] at hc; omega_using [hc]
      have fY := px.fitY
      have ea : a = uY x + BitVec.ofNat 64 (a - uY x).toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      have := congrArg (fun l => l.getD (a - uY x).toNat 0) hb
      rw [VG.Proof.MlKem.bytesAt_getD _ _ hlt, VG.Proof.MlKem.bytesAt_getD _ _ (show _ < uLen y by
        simpa only [uLen, ← p4] using hlt), ← ea, show uY y = uY x by simp only [uY, p3], ← ea] at this
      exact this
    · -- `h`: zeros.
      have hl := px.hlen
      have h₁ := byte_of_zero_words (m := x'.mem) (p := uH x) (N := (x.gpr .a4).toNat)
        (fun t ht => fx.zero t (by omega_using [hl, ht])) hc
      have h₂ := byte_of_zero_words (m := y'.mem) (p := uH y) (N := (y.gpr .a4).toNat)
        (fun t ht => fy.zero t (by have := py.hlen; omega_using [ht, this])) (by simpa only [uhR, uH, ← p6, ← p7] using hc)
      rw [h₁, h₂]

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 84 | .a2 => 80 | .a3 => 0x3000 | .a4 => 1024 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 84⟩]
  wr := [⟨0x3000, 4096⟩]

end VG.Proof.MlDsa.RISCV64.Pack.Hint.Unpack

namespace VG.Proof.MlDsa.RISCV64.Pack

open VG VG.RISCV64 VG.Spec.MlDsa
open VG.Proof.MlDsa.RISCV64.Pack.Hint.Unpack

theorem hintBitUnpack_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Pack.hintBitUnpack (hintBitUnpackContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, ct, ⟨satState, ?_⟩⟩
  · obtain ⟨t, s', he, hpost, hk⟩ := correct (pre_of hs)
    refine ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), ?_⟩
    sig_post [hintBitUnpackContract, hintBitUnpackSig, RISCV64.abi, RISCV64.argRegs]
    exact hpost
  · sig_apply_check
    · decide +kernel
    · sig_reduce [hintBitUnpackContract, hintBitUnpackSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact Region.disjoint_of_sep (by decide)
        | decide +kernel

end VG.Proof.MlDsa.RISCV64.Pack
