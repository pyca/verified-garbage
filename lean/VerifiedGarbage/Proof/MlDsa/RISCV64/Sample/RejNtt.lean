module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Sample.Pro
public import VerifiedGarbage.Proof.MlDsa.Sample.RejNtt
public import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Contracts
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Sample.Pro
meta import VerifiedGarbage.Proof.MlDsa.Sample.RejNtt
meta import VerifiedGarbage.Proof.MlDsa.Contract
meta import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
meta import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Common
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Contracts
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.SigEval

/-!
# ML-DSA on RISC-V: `vg_mldsa_rej_ntt_poly`

As on PPC64LE (`Proof/MlDsa/PPC64LE/Sample/RejNtt.lean` and `RejNttCT.lean`).
The function runs in pieces: the prologue (`J0`), then a try with `N = 280`
(`try_ok`): the sponge, whose output is `G(ρ, 3 N)` (`J6`), the first `3 N`
bytes of `G(ρ, 1008)` (`G_take`), and the loop, iteration `t` of which
starts from `LAt N σ t`, with the coefficients `rnFold` samples from the
first `3t` bytes of output stored. If those are 256, they are all of
`G(ρ, 1008)`'s (`Lt_full`); if not, a try with `N = 336` runs from the
prologue's state again. An iteration loads the value of its 3 bytes and tests
whether to keep it (`pieceA`: it is less than `q` and `j < 256`), stores it
if so (`pieceB`, what `rnStep` does), and steps (`pieceC`). Two runs from
calls that agree on the seed take the same branches and addresses
(`all_ct`), and `rejNTT_verified` puts them together.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Sample.RejNtt

open VG VG.RISCV64
open VG.Proof.MlDsa.RISCV64.Sample
open VG.Impl.MlDsa.RISCV64.Sample
open VG.Impl.Sha3.RISCV64.Stream (mov)
open VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.RISCV64 (ptr_add count_sub count_nz wp_loop_nz)
open VG.Proof.MlKem.RISCV64.Sample (toNat_setWidth8 taint_block relct_wp)
open VG.Spec.MlDsa (Zq q G)
open VG.Proof.MlDsa (PolyIs)
open VG.Spec.Sha3 (bytesAt)

/-- The call, from the entry state: `seed = a0`, `a = a1`, `scratch = a2`. -/
abbrev spOf (σ : State) : Sp := ⟨σ.gpr .a0, 34, σ.gpr .a2, σ.gpr .a1⟩

/-- The seed. -/
abbrev B (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .a0) 34

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := G (B σ) 1008

/-- Byte `i` of the XOF output. -/
abbrev Xb (σ : State) (i : Nat) : Byte := (X σ).getD i 0

/-- The coefficients sampled after `t` iterations. -/
abbrev Lt (σ : State) (t : Nat) : List Zq := rnFold [] ((X σ).take (3 * t))

/-- The value of 3 bytes, as the code computes it. -/
def rnw (b₀ b₁ b₂ : Byte) : BitVec 64 :=
  b₂.setWidth 64 <<< 57 >>> 41 + b₁.setWidth 64 <<< 8 + b₀.setWidth 64

theorem rnw_toNat (b₀ b₁ b₂ : Byte) : (rnw b₀ b₁ b₂).toNat = rnZ b₀ b₁ b₂ := by
  have h0 := b₀.isLt
  have h1 := b₁.isLt
  have h2 := b₂.isLt
  unfold rnw rnZ
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft,
    toNat_setWidth8, toNat_setWidth8, toNat_setWidth8, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    Nat.shiftLeft_eq]
  omega

/-- Nonzero exactly when the value `v` is kept, with `j` coefficients. -/
def accR (v j : BitVec 64) : BitVec 64 :=
  (v - BitVec.ofNat 64 8380417) >>> 63 &&& (j - BitVec.ofNat 64 256) >>> 63

theorem accR_eq {v j : BitVec 64} (hv : v.toNat < 2 ^ 23) (hj : j.toNat ≤ 256) :
    (accR v j == 0) = !decide (v.toNat < 8380417 ∧ j.toNat < 256) := by
  unfold accR
  by_cases h1 : v.toNat < 8380417 <;> by_cases h2 : j.toNat < 256
  · have e1 : (v - BitVec.ofNat 64 8380417) >>> 63 = 1 := by bv_omega
    have e2 : (j - BitVec.ofNat 64 256) >>> 63 = 1 := by bv_omega
    rw [e1, e2]; simp [h1, h2]
  · have e2 : (j - BitVec.ofNat 64 256) >>> 63 = 0 := by bv_omega
    rw [e2]; simp [h1, h2]
  · have e1 : (v - BitVec.ofNat 64 8380417) >>> 63 = 0 := by bv_omega
    rw [e1]; simp [h1, h2]
  · have e1 : (v - BitVec.ofNat 64 8380417) >>> 63 = 0 := by bv_omega
    rw [e1]; simp [h1, h2]

/-- The value of the 3 bytes of iteration `t`. -/
abbrev V (σ : State) (t : Nat) : BitVec 64 := rnw (Xb σ (3 * t)) (Xb σ (3 * t + 1)) (Xb σ (3 * t + 2))

theorem V_lt (σ : State) (t : Nat) : (V σ t).toNat < 2 ^ 23 := by
  rw [rnw_toNat]; unfold rnZ
  have := (Xb σ (3 * t)).isLt; have := (Xb σ (3 * t + 1)).isLt; have := (Xb σ (3 * t + 2)).isLt
  omega

theorem X_length (σ : State) : (X σ).length = 1008 := G_length _ _

theorem take_add_three (L : List Byte) {i : Nat} (h : i + 3 ≤ L.length) :
    L.take (i + 3) = L.take i ++ [L.getD i 0, L.getD (i + 1) 0, L.getD (i + 2) 0] := by
  rw [List.take_add, List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    List.drop_eq_getElem_cons (by omega)]
  simp only [List.take_succ_cons, List.take_zero, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < L.length by omega), List.getElem?_eq_getElem (show i + 1 < L.length by omega),
    List.getElem?_eq_getElem (show i + 2 < L.length by omega), Option.getD_some]

theorem Lt_succ (σ : State) {t : Nat} (ht : t < 336) :
    Lt σ (t + 1) = rnStep (Lt σ t) (Xb σ (3 * t)) (Xb σ (3 * t + 1)) (Xb σ (3 * t + 2)) := by
  simp only [Lt]
  rw [show 3 * (t + 1) = 3 * t + 3 by omega, take_add_three _ (by rw [X_length]; omega),
    rnFold_snoc _ (by rw [List.length_take, X_length]; omega)]

theorem Lt_length_le (σ : State) (t : Nat) : (Lt σ t).length ≤ 256 := rnFold_length_le (by simp) _

/-- At the start of iteration `t` of `N`, with `3 N` bytes of output. -/
structure LAt (N : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  env : Env (spOf σ) σ s
  s8 : s.gpr .s8 = BitVec.ofNat 64 34
  s9 : s.gpr .s9 = σ.gpr .a0
  hN : N ≤ 336
  out : bytesAt s.mem ((spOf σ).at' 840) (3 * N) = (X σ).take (3 * N)
  a0 : s.gpr .a0 = σ.gpr .a2 + BitVec.ofNat 64 (840 + 3 * t)
  a3 : s.gpr .a3 = BitVec.ofNat 64 (N - t)
  a4 : s.gpr .a4 = BitVec.ofNat 64 8380417
  at' : At (spOf σ) (Lt σ t) s

/-- After the value of the 3 bytes and its test. -/
structure M1 (N : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  lat : LAt N σ t s
  a7 : s.gpr .a7 = V σ t
  t2 : s.gpr .t2 = accR (V σ t) (BitVec.ofNat 64 (Lt σ t).length)

/-- After the coefficient of iteration `t`. -/
structure M2 (N : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  env : Env (spOf σ) σ s
  s8 : s.gpr .s8 = BitVec.ofNat 64 34
  s9 : s.gpr .s9 = σ.gpr .a0
  hN : N ≤ 336
  out : bytesAt s.mem ((spOf σ).at' 840) (3 * N) = (X σ).take (3 * N)
  a0 : s.gpr .a0 = σ.gpr .a2 + BitVec.ofNat 64 (840 + 3 * t)
  a3 : s.gpr .a3 = BitVec.ofNat 64 (N - t)
  a4 : s.gpr .a4 = BitVec.ofNat 64 8380417
  at' : At (spOf σ) (Lt σ (t + 1)) s

/-- The registers an iteration's load and test write. -/
abbrev Tmp (r : Reg) : Prop := r ≠ .a5 ∧ r ≠ .a6 ∧ r ≠ .a7 ∧ r ≠ .t1 ∧ r ≠ .t2

theorem tmp_of_pres {r : Reg} (h : r ∈ preserved) : Tmp r := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> exact absurd h (by decide)

theorem take_getD {L : List Byte} {m i : Nat} (h : i < m) : (L.take m).getD i 0 = L.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, h]

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

/-- Byte `k` of iteration `t`. -/
theorem byte_ok {N t : Nat} (ht : t < N) {s : State} (h : LAt N σ t s) {k : Nat} (hk : k < 3) :
    InRegions (s.rd ++ s.wr) (σ.gpr .a2 + BitVec.ofNat 64 (840 + 3 * t) + BitVec.ofNat 64 k) 1 ∧
      s.mem (σ.gpr .a2 + BitVec.ofNat 64 (840 + 3 * t) + BitVec.ofNat 64 k) = Xb σ (3 * t + k) := by
  have := h.hN
  rw [ptr_add]
  refine ⟨inScrRd hp h.env.wr (by omega), ?_⟩
  have e := congrArg (fun L => L.getD (3 * t + k) 0) h.out
  rw [MlKem.bytesAt_getD _ _ (by omega), ptr_add, ← Nat.add_assoc, take_getD (by omega)] at e
  exact e

omit hp in
theorem load_ok {s : State} {x : Addr} {j : BitVec 64} (h0 : s.gpr .a0 = x) (h2 : s.gpr .a2 = j)
    (h4 : s.gpr .a4 = BitVec.ofNat 64 8380417)
    (i0 : InRegions (s.rd ++ s.wr) x 1) (i1 : InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 1) 1)
    (i2 : InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 2) 1) :
    WP isa (.block (rnLoad ++ testJ [.sub .t2 .a7 .a4])) s fun t =>
      t.gpr .a7 = rnw (s.mem x) (s.mem (x + BitVec.ofNat 64 1)) (s.mem (x + BitVec.ofNat 64 2)) ∧
      t.gpr .t2 = accR (rnw (s.mem x) (s.mem (x + BitVec.ofNat 64 1)) (s.mem (x + BitVec.ofNat 64 2))) j ∧
      (∀ r, Tmp r → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  mrun [rnLoad, testJ, rnw, accR, h0, h2, h4, i0, i1, i2]
  intro r ⟨a, b, c, d, e⟩
  simp only [a, b, c, d, e, ite_false]

/-- `LAt` through a block that writes no memory and only the temporaries. -/
theorem LAt.keep {N t : Nat} {s s' : State} (h : LAt N σ t s) (hm : s'.mem = s.mem)
    (g : ∀ r, Tmp r → s'.gpr r = s.gpr r) (rd : s'.rd = s.rd)
    (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) : LAt N σ t s' := by
  have gp : ∀ r ∈ preserved, s'.gpr r = s.gpr r := fun r hr => g r (tmp_of_pres hr)
  have t : ∀ r, r ≠ .a5 → r ≠ .a6 → r ≠ .a7 → r ≠ .t1 → r ≠ .t2 → s'.gpr r = s.gpr r :=
    fun r a b c d e => g r ⟨a, b, c, d, e⟩
  exact ⟨h.env.regs hp hm gp rd wr sp,
    (t _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.s8,
    (t _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.s9, h.hN,
    by rw [hm]; exact h.out,
    (t _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.a0,
    (t _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.a3,
    (t _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.a4,
    ⟨(t _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.at'.a1,
      (t _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.at'.a2, h.at'.len,
      by rw [hm]; exact h.at'.st⟩⟩

theorem pieceA {N t : Nat} (ht : t < N) {s : State} (h : LAt N σ t s) :
    WP isa (.block (rnLoad ++ testJ [.sub .t2 .a7 .a4])) s (M1 N σ t) := by
  obtain ⟨i0, v0⟩ := byte_ok hp ht h (k := 0) (by decide)
  obtain ⟨i1, v1⟩ := byte_ok hp ht h (k := 1) (by decide)
  obtain ⟨i2, v2⟩ := byte_ok hp ht h (k := 2) (by decide)
  rw [BitVec.add_zero] at i0 v0
  rw [Nat.add_zero] at v0
  refine WP.mono (load_ok h.a0 h.at'.a2 h.a4 i0 i1 i2) fun s' ⟨g7, g2, g, m, rd, wr, sp⟩ => ?_
  rw [v0, v1, v2] at g7 g2
  exact ⟨h.keep hp m g rd wr sp, g7, g2⟩

omit hp in
theorem zw_V {t : Nat} (hq : (V σ t).toNat < q) : (V σ t).setWidth 32 = zw (Fin.ofNat q (V σ t).toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [zw_toNat, Fin.val_ofNat, Nat.mod_eq_of_lt hq, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by have := V_lt σ t; omega)]

theorem pieceB {N t : Nat} (ht : t < N) {s : State} (h : M1 N σ t s) : WP isa (accept .a7) s (M2 N σ t) := by
  have l := h.lat
  have hN := l.hN
  have hl : (BitVec.ofNat 64 (Lt σ t).length).toNat = (Lt σ t).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Lt_length_le σ t; omega)]
  have ez := accR_eq (V_lt σ t) (j := BitVec.ofNat 64 (Lt σ t).length) (by rw [hl]; exact Lt_length_le σ t)
  rw [hl, ← h.t2] at ez
  have hstep := Lt_succ σ (show t < 336 by omega)
  rw [rnStep, ← rnw_toNat] at hstep
  by_cases hz : s.gpr .t2 = 0
  · have hn : ¬ ((V σ t).toNat < 8380417 ∧ (Lt σ t).length < 256) := by
      intro hc; rw [hz] at ez; simp [hc] at ez
    have e : Lt σ (t + 1) = Lt σ t := by
      rw [hstep]
      by_cases hl' : (Lt σ t).length < 256
      · rw [ifT (show (Lt σ t).length < Spec.MlDsa.n from hl'),
          ifF (show ¬ (V σ t).toNat < q from fun hq => hn ⟨hq, hl'⟩)]
      · rw [ifF (show ¬ (Lt σ t).length < Spec.MlDsa.n from hl')]
    exact WP.mono (accept_skip hz) fun s' e' => by
      subst e'; exact ⟨l.env, l.s8, l.s9, l.hN, l.out, l.a0, l.a3, l.a4, e ▸ l.at'⟩
  · have hy : (V σ t).toNat < 8380417 ∧ (Lt σ t).length < 256 := by
      have : (s.gpr .t2 == 0) = false := by simpa using hz
      rw [this] at ez; simpa using ez
    have e : Lt σ (t + 1) = Lt σ t ++ [Fin.ofNat q (V σ t).toNat] := by
      rw [hstep, ifT (show (Lt σ t).length < Spec.MlDsa.n from hy.2), ifT (show (V σ t).toNat < q from hy.1)]
    refine WP.mono (accept_store hp l.env l.at' hy.2 (by rw [h.a7]; exact zw_V hy.1) hz)
      fun s' ⟨at', env', rr, hf⟩ => ⟨env', (rr _ (by decide) (by decide)).trans l.s8,
        (rr _ (by decide) (by decide)).trans l.s9, l.hN, ?_, (rr _ (by decide) (by decide)).trans l.a0,
        (rr _ (by decide) (by decide)).trans l.a3, (rr _ (by decide) (by decide)).trans l.a4, e ▸ at'⟩
    rw [MlKem.bytesAt_frame hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (hp.a_scr.sub_right (sub_scr (a := 840) (n := 3 * N) (by omega))).symm) (by omega)]
    exact l.out

theorem pieceC {N t : Nat} (ht : t < N) {s : State} (h : M2 N σ t s) :
    WP isa (.block [.addi .a0 .a0 3, .addi .a3 .a3 (-1)]) s fun s' =>
      LAt N σ (t + 1) s' ∧ (s'.gpr .a3 != 0) = decide (t + 1 ≠ N) := by
  have hN := h.hN
  have hk : WP isa (.block [.addi .a0 .a0 3, .addi .a3 .a3 (-1)]) s fun s' =>
      s'.gpr .a0 = s.gpr .a0 + BitVec.ofNat 64 3 ∧ s'.gpr .a3 = s.gpr .a3 - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .a0 → r ≠ .a3 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
    mrun []
    intro r a b
    simp only [a, b, ite_false]
  refine WP.mono hk fun s' ⟨r0, r3, g, m, rd, wr, sp⟩ => ⟨⟨?_, (g _ (by decide) (by decide)).trans h.s8,
    (g _ (by decide) (by decide)).trans h.s9, h.hN, by rw [m]; exact h.out, ?_, ?_,
    (g _ (by decide) (by decide)).trans h.a4, ⟨(g _ (by decide) (by decide)).trans h.at'.a1,
      (g _ (by decide) (by decide)).trans h.at'.a2, h.at'.len, by rw [m]; exact h.at'.st⟩⟩, ?_⟩
  · exact h.env.regs hp m (fun r hr => g r (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide))) rd wr sp
  · rw [r0, h.a0, ptr_add, show 840 + 3 * t + 3 = 840 + 3 * (t + 1) by omega]
  · rw [r3, h.a3]; exact count_sub ht
  · rw [r3, h.a3, count_sub ht]; exact count_nz ht (by omega)

/-- An iteration. -/
theorem body_ok {N t : Nat} (ht : t < N) {s : State} (h : LAt N σ t s) :
    WP isa rnBody s fun s' => LAt N σ (t + 1) s' ∧ (s'.gpr .a3 != 0) = decide (t + 1 ≠ N) :=
  WP.seq (WP.mono (pieceA hp ht h) fun _ h1 => WP.seq (WP.mono (pieceB hp ht h1) fun _ h2 => pieceC hp ht h2))

omit hp in
theorem Lt_zero : Lt σ 0 = [] := by simp [Lt, rnFold]

/-- The loop's setup, after the sponge. -/
theorem lat0 {N : Nat} (hN : N = 280 ∨ N = 336) {s₀ s : State} (h : J6 168 (3 * N) (spOf σ) σ s₀ s) :
    WP isa (.block (([.addi .a0 .s11 840, mov .a1 .s10, .li .a2 0, .li .a3 N] : List Instr) ++ loadQ)) s
      (LAt N σ 0) := by
  have g10 := h.j0.env.s10
  have g11 := h.j0.env.s11
  have hk : WP isa (.block (([.addi .a0 .s11 840, mov .a1 .s10, .li .a2 0, .li .a3 N] : List Instr) ++ loadQ)) s
      fun s' => s'.gpr .a0 = σ.gpr .a2 + BitVec.ofNat 64 (840 + 3 * 0) ∧ s'.gpr .a1 = σ.gpr .a1 ∧
        s'.gpr .a2 = BitVec.ofNat 64 0 ∧ s'.gpr .a3 = BitVec.ofNat 64 (N - 0) ∧
        s'.gpr .a4 = BitVec.ofNat 64 8380417 ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    simp only [loadQ, VG.Impl.MlDsa.RISCV64.Pack.loadQ, VG.Proof.MlDsa.RISCV64.Arith.loadImm_q, List.cons_append,
      List.nil_append]
    rcases hN with rfl | rfl <;>
    · mrun [mov, g10, g11, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
      decide
  have hN' : N ≤ 336 := by omega
  refine WP.mono hk fun s' ⟨g0, g1, g2, g3, g4, gp, m, rd, wr, sp⟩ => ⟨h.j0.env.regs hp m gp rd wr sp,
    (gp _ (by decide)).trans h.j0.s8, (gp _ (by decide)).trans h.j0.s9, hN',
    by rw [m, h.out, X, G_take _ (show 3 * N ≤ 1008 by omega)]; exact (G_eq _ _).symm, g0, g3, g4, ?_⟩
  rw [Lt_zero]
  exact ⟨by rw [g1]; exact (BitVec.add_zero _).symm, g2, by simp, stored_nil _ _⟩

theorem loop_ok {N : Nat} (hN : N = 280 ∨ N = 336) {s₀ s : State} (h : J6 168 (3 * N) (spOf σ) σ s₀ s) :
    WP isa (rnLoop N) s (LAt N σ N) :=
  WP.seq (WP.mono (lat0 hp hN h) fun _ h0 =>
    wp_loop_nz (LAt N σ) (N := N) (by omega) (fun t ht s h => body_ok hp ht h) (fun _ h => h) h0)

/-- A try, from the state after the prologue. -/
theorem try_ok {N : Nat} (hN : N = 280 ∨ N = 336) {s : State} (h : J0 (spOf σ) σ s) :
    WP isa (rnTry N) s (LAt N σ N) :=
  WP.seq (WP.mono (sponge_ok hp (rate := 168) (outlen := 3 * N) (by decide) (by omega) h) fun _ h2 =>
    loop_ok hp hN h2)

/-- The test of the first try's result: `t0 = j >> 8`. -/
theorem test_ok {N : Nat} {s : State} (h : LAt N σ N s) :
    WP isa (.block [.shift .srl .d .t0 .a2 8]) s fun s' => LAt N σ N s' ∧
      (s'.gpr .t0 == 0) = decide ((Lt σ N).length ≠ 256) := by
  have hk : WP isa (.block [.shift .srl .d .t0 .a2 8]) s fun s' => s'.gpr .t0 = s.gpr .a2 >>> 8 ∧
      (∀ r, r ≠ .t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    mrun []
    intro r a
    simp only [a, ite_false]
  refine WP.mono hk fun s' ⟨r0, g, m, rd, wr, sp⟩ => ⟨⟨h.env.regs hp m (fun r hr => g r
    (by rintro rfl; exact absurd hr (by decide))) rd wr sp, (g _ (by decide)).trans h.s8,
    (g _ (by decide)).trans h.s9, h.hN, by rw [m]; exact h.out, (g _ (by decide)).trans h.a0,
    (g _ (by decide)).trans h.a3, (g _ (by decide)).trans h.a4,
    ⟨(g _ (by decide)).trans h.at'.a1, (g _ (by decide)).trans h.at'.a2, h.at'.len,
      by rw [m]; exact h.at'.st⟩⟩, ?_⟩
  rw [r0, h.at'.a2, VG.Proof.MlKem.RISCV64.Sample.ret_val h.at'.len]
  by_cases e : (Lt σ N).length = 256 <;> simp [e]

omit hp in
theorem Lt_all : Lt σ 336 = rnFold [] (X σ) := by
  simp only [Lt]; rw [List.take_of_length_le (by rw [X_length])]

omit hp in
/-- 256 coefficients from the first 280 iterations are all of them. -/
theorem Lt_full (hl : (Lt σ 280).length = 256) : Lt σ 280 = rnFold [] (X σ) := by
  have e : rnFold [] (X σ) = rnFold (rnFold [] ((X σ).take 840)) ((X σ).drop 840) := by
    have := rnFold_append [] ((X σ).take 840) ((X σ).drop 840) (by rw [List.length_take, X_length]; decide)
    rwa [List.take_append_drop] at this
  rw [e, show rnFold [] ((X σ).take 840) = Lt σ 280 from rfl,
    rnFold_full (show (Lt σ 280).length = Spec.MlDsa.n from hl)]

theorem end_ok {N : Nat} {s : State} (h : LAt N σ N s) (hL : Lt σ N = rnFold [] (X σ)) :
    WP isa (.block (retJ ++ epi)) s fun s' => s'.gpr .a0 = (if (rnFold [] (X σ)).length = 256 then 1 else 0) ∧
      ((rnFold [] (X σ)).length = 256 → PolyIs s'.mem (σ.gpr .a1) (toPoly (rnFold [] (X σ)))) ∧
      abiPreserved σ s' :=
  WP.mono (retEpi_ok hp h.env h.at'.a2 (Lt_length_le _ _)) fun s' ⟨h0, hm, ha⟩ =>
    ⟨by rw [h0, hL], fun hf => by
      rw [hm]
      have hs := h.at'.st
      rw [hL] at hs
      exact stored_polyIs hs hf, ha⟩

/-- The function, from an entry state whose regions are those of a call. -/
theorem correct : WP isa Impl.MlDsa.RISCV64.Sample.rejNTT σ fun s' =>
    s'.gpr .a0 = (if (rnFold [] (X σ)).length = 256 then 1 else 0) ∧
      ((rnFold [] (X σ)).length = 256 → PolyIs s'.mem (σ.gpr .a1) (toPoly (rnFold [] (X σ)))) ∧
      abiPreserved σ s' := by
  refine WP.seq (WP.mono (pro_rn hp rfl rfl rfl rfl) fun _ ⟨j1, _⟩ => WP.seq ?_)
  refine WP.mono (try_ok hp (.inl rfl) j1) fun s₂ h₂ => WP.seq ?_
  refine WP.mono (test_ok hp h₂) fun s₃ ⟨h₃, z⟩ => WP.seq ?_
  refine WP.ite _ (Steps.eval_zero _ _) (fun e => ?_) (fun e => ?_)
  · exact WP.mono (try_ok hp (.inr rfl) ⟨h₃.env, h₃.s9, h₃.s8⟩) fun s₄ h₄ => end_ok hp h₄ Lt_all
  · have hl : (Lt σ 280).length = 256 := by rw [z] at e; simpa using e
    exact WP.block_nil (end_ok hp h₃ (Lt_full hl))

end

/-! ## Constant time -/

/-- Two runs, from entry states that agree on the public data. -/
structure Two (σ₁ σ₂ : State) : Prop where
  hp₁ : SpOk (spOf σ₁) σ₁
  hp₂ : SpOk (spOf σ₂) σ₂
  sp : σ₁.sp = σ₂.sp
  a0 : σ₁.gpr .a0 = σ₂.gpr .a0
  a1 : σ₁.gpr .a1 = σ₂.gpr .a1
  a2 : σ₁.gpr .a2 = σ₂.gpr .a2
  B : B σ₁ = B σ₂

section
variable {σ₁ σ₂ : State} (h : Two σ₁ σ₂)
include h

theorem sp_eq : spOf σ₂ = spOf σ₁ := by simp only [spOf, h.a0, h.a1, h.a2]

theorem X_eq : X σ₁ = X σ₂ := by simp only [X, h.B]

theorem Lt_eq (t : Nat) : Lt σ₁ t = Lt σ₂ t := by simp only [Lt, X_eq h]

theorem V_eq (t : Nat) : V σ₁ t = V σ₂ t := by simp only [V, Xb, X_eq h]

theorem lsp {N t t' : Nat} {a b : State} (ha : LAt N σ₁ t a) (hb : LAt N σ₂ t' b) : a.sp = b.sp := by
  rw [ha.env.sp, hb.env.sp, h.sp]

theorem body_ct {N t : Nat} (ht : t < N) :
    RelCT isa (fun a b => LAt N σ₁ t a ∧ LAt N σ₂ t b) rnBody fun a b =>
      (LAt N σ₁ (t + 1) a ∧ (a.gpr .a3 != 0) = decide (t + 1 ≠ N)) ∧
      (LAt N σ₂ (t + 1) b ∧ (b.gpr .a3 != 0) = decide (t + 1 ≠ N)) := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  refine relct_wp ?_ fun a b hab => ⟨body_ok hp₁ ht hab.1, body_ok hp₂ ht hab.2⟩
  refine RelCT.seq (R := fun a b => M1 N σ₁ t a ∧ M1 N σ₂ t b) (relct_wp ?_ fun a b hab =>
    ⟨pieceA hp₁ ht hab.1, pieceA hp₂ ht hab.2⟩) ?_
  · exact taint_block [.a0] (fun a b hab => lsp h hab.1 hab.2) (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hab.1.a0, hab.2.a0, h.a2]) (by taint_decide)
  refine RelCT.seq (R := fun a b => M2 N σ₁ t a ∧ M2 N σ₂ t b) (relct_wp ?_ fun a b hab =>
    ⟨pieceB hp₁ ht hab.1, pieceB hp₂ ht hab.2⟩) (Pack.relct_noMem rfl)
  refine accept_ct (fun a b hab => lsp h hab.1.lat hab.2.lat) (fun a b hab => ?_) fun a b hab => ?_
  · rw [hab.1.t2, hab.2.t2, V_eq h, Lt_eq h]
  · rw [hab.1.lat.at'.a1, hab.2.lat.at'.a1, Lt_eq h, sp_eq h]

theorem loop_ct {N : Nat} (h0 : 0 < N) :
    RelCT isa (fun a b => LAt N σ₁ 0 a ∧ LAt N σ₂ 0 b) (.loop rnBody (.nonzero .a3)) fun a b =>
      LAt N σ₁ N a ∧ LAt N σ₂ N b := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := rnBody) (c := .nonzero .a3)
    (Q := fun a b => LAt N σ₁ N a ∧ LAt N σ₂ N b)
    (fun n a b => ∃ t, t < N ∧ n = N - t ∧ LAt N σ₁ t a ∧ LAt N σ₂ t b) (fun n => ?_) N)
    (fun a b hab => ⟨0, h0, rfl, hab⟩) (fun _ _ h => h)
  refine RelCT.mono (P := fun a b => ∃ t, t < N ∧ n = N - t ∧ LAt N σ₁ t a ∧ LAt N σ₂ t b)
    (RelCT.exists_ fun t => ?_) (fun _ _ hab => hab) (fun _ _ h => h)
  by_cases ht : t < N
  · by_cases hn : n = N - t
    · refine RelCT.mono (P := fun a b => LAt N σ₁ t a ∧ LAt N σ₂ t b) (body_ct h ht) (fun _ _ hab => hab.2.2)
        fun a b ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
      · rw [Steps.eval_nonzero, Steps.eval_nonzero, z₁, z₂]
      · have : t + 1 = N := by
          have e' : (a.gpr .a3 != 0) = false := by rw [Steps.eval_nonzero] at e; exact Option.some.inj e
          rw [z₁] at e'; simpa using e'
        rw [this] at i₁ i₂; exact ⟨i₁, i₂⟩
      · have : t + 1 ≠ N := by
          have e' : (a.gpr .a3 != 0) = true := by rw [Steps.eval_nonzero] at e; exact Option.some.inj e
          rw [z₁] at e'; simpa using e'
        exact ⟨N - (t + 1), by omega, t + 1, by omega, rfl, i₁, i₂⟩
    · exact RelCT.of_false fun _ _ hab => hn hab.2.1
  · exact RelCT.of_false fun _ _ hab => ht hab.1

/-- A try, in both runs, from the states after the prologue. -/
theorem try_ct {N : Nat} (hN : N = 280 ∨ N = 336) :
    RelCT isa (fun a b => J0 (spOf σ₁) σ₁ a ∧ J0 (spOf σ₁) σ₂ b) (rnTry N) fun a b =>
      LAt N σ₁ N a ∧ LAt N σ₂ N b := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  have eP := sp_eq h
  have hp₂' : SpOk (spOf σ₁) σ₂ := eP ▸ hp₂
  refine RelCT.seq (R := fun a b => (∃ x, J6 168 (3 * N) (spOf σ₁) σ₁ x a) ∧
      (∃ y, J6 168 (3 * N) (spOf σ₁) σ₂ y b))
    (relct_wp (sponge_ct hp₁ hp₂' h.sp (by decide) (by omega)) fun a b hab =>
      ⟨WP.mono (sponge_ok hp₁ (by decide) (by omega) hab.1) fun _ x => ⟨_, x⟩,
        WP.mono (sponge_ok hp₂' (by decide) (by omega) hab.2) fun _ x => ⟨_, x⟩⟩) ?_
  refine RelCT.seq (R := fun a b => LAt N σ₁ 0 a ∧ LAt N σ₂ 0 b) ?_ (loop_ct h (by omega))
  refine relct_wp (Pack.relct_noMem rfl) fun a b ⟨⟨x, ha⟩, ⟨y, hb⟩⟩ =>
    ⟨lat0 hp₁ hN ha, lat0 hp₂ hN (by rw [eP]; exact hb)⟩

theorem all_ct : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) Impl.MlDsa.RISCV64.Sample.rejNTT fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  have eP := sp_eq h
  have hp₂' : SpOk (spOf σ₁) σ₂ := eP ▸ hp₂
  refine RelCT.seq (R := fun a b => J0 (spOf σ₁) σ₁ a ∧ J0 (spOf σ₁) σ₂ b) (relct_wp (pro_rn_ct
    (fun a b hab => by rw [hab.1, hab.2]; exact h.sp) fun a b hab => by rw [hab.1, hab.2]; exact h.a2)
    fun a b hab => ⟨?_, ?_⟩) ?_
  · rw [hab.1]; exact WP.mono (pro_rn hp₁ rfl rfl rfl rfl) fun _ x => x.1
  · rw [hab.2]; exact WP.mono (pro_rn hp₂' h.a0.symm h.a1.symm h.a2.symm rfl) fun _ x => x.1
  refine RelCT.seq (R := fun a b => LAt 280 σ₁ 280 a ∧ LAt 280 σ₂ 280 b) (try_ct h (.inl rfl)) ?_
  -- The test, alike in both runs: their samples agree.
  refine RelCT.seq (R := fun (a b : State) =>
      (LAt 280 σ₁ 280 a ∧ (a.gpr .t0 == 0) = decide ((Lt σ₁ 280).length ≠ 256)) ∧
      (LAt 280 σ₂ 280 b ∧ (b.gpr .t0 == 0) = decide ((Lt σ₂ 280).length ≠ 256)))
    (relct_wp (Pack.relct_noMem rfl) fun a b hab => ⟨test_ok hp₁ hab.1, test_ok hp₂ hab.2⟩) ?_
  refine RelCT.seq (R := fun a b => Env (spOf σ₁) σ₁ a ∧ Env (spOf σ₂) σ₂ b) ?_ ?_
  · refine RelCT.ite (fun a b hab => by rw [Steps.eval_zero, Steps.eval_zero, hab.1.2, hab.2.2, Lt_eq h]) ?_ ?_
    · exact RelCT.mono (P := fun a b => J0 (spOf σ₁) σ₁ a ∧ J0 (spOf σ₁) σ₂ b)
        (Q := fun a b => LAt 336 σ₁ 336 a ∧ LAt 336 σ₂ 336 b) (try_ct h (.inr rfl))
        (fun a b hab => ⟨⟨hab.1.1.1.env, hab.1.1.1.s9, hab.1.1.1.s8⟩,
          eP ▸ (⟨hab.1.2.1.env, hab.1.2.1.s9, hab.1.2.1.s8⟩ : J0 (spOf σ₂) σ₂ b)⟩)
        fun a b hab => ⟨hab.1.env, hab.2.env⟩
    · exact relct_wp (Pack.relct_noMem rfl)
        fun a b hab => ⟨WP.block_nil hab.1.1.1.env, WP.block_nil hab.1.2.1.env⟩
  exact retEpi_ct (fun a b hab => by rw [hab.1.sp, hab.2.sp, h.sp]) fun a b hab => by
    rw [hab.1.s11, hab.2.s11]; exact h.a2

end

/-! ## `Verified` -/

theorem spOk_of {s : State} (h : (Proof.MlDsa.rejNTTContract RISCV64.abi 1168).pre s) : SpOk (spOf s) s := by
  sig_pre [Proof.MlDsa.rejNTTContract, Proof.MlDsa.rejNTTSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨by rw [h2]; exact List.mem_singleton_self _, h3, h4, h5, h6, h7, h8, h9,
    show (34 : Nat) < 2 ^ 64 by decide, h11, h12, h0, h1, h13, h14⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 34⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

end VG.Proof.MlDsa.RISCV64.Sample.RejNtt

namespace VG.Proof.MlDsa.RISCV64.Sample

open VG VG.RISCV64
open VG.Proof.MlDsa.Sample
open RejNtt

theorem rejNTT_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Sample.rejNTT (Proof.MlDsa.rejNTTContract RISCV64.abi 1168) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, h3, hpoly, ha⟩ := correct (spOk_of hs)
    refine ⟨t, s', he, ha, ?_⟩
    sig_post [Proof.MlDsa.rejNTTContract, Proof.MlDsa.rejNTTSig, RISCV64.abi, RISCV64.argRegs]
    rw [h3]
    by_cases hf : (rnFold [] (X s)).length = 256
    · rw [ifT hf]
      have hpi := hpoly hf
      exact ⟨fun _ => hpi.1, .inl ⟨rfl, { Spec.MlDsa.minBounds with rejNTT := 1008 }, by
        show Spec.MlDsa.rejNTTPoly 1008 _ = _
        exact (rejNTT_some hf).trans (congrArg some hpi.2.symm)⟩⟩
    · rw [ifF hf]
      exact ⟨fun e => absurd e (by decide), .inr ⟨rfl, rejNTT_none (B := 1008) (by decide) (by decide) hf⟩⟩
  · sig_pub [Proof.MlDsa.rejNTTContract, Proof.MlDsa.rejNTTSig, RISCV64.abi, RISCV64.argRegs] at hpub
    obtain ⟨hsp, hb, h0, h1, h2⟩ := hpub
    exact (all_ct ⟨spOk_of h₁, spOk_of h₂, hsp, h0, h1, h2,
      (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hb⟩
      s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.rejNTTContract, Proof.MlDsa.rejNTTSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlDsa.RISCV64.Sample
