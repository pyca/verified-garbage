module

public import VerifiedGarbage.Proof.Rsa.X86_64.InvB.Start
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Divstep.Tc
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# RSA's inverse by divsteps on x86-64: the pieces of the end

The loops of the end over `n + 1` words of arrays up to 25, with their
bases set up by the blocks before them: a subtraction (`subN_ok`), a
selection (`selN_ok`) by the sign of an array in two's complement
(`isNeg_ok`, `nonNeg_ok`), the conditional subtraction of `m` (`csubT_ok`),
a doubling modulo `m` (`dbl_ok`), and `rdi` back to the working space's base
(`unwin_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.InvB

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Inv
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- A state of the end: the working space, the stride in `r9` and `n` in `r13`. -/
structure FS (B : Addr) (Z w n : Nat) (s : State) : Prop where
  ws : Ws s B Z w
  z : slot w 26 ≤ Z
  r9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))
  r13 : s.gpr .r13 = BitVec.ofNat 64 n
  n1 : 1 ≤ n
  nw : n ≤ w

theorem FS.of_out {B : Addr} {Z w n : Nat} {s t : State} (h : FS B Z w n s) {j L : Nat}
    (o : Outside B (slot w j) L s.mem t.mem) {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs)
    (h9 : .r9 ∉ regs) (h13 : .r13 ∉ regs) : FS B Z w n t :=
  ⟨wsOut h.ws o k hr, h.z, (k.gpr h9).trans h.r9, (k.gpr h13).trans h.r13, h.n1, h.nw⟩

theorem FS.of_mem {B : Addr} {Z w n : Nat} {s t : State} (h : FS B Z w n s) (m : t.mem = s.mem)
    {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs) (h9 : .r9 ∉ regs) (h13 : .r13 ∉ regs) :
    FS B Z w n t :=
  h.of_out (j := 0) (L := 0) (by rw [m]; exact Outside.refl _ _ _ _) k hr h9 h13

theorem FS.sl {B : Addr} {Z w n : Nat} {s : State} (h : FS B Z w n s) {j : Nat} (hj : j < 26) :
    slot w j + 8 * (w + 2) ≤ Z := Nat.le_trans (slot_lt hj) h.z

/-- `mov32 rbp, 0` and three bases. -/
theorem bases3_ok {s : State} {B : Addr} {Z w n : Nat} (h : FS B Z w n s) (a b c : Nat) :
    WP isa (.block (([.mov32 .rbp (.imm 0)] : List Instr) ++ base a .r8 ++ base b .r10 ++ base c .rsi)) s
      fun t => t.gpr .rbp = mask false ∧ t.gpr .r8 = off B (slot w a) ∧ t.gpr .r10 = off B (slot w b) ∧
        t.gpr .rsi = off B (slot w c) ∧ t.mem = s.mem ∧ Keep [.rbp, .r8, .r10, .rsi] s t := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask false ∧ t.mem = s.mem) (by xrun) rfl)
    fun s₁ ⟨⟨bp₁, m₁⟩, k₁⟩ => ?_
  have di₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans h.ws.rdi
  have r9₁ : s₁.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) := (k₁.gpr (by decide)).trans h.r9
  rw [WP.block_append_iff]
  refine WP.mono (base_ok a (r := .r8) (by decide) di₁ r9₁) fun s₂ ⟨h8, m₂, k₂⟩ => ?_
  refine WP.mono (base2_ok b c (r₁ := .r10) (r₂ := .rsi) (by decide) (by decide) (by decide)
    ((k₂.gpr (by decide)).trans di₁) ((k₂.gpr (by decide)).trans r9₁) (by decide))
    fun t ⟨h10, hsi, mt, kt⟩ => ⟨(kt.gpr (by decide)).trans ((k₂.gpr (by decide)).trans bp₁),
      (kt.gpr (by decide)).trans h8, h10, hsi, by rw [mt, m₂, m₁], ((k₁.trans k₂).trans kt).mono (by decide)⟩

/-- `[c] := [a] - [b]` over `N` words, the borrow in `rbp`. -/
theorem subN_ok {s : State} {B : Addr} {Z w n N : Nat} (h : FS B Z w n s) {a b c : Nat} (ha : a < 26)
    (hb : b < 26) (hc : c < 26) (hac : a ≠ c) (hbc : b ≠ c) (h12 : s.gpr .r12 = BitVec.ofNat 64 N)
    (hN : 1 ≤ N) (hNw : N ≤ w + 2) :
    WP isa (seqs [.block (([.mov32 .rbp (.imm 0)] : List Instr) ++ base a .r8 ++ base b .r10 ++ base c .rsi),
      wordLoop 0 subBody]) s fun t => ∃ cb : Bool, t.gpr .rbp = mask cb ∧
        wv t.mem B (slot w c) N + wv s.mem B (slot w b) N = wv s.mem B (slot w a) N + 2 ^ (64 * N) * cb.toNat ∧
        t.gpr .r8 = off B (slot w a) ∧ t.gpr .rsi = off B (slot w c) ∧
        Outside B (slot w c) (8 * N) s.mem t.mem ∧ Keep [.rax, .rbp, .r14, .r8, .r10, .rsi] s t := by
  have hn := h.ws.scr.nowrap
  have sa := slot_far (w := w) hac; have sb := slot_far (w := w) hbc
  have za := h.sl ha; have zb := h.sl hb; have zc := h.sl hc
  have hw := h.ws.w2
  simp only [seqs]
  refine WP.seq (WP.mono (bases3_ok h a b c) fun s₁ ⟨bp₁, h8, h10, hsi, m₁, k₁⟩ => ?_)
  refine WP.mono (sub_ok (h.ws.scr.congr k₁.2.2) h8 h10 hsi ((k₁.gpr (by decide)).trans h12) bp₁ hN (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)) fun t ⟨cb, hcb, hv, o, kt⟩ => ?_
  rw [m₁] at hv o
  exact ⟨cb, hcb, hv, (kt.gpr (by decide)).trans h8, (kt.gpr (by decide)).trans hsi, o, (k₁.trans kt).mono (by decide)⟩

theorem shr63_toNat (x : BitVec 64) : (x >>> 63).toNat = if 2 ^ 63 ≤ x.toNat then 1 else 0 := by
  have hx := x.isLt
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  split <;> omega

theorem isNeg_mask (x : BitVec 64) :
    BitVec.setWidth 64 (0 : BitVec 32) - x >>> 63 = mask (decide (2 ^ 63 ≤ x.toNat)) := by
  have e := shr63_toNat x
  by_cases h : 2 ^ 63 ≤ x.toNat
  · rw [show x >>> 63 = 1 from BitVec.eq_of_toNat_eq (by rw [e]; simp only [h, ↓reduceIte]; rfl), decide_eq_true h]; rfl
  · rw [show x >>> 63 = 0 from BitVec.eq_of_toNat_eq (by rw [e]; simp only [h, ↓reduceIte]; rfl), decide_eq_false h]; rfl

theorem nonNeg_mask (x : BitVec 64) :
    x >>> 63 - (1 : BitVec 64) = mask (decide (x.toNat < 2 ^ 63)) := by
  have e := shr63_toNat x
  by_cases h : 2 ^ 63 ≤ x.toNat
  · rw [show x >>> 63 = 1 from BitVec.eq_of_toNat_eq (by rw [e]; simp only [h, ↓reduceIte]; rfl),
      decide_eq_false (show ¬ x.toNat < 2 ^ 63 by omega)]; rfl
  · rw [show x >>> 63 = 0 from BitVec.eq_of_toNat_eq (by rw [e]; simp only [h, ↓reduceIte]; rfl),
      decide_eq_true (show x.toNat < 2 ^ 63 by omega)]; rfl

/-- The top bit of `n + 1` words holding `x` in two's complement, `|x| ≤ 2^(64 n)`, is `x`'s sign. -/
theorem top_bit {m : Mem} {B : Addr} {e n : Nat} {x : Int}
    (hc : (wv m B e (n + 1) : Int) % 2 ^ (64 * (n + 1)) = x % 2 ^ (64 * (n + 1)))
    (hx1 : -(2 ^ (64 * n) : Int) ≤ x) (hx2 : x < 2 ^ (64 * n)) :
    2 ^ 63 ≤ (word m B (e + 8 * n)).toNat ↔ x < 0 := by
  have hs := signW_half m B e n
  have hP : (0 : Int) < 2 ^ (64 * n) * 2 ^ 63 := by positivity
  have e2 : (2 : Int) ^ (64 * (n + 1)) = 2 * (2 ^ (64 * n) * 2 ^ 63) := by
    rw [show 64 * (n + 1) = 64 * n + 63 + 1 by omega, pow_succ, pow_add]; ring
  have e2n : (2 : Nat) ^ (64 * (n + 1)) = 2 * (2 ^ (64 * n) * 2 ^ 63) := by
    rw [show 64 * (n + 1) = 64 * n + 63 + 1 by omega, Nat.pow_succ, Nat.pow_add]; ring
  have hlt := wv_lt m B e (n + 1)
  have hP' : (2 ^ (64 * n) : Int) ≤ 2 ^ (64 * n) * 2 ^ 63 :=
    le_mul_of_one_le_right (by positivity) (by norm_num)
  have hV := Divstep.tc_eq (H := 2 ^ (64 * n) * 2 ^ 63) (x := x) (W := (wv m B e (n + 1) : Int)) hP
    (by omega) (by omega) (by positivity) (by rw [← e2]; exact_mod_cast hlt) (by rw [← e2]; exact hc)
  unfold signW at hs
  by_cases hge : 2 ^ (64 * n) * 2 ^ 63 ≤ wv m B e (n + 1)
  · simp only [hge, ↓reduceIte] at hs
    have hge' : ((2 ^ (64 * n) * 2 ^ 63 : Nat) : Int) ≤ wv m B e (n + 1) := by exact_mod_cast hge
    push_cast at hge'
    have ht : 2 ^ 63 ≤ (word m B (e + 8 * n)).toNat := by split at hs <;> omega
    have hx : x < 0 := by
      by_contra hx
      simp only [hx, ↓reduceIte] at hV
      omega
    exact ⟨fun _ => hx, fun _ => ht⟩
  · simp only [hge, ↓reduceIte] at hs
    have ht : ¬ 2 ^ 63 ≤ (word m B (e + 8 * n)).toNat := by split at hs <;> omega
    have hx : ¬ x < 0 := by
      intro hx
      simp only [hx, ↓reduceIte] at hV
      have : ((2 ^ (64 * n) * 2 ^ 63 : Nat) : Int) ≤ wv m B e (n + 1) := by push_cast; omega
      exact hge (by exact_mod_cast this)
    exact ⟨fun h => absurd h ht, fun h => absurd h hx⟩

/-- `isNeg j`: `rbp` the mask of `x < 0`, `[j]` holding `x` in `n + 1` words. -/
theorem isNeg_ok {s : State} {B : Addr} {Z w n : Nat} (h : FS B Z w n s) {j : Nat} (hj : j < 26) {x : Int}
    (hc : (wv s.mem B (slot w j) (n + 1) : Int) % 2 ^ (64 * (n + 1)) = x % 2 ^ (64 * (n + 1)))
    (hx1 : -(2 ^ (64 * n) : Int) ≤ x) (hx2 : x < 2 ^ (64 * n)) :
    WP isa (.block (isNeg j)) s fun t => t.gpr .rbp = mask (decide (x < 0)) ∧ t.mem = s.mem ∧
      Keep [.rbx, .rax, .rbp] s t := by
  have hn := h.ws.scr.nowrap
  have zj := h.sl hj
  have hnw := h.nw
  unfold isNeg
  rw [WP.block_append_iff]
  refine WP.mono (base_ok j (r := .rbx) (by decide) h.ws.rdi h.r9) fun s₁ ⟨bx, m₁, k₁⟩ => ?_
  have hs₁ := h.ws.scr.congr k₁.2.2
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t => t.gpr .rbp = mask (decide (x < 0)) ∧ t.mem = s.mem) (by
    xrun [State.ea, ix, addr0 bx ((k₁.gpr (by decide)).trans h.r13),
      hs₁.ld (d := slot w j + 8 * n) (by omega), m₁, isNeg_mask]
    exact congrArg mask (decide_eq_decide.mpr (top_bit hc hx1 hx2)))
    rfl) fun t ⟨⟨bp, mt⟩, kt⟩ => ⟨bp, by rw [mt], (k₁.trans kt).mono (by decide)⟩

/-- `nonNeg j`: `rbp` the mask of `0 ≤ x`, `[j]` holding `x` in `n + 1` words. -/
theorem nonNeg_ok {s : State} {B : Addr} {Z w n : Nat} (h : FS B Z w n s) {j : Nat} (hj : j < 26) {x : Int}
    (hc : (wv s.mem B (slot w j) (n + 1) : Int) % 2 ^ (64 * (n + 1)) = x % 2 ^ (64 * (n + 1)))
    (hx1 : -(2 ^ (64 * n) : Int) ≤ x) (hx2 : x < 2 ^ (64 * n)) :
    WP isa (.block (nonNeg j)) s fun t => t.gpr .rbp = mask (decide (0 ≤ x)) ∧ t.mem = s.mem ∧
      Keep [.rbx, .rax, .rbp] s t := by
  have hn := h.ws.scr.nowrap
  have zj := h.sl hj
  have hnw := h.nw
  unfold nonNeg
  rw [WP.block_append_iff]
  refine WP.mono (base_ok j (r := .rbx) (by decide) h.ws.rdi h.r9) fun s₁ ⟨bx, m₁, k₁⟩ => ?_
  have hs₁ := h.ws.scr.congr k₁.2.2
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t => t.gpr .rbp = mask (decide (0 ≤ x)) ∧ t.mem = s.mem) (by
    xrun [State.ea, ix, addr0 bx ((k₁.gpr (by decide)).trans h.r13),
      hs₁.ld (d := slot w j + 8 * n) (by omega), m₁, nonNeg_mask]
    have := top_bit hc hx1 hx2
    simp only [Bignum.word] at this
    exact congrArg mask (decide_eq_decide.mpr (by omega)))
    rfl) fun t ⟨⟨bp, mt⟩, kt⟩ => ⟨bp, by rw [mt], (k₁.trans kt).mono (by decide)⟩

/-- A selection of `[a] := lt ? [a] : [c]` over `N` words after a block that sets
the mask (`mk`, writing only `rbx`, `rax`, `rbp`) and the bases. -/
theorem selN_ok {s : State} {B : Addr} {Z w n N : Nat} (h : FS B Z w n s) {mk : List Instr} {lt : Bool}
    (hmk : WP isa (.block mk) s fun t => t.gpr .rbp = mask lt ∧ t.mem = s.mem ∧ Keep [.rbx, .rax, .rbp] s t)
    {a c : Nat} (ha : a < 26) (hc : c < 26) (hac : a ≠ c) (h12 : s.gpr .r12 = BitVec.ofNat 64 N)
    (hN : 1 ≤ N) (hNw : N ≤ w + 2) :
    WP isa (seqs [.block (mk ++ base a .r8 ++ base c .rsi), wordLoop 0 selBody]) s fun t =>
      wv t.mem B (slot w a) N = (if lt then wv s.mem B (slot w a) N else wv s.mem B (slot w c) N) ∧
      Outside B (slot w a) (8 * N) s.mem t.mem ∧ Keep [.rbx, .rax, .rbp, .rdx, .r14, .r8, .rsi] s t := by
  have hn := h.ws.scr.nowrap
  have sa := slot_far (w := w) hac
  have za := h.sl ha; have zc := h.sl hc
  have hw := h.ws.w2
  simp only [seqs, List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono hmk fun s₁ ⟨bp₁, m₁, k₁⟩ =>
    WP.mono (base2_ok a c (r₁ := .r8) (r₂ := .rsi) (by decide) (by decide) (by decide)
      ((k₁.gpr (by decide)).trans h.ws.rdi) ((k₁.gpr (by decide)).trans h.r9) (by decide))
      fun s₂ ⟨h8, hsi, m₂, k₂⟩ => ?_))
  refine WP.mono (sel_ok (h.ws.scr.congr (k₁.trans k₂).2.2) h8 hsi ((k₂.gpr (by decide)).trans bp₁)
    (((k₁.trans k₂).gpr (by decide)).trans h12) hN (by omega) (by omega) (by omega) (by omega))
    fun t ⟨hv, o, kt⟩ => ?_
  rw [m₂, m₁] at hv o
  exact ⟨hv, o, ((k₁.trans k₂).trans kt).mono (by decide)⟩

end VG.Proof.Rsa.X86_64.InvB
