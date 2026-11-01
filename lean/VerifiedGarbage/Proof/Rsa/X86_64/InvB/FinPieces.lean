module

public import VerifiedGarbage.Proof.Rsa.X86_64.InvB.Start
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Loop
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

/-- A change to an array from 16 on, as a frame of the private arrays. -/
theorem frW {m m' : Mem} {B : Addr} {w j L : Nat} (o : Outside B (slot w j) L m m') (hj : 16 ≤ j) (hj' : j < 26)
    (hL : L ≤ 8 * (w + 2)) : Frm B [(slot w 16, 80 * (w + 2))] m m' := fun x hx => o x (by
  have := hx _ (List.mem_singleton.mpr rfl)
  dsimp only at this
  have e := slot_eq w j; have e16 := slot_eq w 16
  have h1 : 16 * (8 * (w + 2)) ≤ j * (8 * (w + 2)) := Nat.mul_le_mul_right _ hj
  have h2 : (j + 1) * (8 * (w + 2)) ≤ 26 * (8 * (w + 2)) := Nat.mul_le_mul_right _ hj'
  rw [Nat.succ_mul] at h2
  omega)

/-- `csubT`: `[t] := [t] - m` if `[t] ≥ m`, over `N` words. -/
theorem csubT_ok {s : State} {B : Addr} {Z w n N : Nat} (h : FS B Z w n s) (h12 : s.gpr .r12 = BitVec.ofNat 64 N)
    (hN : 1 ≤ N) (hNw : N ≤ w + 2) {t p : Nat} (ht : wv s.mem B (slot w aT) N = t)
    (hp : wv s.mem B (slot w aP) N = p) :
    WP isa (seqs csubT) s fun u =>
      wv u.mem B (slot w aT) N = (if t < p then t else t - p) ∧
      Frm B [(slot w aT, 8 * N), (slot w aS, 8 * N)] s.mem u.mem ∧
      Frm B [(slot w 16, 80 * (w + 2))] s.mem u.mem ∧
      Keep [.rax, .rbp, .r14, .r8, .r10, .rsi, .rdx] s u := by
  have hn := h.ws.scr.nowrap
  have zT := h.sl (show aT < 26 by decide); have zS := h.sl (show aS < 26 by decide)
  have eT : slot w aT = 256 + 23 * (8 * (w + 2)) := slot_eq w 23
  have eS : slot w aS = 256 + 24 * (8 * (w + 2)) := slot_eq w 24
  have hw := h.ws.w2
  rw [show csubT = [.block (([.mov32 .rbp (.imm 0)] : List Instr) ++ base aT .r8 ++ base aP .r10 ++ base aS .rsi),
    wordLoop 0 subBody] ++ [wordLoop 0 selBody] from rfl, seqs_append_iff _ _ (by simp) (by simp)]
  refine WP.mono (subN_ok h (a := aT) (b := aP) (c := aS) (by decide) (by decide) (by decide) (by decide)
    (by decide) h12 hN hNw) fun s₁ ⟨cb, bp₁, hv, h8, hsi, o₁, k₁⟩ => ?_
  have hs₁ := h.ws.scr.congr k₁.2.2
  have ht₁ : wv s₁.mem B (slot w aT) N = t := by
    rw [o₁.wv (Or.inl (by omega)) (by omega), ht]
  have hSlt := wv_lt s₁.mem B (slot w aS) N
  refine WP.mono (sel_ok hs₁ h8 hsi bp₁ ((k₁.gpr (by decide)).trans h12) hN (by omega) (by omega) (by omega)
    (by omega)) fun u ⟨hu, o₂, k₂⟩ => ⟨?_, ?_, ?_, (k₁.trans k₂).mono (by decide)⟩
  · rw [hu, ht₁]
    rw [hp] at hv
    cases cb
    · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero, Bool.false_eq_true, ↓reduceIte] at hv ⊢
      split <;> omega
    · simp only [Bool.toNat_true, Nat.mul_one, ↓reduceIte] at hv ⊢
      split <;> omega
  · intro x hx
    rw [o₂ x (hx (slot w aT, 8 * N) (by simp)), o₁ x (hx (slot w aS, 8 * N) (by simp))]
  · exact (frW o₁ (by decide) (by decide) (by omega)).trans (frW o₂ (by decide) (by decide) (by omega))

theorem decR11_ok (s : State) {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 64)
    (hb : s.gpr .r11 = BitVec.ofNat 64 j) :
    WP isa (.block [.alu .sub .r11 (.imm 1)]) s fun s' =>
      s'.gpr .r11 = BitVec.ofNat 64 (j - 1) ∧ s'.zf = some (decide (j - 1 = 0)) ∧ s'.mem = s.mem ∧
        Keep [.r11] s s' := by
  have e := VG.Proof.X25519.X86_64.ofNat_sub_one hj hj'
  have ez := VG.Proof.X25519.X86_64.ofNat_eq_zero (j := j - 1) (by omega)
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 (j - 1) ∧
    t.zf = some (decide (j - 1 = 0)) ∧ t.mem = s.mem) ?_ rfl) fun t ⟨⟨a, b, c⟩, k⟩ => ⟨a, b, c, k⟩
  have e' : BitVec.ofNat 64 j - 1 = BitVec.ofNat 64 (j - 1) := e
  xrun [hb]
  rw [e']; exact ⟨rfl, ez⟩

/-- `dbl`: `[t] := 2 [t]`, less `m` if not below it, over `N` words, and the count less one. -/
theorem dbl_ok {s : State} {B : Addr} {Z w n N : Nat} (h : FS B Z w n s) (h12 : s.gpr .r12 = BitVec.ofNat 64 N)
    (hN : 1 ≤ N) (hNw : N ≤ w + 2) {t p c : Nat} (ht : wv s.mem B (slot w aT) N = t)
    (hp : wv s.mem B (slot w aP) N = p) (h2t : 2 * t < 2 ^ (64 * N))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 c) (hc : 1 ≤ c) (hc' : c < 2 ^ 64) :
    WP isa dbl s fun u =>
      wv u.mem B (slot w aT) N = (if 2 * t < p then 2 * t else 2 * t - p) ∧
      u.gpr .r11 = BitVec.ofNat 64 (c - 1) ∧ u.zf = some (decide (c - 1 = 0)) ∧
      Frm B [(slot w aT, 8 * N), (slot w aS, 8 * N)] s.mem u.mem ∧
      Frm B [(slot w 16, 80 * (w + 2))] s.mem u.mem ∧
      Keep [.rax, .rbp, .r14, .r8, .r10, .rsi, .rdx, .rbx, .r11] s u := by
  have hn := h.ws.scr.nowrap
  have zT := h.sl (show aT < 26 by decide)
  have eT : slot w aT = 256 + 23 * (8 * (w + 2)) := slot_eq w 23
  have eS : slot w aS = 256 + 24 * (8 * (w + 2)) := slot_eq w 24
  have hw := h.ws.w2
  unfold dbl
  rw [seqs_append_iff _ _ (by simp) (by simp), seqs_append_iff _ _ (by simp) (by simp [csubT])]
  simp only [seqs]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask false ∧
    t.mem = s.mem) (by xrun) rfl) fun s₁ ⟨⟨bp₁, m₁⟩, k₁⟩ =>
    WP.mono (base_ok aT (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans h.ws.rdi)
      ((k₁.gpr (by decide)).trans h.r9)) fun s₂ ⟨bx, m₂, k₂⟩ => ?_))
  refine WP.mono (shl_ok (h.ws.scr.congr (k₁.trans k₂).2.2) bx (((k₁.trans k₂).gpr (by decide)).trans h12)
    ((k₂.gpr (by decide)).trans bp₁) hN (by omega) (by omega)) fun s₃ ⟨c₃, _, hv₃, o₃, k₃⟩ => ?_
  rw [m₂, m₁, ht] at hv₃
  rw [m₂, m₁] at o₃
  have hc₃ : c₃ = false := by
    cases c₃
    · rfl
    · have := wv_lt s₃.mem B (slot w aT) N
      simp at hv₃; omega
  subst hc₃
  simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hv₃
  have k13 := (k₁.trans k₂).trans k₃
  have h₃ : FS B Z w n s₃ := h.of_out o₃ k13 (by decide) (by decide) (by decide)
  have hp₃ : wv s₃.mem B (slot w aP) N = p := by
    have eP : slot w aP = 256 + 25 * (8 * (w + 2)) := slot_eq w 25
    have := h.sl (show aP < 26 by decide)
    rw [o₃.wv (Or.inr (by omega)) (by omega), hp]
  refine WP.mono (csubT_ok h₃ ((k13.gpr (by decide)).trans h12) hN hNw hv₃ hp₃)
    fun s₄ ⟨hv₄, f₄, F₄, k₄⟩ => ?_
  refine WP.mono (decR11_ok s₄ hc hc' (((k13.trans k₄).gpr (by decide)).trans h11))
    fun u ⟨r11u, zu, mu, ku⟩ => ⟨by rw [mu]; exact hv₄, r11u, zu, ?_, ?_, ((k13.trans k₄).trans ku).mono (by decide)⟩
  · rw [mu]; exact (Frm.of_outside o₃ (by simp)).trans f₄
  · rw [mu]; exact (frW o₃ (by decide) (by decide) (by omega)).trans F₄

/-- `K` doublings modulo `p` of `[t] = t₀ ≤ p` (`n + 1` words, `p < 2^(64 n)`): `[t] ≤ p`,
`[t] ≡ t₀ 2^K`. -/
theorem dblLoop_ok {s : State} {B : Addr} {Z w n : Nat} (h : FS B Z w n s)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 (n + 1)) {t₀ p K : Nat} (ht : wv s.mem B (slot w aT) (n + 1) = t₀)
    (hp : wv s.mem B (slot w aP) (n + 1) = p) (htp : t₀ ≤ p) (hpn : p < 2 ^ (64 * n))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 K) (hK : 1 ≤ K) (hK' : K < 2 ^ 64) :
    WP isa (.loop dbl .ne) s fun u => FS B Z w n u ∧ u.gpr .r12 = BitVec.ofNat 64 (n + 1) ∧
      wv u.mem B (slot w aT) (n + 1) ≤ p ∧
      (wv u.mem B (slot w aT) (n + 1) : Int) ≡ t₀ * 2 ^ K [ZMOD p] ∧
      Frm B [(slot w aT, 8 * (n + 1)), (slot w aS, 8 * (n + 1))] s.mem u.mem ∧
      Frm B [(slot w 16, 80 * (w + 2))] s.mem u.mem ∧
      Keep [.rax, .rbp, .r14, .r8, .r10, .rsi, .rdx, .rbx, .r11] s u := by
  have hn := h.ws.scr.nowrap
  have hnw := h.nw
  have eT : slot w aT = 256 + 23 * (8 * (w + 2)) := slot_eq w 23
  have eS : slot w aS = 256 + 24 * (8 * (w + 2)) := slot_eq w 24
  have eP : slot w aP = 256 + 25 * (8 * (w + 2)) := slot_eq w 25
  have zP := h.sl (show aP < 26 by decide)
  have hM : 2 * p < 2 ^ (64 * (n + 1)) := by
    rw [show 64 * (n + 1) = 64 * n + 64 by omega, Nat.pow_add]
    have : 2 ≤ 2 ^ 64 := by decide
    have := Nat.mul_le_mul_left (2 ^ (64 * n)) this
    omega
  refine VG.Proof.X25519.X86_64.cntLoop_ok (n := K)
    (Inv := fun j u => FS B Z w n u ∧ u.gpr .r12 = BitVec.ofNat 64 (n + 1) ∧ u.gpr .r11 = BitVec.ofNat 64 j ∧
      wv u.mem B (slot w aT) (n + 1) ≤ p ∧
      (wv u.mem B (slot w aT) (n + 1) : Int) ≡ t₀ * 2 ^ (K - j) [ZMOD p] ∧
      wv u.mem B (slot w aP) (n + 1) = p ∧
      Frm B [(slot w aT, 8 * (n + 1)), (slot w aS, 8 * (n + 1))] s.mem u.mem ∧
      Frm B [(slot w 16, 80 * (w + 2))] s.mem u.mem ∧
      Keep [.rax, .rbp, .r14, .r8, .r10, .rsi, .rdx, .rbx, .r11] s u)
    (fun j u hj1 hjK ⟨hu, u12, u11, tle, tc, up, f₁, F₁, ku⟩ => ?_)
    (fun u ⟨hu, u12, _, tle, tc, _, f₁, F₁, ku⟩ => ⟨hu, u12, tle, by simpa using tc, f₁, F₁, ku⟩) hK
    ⟨h, h12, h11, by rw [ht]; exact htp, by rw [ht, Nat.sub_self, pow_zero, Int.mul_one], hp,
      Frm.refl _ _ _, Frm.refl _ _ _, Keep.refl _ _⟩
  refine WP.mono (dbl_ok hu u12 (by omega) (by omega) rfl up (by omega) u11 hj1 (by omega))
    fun v ⟨hv, v11, vz, f₂, F₂, kv⟩ => ⟨⟨?_, (kv.gpr (by decide)).trans u12, v11, ?_, ?_, ?_, f₁.trans f₂,
      F₁.trans F₂, (ku.trans kv).mono (by decide)⟩, vz⟩
  · refine ⟨hu.ws.congr f₂ (fun r hr => ?_) kv (by decide), hu.z, (kv.gpr (by decide)).trans hu.r9,
      (kv.gpr (by decide)).trans hu.r13, hu.n1, hu.nw⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Mut.ofSlot _ _ _
  · rw [hv]; split <;> omega
  · rw [hv, show K - (j - 1) = (K - j) + 1 by omega, pow_succ]
    split
    · push_cast
      have := tc.mul_left 2
      rw [show (2 : Int) * (t₀ * 2 ^ (K - j)) = t₀ * (2 ^ (K - j) * 2) by ring] at this
      exact this
    · rw [Nat.cast_sub (by omega)]
      push_cast
      have := tc.mul_left 2
      rw [show (2 : Int) * (t₀ * 2 ^ (K - j)) = t₀ * (2 ^ (K - j) * 2) by ring] at this
      exact (Int.modEq_iff_dvd.mpr ⟨1, by ring⟩).trans this
  · rw [f₂.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega) (by omega), up]

end VG.Proof.Rsa.X86_64.InvB
