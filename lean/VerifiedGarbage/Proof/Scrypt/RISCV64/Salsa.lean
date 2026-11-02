module

public import VerifiedGarbage.Impl.Scrypt.RISCV64.Salsa
public import VerifiedGarbage.Proof.Scrypt.Spec
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Scrypt.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Scrypt.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Impl.Scrypt.RISCV64.Salsa
meta import VerifiedGarbage.Proof.Scrypt.Spec
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Spec.Scrypt.Contract
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Scrypt.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# The Salsa20/8 Core on RISC-V

Untrusted: everything here is checked by Lean. The structure of the PPC64LE
proof (`Proof/Scrypt/PPC64LE/Salsa.lean`) and of RISC-V's ChaCha20 block
(`Proof/ChaCha20/RISCV64/Block.lean`): the rounds on the low words of the
registers (`RI`), each line an addition, a rotation by two word shifts and
an `or`, and an XOR (`line_regs`); then the whole function (`correct`),
for both widths of its accesses (`wide`: `lw` and `sw`; otherwise the
byte-wise `loadLE32` and `storeLE32`), constant time, and `salsa_verified`
against `Proof.Scrypt.salsaRISCV64`.
-/

@[expose] public section

namespace VG.Proof.Scrypt

open Spec.Scrypt

open VG.RISCV64 in
/-- RISC-V contract for `vg_salsa20_8(b = a0, save = a1)` (`wide`) and
`vg_salsa20_8_bytes`: replaces the 64 bytes at `b` by their Salsa20/8 Core.
`save` (40 bytes, a multiple of 8) is where the callee-saved registers are
saved; `b` must be a multiple of 4 for `wide`. The pointers are public; the
data is secret. -/
def salsaRISCV64 (wide : Bool) : Contract RISCV64.isa where
  pre s :=
    let b : Region := ⟨s.gpr .a0, 64⟩
    let sv : Region := ⟨s.gpr .a1, 40⟩
    s.rd = [] ∧ s.wr = [b, sv] ∧ b.Disjoint sv ∧ (s.gpr .a1).toNat % 8 = 0 ∧
      (wide = true → (s.gpr .a0).toNat % 4 = 0)
  post s s' := bytesAt s'.mem (s.gpr .a0) 64 = salsa (bytesAt s.mem (s.gpr .a0) 64)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.sp = s₂.sp

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.RISCV64

open VG VG.RISCV64 VG.RISCV64.ByteLoad VG.Impl.Scrypt.RISCV64 VG.Impl.Words.RISCV64
open VG.Spec.Scrypt (Word)
open VG.Proof.Scrypt

/-- The low word of a register. -/
abbrev lo (x : BitVec 64) : Word := x.setWidth 32

/-! ## Registers -/

theorem wreg_inj {j k : Nat} (hj : j < 16) (hk : k < 16) (h : wreg j = wreg k) : j = k := by
  have key : ∀ j, j < 16 → ∀ k, k < 16 → wreg j = wreg k → j = k := by decide
  exact key j hj k hk h

theorem wreg_ne {k : Nat} (hk : k < 16) :
    wreg k ≠ .t0 ∧ wreg k ≠ .t1 ∧ wreg k ≠ .a0 ∧ wreg k ≠ .a1 ∧ wreg k ≠ .ra := by
  have key : ∀ k < 16, wreg k ≠ .t0 ∧ wreg k ≠ .t1 ∧ wreg k ≠ .a0 ∧ wreg k ≠ .a1 ∧ wreg k ≠ .ra := by
    decide
  exact key k hk

/-- The registers that hold words, and the temporaries. -/
def Words (r : Reg) : Prop := (∃ k < 16, r = wreg k) ∨ r = .t0 ∨ r = .t1

theorem not_words {r : Reg} (h : ∀ k < 16, r ≠ wreg k) (h0 : r ≠ .t0) (h1 : r ≠ .t1) :
    ¬ Words r := by
  rintro (⟨k, hk, e⟩ | e | e)
  exacts [h k hk e, h0 e, h1 e]

theorem not_words_a0 : ¬ Words .a0 :=
  not_words (fun _ hk e => (wreg_ne hk).2.2.1 e.symm) (by decide) (by decide)
theorem not_words_a1 : ¬ Words .a1 :=
  not_words (fun _ hk e => (wreg_ne hk).2.2.2.1 e.symm) (by decide) (by decide)
theorem not_words_ra : ¬ Words .ra :=
  not_words (fun _ hk e => (wreg_ne hk).2.2.2.2 e.symm) (by decide) (by decide)

theorem saved_inj {i j : Nat} (hi : i < 5) (hj : j < 5) (h : saved i = saved j) : i = j := by
  have key : ∀ i < 5, ∀ j < 5, saved i = saved j → i = j := by decide
  exact key i hi j hj h

theorem saved_ne_a1 {i : Nat} (hi : i < 5) : saved i ≠ .a1 := by
  have key : ∀ i < 5, saved i ≠ .a1 := by decide
  exact key i hi

/-- A preserved register is saved, or not a word register nor a temporary. -/
theorem preserved_cases {r : Reg} (hr : r ∈ preserved) : (∃ i < 5, r = saved i) ∨ ¬ Words r := by
  have key : ∀ r ∈ preserved,
      (∃ i < 5, r = saved i) ∨ ((∀ k < 16, r ≠ wreg k) ∧ r ≠ .t0 ∧ r ≠ .t1) := by decide
  rcases key r hr with h | ⟨h, h0, h1⟩
  · exact .inl h
  · exact .inr (not_words h h0 h1)

/-! ## One line, on registers -/

/-- `a ^= R(b + c, n)`, through `t0` and `t1`, on the low words. -/
theorem line_regs {a b c : Reg} (ha0 : a ≠ .t0) (ha1 : a ≠ .t1) {n : Nat} (hn0 : 0 < n)
    (hn : n < 32) (s : State) :
    WP isa (.block [.addw .t0 b c, .shift .sll .w .t1 .t0 n, .shift .srl .w .t0 .t0 (32 - n),
        .logic .or .t0 .t0 .t1, .logic .xor a a .t0]) s fun s' =>
      lo (s'.gpr a) = lo (s.gpr a) ^^^ (lo (s.gpr b) + lo (s.gpr c)).rotateLeft n ∧
      (∀ r, r ≠ a → r ≠ .t0 → r ≠ .t1 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hn' : 32 - n < 32 := by omega
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addw, exec_logic, exec_shift_w hn,
    exec_shift_w hn', Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r h₁ h₂ h₃ => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_write, ite_true, ha0, ha1, ite_false, lo32_xor, lo32_or, lo32_sext,
      show Reg.t0 ≠ Reg.t1 by decide, show Reg.t1 ≠ Reg.t0 by decide]
    rw [BitVec.or_comm, rotl_shifts _ hn]
  · simp only [RegUpd.gpr_write, h₁, h₂, h₃, ite_false]

/-! ## Where the words are -/

/-- The words `v` are in the low words of the registers. -/
def Holds (v : Vector Word 16) (s : State) : Prop := ∀ k (hk : k < 16), lo (s.gpr (wreg k)) = v[k]

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (v : Vector Word 16) (s₀ s : State) : Prop where
  holds : Holds v s
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r

/-- The side conditions of `line_ok`, decidable for concrete arguments. -/
def LSide (i j k n : Nat) : Bool :=
  decide (i < 16 ∧ j < 16 ∧ k < 16 ∧ 1 ≤ n ∧ n ≤ 31)

theorem line_ok {i j k n : Nat} (hs : LSide i j k n = true) {v : Vector Word 16} {s₀ s : State}
    (h : RI v s₀ s) : WP isa (.block (line i j k n)) s (RI (stepN v i j k n) s₀) := by
  simp only [LSide, decide_eq_true_eq] at hs
  obtain ⟨hi, hj, hk, h1, h2⟩ := hs
  refine WP.mono (line_regs (wreg_ne hi).1 (wreg_ne hi).2.1 (show 0 < n by omega)
    (show n < 32 by omega) s) fun s' ⟨ha, hr, hm, hrd, hwr⟩ =>
    ⟨fun m hm' => ?_, hm.trans h.mem, hrd.trans h.rd, hwr.trans h.wr, fun r hw => ?_⟩
  · rw [stepN_get v n hi hj hk m hm']
    by_cases e : i = m
    · subst e
      simp only [ite_true]
      rw [ha, h.holds i hi, h.holds j hj, h.holds k hk]
    · simp only [e, ite_false]
      rw [hr _ (fun e' => e (wreg_inj hi hm' e'.symm)) (wreg_ne hm').1 (wreg_ne hm').2.1]
      exact h.holds m hm'
  · rw [hr r (fun e => hw (.inl ⟨i, hi, e⟩)) (fun e => hw (.inr (.inl e)))
      (fun e => hw (.inr (.inr e)))]
    exact h.keep r hw

/-! ## Double rounds -/

theorem lines_ok {s₀ : State} :
    ∀ (l : List (Nat × Nat × Nat × Nat)), (l.all fun (i, j, k, n) => LSide i j k n) = true →
      ∀ (v : Vector Word 16) (s : State), RI v s₀ s →
      WP isa (.block (l.flatMap fun (i, j, k, n) => line i j k n)) s
        (RI (l.foldl (fun x (i, j, k, n) => stepN x i j k n) v) s₀)
  | [], _, _, _, h => WP.block_nil h
  | (i, j, k, n) :: l, hl, v, s, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hl
    rw [List.flatMap_cons, WP.block_append_iff, List.foldl_cons]
    exact WP.mono (line_ok hl.1 h) fun s' h' => lines_ok l hl.2 _ s' h'

theorem doubleRound_eq (v : Vector Word 16) : Spec.Scrypt.doubleRound v =
    lines.foldl (fun x (i, j, k, n) => stepN x i j k n) v := rfl

theorem doubleRound_ok {v : Vector Word 16} {s₀ s : State} (h : RI v s₀ s) :
    WP isa doubleRound s (RI (Spec.Scrypt.doubleRound v) s₀) := by
  rw [doubleRound_eq]
  exact lines_ok lines (by decide) v s h

theorem rounds_ok {v : Vector Word 16} {s₀ : State} (h : Holds v s₀) :
    ∀ n, WP isa (rounds n) s₀ (RI (Nat.repeat Spec.Scrypt.doubleRound n v) s₀)
  | 0 => WP.block_nil ⟨h, rfl, rfl, rfl, fun _ _ => rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds_ok h n) fun _ h' => doubleRound_ok h')

/-! ## The precondition -/

section
variable (s₀ : State)
/-- `b`. -/
abbrev bp : Addr := s₀.gpr .a0
/-- `save`. -/
abbrev svp : Addr := s₀.gpr .a1
abbrev bR : Region := ⟨bp s₀, 64⟩
abbrev svR : Region := ⟨svp s₀, 40⟩
/-- The input words. -/
def V : Vector Word 16 := Vector.ofFn fun j => s₀.mem.readW (bp s₀ + BitVec.ofNat 64 (4 * j.1)) 32
/-- The result of the rounds. -/
abbrev Rs : Vector Word 16 := Nat.repeat Spec.Scrypt.doubleRound 4 (V s₀)
end

structure Pre (wide : Bool) (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [bR s₀, svR s₀]
  disj : (bR s₀).Disjoint (svR s₀)
  sv_al : (svp s₀).toNat % 8 = 0
  b_al : wide = true → (bp s₀).toNat % 4 = 0

theorem pre_of {wide : Bool} (s₀ : State) (h : (Proof.Scrypt.salsaRISCV64 wide).pre s₀) :
    Pre wide s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem V_get (s₀ : State) {k : Nat} (hk : k < 16) :
    (V s₀)[k] = s₀.mem.readW (bp s₀ + BitVec.ofNat 64 (4 * k)) 32 := by
  simp only [V, Vector.getElem_ofFn]

/-- Word `k` of a 4-byte aligned pointer is 4-byte aligned. -/
theorem al4 {p : Addr} (h : p.toNat % 4 = 0) (k : Nat) :
    (p + BitVec.ofNat 64 (4 * k)).toNat % 4 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := p.isLt
  omega

/-- Doubleword `i` of an 8-byte aligned pointer is 8-byte aligned. -/
theorem al8 {p : Addr} (h : p.toNat % 8 = 0) (i : Nat) :
    (p + BitVec.ofNat 64 (8 * i)).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := p.isLt
  omega

namespace Pre
variable {wide : Bool} {s₀ : State} (hp : Pre wide s₀)
include hp

theorem in_b {k : Nat} (hk : k < 16) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (bp s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨bR s₀, by simp [hp.wr], Offset.contains_base _ (by omega) (by omega)⟩

theorem out_b {k : Nat} (hk : k < 16) : InRegions s₀.wr (bp s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
  simpa using hp.in_b hk []

theorem in_sav {i : Nat} (hi : i < 5) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (svp s₀ + BitVec.ofNat 64 (8 * i)) 8 :=
  ⟨svR s₀, by simp [hp.wr], Offset.contains_base _ (by omega) (by omega)⟩

theorem out_sav {i : Nat} (hi : i < 5) : InRegions s₀.wr (svp s₀ + BitVec.ofNat 64 (8 * i)) 8 := by
  simpa using hp.in_sav hi []

end Pre

theorem readW_writeW_word (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 16) (hk : k < 16)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofNat 64 (4 * k)) v).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
      m.readW (p + BitVec.ofNat 64 (4 * j)) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

theorem readW_writeW_sav (m : Mem) (p : Addr) (v : BitVec 64) {i j : Nat} (hi : i < 5) (hj : j < 5)
    (h : i ≠ j) :
    (m.writeW (p + BitVec.ofNat 64 (8 * j)) v).readW (p + BitVec.ofNat 64 (8 * i)) 64 =
      m.readW (p + BitVec.ofNat 64 (8 * i)) 64 :=
  Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

/-! ## Words of `b` -/

/-- `loadWord`: the low word of `d` is the word read, and only `d` and `t1`
change. -/
theorem loadWord_ok {wide : Bool} {s : State} {d : Reg} {off : Nat} (hd0 : d ≠ .a0) (hd1 : d ≠ .t1)
    (ho : off + 3 < 2048) (ha : wide = true → (s.gpr .a0 + BitVec.ofNat 64 off).toNat % 4 = 0)
    (h : InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 off) 4) :
    WP isa (.block (loadWord wide d off)) s fun s' =>
      lo (s'.gpr d) = s.mem.readW (s.gpr .a0 + BitVec.ofNat 64 off) 32 ∧
      (∀ r, r ≠ d → r ≠ .t1 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases wide with
  | true =>
    apply WP.of_runBlock
    simp only [loadWord, ↓reduceIte]
    rw [runBlock_cons, exec_load_w (by omega) (ha rfl) h, runStep_some,
      runBlock_nil]
    refine ⟨_, rfl, ?_, fun r h₁ _ => RegUpd.gpr_write_of_ne _ _ h₁, rfl, rfl, rfl⟩
    dsimp only [lo]
    rw [RegUpd.gpr_write_self, lo32_ext]
  | false =>
    simp only [loadWord, Bool.false_eq_true, ↓reduceIte]
    refine WP.mono (loadLE32_ok hd0 (by decide) hd1 ho h) fun s' e => ?_
    subst e
    refine ⟨?_, fun r h₁ h₂ => ?_, rfl, rfl, rfl⟩
    · dsimp only [lo]
      rw [RegUpd.gpr_write_self, lo32_ext]
    · rw [RegUpd.gpr_write_of_ne _ _ h₁, RegUpd.gpr_write_of_ne _ _ h₂]

/-- `storeWord`: the low word of `v` is written, and only `t1` changes. -/
theorem storeWord_ok {wide : Bool} {s : State} {v : Reg} {off : Nat} (hv1 : v ≠ .t1)
    (ho : off + 3 < 2048) (ha : wide = true → (s.gpr .a0 + BitVec.ofNat 64 off).toNat % 4 = 0)
    (h : InRegions s.wr (s.gpr .a0 + BitVec.ofNat 64 off) 4) :
    WP isa (.block (storeWord wide v off)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .a0 + BitVec.ofNat 64 off) (lo (s.gpr v)) ∧
      (∀ r, r ≠ .t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases wide with
  | true =>
    apply WP.of_runBlock
    simp only [storeWord, ↓reduceIte]
    rw [runBlock_cons, exec_store_w (by omega) (ha rfl) h, runStep_some,
      runBlock_nil]
    exact ⟨_, rfl, rfl, fun _ _ => rfl, rfl, rfl⟩
  | false =>
    simp only [storeWord, Bool.false_eq_true, ↓reduceIte]
    refine WP.mono (storeLE32_ok (Ne.symm hv1) (by decide) ho h) fun s' e => ?_
    subst e
    exact ⟨rfl, fun r h₁ => RegUpd.gpr_write_of_ne _ _ h₁, rfl, rfl⟩

/-! ## Saving the callee-saved registers -/

/-- The first `n` registers are saved. -/
structure SI (s₀ : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [svR s₀] s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (svp s₀ + BitVec.ofNat 64 (8 * i)) 64 = s₀.gpr (saved i)

theorem save_step {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {n : Nat} (hn : n < 5) {s : State}
    (h : SI s₀ n s) : WP isa (.block [.store .d (saved n) .a1 (8 * n)]) s (SI s₀ (n + 1)) := by
  have ha1 : s.gpr .a1 = svp s₀ := by rw [h.gpr]
  apply WP.of_runBlock
  rw [runBlock_cons, exec_store_d (by omega) (by rw [ha1]; exact al8 hp.sv_al n)
    (by rw [h.wr, ha1]; exact hp.out_sav hn), runStep_some, runBlock_nil]
  refine ⟨_, rfl, h.gpr, h.rd, h.wr, h.frame.writeW (List.mem_singleton_self _) _ ?_,
    fun i hi => ?_⟩
  · rw [ha1]; exact Offset.contains_base _ (by omega) (by omega)
  · simp only [ha1]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [readW_writeW_sav _ _ _ (by omega) hn (by omega)]
      exact h.saved i hi
    · rw [Mem.readW_writeW_self64, h.gpr]

/-! ## Loading the input -/

/-- After loading `n` words. -/
structure LI (s₀ : State) (n : Nat) (s : State) : Prop where
  loaded : ∀ j (hj : j < 16), j < n → lo (s.gpr (wreg j)) = (V s₀)[j]
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r

theorem load_step {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {n : Nat} (hn : n < 16) {s : State}
    (h : LI s₀ n s) : WP isa (.block (loadWord wide (wreg n) (4 * n))) s (LI s₀ (n + 1)) := by
  have hr0 : s.gpr .a0 = bp s₀ := h.keep _ not_words_a0
  refine WP.mono (loadWord_ok (wreg_ne hn).2.2.1 (wreg_ne hn).2.1 (by omega)
    (fun hw => by rw [hr0]; exact al4 (hp.b_al hw) n)
    (by rw [h.rd, h.wr, hr0]; exact hp.in_b hn _)) fun s' ⟨hd, hr, hm, hrd, hwr⟩ => ?_
  refine ⟨fun j hj hjn => ?_, hm.trans h.mem, hrd.trans h.rd, hwr.trans h.wr, fun r hw => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · rw [hr _ (fun e => absurd (wreg_inj hj hn e) (by omega)) (wreg_ne hj).2.1]
      exact h.loaded j hj hjn
    · rw [hd, hr0, h.mem, V_get _ hj]
  · rw [hr r (fun e => hw (.inl ⟨n, hn, e⟩)) (fun e => hw (.inr (.inr e)))]
    exact h.keep r hw

/-! ## Adding the input -/

/-- After finishing words `0 … i - 1`: those words of `b` hold the sums, the
others still hold the input, and words `i … 15` of the rounds' result `R` are
still in their registers. -/
structure FI (s₀ : State) (R : Vector Word 16) (i : Nat) (s : State) : Prop where
  out : ∀ j (hj : j < 16), s.mem.readW (bp s₀ + BitVec.ofNat 64 (4 * j)) 32 =
    if j < i then R[j] + (V s₀)[j] else (V s₀)[j]
  rest : ∀ j (hj : j < 16), i ≤ j → lo (s.gpr (wreg j)) = R[j]
  frame : Frame [bR s₀] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r

theorem finish_step {wide : Bool} {s₀ : State} (hp : Pre wide s₀) {R : Vector Word 16} {i : Nat}
    (hi : i < 16) {s : State} (h : FI s₀ R i s) :
    WP isa (.block (finishWord wide i)) s (FI s₀ R (i + 1)) := by
  have hr0 : s.gpr .a0 = bp s₀ := h.keep _ not_words_a0
  have hne := wreg_ne hi
  have hv : s.mem.readW (bp s₀ + BitVec.ofNat 64 (4 * i)) 32 = (V s₀)[i] := by
    rw [h.out i hi, ite_eq_right_iff.mpr fun h => absurd h (Nat.lt_irrefl i)]
  unfold finishWord
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadWord_ok (d := .t0) (by decide) (by decide) (by omega)
    (fun hw => by rw [hr0]; exact al4 (hp.b_al hw) i)
    (by rw [h.rd, h.wr, hr0]; exact hp.in_b hi _)) fun s₁ ⟨t₁, g₁, m₁, rd₁, wr₁⟩ => ?_
  rw [List.singleton_append]
  refine Steps.WP.cons exec_addw ?_
  have hb₁ : s₁.gpr .a0 = bp s₀ := by rw [g₁ _ (by decide) (by decide), hr0]
  have hw : lo (sext32 (lo (s₁.gpr (wreg i)) + lo (s₁.gpr .t0))) = R[i] + (V s₀)[i] := by
    dsimp only [lo] at t₁ ⊢
    rw [lo32_sext, t₁, hr0, hv, g₁ _ hne.1 hne.2.1]
    have := h.rest i hi (Nat.le_refl _)
    dsimp only [lo] at this
    rw [this]
  refine WP.mono (storeWord_ok (s := s₁.write (wreg i) _) (v := wreg i) hne.2.1 (by omega)
    (fun hwd => by rw [RegUpd.gpr_write_of_ne _ _ (Ne.symm hne.2.2.1), hb₁]; exact al4 (hp.b_al hwd) i)
    (by rw [RegUpd.wr_write, RegUpd.gpr_write_of_ne _ _ (Ne.symm hne.2.2.1), hb₁, wr₁, h.wr]
        exact hp.out_b hi)) fun s' ⟨m', g', rd', wr'⟩ => ?_
  have hm : s'.mem = s.mem.writeW (bp s₀ + BitVec.ofNat 64 (4 * i)) (R[i] + (V s₀)[i]) := by
    rw [m', RegUpd.mem_write, RegUpd.gpr_write_of_ne _ _ (Ne.symm hne.2.2.1), hb₁,
      RegUpd.gpr_write_self, hw, m₁]
  have g₂ : ∀ r, r ≠ wreg i → r ≠ .t0 → r ≠ .t1 → s'.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by
    rw [g' r h₃, RegUpd.gpr_write_of_ne _ _ h₁, g₁ r h₂ h₃]
  have hfr : Frame [bR s₀] s₀.mem s'.mem := by
    rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  have hrd : s'.rd = s₀.rd := by rw [rd', RegUpd.rd_write, rd₁, h.rd]
  have hwr : s'.wr = s₀.wr := by rw [wr', RegUpd.wr_write, wr₁, h.wr]
  refine ⟨fun j hj => ?_, fun j hj hij => ?_, hfr, hrd, hwr, fun r hw' => ?_⟩
  · rw [hm]
    by_cases e : j = i
    · subst e
      rw [Mem.readW_writeW_self32, ite_eq_left_iff.mpr fun h => absurd (Nat.lt_succ_self j) h]
    · rw [readW_writeW_word _ _ _ hj hi e, h.out j hj]
      by_cases hji : j < i
      · rw [ite_eq_left_iff.mpr fun h => absurd hji h,
          ite_eq_left_iff.mpr fun h => absurd (by omega) h]
      · rw [ite_eq_right_iff.mpr fun h => absurd h hji,
          ite_eq_right_iff.mpr fun h => absurd h (by omega)]
  · rw [g₂ _ (fun e => absurd (wreg_inj hj hi e) (by omega)) (wreg_ne hj).1 (wreg_ne hj).2.1]
    exact h.rest j hj (by omega)
  · rw [g₂ r (fun e => hw' (.inl ⟨i, hi, e⟩)) (fun e => hw' (.inr (.inl e)))
      (fun e => hw' (.inr (.inr e)))]
    exact h.keep r hw'

/-! ## Restoring the callee-saved registers -/

/-- The first `n` registers are restored, from the state `sB` the restoring
starts in. -/
structure RI' (s₀ sB : State) (n : Nat) (s : State) : Prop where
  restored : ∀ i < n, s.gpr (saved i) = s₀.gpr (saved i)
  others : ∀ r, (∀ i < 5, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem restore_step {wide : Bool} {s₀ sB : State} (hp : Pre wide s₀) (ha1 : sB.gpr .a1 = svp s₀)
    (hsav : ∀ i < 5, sB.mem.readW (svp s₀ + BitVec.ofNat 64 (8 * i)) 64 = s₀.gpr (saved i))
    {n : Nat} (hn : n < 5) {s : State} (h : RI' s₀ sB n s) :
    WP isa (.block [.load .d (saved n) .a1 (8 * n)]) s (RI' s₀ sB (n + 1)) := by
  have ha1' : s.gpr .a1 = svp s₀ := by
    rw [h.others _ fun i hi e => saved_ne_a1 hi e.symm, ha1]
  apply WP.of_runBlock
  rw [runBlock_cons, exec_load_d (by omega) (by rw [ha1']; exact al8 hp.sv_al n)
    (by rw [h.rd, h.wr, ha1']; exact hp.in_sav hn _), runStep_some, runBlock_nil]
  refine ⟨_, rfl, fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [RegUpd.gpr_write_of_ne _ _ fun e => absurd (saved_inj (by omega) hn e) (by omega)]
      exact h.restored i hi
    · rw [RegUpd.gpr_write_self, ha1', h.mem, hsav i hn]
  · rw [RegUpd.gpr_write_of_ne _ _ (hr n hn)]; exact h.others r hr

/-! ## The whole function -/

/-- The input words are those the specification reads from the bytes. -/
theorem input_eq (s₀ : State) :
    (Vector.ofFn fun j : Fin 16 => Spec.Scrypt.wordLE (Spec.Scrypt.bytesAt s₀.mem (bp s₀) 64) j.1) =
      V s₀ := by
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_ofFn, V_get _ hj, wordLE_bytesAt _ _ (by omega)]

/-- The result words are where the specification writes its bytes. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ j (hj : j < 16), m.readW (bp s₀ + BitVec.ofNat 64 (4 * j)) 32 = (Rs s₀)[j] + (V s₀)[j]) :
    Spec.Scrypt.bytesAt m (bp s₀) 64 = Spec.Scrypt.salsa (Spec.Scrypt.bytesAt s₀.mem (bp s₀) 64) := by
  rw [Spec.Scrypt.salsa, input_eq]
  refine bytesAt_eq_serialize _ _ _ fun j hj => ?_
  rw [Spec.Scrypt.core, Vector.getElem_zipWith, ← h j hj]

/-- The main part, from the state `s₁` after saving the registers. -/
theorem main_ok {wide : Bool} {s₁ : State} (hp : Pre wide s₁) :
    WP isa (main wide) s₁ fun s' =>
      (∀ j (hj : j < 16), s'.mem.readW (bp s₁ + BitVec.ofNat 64 (4 * j)) 32 = (Rs s₁)[j] + (V s₁)[j]) ∧
      Frame [bR s₁] s₁.mem s'.mem ∧ s'.rd = s₁.rd ∧ s'.wr = s₁.wr ∧
      (∀ r, ¬ Words r → s'.gpr r = s₁.gpr r) := by
  have hl₀ : LI s₁ 0 s₁ := ⟨fun _ _ h => absurd h (by omega), rfl, rfl, rfl, fun _ _ => rfl⟩
  have hload : WP isa (.block (load wide)) s₁ (LI s₁ 16) := by
    unfold load
    exact wp_range_flatMap (M := isa) (LI s₁) (fun k s hk h => load_step hp hk h) 16 (Nat.le_refl _)
      s₁ hl₀
  refine WP.seq (WP.mono hload fun s₂ h₂ => ?_)
  have hh₂ : Holds (V s₁) s₂ := fun k hk => h₂.loaded k hk hk
  refine WP.seq (WP.mono (rounds_ok hh₂ 4) fun s₃ h₃ => ?_)
  have hf₃ : FI s₁ (Rs s₁) 0 s₃ :=
    ⟨fun j hj => by
        rw [ite_eq_right_iff.mpr fun h => absurd h (Nat.not_lt_zero j), h₃.mem, h₂.mem, V_get _ hj],
      fun j hj _ => h₃.holds j hj, by rw [h₃.mem, h₂.mem]; exact Frame.refl _ _,
      h₃.rd.trans h₂.rd, h₃.wr.trans h₂.wr, fun r hw => (h₃.keep r hw).trans (h₂.keep r hw)⟩
  unfold finish
  exact WP.mono (wp_range_flatMap (M := isa) (FI s₁ (Rs s₁)) (fun i s hi h => finish_step hp hi h) 16
    (Nat.le_refl _) s₃ hf₃) fun s' h =>
      ⟨fun j hj => by rw [h.out j hj, ite_eq_left_iff.mpr fun e => absurd hj e],
        h.frame, h.rd, h.wr, h.keep⟩

theorem correct {wide : Bool} {s₀ : State} (hp : Pre wide s₀) :
    WP isa (salsa wide) s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      (Proof.Scrypt.salsaRISCV64 wide).post s₀ s' := by
  have hs₀ : SI s₀ 0 s₀ := ⟨rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  have hsave : WP isa (.block save) s₀ (SI s₀ 5) := by
    unfold save
    exact wp_range_flatMap (M := isa) (SI s₀) (fun k s hk h => save_step hp hk h) 5 (Nat.le_refl _)
      s₀ hs₀
  refine WP.seq (WP.mono hsave fun s₁ h₁ => ?_)
  have hb : bp s₁ = bp s₀ := by simp only [bp, h₁.gpr]
  have hs : svp s₁ = svp s₀ := by simp only [svp, h₁.gpr]
  have hp₁ : Pre wide s₁ := ⟨by rw [h₁.rd, hp.rd], by rw [h₁.wr, hp.wr, bR, bR, svR, svR, hb, hs],
    by simpa only [bR, svR, hb, hs] using hp.disj, by rw [hs]; exact hp.sv_al,
    fun hw => by rw [hb]; exact hp.b_al hw⟩
  have hV : V s₁ = V s₀ := by
    apply Vector.ext
    intro j hj
    rw [V_get _ hj, V_get _ hj, hb]
    exact h₁.frame.readW (r := bR s₀) (Offset.contains_base _ (by omega) (by omega))
      (by simpa using hp.disj) (by decide)
  refine WP.seq (WP.mono (main_ok hp₁) fun s₃ ⟨hout, hf, hrd, hwr, hk⟩ => ?_)
  have ha1 : s₃.gpr .a1 = svp s₀ := by rw [hk _ not_words_a1, h₁.gpr]
  have hsav : ∀ i < 5, s₃.mem.readW (svp s₀ + BitVec.ofNat 64 (8 * i)) 64 = s₀.gpr (saved i) :=
    fun i hi => by
      rw [hf.readW (r := svR s₀) (Offset.contains_base _ (by omega) (by omega))
        (by simpa [bR, hb] using hp.disj.symm) (by decide)]
      exact h₁.saved i hi
  have hr₀ : RI' s₀ s₃ 0 s₃ :=
    ⟨fun _ h => absurd h (by omega), fun _ _ => rfl, rfl, hrd.trans h₁.rd, hwr.trans h₁.wr⟩
  refine WP.mono (wp_range_flatMap (M := isa) (RI' s₀ s₃)
    (fun k s hk h => restore_step hp ha1 hsav hk h) 5 (Nat.le_refl _) s₃ hr₀) fun s' h =>
      ⟨?_, ?_, ?_⟩
  · intro r hr
    rcases preserved_cases hr with ⟨i, hi, rfl⟩ | hw
    · exact h.restored i hi
    · rw [h.others r fun i hi e => ?_, hk r hw, h₁.gpr]
      have key : ∀ i < 5, ∃ k < 16, saved i = wreg k := by decide
      obtain ⟨k, hk', e'⟩ := key i hi
      exact hw (.inl ⟨k, hk', e.trans e'⟩)
  · rw [h.others _ fun i hi e => ?_, hk _ not_words_ra, h₁.gpr]
    have key : ∀ i < 5, saved i ≠ .ra := by decide
    exact key i hi e.symm
  · show Spec.Scrypt.bytesAt s'.mem (bp s₀) 64 = Spec.Scrypt.salsa (Spec.Scrypt.bytesAt s₀.mem (bp s₀) 64)
    rw [h.mem]
    refine post_of fun j hj => ?_
    rw [← hb, hout j hj, Rs, hV]

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 40⟩]

theorem salsa_ct (wide : Bool) :
    ConstantTime isa (Proof.Scrypt.salsaRISCV64 wide).pre (Proof.Scrypt.salsaRISCV64 wide).pub
      (Impl.Scrypt.RISCV64.salsa wide) := by
  have agree : ∀ s₁ s₂ : State, (Proof.Scrypt.salsaRISCV64 wide).pub s₁ s₂ →
      s₁.sp = s₂.sp ∧ ∀ r ∈ Taint.ofRegs [.a0, .a1], s₁.gpr r = s₂.gpr r := by
    intro s₁ s₂ ⟨h1, h2, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h1, h2]
  cases wide
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1])
      (fun s₁ s₂ _ _ h => agree s₁ s₂ h) (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1])
      (fun s₁ s₂ _ _ h => agree s₁ s₂ h) (by taint_decide)

theorem salsa_verified (wide : Bool) :
    Verified RISCV64.target (Impl.Scrypt.RISCV64.salsa wide) (Proof.Scrypt.salsaRISCV64 wide) := by
  refine ⟨fun s hs => ?_, salsa_ct wide, ?_⟩
  · obtain ⟨t, s', he, h₁, hra, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he, hra⟩, h₂⟩
  · exact ⟨satState, rfl, rfl, Region.disjoint_of_sep (by decide), by decide, fun _ => by decide⟩

end VG.Proof.Scrypt.RISCV64
