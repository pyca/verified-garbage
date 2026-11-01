module

public import VerifiedGarbage.Impl.Scrypt.PPC64LE.Salsa
public import VerifiedGarbage.Proof.Scrypt.Spec
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.Scrypt.Contract
public import VerifiedGarbage.Proof.Scrypt.Contract
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Impl.Scrypt.PPC64LE.Salsa
meta import VerifiedGarbage.Proof.Scrypt.Spec
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Spec.Scrypt.Contract

/-!
# The Salsa20/8 Core on PPC64LE

The rounds on the low words of the registers (`RI`), then the whole function
(`correct`), constant time, and `salsa_verified` against
`Proof.Scrypt.salsaContract`.
-/

@[expose] public section

namespace VG.Proof.Scrypt.PPC64LE

open VG VG.PPC64LE VG.Impl.Scrypt.PPC64LE
open VG.Spec.Scrypt (Word)
open VG.Proof.Scrypt

/-! ## Registers -/

theorem wreg_inj {j k : Nat} (hj : j < 16) (hk : k < 16) (h : wreg j = wreg k) : j = k := by
  have key : ∀ j, j < 16 → ∀ k, k < 16 → wreg j = wreg k → j = k := by decide
  exact key j hj k hk h

theorem wreg_ne_r0 {k : Nat} (hk : k < 16) : wreg k ≠ .r0 := by
  have key : ∀ k < 16, wreg k ≠ .r0 := by decide
  exact key k hk

/-- The registers that hold words. -/
def Words (r : Reg) : Prop := ∃ k < 16, r = wreg k

theorem not_words_r0 : ¬ Words .r0 := fun ⟨_, hk, h⟩ => wreg_ne_r0 hk h.symm

theorem not_words_r3 : ¬ Words .r3 := fun ⟨k, hk, h⟩ => by
  have key : ∀ k < 16, wreg k ≠ .r3 := by decide
  exact key k hk h.symm

theorem not_words_r4 : ¬ Words .r4 := fun ⟨k, hk, h⟩ => by
  have key : ∀ k < 16, wreg k ≠ .r4 := by decide
  exact key k hk h.symm

theorem saved_words {i : Nat} (hi : i < 8) : Words (saved i) := by
  have key : ∀ i < 8, saved i = wreg (i + 8) := by decide
  exact ⟨i + 8, by omega_arith, key i hi⟩

theorem saved_inj {i j : Nat} (hi : i < 8) (hj : j < 8) (h : saved i = saved j) : i = j := by
  have key : ∀ i < 8, ∀ j < 8, saved i = saved j → i = j := by decide
  exact key i hi j hj h

theorem saved_ne_r4 {i : Nat} (hi : i < 8) : saved i ≠ .r4 := by
  have key : ∀ i < 8, saved i ≠ .r4 := by decide
  exact key i hi

/-- A preserved register is saved, or not a word register (nor `r0`). -/
theorem preserved_cases {r : Reg} (hr : r ∈ preserved) :
    (∃ i < 8, r = saved i) ∨ (¬ Words r ∧ r ≠ .r0) := by
  have key : ∀ r ∈ preserved, (∃ i < 8, r = saved i) ∨ (∀ k < 16, r ≠ wreg k) ∧ r ≠ .r0 := by
    decide
  rcases key r hr with h | ⟨h, h0⟩
  · exact .inl h
  · exact .inr ⟨fun ⟨k, hk, e⟩ => h k hk e, h0⟩

/-! ## One line, on registers -/

/-- `a ^= R(b + c)` through `r0`, rotating right by `sh`, on the low words. -/
theorem line_regs {a b c : Reg} (ha : a ≠ .r0) {sh : Nat} (hsh : sh < 32) (s : State) (va vb vc : Word)
    (hva : (s.gpr a).setWidth 32 = va) (hvb : (s.gpr b).setWidth 32 = vb)
    (hvc : (s.gpr c).setWidth 32 = vc) :
    WP isa (.block [.add .r0 b c, .rotr .w .r0 .r0 sh, .logic .xor a a .r0]) s fun s' =>
      (s'.gpr a).setWidth 32 = va ^^^ (vb + vc).rotateRight sh ∧
      (∀ r, r ≠ a → r ≠ .r0 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_logic, exec_rotr_w hsh, isa,
    State.write, ha, Option.some.injEq, exists_eq_left', ↓reduceIte]
  simp only [lo32_add, BitVec.setWidth_xor, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    hva, hvb, hvc, Nat.reduceLeDiff]
  refine ⟨trivial, fun r h1 h2 => ?_, trivial, trivial, trivial⟩
  simp only [h1, h2, ite_false]

/-! ## Where the words are -/

/-- The words `v` are in the low words of the registers. -/
def Holds (v : Vector Word 16) (s : State) : Prop :=
  ∀ k (hk : k < 16), (s.gpr (wreg k)).setWidth 32 = v[k]

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (v : Vector Word 16) (s₀ s : State) : Prop where
  holds : Holds v s
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → r ≠ .r0 → s.gpr r = s₀.gpr r

/-- The side conditions of `line_ok`, decidable for concrete arguments. -/
def LSide (i j k n : Nat) : Bool :=
  decide (i < 16 ∧ j < 16 ∧ k < 16 ∧ 1 ≤ n ∧ n ≤ 31)

theorem line_ok {i j k n : Nat} (hs : LSide i j k n = true) {v : Vector Word 16} {s₀ s : State}
    (h : RI v s₀ s) : WP isa (.block (line i j k n)) s (RI (stepN v i j k n) s₀) := by
  simp only [LSide, decide_eq_true_eq] at hs
  obtain ⟨hi, hj, hk, h1, h2⟩ := hs
  have ne : ∀ {a b}, a < 16 → b < 16 → a ≠ b → wreg a ≠ wreg b := fun ha hb hab e =>
    hab (wreg_inj ha hb e)
  refine WP.mono (line_regs (wreg_ne_r0 hi) (show 32 - n < 32 by omega_arith) s _ _ _ (h.holds i hi)
    (h.holds j hj) (h.holds k hk)) fun s' ⟨ha, hr, hm, hrd, hwr⟩ =>
    ⟨fun m hm' => ?_, hm.trans h.mem, hrd.trans h.rd, hwr.trans h.wr, fun r hw hx => ?_⟩
  · rw [stepN_get v n hi hj hk m hm']
    by_cases e : i = m
    · subst e
      simp only [ite_true]
      rw [ha, rotateLeft_eq _ (by omega_arith) (by omega_arith)]
    · simp only [e, ite_false]
      rw [hr _ (ne hm' hi (Ne.symm e)) (wreg_ne_r0 hm')]
      exact h.holds m hm'
  · rw [hr r (fun e => hw ⟨i, hi, e⟩) hx]
    exact h.keep r hw hx

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
  | 0 => WP.block_nil ⟨h, rfl, rfl, rfl, fun _ _ _ => rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds_ok h n) fun _ h' => doubleRound_ok h')

end VG.Proof.Scrypt.PPC64LE

namespace VG.Proof.Scrypt

open Spec.Scrypt

open VG.PPC64LE in
/-- PPC64LE contract for `vg_salsa20_8(b: *mut [u8; 64], scratch: *mut [u32;
16])`: replaces the 64 bytes at `b` by their Salsa20/8 Core.

The code may read and write `b` and `scratch` (64 bytes each; the contents of
`scratch` on exit are unspecified), which may not overlap. The pointers are
public; the data is secret. -/
def salsaPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let b : Region := ⟨s.gpr .r3, 64⟩
    let scratch : Region := ⟨s.gpr .r4, 64⟩
    s.rd = [] ∧ s.wr = [b, scratch] ∧ b.Disjoint scratch
  post s s' := bytesAt s'.mem (s.gpr .r3) 64 = salsa (bytesAt s.mem (s.gpr .r3) 64)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.sp = s₂.sp

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.PPC64LE

open VG VG.PPC64LE VG.Impl.Scrypt.PPC64LE
open VG.Spec.Scrypt (Word)
open VG.Proof.Scrypt

/-! ## The precondition -/

section
variable (s₀ : State)
/-- `b`. -/
abbrev bp : Addr := s₀.gpr .r3
/-- `scratch`. -/
abbrev sp' : Addr := s₀.gpr .r4
abbrev bR : Region := ⟨bp s₀, 64⟩
abbrev sR : Region := ⟨sp' s₀, 64⟩
/-- The input words. -/
def V : Vector Word 16 := Vector.ofFn fun j => s₀.mem.readW (bp s₀ + BitVec.ofNat 64 (4 * j.1)) 32
/-- The result of the rounds. -/
abbrev Rs : Vector Word 16 := Nat.repeat Spec.Scrypt.doubleRound 4 (V s₀)
end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [bR s₀, sR s₀]
  disj : (bR s₀).Disjoint (sR s₀)

theorem pre_of (s₀ : State) (h : Proof.Scrypt.salsaPPC64LE.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem V_get (s₀ : State) {k : Nat} (hk : k < 16) :
    (V s₀)[k] = s₀.mem.readW (bp s₀ + BitVec.ofNat 64 (4 * k)) 32 := by
  simp only [V, Vector.getElem_ofFn]

theorem contains_off {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem in_b {k : Nat} (hk : k < 16) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (bp s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨bR s₀, by simp [hp.wr], contains_off (by omega_arith) (by omega_arith)⟩

theorem out_b {k : Nat} (hk : k < 16) : InRegions s₀.wr (bp s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨bR s₀, by simp [hp.wr], contains_off (by omega_arith) (by omega_arith)⟩

theorem in_sav {i : Nat} (hi : i < 8) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (sp' s₀ + BitVec.ofNat 64 (8 * i)) 8 :=
  ⟨sR s₀, by simp [hp.wr], contains_off (by omega_arith) (by omega_arith)⟩

theorem out_sav {i : Nat} (hi : i < 8) : InRegions s₀.wr (sp' s₀ + BitVec.ofNat 64 (8 * i)) 8 :=
  ⟨sR s₀, by simp [hp.wr], contains_off (by omega_arith) (by omega_arith)⟩

end Pre

theorem readW_writeW_word (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 16) (hk : k < 16)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofNat 64 (4 * k)) v).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
      m.readW (p + BitVec.ofNat 64 (4 * j)) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)

theorem sav_sep (p : Addr) {i j : Nat} (hi : i < 8) (hj : j < 8) (h : i ≠ j) :
    Mem.Sep (p + BitVec.ofNat 64 (8 * i)) 8 (p + BitVec.ofNat 64 (8 * j)) 8 :=
  Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)

/-! ## Saving the nonvolatile registers -/

/-- The first `n` registers are saved. -/
structure SI (s₀ : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [sR s₀] s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (sp' s₀ + BitVec.ofNat 64 (8 * i)) 64 = s₀.gpr (saved i)

theorem save_step {s₀ : State} (hp : Pre s₀) {n : Nat} (hn : n < 8) {s : State} (h : SI s₀ n s) :
    WP isa (.block [.store .d (saved n) .r4 (8 * n)]) s (SI s₀ (n + 1)) := by
  have hr4 : s.gpr .r4 = sp' s₀ := by rw [h.gpr]
  have hout : InRegions s.wr (s.gpr .r4 + BitVec.ofNat 64 (8 * n)) 8 := by
    rw [h.wr, hr4]; exact hp.out_sav hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (by decide) (show 8 * n < 2 ^ 15 ∧ (8 * n) % 4 = 0 by omega_arith) hout,
    Option.some.injEq, exists_eq_left', hr4]
  refine ⟨h.gpr, h.rd, h.wr, h.frame.writeW (List.mem_singleton_self _) _
    (contains_off (by omega_arith) (by omega_arith)), fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · rw [Mem.readW_writeW_sep (sav_sep _ (by omega_arith) hn (by omega_arith)) (by decide)]
    exact h.saved i hi
  · rw [Mem.readW_writeW_self64, h.gpr]

/-! ## Loading the input -/

/-- After loading `n` words. -/
structure LI (s₀ : State) (n : Nat) (s : State) : Prop where
  loaded : ∀ j (hj : j < 16), j < n → (s.gpr (wreg j)).setWidth 32 = (V s₀)[j]
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r

theorem load_step {s₀ : State} (hp : Pre s₀) {n : Nat} (hn : n < 16) {s : State} (h : LI s₀ n s) :
    WP isa (.block [.load .w (wreg n) .r3 (4 * n)]) s (LI s₀ (n + 1)) := by
  have hr3 : s.gpr .r3 = bp s₀ := h.keep _ not_words_r3
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (4 * n)) 4 := by
    rw [h.rd, h.wr, hr3]; exact hp.in_b hn _
  have hv : s.mem.readW (bp s₀ + BitVec.ofNat 64 (4 * n)) 32 = (V s₀)[n] := by
    rw [h.mem, V_get _ hn]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_w (by decide) (show 4 * n < 2 ^ 15 by omega_arith) hin, isa,
    Option.some.injEq, exists_eq_left', hr3, hv]
  refine ⟨fun j hj hjn => ?_, h.mem, h.rd, h.wr, fun r hr => ?_⟩
  · simp only [State.write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · have e : wreg j ≠ wreg n := fun e => absurd (wreg_inj hj hn e) (by omega_arith)
      simp only [e, ite_false]; exact h.loaded j hj hjn
    · simp
  · have e : r ≠ wreg n := fun e => hr ⟨n, hn, e⟩
    simp only [State.write, e, ite_false]; exact h.keep r hr

/-! ## Adding the input -/

/-- After finishing words `0 … i - 1`: those words of `b` hold the sums, the
others still hold the input, and words `i … 15` of the rounds' result `R` are
still in their registers. -/
structure FI (s₀ : State) (R : Vector Word 16) (i : Nat) (s : State) : Prop where
  out : ∀ j (hj : j < 16), s.mem.readW (bp s₀ + BitVec.ofNat 64 (4 * j)) 32 =
    if j < i then R[j] + (V s₀)[j] else (V s₀)[j]
  rest : ∀ j (hj : j < 16), i ≤ j → (s.gpr (wreg j)).setWidth 32 = R[j]
  frame : Frame [bR s₀] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → r ≠ .r0 → s.gpr r = s₀.gpr r

theorem finish_step {s₀ : State} (hp : Pre s₀) {R : Vector Word 16} {i : Nat} (hi : i < 16)
    {s : State} (h : FI s₀ R i s) : WP isa (.block (finishWord i)) s (FI s₀ R (i + 1)) := by
  have hr3 : s.gpr .r3 = bp s₀ := h.keep _ not_words_r3 (by decide)
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [h.rd, h.wr, hr3]; exact hp.in_b hi _
  have hout : InRegions s.wr (s.gpr .r3 + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [h.wr, hr3]; exact hp.out_b hi
  have hv : s.mem.readW (bp s₀ + BitVec.ofNat 64 (4 * i)) 32 = (V s₀)[i] := by
    rw [h.out i hi, ite_eq_right_iff.mpr fun h => absurd h (Nat.lt_irrefl i)]
  have hr := h.rest i hi (Nat.le_refl i)
  have hne : wreg i ≠ .r0 := wreg_ne_r0 hi
  have n3 : Reg.r3 ≠ wreg i := fun e => not_words_r3 ⟨i, hi, e⟩
  have n30 : Reg.r3 ≠ .r0 := by decide
  apply WP.of_runBlock
  simp only [finishWord, runBlock_cons, runStep_some,
    exec_load_w (by decide) (show 4 * i < 2 ^ 15 by omega_arith) hin, exec_add, isa, hr3, hv]
  simp only [State.write, hne, ite_false, ite_true]
  rw [exec_store_w (by decide) (show 4 * i < 2 ^ 15 by omega_arith)
    (by simpa [State.write, hne, n3, n30] using hout)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left', ite_true, ite_false,
    hr3, n3, n30]
  refine ⟨fun j hj => ?_, fun j hj hij => ?_,
    h.frame.writeW (List.mem_singleton_self _) _ (contains_off (by omega_arith) (by omega_arith)),
    h.rd, h.wr, fun r hw hx => ?_⟩
  · by_cases e : j = i
    · subst e
      rw [Mem.readW_writeW_self32, lo32_add, hr, lo32_ext,
        ite_eq_left_iff.mpr fun h => absurd (Nat.lt_succ_self j) h]
    · rw [readW_writeW_word _ _ _ hj hi e, h.out j hj]
      by_cases hji : j < i
      · rw [ite_eq_left_iff.mpr fun h => absurd hji h, ite_eq_left_iff.mpr fun h => absurd (by omega_arith) h]
      · rw [ite_eq_right_iff.mpr fun h => absurd h hji, ite_eq_right_iff.mpr fun h => absurd h (by omega_arith)]
  · have e1 : wreg j ≠ wreg i := fun e => absurd (wreg_inj hj hi e) (by omega_arith)
    have e2 : wreg j ≠ .r0 := wreg_ne_r0 hj
    simp only [e1, e2, ite_false]; exact h.rest j hj (by omega_arith)
  · have e1 : r ≠ wreg i := fun e => hw ⟨i, hi, e⟩
    simp only [e1, hx, ite_false]; exact h.keep r hw hx

/-! ## Restoring the nonvolatile registers -/

/-- The first `n` registers are restored, from the state `sB` the restoring
starts in. -/
structure RI' (s₀ sB : State) (n : Nat) (s : State) : Prop where
  restored : ∀ i < n, s.gpr (saved i) = s₀.gpr (saved i)
  others : ∀ r, (∀ i < 8, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem restore_step {s₀ sB : State} (hp : Pre s₀) (hr4 : sB.gpr .r4 = sp' s₀)
    (hsav : ∀ i < 8, sB.mem.readW (sp' s₀ + BitVec.ofNat 64 (8 * i)) 64 = s₀.gpr (saved i))
    {n : Nat} (hn : n < 8) {s : State} (h : RI' s₀ sB n s) :
    WP isa (.block [.load .d (saved n) .r4 (8 * n)]) s (RI' s₀ sB (n + 1)) := by
  have hr4' : s.gpr .r4 = sp' s₀ := by
    rw [h.others _ fun i hi e => saved_ne_r4 hi e.symm, hr4]
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r4 + BitVec.ofNat 64 (8 * n)) 8 := by
    rw [h.rd, h.wr, hr4']; exact hp.in_sav hn _
  have hv : s.mem.readW (sp' s₀ + BitVec.ofNat 64 (8 * n)) 64 = s₀.gpr (saved n) := by
    rw [h.mem]; exact hsav n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (by decide) (show 8 * n < 2 ^ 15 ∧ (8 * n) % 4 = 0 by omega_arith) hin,
    Option.some.injEq, exists_eq_left', hr4', hv]
  refine ⟨fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr⟩
  · simp only [State.write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : saved i ≠ saved n := fun e => absurd (saved_inj (by omega_arith) hn e) (by omega_arith)
      simp only [e, ite_false]; exact h.restored i hi
    · simp
  · simp only [State.write, hr n hn, ite_false]; exact h.others r hr

/-! ## The whole function -/

/-- The input words are those the specification reads from the bytes. -/
theorem input_eq (s₀ : State) :
    (Vector.ofFn fun j : Fin 16 => Spec.Scrypt.wordLE (Spec.Scrypt.bytesAt s₀.mem (bp s₀) 64) j.1) =
      V s₀ := by
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_ofFn, V_get _ hj, wordLE_bytesAt _ _ (by omega_arith)]

/-- The result words are where the specification writes its bytes. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ j (hj : j < 16), m.readW (bp s₀ + BitVec.ofNat 64 (4 * j)) 32 = (Rs s₀)[j] + (V s₀)[j]) :
    Spec.Scrypt.bytesAt m (bp s₀) 64 = Spec.Scrypt.salsa (Spec.Scrypt.bytesAt s₀.mem (bp s₀) 64) := by
  rw [Spec.Scrypt.salsa, input_eq]
  refine bytesAt_eq_serialize _ _ _ fun j hj => ?_
  rw [Spec.Scrypt.core, Vector.getElem_zipWith, ← h j hj]

/-- The main part, from the state `s₁` after saving the registers. -/
theorem main_ok {s₁ : State} (hp : Pre s₁) :
    WP isa main s₁ fun s' =>
      (∀ j (hj : j < 16), s'.mem.readW (bp s₁ + BitVec.ofNat 64 (4 * j)) 32 = (Rs s₁)[j] + (V s₁)[j]) ∧
      Frame [bR s₁] s₁.mem s'.mem ∧ s'.rd = s₁.rd ∧ s'.wr = s₁.wr ∧
      (∀ r, ¬ Words r → r ≠ .r0 → s'.gpr r = s₁.gpr r) := by
  have hl₀ : LI s₁ 0 s₁ := ⟨fun _ _ h => absurd h (by omega_arith), rfl, rfl, rfl, fun _ _ => rfl⟩
  have hload : WP isa (.block load) s₁ (LI s₁ 16) := by
    unfold load
    exact wp_range_flatMap (M := isa) (LI s₁) (fun k s hk h => load_step hp hk h) 16 (Nat.le_refl _) s₁ hl₀
  refine WP.seq (WP.mono hload fun s₂ h₂ => ?_)
  have hh₂ : Holds (V s₁) s₂ := fun k hk => h₂.loaded k hk hk
  refine WP.seq (WP.mono (rounds_ok hh₂ 4) fun s₃ h₃ => ?_)
  have hf₃ : FI s₁ (Rs s₁) 0 s₃ :=
    ⟨fun j hj => by
        rw [ite_eq_right_iff.mpr fun h => absurd h (Nat.not_lt_zero j), h₃.mem, h₂.mem, V_get _ hj],
      fun j hj _ => h₃.holds j hj, by rw [h₃.mem, h₂.mem]; exact Frame.refl _ _,
      h₃.rd.trans h₂.rd, h₃.wr.trans h₂.wr,
      fun r hw hx => (h₃.keep r hw hx).trans (h₂.keep r hw)⟩
  unfold finish
  exact WP.mono (wp_range_flatMap (M := isa) (FI s₁ (Rs s₁)) (fun i s hi h => finish_step hp hi h) 16
    (Nat.le_refl _) s₃ hf₃) fun s' h => ⟨fun j hj => by rw [h.out j hj, ite_eq_left_iff.mpr fun e => absurd hj e],
      h.frame, h.rd, h.wr, h.keep⟩

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa salsa s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Scrypt.salsaPPC64LE.post s₀ s' := by
  have hs₀ : SI s₀ 0 s₀ := ⟨rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega_arith)⟩
  have hsave : WP isa (.block save) s₀ (SI s₀ 8) := by
    unfold save
    exact wp_range_flatMap (M := isa) (SI s₀) (fun k s hk h => save_step hp hk h) 8 (Nat.le_refl _) s₀ hs₀
  refine WP.seq (WP.mono hsave fun s₁ h₁ => ?_)
  have hb : bp s₁ = bp s₀ := by simp only [bp, h₁.gpr]
  have hs : sp' s₁ = sp' s₀ := by simp only [sp', h₁.gpr]
  have hp₁ : Pre s₁ := ⟨by rw [h₁.rd, hp.rd], by rw [h₁.wr, hp.wr, bR, bR, sR, sR, hb, hs],
    by simpa only [bR, sR, hb, hs] using hp.disj⟩
  have hV : V s₁ = V s₀ := by
    apply Vector.ext
    intro j hj
    rw [V_get _ hj, V_get _ hj, hb]
    exact h₁.frame.readW (r := bR s₀) (contains_off (by omega_arith) (by omega_arith))
      (by simpa using hp.disj) (by decide)
  refine WP.seq (WP.mono (main_ok hp₁) fun s₃ ⟨hout, hf, hrd, hwr, hk⟩ => ?_)
  have hr4 : s₃.gpr .r4 = sp' s₀ := by rw [hk _ not_words_r4 (by decide), h₁.gpr]
  have hsav : ∀ i < 8, s₃.mem.readW (sp' s₀ + BitVec.ofNat 64 (8 * i)) 64 = s₀.gpr (saved i) :=
    fun i hi => by
      rw [hf.readW (r := sR s₀) (contains_off (by omega_arith) (by omega_arith))
        (by simpa [bR, hb] using hp.disj.symm) (by decide)]
      exact h₁.saved i hi
  have hr₀ : RI' s₀ s₃ 0 s₃ :=
    ⟨fun _ h => absurd h (by omega_arith), fun _ _ => rfl, rfl, hrd.trans h₁.rd, hwr.trans h₁.wr⟩
  refine WP.mono (wp_range_flatMap (M := isa) (RI' s₀ s₃)
    (fun k s hk h => restore_step hp hr4 hsav hk h) 8 (Nat.le_refl _) s₃ hr₀) fun s' h => ⟨?_, ?_⟩
  · intro r hr
    rcases preserved_cases hr with ⟨i, hi, rfl⟩ | ⟨hw, h0⟩
    · exact h.restored i hi
    · rw [h.others r fun i hi e => hw (e ▸ saved_words hi), hk r hw h0, h₁.gpr]
  · show Spec.Scrypt.bytesAt s'.mem (bp s₀) 64 = Spec.Scrypt.salsa (Spec.Scrypt.bytesAt s₀.mem (bp s₀) 64)
    rw [h.mem]
    refine post_of fun j hj => ?_
    rw [← hb, hout j hj, Rs, hV]

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩]

theorem salsa_correct (s : State) (hs : Proof.Scrypt.salsaPPC64LE.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.PPC64LE.salsa s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.salsaPPC64LE.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.lr he (by decide +kernel)
    (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, h₂⟩

theorem salsa_ct : ConstantTime isa Proof.Scrypt.salsaPPC64LE.pre Proof.Scrypt.salsaPPC64LE.pub
    Impl.Scrypt.PPC64LE.salsa := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> with_reducible assumption

theorem salsa_verified :
    Verified PPC64LE.target Impl.Scrypt.PPC64LE.salsa (Proof.Scrypt.salsaContract PPC64LE.abi) :=
  Verified.of_correct salsa_correct salsa_ct (by
    sig_implies [Proof.Scrypt.salsaContract, Proof.Scrypt.salsaSig, Proof.Scrypt.salsaPPC64LE,
      PPC64LE.abi, PPC64LE.argRegs] [Proof.Scrypt.PPC64LE.satState] using
      Proof.Scrypt.PPC64LE.satState)

end VG.Proof.Scrypt.PPC64LE
