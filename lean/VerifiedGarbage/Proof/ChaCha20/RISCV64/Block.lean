module

public import VerifiedGarbage.Proof.ChaCha20.RISCV64.Rounds
meta import VerifiedGarbage.Proof.ChaCha20.RISCV64.Rounds
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.ChaCha20.RISCV64.Contract
meta import VerifiedGarbage.Proof.ChaCha20.RISCV64.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
meta import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.TCB.RISCV64.Target

/-!
# ChaCha20 block function on RISC-V: the whole function

Untrusted: everything here is checked by Lean. The structure of the PPC64LE
proof (`Proof/ChaCha20/PPC64LE/Block.lean`), with the state read and the
result written a word at a time (`lwu`, `sw`: both are 4-byte aligned),
and the callee-saved registers saved at `buf + 64` rounded up to a multiple
of 8 (`Proof/Framework/RISCV64/Align.lean`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.RISCV64

open VG VG.RISCV64 VG.RISCV64.ByteLoad VG.RISCV64.Align VG.Impl.ChaCha20.RISCV64
  VG.Impl.Words.RISCV64 VG.Proof.ChaCha20
open VG.Spec.ChaCha20 (Word stateAt innerBlock)

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev st : Addr := s₀.gpr .a0
abbrev buf : Addr := s₀.gpr .a1
abbrev stR : Region := ⟨st s₀, 64⟩
abbrev bufR : Region := ⟨buf s₀, 256⟩
abbrev outR : Region := ⟨buf s₀, 64⟩
/-- How far `buf + 64` is below a multiple of 8. -/
abbrev q : Nat := pad (buf s₀ + BitVec.ofNat 64 64)
/-- Where the callee-saved registers are saved: `buf + 64`, rounded up. -/
abbrev sv : Addr := buf s₀ + BitVec.ofNat 64 64 + BitVec.ofNat 64 (q s₀)
abbrev savR : Region := ⟨buf s₀ + BitVec.ofNat 64 (64 + q s₀), 40⟩
/-- The input state. -/
abbrev V : CState := stateAt s₀.mem (st s₀)
/-- The result of the rounds. -/
abbrev Rs : CState := Nat.repeat innerBlock 10 (V s₀)
end

theorem q_lt (s₀ : State) : q s₀ < 8 := pad_lt _

theorem sv_add (s₀ : State) (d : Nat) :
    sv s₀ + BitVec.ofNat 64 d = buf s₀ + BitVec.ofNat 64 (64 + q s₀ + d) := align_add _ _ _

theorem sv_al (s₀ : State) {d : Nat} (hd : d % 8 = 0) : (sv s₀ + BitVec.ofNat 64 d).toNat % 8 = 0 :=
  align_al_add _ hd

theorem savR_sub (s₀ : State) : Region.Sub (savR s₀) (bufR s₀) :=
  Offset.sub_base _ (by have := q_lt s₀; omega)

theorem outR_sav (s₀ : State) : (outR s₀).Disjoint (savR s₀) :=
  Offset.base_disjoint _ (by omega) (by have := q_lt s₀; omega)

theorem sav_contains (s₀ : State) {i : Nat} (hi : i < 5) :
    (savR s₀).Contains (sv s₀ + BitVec.ofNat 64 (8 * i)) 8 := by
  have := q_lt s₀
  rw [sv_add]
  exact Offset.contains _ (by omega) (by omega) (by omega)

theorem outR_sub (s₀ : State) : Region.Sub (outR s₀) (bufR s₀) := Region.sub_prefix (by omega)

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [stR s₀]
  wr : s₀.wr = [bufR s₀]
  buf_st : (bufR s₀).Disjoint (stR s₀)
  st_al : (st s₀).toNat % 4 = 0
  buf_al : (buf s₀).toNat % 4 = 0

theorem pre_of (s₀ : State) (h : Proof.ChaCha20.blockRISCV64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Word `k` of a 4-byte aligned pointer is 4-byte aligned. -/
theorem al4 {p : Addr} (h : p.toNat % 4 = 0) (k : Nat) : (p + BitVec.ofNat 64 (4 * k)).toNat % 4 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := p.isLt
  omega

/-- `lwu d, off(n)`. -/
theorem loadW_ok {s : State} {d n : Reg} {off : Nat} (ho : off < 2048)
    (ha : (s.gpr n + BitVec.ofNat 64 off).toNat % 4 = 0)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 4) :
    WP isa (.block [.load .w d n off]) s
      (· = s.write d ((s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 32).setWidth 64)) := by
  apply WP.of_runBlock
  rw [runBlock_cons, exec_load_w ho ha h, runStep_some, runBlock_nil]
  exact ⟨_, rfl, rfl⟩

/-- `sw v, off(n)`. -/
theorem storeW_ok {s : State} {v n : Reg} {off : Nat} (ho : off < 2048)
    (ha : (s.gpr n + BitVec.ofNat 64 off).toNat % 4 = 0)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 4) :
    WP isa (.block [.store .w v n off]) s
      (· = { s with mem := s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) ((s.gpr v).setWidth 32) }) := by
  apply WP.of_runBlock
  rw [runBlock_cons, exec_store_w ho ha h, runStep_some, runBlock_nil]
  exact ⟨_, rfl, rfl⟩

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem in_st {k : Nat} (hk : k < 16) (ws : List Region) :
    InRegions (s₀.rd ++ ws) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [hp.rd], Offset.contains_base _ (by omega) (by omega)⟩

theorem out_out {k : Nat} (hk : k < 16) : InRegions s₀.wr (buf s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨bufR s₀, by simp [hp.wr], Offset.contains_base _ (by omega) (by omega)⟩

theorem in_sav {i : Nat} (hi : i < 5) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (sv s₀ + BitVec.ofNat 64 (8 * i)) 8 :=
  ⟨bufR s₀, by simp [hp.wr], by
    rw [sv_add]; exact Offset.contains_base _ (by have := q_lt s₀; omega) (by have := q_lt s₀; omega)⟩

theorem out_sav {i : Nat} (hi : i < 5) : InRegions s₀.wr (sv s₀ + BitVec.ofNat 64 (8 * i)) 8 := by
  simpa using hp.in_sav hi []

/-- Reading the input state after writes to `buf` only. -/
theorem read_st {m : Mem} (hf : Frame [bufR s₀] s₀.mem m) {k : Nat} (hk : k < 16) :
    m.readW (st s₀ + BitVec.ofNat 64 (4 * k)) 32 = (V s₀)[k] := by
  rw [hf.readW (r := stR s₀) (Offset.contains_base _ (by omega) (by omega))
    (by simpa using hp.buf_st.symm) (by decide)]
  simp only [V, stateAt, Vector.getElem_ofFn]

end Pre

theorem readW_writeW_out (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 16) (hk : k < 16)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofNat 64 (4 * k)) v).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
      m.readW (p + BitVec.ofNat 64 (4 * j)) 32 :=
  Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

theorem readW_writeW_sav (m : Mem) (p : Addr) (v : BitVec 64) {i j : Nat} (hi : i < 5) (hj : j < 5)
    (h : i ≠ j) :
    (m.writeW (p + BitVec.ofNat 64 (8 * j)) v).readW (p + BitVec.ofNat 64 (8 * i)) 64 =
      m.readW (p + BitVec.ofNat 64 (8 * i)) 64 :=
  Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

/-! ## Registers -/

theorem wreg_ne {k : Nat} (hk : k < 16) : wreg k ≠ .a0 ∧ wreg k ≠ .a1 ∧ wreg k ≠ U ∧ wreg k ≠ .ra := by
  have key : ∀ k < 16, wreg k ≠ .a0 ∧ wreg k ≠ .a1 ∧ wreg k ≠ U ∧ wreg k ≠ .ra := by decide
  exact key k hk

theorem not_words {r : Reg} (h : ∀ k < 16, r ≠ wreg k) (hT : r ≠ T) : ¬ Words r := by
  rintro (⟨k, hk, e⟩ | e)
  exacts [h k hk e, hT e]

theorem not_words_a0 : ¬ Words .a0 := not_words (fun _ hk e => (wreg_ne hk).1 e.symm) (by decide)
theorem not_words_a1 : ¬ Words .a1 := not_words (fun _ hk e => (wreg_ne hk).2.1 e.symm) (by decide)
theorem not_words_U : ¬ Words U := not_words (fun _ hk e => (wreg_ne hk).2.2.1 e.symm) (by decide)
theorem not_words_ra : ¬ Words .ra := not_words (fun _ hk e => (wreg_ne hk).2.2.2 e.symm) (by decide)

theorem t0_words : Words .t0 := .inl ⟨0, by decide, rfl⟩

theorem saved_inj {i j : Nat} (hi : i < 5) (hj : j < 5) (h : saved i = saved j) : i = j := by
  have key : ∀ i < 5, ∀ j < 5, saved i = saved j → i = j := by decide
  exact key i hi j hj h

theorem saved_ne {i : Nat} (hi : i < 5) : saved i ≠ .t0 ∧ saved i ≠ .a1 := by
  have key : ∀ i < 5, saved i ≠ .t0 ∧ saved i ≠ .a1 := by decide
  exact key i hi

/-- A preserved register is saved, or neither a word register, the
temporary `U` nor `t0`. -/
theorem preserved_cases {r : Reg} (hr : r ∈ preserved) :
    (∃ i < 5, r = saved i) ∨ (¬ Words r ∧ r ≠ U) := by
  have key : ∀ r ∈ preserved, (∃ i < 5, r = saved i) ∨ ((∀ k < 16, r ≠ wreg k) ∧ r ≠ T ∧ r ≠ U) := by
    decide
  rcases key r hr with h | ⟨h, hT, hU⟩
  · exact .inl h
  · exact .inr ⟨not_words h hT, hU⟩

/-! ## Saving the callee-saved registers -/

theorem savePtr_ok {s : State} (h : s.gpr .a1 = buf s) :
    WP isa (.block savePtr) s (· = s.write .t0 (sv s)) := by
  apply WP.of_runBlock
  simp only [savePtr, runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 71 by decide),
    exec_logicImm (show imm12 (-8) by decide), RegUpd.gpr_write_self, RegUpd.write_write,
    Option.some.injEq, exists_eq_left', h]
  rw [align_off_eq _ (off := 64) (by decide) (by decide)]

/-- The first `n` registers are saved. -/
structure SI (s₀ : State) (n : Nat) (s : State) : Prop where
  t0 : s.gpr .t0 = sv s₀
  gpr : ∀ r, r ≠ .t0 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [savR s₀] s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (sv s₀ + BitVec.ofNat 64 (8 * i)) 64 = s₀.gpr (saved i)

theorem save_step {s₀ : State} (hp : Pre s₀) {n : Nat} (hn : n < 5) {s : State} (h : SI s₀ n s) :
    WP isa (.block [.store .d (saved n) .t0 (8 * n)]) s (SI s₀ (n + 1)) := by
  apply WP.of_runBlock
  rw [runBlock_cons, exec_store_d (by omega) (by rw [h.t0]; exact sv_al _ (by omega))
    (by rw [h.wr, h.t0]; exact hp.out_sav hn), runStep_some, runBlock_nil]
  refine ⟨_, rfl, h.t0, h.gpr, h.rd, h.wr, h.frame.writeW (List.mem_singleton_self _) _ ?_,
    fun i hi => ?_⟩
  · rw [h.t0]; exact sav_contains s₀ hn
  · simp only [h.t0]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [readW_writeW_sav _ _ _ (by omega) hn (by omega)]
      exact h.saved i hi
    · rw [Mem.readW_writeW_self64, h.gpr _ (saved_ne hn).1]

theorem save_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block save) s₀ (SI s₀ 5) := by
  rw [save, WP.block_append_iff]
  refine WP.mono (savePtr_ok rfl) fun s₁ e => ?_
  subst e
  exact wp_range_flatMap (M := isa) (SI s₀) (fun k s hk h => save_step hp hk h) 5 (Nat.le_refl _) _
    ⟨RegUpd.gpr_write_self _ _ _, fun r h => RegUpd.gpr_write_of_ne _ _ h, rfl, rfl,
      Frame.refl _ _, fun _ h => absurd h (by omega)⟩

/-! ## Loading the state -/

/-- After loading `n` words. -/
structure LI (s₀ : State) (n : Nat) (s : State) : Prop where
  loaded : ∀ j (hj : j < 16), j < n → lo (s.gpr (wreg j)) = (V s₀)[j]
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r

theorem load_step {s₀ : State} (hp : Pre s₀) {n : Nat} (hn : n < 16) {s : State} (h : LI s₀ n s) :
    WP isa (.block [.load .w (wreg n) .a0 (4 * n)]) s (LI s₀ (n + 1)) := by
  have hr0 : s.gpr .a0 = st s₀ := h.keep _ not_words_a0
  refine WP.mono (loadW_ok (by omega) (by rw [hr0]; exact al4 hp.st_al n)
    (by rw [h.rd, h.wr, hr0]; exact hp.in_st hn _)) fun s' e => ?_
  subst e
  have hv : s.mem.readW (st s₀ + BitVec.ofNat 64 (4 * n)) 32 = (V s₀)[n] := by
    rw [h.mem]; exact hp.read_st (Frame.refl _ _) hn
  refine ⟨fun j hj hjn => ?_, h.mem, h.rd, h.wr, fun r hr => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · rw [RegUpd.gpr_write_of_ne _ _ (fun e => absurd (wreg_inj hj hn e) (by omega))]
      exact h.loaded j hj hjn
    · dsimp only [lo]
      rw [RegUpd.gpr_write_self, lo32_ext, hr0, hv]
  · rw [RegUpd.gpr_write_of_ne _ _ (fun e => hr (.inl ⟨n, hn, e⟩))]
    exact h.keep r hr

/-! ## Adding the input state -/

/-- After finishing words `0 … i - 1`: they are in the output, and words
`i … 15` of the rounds' result `R` are still in their registers. -/
structure FI (s₀ : State) (R : CState) (i : Nat) (s : State) : Prop where
  done : ∀ j (hj : j < 16), j < i →
    s.mem.readW (buf s₀ + BitVec.ofNat 64 (4 * j)) 32 = R[j] + (V s₀)[j]
  rest : ∀ j (hj : j < 16), i ≤ j → lo (s.gpr (wreg j)) = R[j]
  frame : Frame [outR s₀] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → r ≠ U → s.gpr r = s₀.gpr r

theorem add_step {s₀ : State} (hp : Pre s₀) {R : CState} {i : Nat} (hi : i < 16)
    {s : State} (h : FI s₀ R i s) :
    WP isa (.block (addWord i)) s (FI s₀ R (i + 1)) := by
  have hr0 : s.gpr .a0 = st s₀ := h.keep _ not_words_a0 (by decide)
  have hr1 : s.gpr .a1 = buf s₀ := h.keep _ not_words_a1 (by decide)
  have hne := wreg_ne hi
  have hv := hp.read_st (h.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨bufR s₀, List.mem_singleton_self _, outR_sub s₀⟩) hi
  unfold addWord
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadW_ok (by omega) (by rw [hr0]; exact al4 hp.st_al i)
    (by rw [h.rd, h.wr, hr0]; exact hp.in_st hi _)) fun s₁ e₁ => ?_
  have g₁ : ∀ r, r ≠ T → r ≠ U → s₁.gpr r = s.gpr r := fun r h₁ _ => by
    rw [e₁, RegUpd.gpr_write_of_ne _ _ h₁]
  have t₁ : lo (s₁.gpr T) = (V s₀)[i] := by
    dsimp only [lo]
    rw [e₁, RegUpd.gpr_write_self, lo32_ext, hr0, hv]
  have m₁ : s₁.mem = s.mem := by rw [e₁]; rfl
  have rd₁ : s₁.rd = s.rd := by rw [e₁]; rfl
  have wr₁ : s₁.wr = s.wr := by rw [e₁]; rfl
  rw [List.singleton_append]
  refine Steps.wp_add fun s₂ u₂ => ?_
  have g₂ : ∀ r, r ≠ wreg i → r ≠ T → r ≠ U → s₂.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by
    rw [u₂.other r h₁, g₁ r h₂ h₃]
  have hw : lo (s₂.gpr (wreg i)) = R[i] + (V s₀)[i] := by
    rw [u₂.gpr]
    have hr := h.rest i hi (Nat.le_refl _)
    dsimp only [lo] at t₁ hr ⊢
    rw [lo32_add, t₁, g₁ _ (wreg_ne_T hi) hne.2.2.1, hr]
  have hr1₂ : s₂.gpr .a1 = buf s₀ := by
    rw [g₂ _ (fun e => hne.2.1 e.symm) (by decide) (by decide), hr1]
  have ho : (outR s₀).Contains (buf s₀ + BitVec.ofNat 64 (4 * i)) 4 :=
    Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (storeW_ok (by omega) (by rw [hr1₂]; exact al4 hp.buf_al i)
    (by rw [hr1₂, u₂.wr, wr₁, h.wr]; exact hp.out_out hi)) fun s' e => ?_
  subst e
  have hm : s₂.mem.writeW (s₂.gpr .a1 + BitVec.ofNat 64 (4 * i)) ((s₂.gpr (wreg i)).setWidth 32) =
      s.mem.writeW (buf s₀ + BitVec.ofNat 64 (4 * i)) (lo (s₂.gpr (wreg i))) := by
    rw [hr1₂, u₂.mem, m₁]
  refine ⟨fun j hj hji => ?_, fun j hj hij => ?_, ?_, by simp only [u₂.rd, rd₁, h.rd],
    by simp only [u₂.wr, wr₁, h.wr], fun r hr' hU => ?_⟩
  · simp only [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hji with hji | rfl
    · rw [readW_writeW_out _ _ _ hj hi (by omega)]; exact h.done j hj hji
    · rw [Mem.readW_writeW_self32, hw]
  · rw [g₂ _ (fun e => absurd (wreg_inj hj hi e) (by omega)) (wreg_ne_T hj) (wreg_ne hj).2.2.1]
    exact h.rest j hj (by omega)
  · simp only [hm]; exact h.frame.writeW (List.mem_singleton_self _) _ ho
  · show s₂.gpr r = _
    rw [g₂ r (fun e => hr' (.inl ⟨i, hi, e⟩)) (fun e => hr' (.inr e)) hU]
    exact h.keep r hr' hU

/-! ## Restoring the callee-saved registers -/

/-- The first `n` registers are restored, from the state `sB` the
restoring starts in (`t0` pointing at them). -/
structure RI' (s₀ sB : State) (n : Nat) (s : State) : Prop where
  t0 : s.gpr .t0 = sv s₀
  restored : ∀ i < n, s.gpr (saved i) = s₀.gpr (saved i)
  others : ∀ r, r ≠ .t0 → (∀ i < 5, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem restore_step {s₀ sB : State} (hp : Pre s₀)
    (hsav : ∀ i < 5, sB.mem.readW (sv s₀ + BitVec.ofNat 64 (8 * i)) 64 = s₀.gpr (saved i))
    {n : Nat} (hn : n < 5) {s : State} (h : RI' s₀ sB n s) :
    WP isa (.block [.load .d (saved n) .t0 (8 * n)]) s (RI' s₀ sB (n + 1)) := by
  apply WP.of_runBlock
  rw [runBlock_cons, exec_load_d (by omega) (by rw [h.t0]; exact sv_al _ (by omega))
    (by rw [h.rd, h.wr, h.t0]; exact hp.in_sav hn _), runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, fun i hi => ?_, fun r h₁ h₂ => ?_, h.mem, h.rd, h.wr⟩
  · rw [RegUpd.gpr_write_of_ne _ _ (saved_ne hn).1.symm, h.t0]
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [RegUpd.gpr_write_of_ne _ _ fun e => absurd (saved_inj (by omega) hn e) (by omega)]
      exact h.restored i hi
    · rw [RegUpd.gpr_write_self, h.t0, h.mem, hsav i hn]
  · rw [RegUpd.gpr_write_of_ne _ _ (h₂ n hn)]; exact h.others r h₁ h₂

/-! ## The whole function -/

theorem block_post {p : Addr} {m : Mem} {R v : CState}
    (h : ∀ j (hj : j < 16), m.readW (p + BitVec.ofNat 64 (4 * j)) 32 = R[j] + v[j]) :
    stateAt m p = Vector.zipWith (· + ·) R v := by
  apply Vector.ext
  intro j hj
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_zipWith]
  exact h j hj

/-- The main part, from the state `s₁` after saving the registers. -/
theorem main_ok {s₁ : State} (hp : Pre s₁) :
    WP isa main s₁ fun s' =>
      (∀ j (hj : j < 16),
        s'.mem.readW (buf s₁ + BitVec.ofNat 64 (4 * j)) 32 = (Rs s₁)[j] + (V s₁)[j]) ∧
      Frame [outR s₁] s₁.mem s'.mem ∧ s'.rd = s₁.rd ∧ s'.wr = s₁.wr ∧
      (∀ r, ¬ Words r → r ≠ U → s'.gpr r = s₁.gpr r) := by
  have hl₀ : LI s₁ 0 s₁ := ⟨fun _ _ h => absurd h (by omega), rfl, rfl, rfl, fun _ _ => rfl⟩
  have hload : WP isa (.block load) s₁ (LI s₁ 16) := by
    unfold load
    exact wp_range_flatMap (M := isa) (LI s₁) (fun k s hk h => load_step hp hk h) 16 (Nat.le_refl _) s₁ hl₀
  refine WP.seq (WP.mono hload fun s₂ h₂ => ?_)
  have hh₂ : Holds (V s₁) s₂ := fun k hk => h₂.loaded k hk hk
  refine WP.seq (WP.mono (rounds_ok hh₂) fun s₃ ⟨hh₃, hm₃, hrd₃, hwr₃, hk₃⟩ => ?_)
  have hf₃ : FI s₁ (Rs s₁) 0 s₃ :=
    ⟨fun _ _ h => absurd h (by omega), fun j hj _ => hh₃ j hj,
      by rw [hm₃, h₂.mem]; exact Frame.refl _ _, hrd₃.trans h₂.rd, hwr₃.trans h₂.wr,
      fun r hr hru => (hk₃ r hr hru).trans (h₂.keep r hr)⟩
  unfold finish
  exact WP.mono (wp_range_flatMap (M := isa) (FI s₁ (Rs s₁)) (fun i s hi h => add_step hp hi h) 16
    (Nat.le_refl _) s₃ hf₃) fun s' h => ⟨fun j hj => h.done j hj hj, h.frame, h.rd, h.wr, h.keep⟩

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa block s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      Proof.ChaCha20.blockRISCV64.post s₀ s' := by
  refine WP.seq (WP.mono (save_ok hp) fun s₁ h₁ => ?_)
  have hg : ∀ r, r ≠ .t0 → s₁.gpr r = s₀.gpr r := h₁.gpr
  have hp₁ : Pre s₁ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [stR, bufR, st, buf, hg .a0 (by decide), hg .a1 (by decide), h₁.rd, h₁.wr] <;>
      first | exact hp.rd | exact hp.wr | exact hp.buf_st | exact hp.st_al | exact hp.buf_al
  have hbuf : buf s₁ = buf s₀ := hg .a1 (by decide)
  have hV : V s₁ = V s₀ := by
    apply Vector.ext
    intro j hj
    simp only [V, stateAt, Vector.getElem_ofFn, st, hg .a0 (by decide)]
    rw [h₁.frame.readW (r := stR s₀) (Offset.contains_base _ (by omega) (by omega))
      (by simpa using Region.Disjoint.sub_right hp.buf_st.symm (savR_sub s₀)) (by decide)]
  refine WP.seq (WP.mono (main_ok hp₁) fun s₃ ⟨hout, hf, hrd, hwr, hk⟩ => ?_)
  have hf' : Frame [outR s₀] s₁.mem s₃.mem := by simpa only [outR, hbuf] using hf
  have hr1 : s₃.gpr .a1 = buf s₀ := by rw [hk _ not_words_a1 (by decide)]; exact hbuf
  have hsav : ∀ i < 5, s₃.mem.readW (sv s₀ + BitVec.ofNat 64 (8 * i)) 64 = s₀.gpr (saved i) :=
    fun i hi => by
      rw [hf'.readW (r := savR s₀) (sav_contains s₀ hi) (by simpa using (outR_sav s₀).symm)
        (by decide)]
      exact h₁.saved i hi
  rw [restore, WP.block_append_iff]
  refine WP.mono (savePtr_ok (s := s₃) rfl) fun s₄ e => ?_
  subst e
  have hsv : sv s₃ = sv s₀ := by simp only [sv, q, buf, hr1]
  have hr₀ : RI' s₀ (s₃.write .t0 (sv s₃)) 0 (s₃.write .t0 (sv s₃)) :=
    ⟨by rw [RegUpd.gpr_write_self, hsv], fun _ h => absurd h (by omega), fun _ _ _ => rfl, rfl,
      by rw [RegUpd.rd_write, hrd, h₁.rd], by rw [RegUpd.wr_write, hwr, h₁.wr]⟩
  refine WP.mono (wp_range_flatMap (M := isa) (RI' s₀ (s₃.write .t0 (sv s₃)))
    (fun k s hk h => restore_step hp (by simpa only [RegUpd.mem_write] using hsav) hk h) 5 (Nat.le_refl _)
    _ hr₀) fun s' h => ⟨?_, ?_, ?_⟩
  · intro r hr
    rcases preserved_cases hr with ⟨i, hi, rfl⟩ | ⟨hw, hU⟩
    · exact h.restored i hi
    · have ht : r ≠ .t0 := fun e => hw (e ▸ t0_words)
      rw [h.others r ht fun i hi e => hw (e ▸ .inr ?_), RegUpd.gpr_write_of_ne _ _ ht, hk r hw hU,
        hg r ht]
      have key : ∀ i < 5, saved i = T ∨ saved i = U ∨ ∃ k < 16, saved i = wreg k := by decide
      rcases key i hi with e' | e' | ⟨k, hk', e'⟩
      · exact e'
      · exact absurd (e.trans e') hU
      · exact absurd (.inl ⟨k, hk', e.trans e'⟩) hw
  · rw [h.others _ (by decide) fun i hi e => ?_, RegUpd.gpr_write_of_ne _ _ (by decide),
      hk _ not_words_ra (by decide), hg _ (by decide)]
    have key : ∀ i < 5, saved i ≠ .ra := by decide
    exact key i hi e.symm
  · show stateAt s'.mem (s₀.gpr .a1) = Spec.ChaCha20.block (stateAt s₀.mem (s₀.gpr .a0))
    rw [h.mem, RegUpd.mem_write]
    have := block_post (m := s₃.mem) (p := buf s₁) (R := Rs s₁) (v := V s₁) hout
    rw [hbuf] at this
    simp only [Rs, hV] at this
    exact this

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 256⟩]

theorem block_verified :
    Verified RISCV64.target Impl.ChaCha20.RISCV64.block Proof.ChaCha20.blockRISCV64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, hra, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he, hra⟩, h₂⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h1, h2]
  · exact ⟨satState, rfl, rfl, Region.disjoint_of_sep (by decide), by decide, by decide⟩

end VG.Proof.ChaCha20.RISCV64
