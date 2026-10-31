module

public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.ChaCha20.Spec
public import VerifiedGarbage.Impl.ChaCha20.RISCV64
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# ChaCha20 block function on RISC-V: the rounds

Untrusted: everything here is checked by Lean. The structure of the PPC64LE
proof (`Proof/ChaCha20/PPC64LE/Rounds.lean`), with each step of the quarter
round (an addition, an XOR and a rotation by two word shifts) proven once
(`qstep_ok`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.RISCV64

open VG VG.RISCV64 VG.Impl.ChaCha20.RISCV64 VG.Proof.ChaCha20
open VG.Spec.ChaCha20 (Word quarterRound qround innerBlock)

/-- The low word of a register. -/
abbrev lo (x : BitVec 64) : Word := x.setWidth 32

theorem qstep_ok {a b d : Reg} (had : a ≠ d) (haT : a ≠ T)
    (hdT : d ≠ T) {k : Nat} (hk0 : 0 < k) (hk : k < 32) (s : State) :
    WP isa (.block (qstep a b d k)) s fun s' =>
      lo (s'.gpr a) = lo (s.gpr a) + lo (s.gpr b) ∧
      lo (s'.gpr d) = (lo (s.gpr d) ^^^ (lo (s.gpr a) + lo (s.gpr b))).rotateLeft k ∧
      (∀ r, r ≠ a → r ≠ d → r ≠ T → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hk' : 32 - k < 32 := by omega
  apply WP.of_runBlock
  simp only [qstep, runBlock_cons, runStep_some, runBlock_nil, exec_add, exec_logic,
    exec_shift_w hk, exec_shift_w hk', Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, fun r h₁ h₂ h₃ => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_write, had, haT, ite_false, ite_true, lo32_add]
  · simp only [RegUpd.gpr_write, ite_true, hdT, Ne.symm hdT, ite_false, lo32_or, lo32_sext,
      Ne.symm had, lo32_xor, lo32_add]
    rw [BitVec.or_comm, rotl_shifts _ hk]
  · simp only [RegUpd.gpr_write, h₁, h₂, h₃, ite_false]

theorem qr_ok {a b c d : Reg} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (haT : a ≠ T) (hbT : b ≠ T) (hcT : c ≠ T) (hdT : d ≠ T)
    (s : State) (va vb vc vd : Word)
    (ha : lo (s.gpr a) = va) (hb : lo (s.gpr b) = vb) (hc : lo (s.gpr c) = vc)
    (hd : lo (s.gpr d) = vd) :
    WP isa (.block (qr a b c d)) s fun s' =>
      lo (s'.gpr a) = (quarterRound va vb vc vd).1 ∧
      lo (s'.gpr b) = (quarterRound va vb vc vd).2.1 ∧
      lo (s'.gpr c) = (quarterRound va vb vc vd).2.2.1 ∧
      lo (s'.gpr d) = (quarterRound va vb vc vd).2.2.2 ∧
      (∀ r, r ≠ a → r ≠ b → r ≠ c → r ≠ d → r ≠ T → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold qr
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (qstep_ok had haT hdT (k := 16) (by decide) (by decide) s)
    fun s₁ ⟨a₁, d₁, o₁, m₁, r₁, w₁⟩ => ?_
  refine WP.mono (qstep_ok hbc.symm hcT hbT (k := 12) (by decide) (by decide) s₁)
    fun s₂ ⟨c₂, b₂, o₂, m₂, r₂, w₂⟩ => ?_
  refine WP.mono (qstep_ok had haT hdT (k := 8) (by decide) (by decide) s₂)
    fun s₃ ⟨a₃, d₃, o₃, m₃, r₃, w₃⟩ => ?_
  refine WP.mono (qstep_ok hbc.symm hcT hbT (k := 7) (by decide) (by decide) s₃)
    fun s₄ ⟨c₄, b₄, o₄, m₄, r₄, w₄⟩ => ?_
  -- The registers each step leaves alone.
  have ea₂ : lo (s₂.gpr a) = lo (s₁.gpr a) := by rw [o₂ a hac hab haT]
  have ed₂ : lo (s₂.gpr d) = lo (s₁.gpr d) := by rw [o₂ d hcd.symm hbd.symm hdT]
  have ec₁ : lo (s₁.gpr c) = lo (s.gpr c) := by rw [o₁ c hac.symm hcd hcT]
  have eb₁ : lo (s₁.gpr b) = lo (s.gpr b) := by rw [o₁ b hab.symm hbd hbT]
  have ec₃ : lo (s₃.gpr c) = lo (s₂.gpr c) := by rw [o₃ c hac.symm hcd hcT]
  have eb₃ : lo (s₃.gpr b) = lo (s₂.gpr b) := by rw [o₃ b hab.symm hbd hbT]
  have ea₄ : lo (s₄.gpr a) = lo (s₃.gpr a) := by rw [o₄ a hac hab haT]
  have ed₄ : lo (s₄.gpr d) = lo (s₃.gpr d) := by rw [o₄ d hcd.symm hbd.symm hdT]
  refine ⟨?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ h₅ => ?_, m₄.trans (m₃.trans (m₂.trans m₁)),
    r₄.trans (r₃.trans (r₂.trans r₁)), w₄.trans (w₃.trans (w₂.trans w₁))⟩
  all_goals first
    | rw [o₄ r h₃ h₂ h₅, o₃ r h₁ h₄ h₅, o₂ r h₃ h₂ h₅, o₁ r h₁ h₄ h₅]
    | simp only [ea₄, ed₄, b₄, c₄, eb₃, ec₃, a₃, d₃, ea₂, ed₂, b₂, c₂, eb₁, ec₁, a₁, d₁, ha, hb,
        hc, hd, quarterRound]

/-! ## Where the words are -/

/-- The state `v` is in the registers. -/
def Holds (v : CState) (s : State) : Prop := ∀ k (hk : k < 16), lo (s.gpr (wreg k)) = v[k]

/-- The registers that hold state words, and the temporary. -/
def Words (r : Reg) : Prop := (∃ k < 16, r = wreg k) ∨ r = T

theorem wreg_inj {j k : Nat} (hj : j < 16) (hk : k < 16) (h : wreg j = wreg k) : j = k := by
  have key : ∀ j, j < 16 → ∀ k, k < 16 → wreg j = wreg k → j = k := by decide
  exact key j hj k hk h

theorem wreg_ne_T {k : Nat} (hk : k < 16) : wreg k ≠ T := by
  have key : ∀ k < 16, wreg k ≠ T := by decide
  exact key k hk

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (v : CState) (s₀ s : State) : Prop where
  holds : Holds v s
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r

theorem quarter_step {x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16) (hw : w < 16)
    (hd : [x, y, z, w].Nodup) {v : CState} {s₀ s : State} (h : RI v s₀ s) :
    WP isa (quarter x y z w) s (RI (qround v ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s₀) := by
  have nd : (x ≠ y ∧ x ≠ z ∧ x ≠ w) ∧ (y ≠ z ∧ y ≠ w) ∧ z ≠ w := by simpa using hd
  obtain ⟨⟨nxy, nxz, nxw⟩, ⟨nyz, nyw⟩, nzw⟩ := nd
  have ne : ∀ {i j}, i < 16 → j < 16 → i ≠ j → wreg i ≠ wreg j := fun hi hj hij e =>
    hij (wreg_inj hi hj e)
  refine WP.mono (qr_ok (ne hx hy nxy) (ne hx hz nxz) (ne hx hw nxw) (ne hy hz nyz)
    (ne hy hw nyw) (ne hz hw nzw) (wreg_ne_T hx) (wreg_ne_T hy) (wreg_ne_T hz) (wreg_ne_T hw)
    s _ _ _ _ (h.holds x hx) (h.holds y hy) (h.holds z hz) (h.holds w hw))
    fun s' ⟨ha, hb, hc, hd, hr, hm, hrd, hwr⟩ =>
    ⟨fun k hk => ?_, hm.trans h.mem, hrd.trans h.rd, hwr.trans h.wr, fun r hr' => ?_⟩
  · rw [qround_get _ _ _ _ _ k hk]
    simp only
    by_cases ew : w = k
    · subst ew; simp only [ite_true]; exact hd
    by_cases ez : z = k
    · subst ez; simp only [ite_true, ew, ite_false]; exact hc
    by_cases ey : y = k
    · subst ey; simp only [ite_true, ew, ez, ite_false]; exact hb
    by_cases ex : x = k
    · subst ex; simp only [ite_true, ew, ez, ey, ite_false]; exact ha
    simp only [ew, ez, ey, ex, ite_false]
    rw [hr _ (ne hk hx (Ne.symm ex)) (ne hk hy (Ne.symm ey)) (ne hk hz (Ne.symm ez))
      (ne hk hw (Ne.symm ew)) (wreg_ne_T hk)]
    exact h.holds k hk
  · have nw : ∀ i < 16, r ≠ wreg i := fun i hi e => hr' (.inl ⟨i, hi, e⟩)
    rw [hr r (nw x hx) (nw y hy) (nw z hz) (nw w hw) fun e => hr' (.inr e)]
    exact h.keep r hr'

theorem doubleRound_ok {v : CState} {s₀ s : State} (h : RI v s₀ s) :
    WP isa doubleRound s (RI (innerBlock v) s₀) := by
  unfold doubleRound
  refine WP.seq (WP.mono (quarter_step (x := 0) (y := 4) (z := 8) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 1) (y := 5) (z := 9) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₆) fun s₇ h₇ => ?_)
  exact WP.mono (quarter_step (x := 3) (y := 4) (z := 9) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₇) fun _ h => h

/-- The counter is separate from the sixteen words and the rotation temporary. -/
theorem counter_not_words : ¬ Words U := by
  rintro (⟨k, hk, e⟩ | e)
  · have key : ∀ k < 16, U ≠ wreg k := by decide
    exact key k hk e
  · exact absurd e (by decide)

theorem rounds_ok {v : CState} {s₀ : State} (h : Holds v s₀) :
    WP isa rounds s₀ fun s =>
      Holds (Nat.repeat innerBlock 10 v) s ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
      (∀ r, ¬ Words r → r ≠ U → s.gpr r = s₀.gpr r) := by
  unfold rounds
  apply WP.seq
  have hi : WP isa (.block [.li U 10]) s₀ (· = s₀.write U 10) := by
    apply WP.of_runBlock
    simp only [runBlock_cons, exec_li (show imm12 10 by decide), runStep_some, runBlock_nil,
      Option.some.injEq, exists_eq_left']
    rfl
  refine hi.mono fun a ea => ?_
  subst ea
  let Inv : Nat → State → Prop := fun n s =>
    0 < n ∧ n ≤ 10 ∧ s.gpr U = BitVec.ofNat 64 n ∧
    Holds (Nat.repeat innerBlock (10 - n) v) s ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
    (∀ r, ¬ Words r → r ≠ U → s.gpr r = s₀.gpr r)
  refine WP.loop (M := isa) Inv ?_ 10 (s₀.write U 10) ?_
  · intro n s ⟨hn, hle, hc, hv, hm, hr, hw, hk⟩
    apply WP.seq
    refine (doubleRound_ok (s₀ := s) ⟨hv, rfl, rfl, rfl, fun _ _ => rfl⟩).mono fun b hb => ?_
    have hcb : b.gpr U = BitVec.ofNat 64 n := (hb.keep U counter_not_words).trans hc
    have hd : WP isa (.block [.addi U U (-1)]) b (· = b.write U (b.gpr U - (1#64))) := by
      apply WP.of_runBlock
      simp only [runBlock_cons, exec_addi (show imm12 (-1) by decide), runStep_some, runBlock_nil,
        Option.some.injEq, exists_eq_left']
      rw [show BitVec.ofInt 64 (-1) = -(1#64) from rfl, ← BitVec.sub_eq_add_neg]
    refine hd.mono fun c ec => ?_
    subst ec
    have hcc : (b.write U (b.gpr U - (1#64))).gpr U = BitVec.ofNat 64 (n - 1) := by
      rw [RegUpd.gpr_write_self, hcb]
      exact Offset.ofNat_sub_ofNat (k := n) (d := 1) (by omega)
    have hv' : Holds (Nat.repeat innerBlock (10 - (n - 1)) v) (b.write U (b.gpr U - (1#64))) := by
      rw [show 10 - (n - 1) = (10 - n) + 1 by omega]
      intro k hlt
      rw [RegUpd.gpr_write_of_ne _ _ (fun e => counter_not_words (.inl ⟨k, hlt, e.symm⟩))]
      exact hb.holds k hlt
    have hk' : ∀ r, ¬ Words r → r ≠ U →
        (b.write U (b.gpr U - (1#64))).gpr r = s₀.gpr r := by
      intro r hwr hru
      rw [RegUpd.gpr_write_of_ne _ _ hru, hb.keep r hwr, hk r hwr hru]
    have he := Steps.eval_nonzero_ofNat (b.write U (b.gpr U - (1#64))) U (by omega) hcc
    by_cases hz : n = 1
    · left
      refine ⟨?_, ?_, hb.mem.trans hm, hb.rd.trans hr, hb.wr.trans hw, hk'⟩
      · simpa only [hz, Nat.sub_self, ne_eq, not_true_eq_false, decide_false] using he
      · simpa only [hz, Nat.sub_self, Nat.sub_zero] using hv'
    · right
      refine ⟨?_, n - 1, by omega, by omega, by omega, hcc, hv', hb.mem.trans hm,
        hb.rd.trans hr, hb.wr.trans hw, hk'⟩
      simpa only [decide_eq_true (by omega : n - 1 ≠ 0)] using he
  · refine ⟨by decide, by decide, RegUpd.gpr_write_self .., ?_, rfl, rfl, rfl,
      fun r _ hru => RegUpd.gpr_write_of_ne _ _ hru⟩
    intro k hk
    rw [RegUpd.gpr_write_of_ne _ _ (fun e => counter_not_words (.inl ⟨k, hk, e.symm⟩))]
    exact h k hk

end VG.Proof.ChaCha20.RISCV64
