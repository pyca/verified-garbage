module

public import VerifiedGarbage.Impl.Dispatch.X86
public import VerifiedGarbage.Proof.Framework.Dispatch
public import VerifiedGarbage.Proof.Framework.X86.Call

/-!
# Choosing code by a public selector on x86 (32-bit): proofs

The tests of `Dispatch.X86.chain r` (`cmp r, k`) for keys below `2^31`
(`tests r`): each leaks nothing, sets `ZF` to whether `r` is `k`, and
changes only the flags (`FlagsOnly`), so `Dispatch.chain_wp`, `chain_exec`
and `chain_relCT` apply with the selector `r`.

A call's arguments are pushed once, around the chain, whose cases are bare
calls (`.frame (.push rs) (chain r cs) (.pop q n)`): the tests change only
the flags, so the frame around the chain runs as the frame around the case
of the selector, from a state with other flags (`frame_chain_exec`,
`frame_chain_wp`, `frame_chain_relCT`).
-/

@[expose] public section

namespace VG.Proof.Dispatch.X86

open VG.X86 VG.Impl.Dispatch.X86

/-- The selector: the register `r`. -/
def sel (r : Reg) (s : State) : Nat := (s.gpr r).toNat

/-- `s'` is `s` with other flags. -/
def FlagsOnly (s s' : State) : Prop := ∃ c o z f, s' = s.setFlags c o z f

theorem FlagsOnly.refl (s : State) : FlagsOnly s s := ⟨s.cf, s.of, s.zf, s.sf, rfl⟩

theorem FlagsOnly.trans {a b c : State} (h₁ : FlagsOnly a b) (h₂ : FlagsOnly b c) : FlagsOnly a c := by
  obtain ⟨_, _, _, _, rfl⟩ := h₁
  obtain ⟨c', o', z', f', rfl⟩ := h₂
  exact ⟨c', o', z', f', rfl⟩

theorem FlagsOnly.gpr {s s' : State} (h : FlagsOnly s s') (r : Reg) : s'.gpr r = s.gpr r := by
  obtain ⟨_, _, _, _, rfl⟩ := h; rfl

theorem FlagsOnly.mem {s s' : State} (h : FlagsOnly s s') : s'.mem = s.mem := by
  obtain ⟨_, _, _, _, rfl⟩ := h; rfl

theorem FlagsOnly.rd {s s' : State} (h : FlagsOnly s s') : s'.rd = s.rd := by
  obtain ⟨_, _, _, _, rfl⟩ := h; rfl

theorem FlagsOnly.wr {s s' : State} (h : FlagsOnly s s') : s'.wr = s.wr := by
  obtain ⟨_, _, _, _, rfl⟩ := h; rfl

theorem FlagsOnly.syms {s s' : State} (h : FlagsOnly s s') : s'.syms = s.syms := by
  obtain ⟨_, _, _, _, rfl⟩ := h; rfl

/-- `cmp r, k`, for `k < 2^31`. -/
theorem tests (r : Reg) : Proof.Dispatch.Tests (M := isa) (test r) Cond.e (sel r) FlagsOnly (2 ^ 31) where
  step k hk s := by
    refine ⟨_, rfl, ?_, ⟨_, _, _, _, rfl⟩, rfl⟩
    simp only [eval, arithFlags, State.setFlags]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.sub_eq_iff_eq_add,
      show (0 : BitVec 32) + BitVec.ofNat 32 k = BitVec.ofNat 32 k from BitVec.zero_add _]
    show _ ↔ (s.gpr r).toNat = k
    constructor
    · intro h; rw [h, BitVec.toNat_ofNat]; omega
    · intro h; apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat]; omega
  refl := FlagsOnly.refl
  trans := FlagsOnly.trans

/-! ## A frame around the chain -/

theorem pushRegs_setFlags (c o z f : Option Bool) :
    ∀ (rs : List Reg) (s : State), pushRegs (s.setFlags c o z f) rs = (pushRegs s rs).setFlags c o z f
  | [], _ => rfl
  | r :: rs, s => pushRegs_setFlags c o z f rs
      { s.setReg .esp (s.gpr .esp - 4) with mem := s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.gpr r) }

theorem pushed_setFlags (rs : List Reg) (s : State) (c o z f : Option Bool) :
    pushed rs (s.setFlags c o z f) = (pushed rs s).setFlags c o z f := by
  simp only [pushed, pushRegs_setFlags]
  rfl

theorem flagsOnly_pushed {rs : List Reg} {s u : State} (h : FlagsOnly (pushed rs s) u) :
    ∃ s₀, FlagsOnly s s₀ ∧ u = pushed rs s₀ := by
  obtain ⟨c, o, z, f, rfl⟩ := h
  exact ⟨_, ⟨c, o, z, f, rfl⟩, (pushed_setFlags rs s c o z f).symm⟩

theorem FlagsOnly.esp {s s' : State} (h : FlagsOnly s s') : s'.gpr .esp = s.gpr .esp := h.gpr _

/-- A run of the frame around the chain is a run of the frame around the
selector's case, from `s` with other flags, with the tests' branches after
the push's addresses. -/
theorem frame_chain_exec {rs : List Reg} {q : Reg} {n : Nat} {r : Reg} (hr : r ≠ .esp)
    {cs : List (Nat × Prog isa)} (hB : ∀ k ∈ Proof.Dispatch.keys cs, k < 2 ^ 31) {s s' : State} {t : List Leak}
    (hk : sel r s ∈ Proof.Dispatch.keys cs) (e : Exec isa (.frame (.push rs) (chain r cs) (.pop q n)) s t s') :
    ∃ c s₀ t₀, (sel r s, c) ∈ cs ∧ FlagsOnly s s₀ ∧ Exec isa (.frame (.push rs) c (.pop q n)) s₀ t₀ s' ∧
      t = t₀.take rs.length ++ Proof.Dispatch.trace (sel r s) cs ++ t₀.drop rs.length := by
  cases e with
  | frame hp hb hq =>
    obtain ⟨hne, hrs, hn, rfl⟩ := push_some hp
    have hsel : sel r (pushed rs s) = sel r s := by simp only [sel, pushed_gpr rs s hr]
    obtain ⟨c, u, t₁, hm, hf, -, e₁, rfl⟩ :=
      Proof.Dispatch.chain_exec (tests r) cs hB (by rw [hsel]; exact hk) hb
    obtain ⟨s₀, h₀, rfl⟩ := flagsOnly_pushed hf
    have hesp : s₀.gpr .esp = s.gpr .esp := h₀.esp
    have hwr : s₀.wr = s.wr := h₀.wr
    refine ⟨c, s₀, _, by rw [← hsel]; exact hm, h₀,
      .frame (push_pushed hne hrs (by rw [hesp]; exact hn)) e₁ (by
        simp only [isa, pop, pushed_esp, pushed_wr, hesp, hwr] at hq ⊢; exact hq), ?_⟩
    have ha : isa.addrs (.push rs) s₀ = isa.addrs (.push rs) s := by simp only [addrs, hesp]
    have hl : ((isa.addrs (.push rs) s).map Leak.addr).length = rs.length := by
      simp only [addrs, List.length_map, List.length_range]
    rw [ha, hsel, List.append_assoc _ t₁, List.take_left' hl, List.drop_left' hl]
    simp only [List.append_assoc]

/-- The frame around the chain: as the frame around the selector's case,
from `s` with any flags. -/
theorem frame_chain_wp {rs : List Reg} {q : Reg} {r : Reg} (hr : r ≠ .esp) (hq : q ≠ .esp)
    (hne : rs ≠ []) (hrs : .esp ∉ rs) {cs : List (Nat × Prog isa)}
    (hB : ∀ k ∈ Proof.Dispatch.keys cs, k < 2 ^ 31) (hnd : (Proof.Dispatch.keys cs).Nodup)
    (hsp : NoSp (chain r cs)) {s : State} {Q : State → Prop}
    (hn : 4 * rs.length ≤ (s.gpr .esp).toNat) (hk : sel r s ∈ Proof.Dispatch.keys cs)
    (h : ∀ c, (sel r s, c) ∈ cs → ∀ s₀, FlagsOnly s s₀ → WP isa (.frame (.push rs) c (.pop q rs.length)) s₀ Q) :
    WP isa (.frame (.push rs) (chain r cs) (.pop q rs.length)) s Q := by
  have hsel : sel r (pushed rs s) = sel r s := by simp only [sel, pushed_gpr rs s hr]
  refine WP.frame hne hrs hq hn hsp ?_
  refine Proof.Dispatch.chain_wp (tests r) cs hB (by rw [hsel]; exact hk) hnd fun c hc u hf _ => ?_
  obtain ⟨s₀, h₀, rfl⟩ := flagsOnly_pushed hf
  obtain ⟨t, s', e, hQ⟩ := h c (by rw [← hsel]; exact hc) s₀ h₀
  cases e with
  | frame hp hb hpop =>
    obtain ⟨-, -, -, rfl⟩ := push_some hp
    refine ⟨_, _, hb, ?_⟩
    simp only [isa, pop] at hpop
    split at hpop
    · cases hpop; exact hQ
    · cases hpop

/-- Two runs of the frame around the chain with the same selector leak the
same if the frames around its case do, from states with other flags. -/
theorem frame_chain_relCT {rs : List Reg} {q : Reg} {n : Nat} {r : Reg} (hr : r ≠ .esp)
    {cs : List (Nat × Prog isa)} (hB : ∀ k ∈ Proof.Dispatch.keys cs, k < 2 ^ 31)
    (hnd : (Proof.Dispatch.keys cs).Nodup) {P : State → State → Prop}
    (hs : ∀ s₁ s₂, P s₁ s₂ → sel r s₁ = sel r s₂ ∧ sel r s₁ ∈ Proof.Dispatch.keys cs)
    (h : ∀ k c, (k, c) ∈ cs → RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ sel r s₁ = k ∧
      FlagsOnly s₁ a ∧ FlagsOnly s₂ b) (.frame (.push rs) c (.pop q n)) fun _ _ => True) :
    RelCT isa P (.frame (.push rs) (chain r cs) (.pop q n)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨he, hk⟩ := hs _ _ hp
  obtain ⟨c₁, a₁, u₁, m₁, f₁, x₁, rfl⟩ := frame_chain_exec hr hB hk e₁
  obtain ⟨c₂, a₂, u₂, m₂, f₂, x₂, rfl⟩ := frame_chain_exec hr hB (he ▸ hk) e₂
  rw [← he] at m₂ ⊢
  rw [Proof.Dispatch.case_unique hnd m₂ m₁] at x₂
  obtain ⟨rfl, -⟩ := h _ _ m₁ _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, f₁, f₂⟩ x₁ x₂
  exact ⟨rfl, trivial⟩

end VG.Proof.Dispatch.X86
