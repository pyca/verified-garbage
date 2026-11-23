module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Hash
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
public import VerifiedGarbage.Proof.Framework.ICall
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-! # Calling a function by the address in a frame word (x86-64)

`viaSlot d n c` loads the frame word at `rsp + d` into `rax` and calls the
address there, an indirect call of the one function `n`, whose code is `c`.
Where the word holds `n`'s address, it runs as the call of `c`
(`viaSlot_ok`), from the state with that address in `rax`. Two runs of it
are two runs of the call wherever the runs agree on `n`'s address
(`viaSlot_ct`): the address is all the indirect call observes beyond the
call's trace, and a run of it at all means the word held it. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Dsa.X86_64.Generation (viaSlot)

/-- The functions the search calls by their addresses: its hash's `update`
and `finalize`, and its prime test. -/
structure FnNames where
  upd : String
  fin : String
  prime : String

/-- Frame words 29, 30 and 31 (`updSlot`, `finSlot`, `primeSlot`) hold the
addresses of the functions `n`. -/
structure FnSlots (n : FnNames) (W : Nat → BitVec 64) (s : State) : Prop where
  upd : W 29 = s.syms n.upd
  fin : W 30 = s.syms n.fin
  prime : W 31 = s.syms n.prime

theorem FnSlots.congr {n : FnNames} {W W' : Nat → BitVec 64} {s t : State} (h : FnSlots n W s)
    (h29 : W' 29 = W 29) (h30 : W' 30 = W 30) (h31 : W' 31 = W 31) (hy : t.syms = s.syms) :
    FnSlots n W' t :=
  ⟨by rw [h29, hy]; exact h.upd, by rw [h30, hy]; exact h.fin, by rw [h31, hy]; exact h.prime⟩

/-- The state of the call: the address in `rax`. -/
abbrev slotState (s : State) (n : String) : State := s.setReg .rax (s.syms n)

theorem slotState_gpr (s : State) (n : String) {r : Reg} (h : r ≠ .rax) :
    (slotState s n).gpr r = s.gpr r := RegUpd.gpr_setReg_of_ne _ _ h

theorem lay_slotState {s : State} {F S : Addr} (L : Lay s F S) (n : String) :
    Lay (slotState s n) F S :=
  L.congr (slotState_gpr s n (by decide)) (RegUpd.wr_setReg _ _ _) (by rw [RegUpd.mem_setReg])

theorem viaSlot_ok {s : State} {F S : Addr} (L : Lay s F S) {d : Nat} (hd : d + 8 ≤ frameBytes)
    {n : String} {c : Prog isa} (hw : word s.mem F d = s.syms n) {Q : State → Prop}
    (h : WP isa (.call n c) (slotState s n) Q) : WP isa (viaSlot d n c) s Q := by
  have hw' : s.mem.readW (off F d) 64 = s.syms n := hw
  unfold viaSlot
  refine WP.seq ?_
  xrun [ea_sp, L.rsp, L.ld hd, hw']
  exact WP.icalls_of_call (i := (Instr.callr .rax : Instr)) (ts := [(n, c)]) (a := s.syms n)
    (by simp only [icall, RegUpd.gpr_setReg_self]) (by simp [icallTarget, isa, setReg_syms]) h

theorem exec_movRax {m : MemOp} {s a : State} (h : exec (.mov .rax (.mem m)) s = some a) :
    ∃ v, a = s.setReg .rax v := by
  simp only [reduceExec, Option.map_eq_some_iff] at h
  obtain ⟨_, _, rfl⟩ := h
  exact ⟨_, rfl⟩

/-- A run of the load of a frame word into `rax`. -/
theorem exec_slotLoad {d : Nat} {s a : State} {t : List Leak}
    (h : Exec isa (.block [.mov .rax (.mem (Impl.Mgf1.X86_64.sp d))]) s t a) :
    (∃ v, a = s.setReg .rax v) ∧ t = (isa.addrs (.mov .rax (.mem (Impl.Mgf1.X86_64.sp d))) s).map Leak.addr := by
  cases h with
  | block hb =>
    simp only [execBlock] at hb
    split at hb
    · cases hb
    · rename_i a' he
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, List.append_nil] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨exec_movRax he, rfl⟩

theorem addrs_slotLoad {d : Nat} {s₁ s₂ : State} (h : s₁.gpr .rsp = s₂.gpr .rsp) :
    isa.addrs (.mov .rax (.mem (Impl.Mgf1.X86_64.sp d))) s₁ =
      isa.addrs (.mov .rax (.mem (Impl.Mgf1.X86_64.sp d))) s₂ := by
  simp only [addrs, srcAddrs, State.ea, Impl.Mgf1.X86_64.sp, h]

/-- Two runs of the call by the address in a frame word, from states with
the same stack pointer that agree on `n`'s address, are two runs of the
call of `n`, with the address in `rax`. -/
theorem viaSlot_ct {d : Nat} {n : String} {c : Prog isa} {P Q : State → State → Prop}
    (hs : ∀ s₁ s₂, P s₁ s₂ → s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.syms n = s₂.syms n)
    (h : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = slotState s₁ n ∧ b = slotState s₂ n) (.call n c) Q) :
    RelCT isa P (viaSlot d n c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨hsp, hsy⟩ := hs _ _ hp
  unfold viaSlot at e₁ e₂
  cases e₁ with | seq b₁ i₁ => cases e₂ with | seq b₂ i₂ =>
  obtain ⟨⟨v₁, rfl⟩, rfl⟩ := exec_slotLoad b₁
  obtain ⟨⟨v₂, rfl⟩, rfl⟩ := exec_slotLoad b₂
  obtain ⟨a₁, n₁, c₁, x₁, y₁, u₁, hi₁, hf₁, hc₁, hb₁, hr₁, rfl⟩ := Exec.icalls_inv i₁
  obtain ⟨a₂, n₂, c₂, x₂, y₂, u₂, hi₂, hf₂, hc₂, hb₂, hr₂, rfl⟩ := Exec.icalls_inv i₂
  simp only [icallTarget, List.find?_cons, List.find?_nil] at hf₁ hf₂
  split at hf₁ <;> [rename_i ha₁; cases hf₁]
  split at hf₂ <;> [rename_i ha₂; cases hf₂]
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hf₁)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hf₂)
  simp only [beq_iff_eq] at ha₁ ha₂
  simp only [icall, RegUpd.gpr_setReg_self, Option.some.injEq] at hi₁ hi₂
  subst hi₁ hi₂
  have e₁ : v₁ = s₁.syms n := by rw [← ha₁]; rfl
  have e₂ : v₂ = s₂.syms n := by rw [← ha₂]; rfl
  subst e₁ e₂
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ (.call hc₁ hb₁ hr₁) (.call hc₂ hb₂ hr₂)
  refine ⟨?_, hq⟩
  simp only [icallTrace]
  rw [hsy]
  have hl : addrs (.mov .rax (.mem (Impl.Mgf1.X86_64.sp d))) s₁ =
      addrs (.mov .rax (.mem (Impl.Mgf1.X86_64.sp d))) s₂ := addrs_slotLoad hsp
  rw [hl]
  exact congrArg (_ ++ ·) (congrArg (_ ++ ·) (congrArg (List.cons _) ht))

/-- `viaSlot_ct` for two runs with the same public data `a`, of which the
stack pointer and `n`'s address are functions. -/
theorem two_viaSlot {α : Type} {Φ : α → State → Prop} {d : Nat} {n : String} {c : Prog isa}
    (hs : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.syms n = s₂.syms n)
    (h : RelCT isa (VG.Proof.Bignum.X86_64.Two fun a t => ∃ t₀, Φ a t₀ ∧ t = slotState t₀ n) (.call n c)
      fun _ _ => True) :
    RelCT isa (VG.Proof.Bignum.X86_64.Two Φ) (viaSlot d n c) fun _ _ => True :=
  viaSlot_ct (fun s₁ s₂ ⟨a, h₁, h₂⟩ => hs a s₁ s₂ h₁ h₂)
    (h.mono (fun _ _ ⟨s₁, s₂, ⟨a, h₁, h₂⟩, e₁, e₂⟩ => ⟨a, ⟨s₁, h₁, e₁⟩, ⟨s₂, h₂, e₂⟩⟩) fun _ _ h => h)

end VG.Proof.Dsa.X86_64.Generation
