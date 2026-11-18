module

public import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
public import VerifiedGarbage.Proof.Framework.AArch64.Depth
import VerifiedGarbage.Proof.Framework.AArch64.ResidueCT
import VerifiedGarbage.Proof.Framework.AArch64.ResidueTaint
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Returning without secret residue, whatever the code leaves (AArch64)

`ScrubAll.noResidue_scrubAll`: code verified against its contract, whose
frames stay within the `W` bytes below the stack pointer, that writes no
PSTATE.DIT and calls nothing indirectly, followed by `scrubAll W rb`, which
clears every register the calling convention does not preserve but the
result's `rb` bits of `x0`, the flags and the high halves of `v8`–`v15`, and
zeroes those `W` bytes, returns without secret residue. It needs no analysis
of the code: the registers it clears hold constants, those the calling
convention preserves are what they were on entry (`abiPreserved`), the memory
the code may change outside the buffers is within those `W` bytes
(`Exec.frameSp`), which the clearing zeroes, and the two runs end with the
same unknowns, since their traces are the same (`Exec.unknowns_agree`). So it
serves code generic over the implementations of the functions it calls,
whose code is not known, as x86-64's `X86_64.Scrub.withScrubAll` does.
-/

@[expose] public section

namespace VG.AArch64.ScrubAll

open VG.AArch64 VG.AArch64.Residue VG.Impl.Residue.AArch64

/-! ## The unknowns of two runs along the same trace -/

/-- `c` calls nothing indirectly. -/
def noIcall : Prog isa → Bool
  | .block _ => true
  | .seq a b => noIcall a && noIcall b
  | .ite _ t e => noIcall t && noIcall e
  | .loop b _ => noIcall b
  | .call _ b => noIcall b
  | .frame _ b _ => noIcall b
  | .icall .. => false

theorem execBlock_unknowns : ∀ {is : List Instr} {s₁ s₂ a b : State} {t₁ t₂ : List Leak},
    execBlock isa is s₁ = some (a, t₁) → execBlock isa is s₂ = some (b, t₂) →
      t₁.length = t₂.length ∧ a.unknowns = s₁.unknowns ∧ b.unknowns = s₂.unknowns
  | [], _, _, _, _, _, _, h₁, h₂ => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
    obtain ⟨rfl, rfl⟩ := h₁; obtain ⟨rfl, rfl⟩ := h₂; exact ⟨rfl, rfl, rfl⟩
  | i :: is, s₁, s₂, a, b, t₁, t₂, h₁, h₂ => by
    simp only [execBlock] at h₁ h₂
    cases e₁ : exec i s₁ with
    | none => simp only [e₁] at h₁; cases h₁
    | some u₁ =>
      cases e₂ : exec i s₂ with
      | none => simp only [e₂] at h₂; cases h₂
      | some u₂ =>
        simp only [isa, e₁, e₂] at h₁ h₂
        obtain ⟨p₁, hp₁, hq₁⟩ := Option.map_eq_some_iff.mp h₁
        obtain ⟨p₂, hp₂, hq₂⟩ := Option.map_eq_some_iff.mp h₂
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq₁
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq₂
        obtain ⟨hl, ha, hb⟩ := execBlock_unknowns (s₁ := u₁) (s₂ := u₂) (by rw [hp₁]) (by rw [hp₂])
        refine ⟨?_, ha.trans (RTaint.exec_ud e₁).1, hb.trans (RTaint.exec_ud e₂).1⟩
        simp only [List.length_append, List.length_map, hl, RTaintCT.addrs_length i s₁ s₂]

theorem push_unknowns {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) : s₁.unknowns = s.unknowns := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h <;> split at h <;> cases h <;> rfl

/-- The unknowns a frame's release uses. -/
def popK : Instr → Nat
  | .pop _ => 4
  | .free b => b / 4
  | _ => 0

theorem pop_unknowns {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') :
    s'.unknowns = fun n => s₂.unknowns (n + popK j) := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h <;> split at h <;> cases h <;> rfl

theorem call_unknowns {s s₁ : State} (h : isa.call s = some s₁) :
    s₁.unknowns = fun n => s.unknowns (n + 4) := by
  simp only [isa, call, Option.some.injEq] at h; subst h; rfl

theorem ret_unknowns {s₁ s₂ s' : State} (h : isa.ret s₁ s₂ = some s') : s'.unknowns = s₂.unknowns := by
  simp only [isa, ret] at h; split at h <;> cases h; rfl

theorem branch_ne {r₁ r₂ : List Leak} : Leak.branch true :: r₁ ≠ Leak.branch false :: r₂ := by
  intro h; cases h

/-- Two runs of code that calls nothing indirectly, from the same unknowns,
one of whose traces is a prefix of the other's continued, have the same trace
and end with the same unknowns. -/
theorem Exec.unknowns_agree {c : Prog isa} (hc : noIcall c = true) {s₁ s₁' : State} {t₁ : List Leak}
    (e₁ : Exec isa c s₁ t₁ s₁') :
    ∀ {s₂ s₂' : State} {t₂ : List Leak} (r₁ r₂ : List Leak), Exec isa c s₂ t₂ s₂' →
      s₁.unknowns = s₂.unknowns → t₁ ++ r₁ = t₂ ++ r₂ → t₁ = t₂ ∧ s₁'.unknowns = s₂'.unknowns := by
  induction e₁ with
  | block h₁ =>
    intro _ _ _ r₁ r₂ e₂ hu ht
    cases e₂ with
    | block h₂ =>
      obtain ⟨hl, ha, hb⟩ := execBlock_unknowns h₁ h₂
      exact ⟨(List.append_inj ht hl).1, ha.trans (hu.trans hb.symm)⟩
  | seq _ _ ih₁ ih₂ =>
    intro _ _ _ r₁ r₂ e₂ hu ht
    simp only [noIcall, Bool.and_eq_true] at hc
    cases e₂ with
    | seq a₂ b₂ =>
      rw [List.append_assoc, List.append_assoc] at ht
      obtain ⟨rfl, hu'⟩ := ih₁ hc.1 _ _ a₂ hu ht
      obtain ⟨rfl, hu''⟩ := ih₂ hc.2 _ _ b₂ hu' (List.append_cancel_left ht)
      exact ⟨rfl, hu''⟩
  | iteT _ _ ih =>
    intro _ _ _ r₁ r₂ e₂ hu ht
    simp only [noIcall, Bool.and_eq_true] at hc
    cases e₂ with
    | iteT _ a₂ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      obtain ⟨rfl, hu'⟩ := ih hc.1 _ _ a₂ hu ht
      exact ⟨rfl, hu'⟩
    | iteF _ _ => exact absurd ht branch_ne
  | iteF _ _ ih =>
    intro _ _ _ r₁ r₂ e₂ hu ht
    simp only [noIcall, Bool.and_eq_true] at hc
    cases e₂ with
    | iteT _ _ => exact absurd ht.symm branch_ne
    | iteF _ a₂ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      obtain ⟨rfl, hu'⟩ := ih hc.2 _ _ a₂ hu ht
      exact ⟨rfl, hu'⟩
  | loopExit _ _ ih =>
    intro _ _ _ r₁ r₂ e₂ hu ht
    simp only [noIcall] at hc
    cases e₂ with
    | loopExit b₂ _ =>
      rw [List.append_assoc, List.append_assoc] at ht
      obtain ⟨rfl, hu'⟩ := ih hc ([.branch false] ++ r₁) ([.branch false] ++ r₂) b₂ hu ht
      exact ⟨rfl, hu'⟩
    | loopNext b₂ _ _ =>
      rw [List.append_assoc, List.append_assoc] at ht
      obtain ⟨rfl, -⟩ := ih hc _ _ b₂ hu ht
      exact absurd (List.append_cancel_left ht).symm branch_ne
  | loopNext _ _ _ ih₁ ih₂ =>
    intro _ _ _ r₁ r₂ e₂ hu ht
    have hc' := hc
    simp only [noIcall] at hc'
    cases e₂ with
    | loopExit b₂ _ =>
      rw [List.append_assoc, List.append_assoc] at ht
      obtain ⟨rfl, -⟩ := ih₁ hc' _ _ b₂ hu ht
      exact absurd (List.append_cancel_left ht) branch_ne
    | loopNext b₂ _ n₂ =>
      rw [List.append_assoc, List.append_assoc] at ht
      obtain ⟨rfl, hu'⟩ := ih₁ hc' _ _ b₂ hu ht
      have ht' := List.append_cancel_left ht
      simp only [List.cons_append, List.cons.injEq, true_and] at ht'
      obtain ⟨rfl, hu''⟩ := ih₂ hc _ _ n₂ hu' ht'
      exact ⟨rfl, hu''⟩
  | call hc₁ _ hr ih =>
    intro _ _ _ r₁ r₂ e₂ hu ht
    simp only [noIcall] at hc
    cases e₂ with
    | call hc₂ b₂ hr₂ =>
      simp only [List.map_nil, List.nil_append, List.append_nil] at ht ⊢
      obtain ⟨rfl, hu'⟩ := ih hc _ _ b₂ (by rw [call_unknowns hc₁, call_unknowns hc₂, hu]) ht
      exact ⟨rfl, by rw [ret_unknowns hr, ret_unknowns hr₂, hu']⟩
  | @frame i j _ s₀ _ s₂ _ _ hp _ hq ih =>
    intro s₀' _ _ r₁ r₂ e₂ hu ht
    simp only [noIcall] at hc
    cases e₂ with
    | @frame _ _ _ _ _ s₂' _ _ hp₂ b₂ hq₂ =>
      rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc] at ht
      have hl : (List.map Leak.addr (isa.addrs i s₀)).length = (List.map Leak.addr (isa.addrs i s₀')).length := by
        simp only [List.length_map]; exact RTaintCT.addrs_length i s₀ s₀'
      obtain ⟨h₀, ht'⟩ := List.append_inj ht hl
      obtain ⟨rfl, hu'⟩ := ih hc _ _ b₂ (by rw [push_unknowns hp, push_unknowns hp₂, hu]) ht'
      have hl' : (List.map Leak.addr (isa.addrs j s₂)).length = (List.map Leak.addr (isa.addrs j s₂')).length := by
        simp only [List.length_map]; exact RTaintCT.addrs_length j s₂ s₂'
      have h₃ := (List.append_inj (List.append_cancel_left ht') hl').1
      refine ⟨by rw [h₀, h₃], ?_⟩
      rw [pop_unknowns hq, pop_unknowns hq₂, hu']
  | icall => simp only [noIcall, Bool.false_eq_true] at hc
  | icallNext => simp only [noIcall, Bool.false_eq_true] at hc

/-! ## What the clearing leaves -/

theorem movzs_run : ∀ (rs : List Reg) (u : State),
    execBlock isa (rs.map fun r => .movz .x r 0 0) u =
      some ({ u with gpr := fun q => if q ∈ rs then 0 else u.gpr q }, [])
  | [], u => by
    simp only [List.map_nil, execBlock, List.not_mem_nil, ↓reduceIte]
  | r :: rs, u => by
    simp only [List.map_cons, execBlock, isa, exec, show 16 * 0 < Size.x.bits by decide, ↓reduceIte]
    rw [movzs_run rs]
    simp only [addrs, List.map_nil, List.nil_append, Option.map_some, State.write, List.mem_cons,
      Option.some.injEq, Prod.mk.injEq, and_true]
    congr 1
    funext q
    by_cases h : q ∈ rs
    · simp [h]
    · by_cases hq : q = r
      · subst hq; simp
      · simp [h, hq]

theorem movis_run : ∀ (vs : List VReg) (u : State),
    execBlock isa (vs.map fun v => .vop (.movi0 v)) u =
      some ({ u with v := fun w => if w ∈ vs then 0 else u.v w }, [])
  | [], u => by
    simp only [List.map_nil, execBlock, List.not_mem_nil, ↓reduceIte]
  | v :: vs, u => by
    simp only [List.map_cons, execBlock, isa, exec, VOp.eval, Option.map_some]
    rw [movis_run vs]
    simp only [addrs, List.map_nil, List.nil_append, Option.map_some, State.setV, List.mem_cons,
      Option.some.injEq, Prod.mk.injEq, and_true]
    congr 1
    funext w
    by_cases h : w ∈ vs
    · simp [h]
    · by_cases hw : w = v
      · subst hw; simp
      · simp [h, hw]

theorem inss_run (z : Reg) : ∀ (vs : List VReg) (u : State), u.gpr z = 0 →
    execBlock isa (vs.map fun v => .vop (.ins .d2 v 1 z)) u =
      some ({ u with v := fun w => if w ∈ vs then setLane (u.v w) 64 1 0 else u.v w }, [])
  | [], u, _ => by
    simp only [List.map_nil, execBlock, List.not_mem_nil, ↓reduceIte]
  | v :: vs, u, hz => by
    simp only [List.map_cons, execBlock, isa, exec, VOp.eval, show 1 < 2 by decide, ↓reduceIte,
      Option.map_some, hz]
    rw [inss_run z vs _ (by simp only [State.setV]; exact hz)]
    simp only [addrs, List.map_nil, List.nil_append, Option.map_some, State.setV, List.mem_cons,
      Option.some.injEq, Prod.mk.injEq, and_true]
    congr 1
    funext w
    by_cases h : w ∈ vs
    · by_cases hw : w = v
      · subst hw; simp [h, setLane, BitVec.and_assoc]
      · simp [h, hw]
    · by_cases hw : w = v
      · subst hw; simp [h]
      · simp [h, hw]

/-- The state after `clearsAll` from `u`. -/
def cleared (u : State) : State :=
  { u with
    gpr := fun q => if q ∈ allGprs then 0 else u.gpr q
    v := fun w => if w ∈ hiVecs then setLane (u.v w) 64 1 0 else if w ∈ allVecs then 0 else u.v w
    nf := false, zf := true, c := false, vf := false }

theorem clearsAll_run (u : State) : execBlock isa clearsAll u = some (cleared u, []) := by
  unfold clearsAll
  rw [execBlock_append (M := isa), execBlock_append (M := isa), execBlock_append (M := isa), movzs_run,
    Option.bind_some, movis_run, Option.map_some, Option.bind_some]
  have hx1 : Reg.x1 ∈ allGprs := by decide
  have ht : ∀ w : State, w.gpr .x1 = 0 → execBlock isa [.tst .x .x1 .x1] w =
      some ({ w with nf := false, zf := true, c := false, vf := false }, []) := by
    intro w hw
    simp [execBlock, isa, exec, State.read, hw, addrs]
  rw [ht _ (by simp [hx1]), Option.map_some, Option.bind_some, inss_run .x1 hiVecs _ (by simp [hx1])]
  simp only [Option.map_some, List.append_nil, cleared, Option.some.injEq, Prod.mk.injEq, and_true]
  congr 1
  funext w
  by_cases h : w ∈ hiVecs
  · have : w ∉ allVecs := by revert h; revert w; decide
    simp [h, this]
  · simp [h]

theorem preserved_of {q : Reg} (h0 : q ≠ .x0) (h : q ∉ allGprs) : q ∈ preserved := by
  cases q <;> simp_all [allGprs, preserved]

theorem vreg_cover (w : VReg) (h : w ∉ hiVecs) : w ∈ allVecs := by
  cases w <;> simp_all [hiVecs, allVecs]

theorem preservedV_of {w : VReg} (h : w ∈ hiVecs) : w ∈ preservedV := by
  cases w <;> simp_all [hiVecs, preservedV]

theorem setLane_hi0 {x y : BitVec 128} (h : x.extractLsb' 0 64 = y.extractLsb' 0 64) :
    setLane x 64 1 0 = setLane y 64 1 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb : i < 64 → x.getLsbD i = y.getLsbD i := fun h64 => by
    have := congrArg (fun z : BitVec 64 => z.getLsbD i) h
    simpa [BitVec.getLsbD_extractLsb', h64] using this
  by_cases h64 : i < 64
  · simp [setLane, BitVec.getLsbD_and, hb h64]
  · have hm : (18446744073709551615#128).getLsbD i = false := by
      rw [BitVec.getLsbD_ofNat, show (18446744073709551615 : Nat) = 2 ^ 64 - 1 by decide,
        Nat.testBit_two_pow_sub_one]
      simp [h64]
    simp only [setLane]
    simp [hm]

/-- The bits of `x0` above an `rb`-bit result are zero after `retFix rb`. -/
theorem retFix_hi {rb : Nat} (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) (s : State) :
    ∃ g, execBlock isa (retFix rb) s = some ({ s with gpr := g }, []) ∧ (∀ q, q ≠ .x0 → g q = s.gpr q) ∧
      g .x0 >>> rb = 0 := by
  rcases hrb with rfl | rfl | rfl
  · refine ⟨fun q => if q = .x0 then 0 else s.gpr q, ?_, fun q hq => by simp [hq], by simp⟩
    simp [retFix, execBlock, isa, exec, addrs, State.write]
  · refine ⟨fun q => if q = .x0 then ((s.gpr .x0).setWidth 32 + 0).setWidth 64 else s.gpr q, ?_,
      fun q hq => by simp [hq], ?_⟩
    · simp [retFix, execBlock, isa, exec, addrs, State.write, State.read]
    · apply BitVec.eq_of_toNat_eq
      have := ((s.gpr .x0).setWidth 32).isLt
      simp only [↓reduceIte, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_add,
        Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_setWidth] at this
      apply Nat.div_eq_of_lt
      omega
  · refine ⟨s.gpr, by simp [retFix, execBlock], fun _ _ => rfl, ?_⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := (s.gpr .x0).isLt
    exact Nat.div_eq_of_lt this

end VG.AArch64.ScrubAll
