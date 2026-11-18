module

public import VerifiedGarbage.Proof.Framework.AArch64.ResidueWin
public import VerifiedGarbage.Proof.Framework.AArch64.Depth
import VerifiedGarbage.Proof.Framework.AArch64.ResidueCT
import VerifiedGarbage.Proof.Framework.AArch64.ResidueTaint
import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Framework.AArch64.Syms
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

/-- The bits of `x0` above an `rb`-bit result are zero after `retFix rb`, and
its low `rb` bits are what they were. -/
theorem retFix_hi {rb : Nat} (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) (s : State) :
    ∃ g, execBlock isa (retFix rb) s = some ({ s with gpr := g }, []) ∧ (∀ q, q ≠ .x0 → g q = s.gpr q) ∧
      g .x0 >>> rb = (0 : BitVec 64) ∧ (g .x0).setWidth rb = (s.gpr .x0).setWidth rb := by
  rcases hrb with rfl | rfl | rfl
  · refine ⟨fun q => if q = .x0 then 0 else s.gpr q, ?_, fun q hq => by simp [hq], by simp, ?_⟩
    · simp [retFix, execBlock, isa, exec, addrs, State.write]
    · apply BitVec.eq_of_toNat_eq
      have h1 := ((0 : BitVec 64).setWidth 0).isLt
      have h2 := ((s.gpr .x0).setWidth 0).isLt
      simp only [Nat.pow_zero] at h1 h2
      simp only [↓reduceIte]
      omega
  · refine ⟨fun q => if q = .x0 then ((s.gpr .x0).setWidth 32 + 0).setWidth 64 else s.gpr q, ?_,
      fun q hq => by simp [hq], ?_, by simp⟩
    · simp [retFix, execBlock, isa, exec, addrs, State.write, State.read]
    · apply BitVec.eq_of_toNat_eq
      have := ((s.gpr .x0).setWidth 32).isLt
      simp only [↓reduceIte, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_add,
        Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_setWidth] at this
      apply Nat.div_eq_of_lt
      omega
  · refine ⟨s.gpr, by simp [retFix, execBlock], fun _ _ => rfl, ?_, rfl⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := (s.gpr .x0).isLt
    exact Nat.div_eq_of_lt this

/-! ## The theorem -/

open VG.AArch64.Scrub VG.AArch64.RTaintG in
theorem withScrubG_range {W : Nat} (hW : 0 < W ∧ W < 4096 ∧ W % 16 = 0) (c : Prog isa) :
    withScrubG W (List.range (W / 16)) c = .seq c (scrubTailG W (List.range (W / 16))) := by
  have : List.range (W / 16) ≠ [] := by simp; omega
  cases h : List.range (W / 16) with
  | nil => exact absurd h this
  | cons a l => rfl

theorem range_ok {W : Nat} : ∀ k ∈ List.range (W / 16), 16 * k + 16 ≤ W := by
  intro k hk; have := List.mem_range.mp hk; omega

open VG.AArch64.Scrub in
theorem zeroG_all {W : Nat} (hW : W % 16 = 0) {b x : Addr} (m : Mem) (h : (x - b).toNat < W) :
    zeroG b (List.range (W / 16)) m x = 0 := by
  have hin : inG b (List.range (W / 16)) x = true := by
    simp only [inG, List.any_eq_true, List.mem_range, decide_eq_true_eq]
    exact ⟨(x - b).toNat / 16, by omega, by omega, by omega⟩
  simp [zeroG, hin]

/-- The bytes outside the `W` bytes below `sp` are outside the `n ≤ W` bytes below it. -/
theorem not_below {sp x : Addr} {n W : Nat} (hn : n ≤ W) (hW : W ≤ sp.toNat)
    (h : ¬ (x - (sp - BitVec.ofNat 64 W)).toNat < W) : ¬ (below sp n).Contains x 1 := by
  intro hc
  have hs := below_sub (sp := sp) hn (by have := sp.isLt; omega) x hc
  simp only [Region.Contains] at hs
  omega

open VG.AArch64.Scrub VG.AArch64.RTaintG VG.AArch64.RTaintF in
/-- Code verified against its contract, whose frames stay within the `W`
bytes below the stack pointer (which the contract leaves it), that writes no
PSTATE.DIT and calls nothing indirectly, run by `scrubAll W rb`, returns
without secret residue with an `rb`-bit result. -/
theorem noResidue_scrubAll {c : Prog isa} {k : Contract isa} {W rb : Nat}
    (hv : Verified target c k) (hW : 0 < W ∧ W < 4096 ∧ W % 16 = 0)
    (hsp : ∀ s, k.pre s → W ≤ s.sp.toNat) (hd : 16 * c.aarch64Depth ≤ W)
    (hdit : c.all (fun i => !i.writesDit) = true) (hni : noIcall c = true)
    (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) :
    NoResidue (scrubAll W rb c) k rb := by
  intro s₁ s₂ t₁ t₂ s₁'' s₂'' h₁ h₂ hp ho hu e₁ e₂
  unfold scrubAll at e₁ e₂
  rw [withScrubG_range hW] at e₁ e₂
  -- One run: the code, the clearing, the result's fix and the tail.
  have run : ∀ s t s'', k.pre s → Exec isa (.seq (withRet rb (.seq c (.block clearsAll)))
      (scrubTailG W (List.range (W / 16)))) s t s'' →
      ∃ (t' : List Leak) (u : State) (g : Reg → BitVec 64), Exec isa c s t' u ∧ abiPreserved s u ∧
        (∀ q, q ≠ .x0 → g q = (cleared u).gpr q) ∧ g .x0 >>> rb = (0 : BitVec 64) ∧ TailRunG W (List.range (W / 16)) { cleared u with gpr := g } s'' := by
    intro s t s'' hs e
    obtain ⟨t', u, f, ha, -⟩ := hv.1 s hs
    cases e with
    | seq ea eb =>
    cases ea with
    | seq ea eb' =>
    cases ea with
    | seq ec ecl =>
    obtain ⟨-, rfl⟩ := Exec.det f ec
    cases ecl with
    | block hb =>
    rw [clearsAll_run] at hb
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hb)
    cases eb' with
    | block hb' =>
    obtain ⟨g, hg, hgq, hg0, -⟩ := retFix_hi hrb (cleared u)
    rw [hg] at hb'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hb')
    obtain ⟨u', x, tr⟩ := tailG_run hW range_ok { cleared u with gpr := g }
      (by show W ≤ u.sp.toNat; rw [ha.2.1]; exact hsp s hs)
    obtain ⟨-, rfl⟩ := Exec.det eb x
    exact ⟨t', u, g, f, ha, hgq, hg0, tr⟩
  obtain ⟨t₁', u₁, g₁, f₁, ha₁, hgq₁, hg0₁, tr₁⟩ := run s₁ t₁ s₁'' h₁ e₁
  obtain ⟨t₂', u₂, g₂, f₂, ha₂, hgq₂, hg0₂, tr₂⟩ := run s₂ t₂ s₂'' h₂ e₂
  obtain ⟨hrd, hwr, hg, -, hsp0, hc, hn, hz, hvf, hdi, hvv, hm⟩ := ho
  obtain ⟨hrd₁, hwr₁, hsp₁⟩ := Exec.rdwr f₁
  obtain ⟨hrd₂, hwr₂, hsp₂⟩ := Exec.rdwr f₂
  have hU : u₁.unknowns = u₂.unknowns :=
    (Exec.unknowns_agree hni f₁ [] [] f₂ hu
      (by rw [List.append_nil, List.append_nil]; exact hv.2.1 _ _ _ _ _ _ h₁ h₂ hp f₁ f₂)).2
  have hspu : u₁.sp = u₂.sp := by rw [hsp₁, hsp₂, hsp0]
  refine ⟨by rw [tr₁.rd, tr₂.rd]; exact hrd₁.trans (hrd.trans hrd₂.symm),
    by rw [tr₁.wr, tr₂.wr]; exact hwr₁.trans (hwr.trans hwr₂.symm), fun q hq0 => ?_, ?_,
    by rw [tr₁.sp, tr₂.sp]; exact hspu, by rw [tr₁.c, tr₂.c]; rfl, by rw [tr₁.nf, tr₂.nf]; rfl,
    by rw [tr₁.zf, tr₂.zf]; rfl, by rw [tr₁.vf, tr₂.vf]; rfl,
    by rw [tr₁.dit, tr₂.dit]; exact (Exec.dit hdit f₁).trans (hdi.trans (Exec.dit hdit f₂).symm), ?_, ?_⟩
  · rw [tr₁.gpr, tr₂.gpr]
    by_cases h9 : q = .x9
    · simp only [h9, ↓reduceIte]; show u₁.sp - _ = u₂.sp - _; rw [hspu]
    · simp only [h9, ↓reduceIte, hgq₁ q hq0, hgq₂ q hq0, cleared]
      by_cases hq : q ∈ allGprs
      · simp [hq]
      · simp only [hq, ↓reduceIte]
        have := preserved_of hq0 hq
        rw [ha₁.1 q this, ha₂.1 q this]; exact hg q hq0
  · rw [tr₁.gpr, tr₂.gpr]
    simp only [reduceCtorEq, ↓reduceIte, hg0₁, hg0₂]
  · rw [tr₁.v, tr₂.v]
    funext w
    by_cases h31 : w = .v31
    · simp [h31]
    · simp only [h31, ↓reduceIte, cleared]
      by_cases hh : w ∈ hiVecs
      · simp only [hh, ↓reduceIte]
        apply setLane_hi0
        rw [ha₁.2.2 w (preservedV_of hh), ha₂.2.2 w (preservedV_of hh), hvv]
      · simp [hh, vreg_cover w hh]
  · intro x hx
    rw [tr₁.rd, tr₁.wr] at hx
    change ∀ r ∈ u₁.rd ++ u₁.wr, ¬ r.Contains x 1 at hx
    rw [tr₁.mem, tr₂.mem]
    show lose (zeroG (u₁.sp - _) _ u₁.mem) (u₁.sp - _) W u₁.unknowns x =
      lose (zeroG (u₂.sp - _) _ u₂.mem) (u₂.sp - _) W u₂.unknowns x
    rw [← hspu, ← hU]
    by_cases hin : (x - (u₁.sp - BitVec.ofNat 64 W)).toNat < W
    · exact lose_agree (by rw [zeroG_all hW.2.2 _ hin, zeroG_all hW.2.2 _ hin])
    · rw [lose_out hin, lose_out hin, zeroG_out range_ok _ hin, zeroG_out range_ok _ hin]
      have hd64 : 16 * c.aarch64Depth < 2 ^ 64 := by omega
      have hout : ∀ (s u : State), u.sp = s.sp → u.wr = s.wr → W ≤ s.sp.toNat →
          Frame (s.wr ++ [below s.sp (16 * c.aarch64Depth)]) s.mem u.mem →
          (∀ r ∈ s.wr, ¬ r.Contains x 1) → ¬ (x - (u.sp - BitVec.ofNat 64 W)).toNat < W → u.mem x = s.mem x := by
        intro s u hsp' _ hWs hf hw hn
        refine hf x fun r hr => ?_
        rcases List.mem_append.mp hr with hr | hr
        · exact hw r hr
        · simp only [List.mem_singleton] at hr; subst hr
          rw [hsp'] at hn
          exact not_below hd hWs hn
      rw [hrd₁, hwr₁] at hx
      have hx₂ : ∀ r ∈ s₂.wr, ¬ r.Contains x 1 := fun r hr => hx r (List.mem_append_right _ (hwr ▸ hr))
      rw [hout s₁ u₁ hsp₁ hwr₁ (hsp s₁ h₁) (Exec.frameSp f₁ hd64)
          (fun r hr => hx r (List.mem_append_right _ hr)) hin,
        hout s₂ u₂ hsp₂ hwr₂ (hsp s₂ h₂) (Exec.frameSp f₂ hd64) hx₂ (by rw [← hspu]; exact hin)]
      exact hm x hx

/-! ## Keeping the code verified -/

theorem setLane_lo (x : BitVec 128) : (setLane x 64 1 0).extractLsb' 0 64 = x.extractLsb' 0 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi' : i < 128 := by omega
  simp [setLane, hi, hi']
  have hm : (18446744073709551615#128).getLsbD i = true := by
    rw [BitVec.getLsbD_ofNat, show (18446744073709551615 : Nat) = 2 ^ 64 - 1 by decide,
      Nat.testBit_two_pow_sub_one]
    simp [hi, hi']
  simp [hm]

/-- What `Verified.scrubAll` needs of a contract: room for the `W` bytes below
the stack pointer, a postcondition that reads neither them, nor any register
but the low `rb` bits of `x0`, and a public stack pointer. -/
structure ScrubAllOk (k : Contract isa) (W rb : Nat) : Prop where
  sp : ∀ s, k.pre s → W ≤ s.sp.toNat
  post : ∀ s u u', k.pre s → k.post s u →
    (∀ a, ¬ (a - (s.sp - BitVec.ofNat 64 W)).toNat < W → u'.mem a = u.mem a) →
    (u'.gpr .x0).setWidth rb = (u.gpr .x0).setWidth rb → k.post s u'
  pub : ∀ s₁ s₂, k.pub s₁ s₂ → s₁.sp = s₂.sp

open VG.AArch64.Scrub VG.AArch64.RTaintG VG.AArch64.RTaintF in
theorem Verified.scrubAll {c : Prog isa} {k : Contract isa} {W rb : Nat} (h : Verified target c k)
    (hW : 0 < W ∧ W < 4096 ∧ W % 16 = 0) (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) (hk : ScrubAllOk k W rb) :
    Verified target (scrubAll W rb c) k := by
  obtain ⟨hcor, hct, hsat⟩ := h
  have hrun : ∀ s, k.pre s → ∃ t u g u'',
      Exec isa c s t u ∧ abiPreserved s u ∧ k.post s u ∧
      execBlock isa (retFix rb) (cleared u) = some ({ cleared u with gpr := g }, []) ∧
      (∀ q, q ≠ .x0 → g q = (cleared u).gpr q) ∧ (g .x0).setWidth rb = ((cleared u).gpr .x0).setWidth rb ∧
      Exec isa (scrubTailG W (List.range (W / 16))) { cleared u with gpr := g }
        (tailTraceG u.sp W (List.range (W / 16))) u'' ∧
      TailRunG W (List.range (W / 16)) { cleared u with gpr := g } u'' := by
    intro s hs
    obtain ⟨t, u, he, ha, hq⟩ := hcor s hs
    obtain ⟨g, hg, hgq, -, hgx⟩ := retFix_hi hrb (cleared u)
    obtain ⟨u'', ex, tr⟩ := tailG_run hW range_ok { cleared u with gpr := g }
      (by show W ≤ u.sp.toNat; rw [ha.2.1]; exact hk.sp s hs)
    exact ⟨t, u, g, u'', he, ha, hq, hg, hgq, hgx, ex, tr⟩
  have hx0 : Reg.x0 ∉ allGprs := by decide
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, u, g, u'', he, ha, hq, hg, hgq, hgx, ex, tr⟩ := hrun s hs
    refine ⟨((t ++ []) ++ []) ++ tailTraceG u.sp W (List.range (W / 16)), u'', ?_,
      ⟨fun q hq' => ?_, by rw [tr.sp]; exact ha.2.1, fun w hw => ?_⟩, ?_⟩
    · unfold VG.Impl.Residue.AArch64.scrubAll
      rw [withScrubG_range hW]
      exact Exec.seq (Exec.seq (Exec.seq he (Exec.block (clearsAll_run u))) (Exec.block hg)) ex
    · have h9 : q ≠ .x9 := by rintro rfl; simp [preserved] at hq'
      have h0 : q ≠ .x0 := by rintro rfl; simp [preserved] at hq'
      have hng : q ∉ allGprs := by cases q <;> simp_all [preserved, allGprs]
      rw [tr.gpr]; simp only [h9, ↓reduceIte, hgq q h0, cleared, hng]; exact ha.1 q hq'
    · have h31 : w ≠ .v31 := by rintro rfl; simp [preservedV] at hw
      have hh : w ∈ hiVecs := by cases w <;> simp_all [preservedV, hiVecs]
      rw [tr.v]; simp only [h31, ↓reduceIte, cleared, hh, setLane_lo]; exact ha.2.2 w hw
    · refine hk.post s u u'' hs hq (fun a ha' => ?_) ?_
      · have ha'' : ¬ (a - (u.sp - BitVec.ofNat 64 W)).toNat < W := by rw [ha.2.1]; exact ha'
        rw [tr.mem]
        show lose (zeroG (u.sp - BitVec.ofNat 64 W) _ u.mem) (u.sp - BitVec.ofNat 64 W) W _ a = u.mem a
        rw [lose_out ha'', zeroG_out range_ok _ ha'']
      · rw [tr.gpr]
        simp only [reduceCtorEq, ↓reduceIte]
        rw [hgx]
        simp [cleared, hx0]
  · unfold VG.Impl.Residue.AArch64.scrubAll at e₁ e₂
    rw [withScrubG_range hW] at e₁ e₂
    cases e₁ with
    | seq a₁ b₁ =>
    cases e₂ with
    | seq a₂ b₂ =>
    cases a₁ with
    | seq a₁ r₁ =>
    cases a₂ with
    | seq a₂ r₂ =>
    cases a₁ with
    | seq c₁ l₁ =>
    cases a₂ with
    | seq c₂ l₂ =>
    obtain ⟨_, u₁, g₁, _, f₁, p₁, -, hg₁, -, -, x₁, -⟩ := hrun s₁ h₁
    obtain ⟨_, u₂, g₂, _, f₂, p₂, -, hg₂, -, -, x₂, -⟩ := hrun s₂ h₂
    obtain ⟨rfl, rfl⟩ := Exec.det c₁ f₁
    obtain ⟨rfl, rfl⟩ := Exec.det c₂ f₂
    cases l₁ with
    | block hl₁ =>
    cases l₂ with
    | block hl₂ =>
    rw [clearsAll_run] at hl₁ hl₂
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl₁)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl₂)
    cases r₁ with
    | block hr₁ =>
    cases r₂ with
    | block hr₂ =>
    rw [hg₁] at hr₁
    rw [hg₂] at hr₂
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr₁)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr₂)
    rw [(Exec.det b₁ x₁).1, (Exec.det b₂ x₂).1, p₁.2.1, p₂.2.1,
      hct _ _ _ _ _ _ h₁ h₂ hp c₁ c₂, hk.pub s₁ s₂ hp]

end VG.AArch64.ScrubAll
