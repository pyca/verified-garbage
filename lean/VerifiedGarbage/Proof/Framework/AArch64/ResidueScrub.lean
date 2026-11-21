module

public import VerifiedGarbage.Proof.Framework.AArch64.ResidueFrame
public import VerifiedGarbage.Proof.Framework.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratchConsts
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem

/-!
# What the clearing of the stack needs, after the analysis through calls and frames (AArch64)

The pieces of the residue analysis through calls and frames (`rtaintF W`,
`ResidueFrame.lean`) that the analysis of the cleared window
(`ResidueWin.lean`, `AArch64.Scrub.verifiedScrubbedSel`) builds on:

* `doneF r`: the analysis ends with the registers the calling convention
  does not preserve public (but `x9` and `v31`, which the clearing writes),
  the flags public and the result public above bit `r`; `agree_init`, where
  it starts.
* `ScrubOk k W`: what the clearing of `W` bytes below the stack pointer
  needs of a contract `k`: room for them, a postcondition that reads neither
  them nor any register but `x0`, and a public stack pointer. `scrubOk_regs`
  and `scrubOk_consts` prove it of a contract whose arguments are all in
  registers, given that its postcondition reads the memory on return only
  within the buffers.
* `Verified.withRet`: clearing the bits of `x0` above the result keeps code
  verified.
-/

@[expose] public section

namespace VG.AArch64.RTaintF

open VG.AArch64 VG.AArch64.Residue VG.AArch64.Scrub VG.Impl.Scrub.AArch64

/-- The registers the calling convention does not preserve, but `x0` and `x9`. -/
def scratchNo9 : List Reg :=
  [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

theorem mem_scratchNo9 {q : Reg} (hq : q ≠ .x0) (h9 : q ≠ .x9) (hp : q ∉ preserved) :
    q ∈ scratchNo9 := by
  cases q <;> simp_all [scratchNo9, preserved]

/-- The analysis ends at the depth it started from, with the registers the
calling convention does not preserve public but `x9`, `v31` and what it
preserves of `v8`–`v15` (their low halves), the flags public, and the result
public above bit `r`. -/
def doneF (r : Nat) (τ : T) : Bool :=
  τ.2 == some 0 &&
    scratchNo9.all (fun q => τ.1.1.1.1.1.mem q) &&
    RTaintL.vregs.all (fun v => v == .v31 || (if preservedV.contains v then
      τ.1.1.1.1.2.mem v || τ.1.1.2.2.mem v else RTaintL.vpub τ.1.1 v)) &&
    τ.1.1.1.2.1 &&
    (Nat.ble τ.1.1.1.2.2 r || Nat.ble (RTaintB.wget τ.1.2 .x0) r)

theorem outside0_ghost {s₁ s₂ : State} (h : Outside 0 s₁ s₂) : Outside 0 s₁ (ghost s₁ s₂) := by
  obtain ⟨hrd, hwr, hg, hx0, hsp, hc, hn, hz, hv, hd, hvr, hm⟩ := h
  refine ⟨hrd, hwr, hg, hx0, hsp, hc, hn, hz, hv, hd, hvr, fun x hx => ?_⟩
  exact ghost_off hrd hwr x hx

theorem agree_init {W : Nat} (hW : W < 2 ^ 64) {s₁ s₂ : State} (h : Outside 0 s₁ s₂)
    (hu : s₁.unknowns = s₂.unknowns) : Agree W (RTaintB.init, some 0) s₁ s₂ :=
  ⟨0, Or.inl rfl, ⟨RTaintL.agree_init (outside0_ghost h) hu, (fun _ h => nomatch h),
    (fun _ h => nomatch h)⟩, Nat.zero_le _, hW,
    fun x hx _ => h.2.2.2.2.2.2.2.2.2.2.2 x (by rw [h.1, h.2.1]; exact hx)⟩

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- The `W ≤ stack` bytes below the stack pointer on entry are apart from the buffers. -/
theorem scrub_disjoint (hk : (sig.words abi.ptrBits).length ≤ 8) {W : Nat} (hW : 0 < W)
    (hWs : W ≤ stack) {s : State} (hs : (sig.contract abi pre post wa stack leak).pre s) :
    ∀ b ∈ Sig.bufs sig.params (regArgs sig s), b.1.Disjoint ⟨s.sp - BitVec.ofNat 64 W, W⟩ := by
  intro b hb
  rw [pre_regs hk] at hs
  obtain ⟨-, -, -, -, hres, -, -⟩ := hs
  have hst : stackBelow s.sp stack = [⟨s.sp - BitVec.ofNat 64 stack, stack⟩] := by
    cases stack with
    | zero => omega
    | succ n => rfl
  have hr := hres ⟨s.sp - BitVec.ofNat 64 stack, stack⟩ (by rw [hst]; exact List.mem_singleton_self _)
    b (List.mem_append_left _ hb)
  exact hr.symm.sub_right (Offset.sub_below _ hWs (by omega))

/-- What the clearing of the `W` bytes (`Verified.scrubSel`) needs of a contract: room for the `W` bytes
below the stack pointer, a postcondition that reads neither them nor any
register but `x0`, and a public stack pointer. -/
structure ScrubOk (k : Contract isa) (W : Nat) : Prop where
  sp : ∀ s, k.pre s → W ≤ s.sp.toNat
  post : ∀ s u u', k.pre s → k.post s u →
    (∀ a, ¬ (a - (s.sp - BitVec.ofNat 64 W)).toNat < W → u'.mem a = u.mem a) →
    u'.gpr .x0 = u.gpr .x0 → k.post s u'
  pub : ∀ s₁ s₂, k.pub s₁ s₂ → s₁.sp = s₂.sp

/-- `ScrubOk` of a contract whose arguments are all in registers, whose
stack holds the `W` bytes and whose postcondition reads the memory on return
only within the buffers. -/
theorem scrubOk_regs (hk : (sig.words abi.ptrBits).length ≤ 8) {W : Nat} (hW : 0 < W)
    (hWs : W ≤ stack)
    (hpost : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r) :
    ScrubOk (sig.contract abi pre post wa stack leak) W where
  sp s hs := by
    rw [pre_regs hk] at hs
    rcases hs.1 with h0 | h0 <;> omega
  post s u u' hs hq hm hx := by
    rw [post_regs hk] at hq ⊢
    rw [hx]
    refine hpost _ _ _ _ _ (regArgs_length sig s hk) (fun b hb a ha' => ?_) hq
    have hd := scrub_disjoint hk hW hWs hs b hb a ha'
    exact (hm a fun hlt => hd (show (a - (s.sp - BitVec.ofNat 64 W)).toNat + 1 ≤ W by omega)).symm
  pub s₁ s₂ hp := ((pub_regs hk).mp hp).1.1.1

/-- `ScrubOk` under the calling convention with tables of constants
(`abi.withConsts`), from that without them. -/
theorem scrubOk_consts {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    (hk : (sig.words abi.ptrBits).length ≤ 8) {W : Nat} (hW : 0 < W) (hWs : W ≤ stack)
    (hpost : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r) :
    ScrubOk (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa stack leak) W where
  sp s hs := (scrubOk_regs (pre := pre) (post := post) (wa := wa) (leak := leak) hk hW hWs hpost).sp
    (stripConsts (c₀ :: cs) s) (pre_consts.mp hs).1
  post s u u' hs hq hm hx := by
    have e : ∀ v, (sig.contract abi pre post wa stack leak).post s v ↔
        (sig.contract abi pre post wa stack leak).post (stripConsts (c₀ :: cs) s) v := fun v => by
      rw [post_regs hk, post_regs hk]; rfl
    exact post_consts.mpr ((e u').mpr
      ((scrubOk_regs (pre := pre) (post := post) (wa := wa) (leak := leak) hk hW hWs hpost).post
        _ u u' (pre_consts.mp hs).1 ((e u).mp (post_consts.mp hq)) hm hx))
  pub s₁ s₂ hp := (scrubOk_regs (pre := pre) (post := post) (wa := wa) (leak := leak) hk hW hWs
    hpost).pub s₁ s₂ (pub_consts.mp hp).1

end

/-! ## The result's upper bits -/

theorem retFix_run (rb : Nat) (s : State) : ∃ g, execBlock isa (retFix rb) s =
    some ({ s with gpr := g }, []) ∧ (∀ q, q ≠ .x0 → g q = s.gpr q) ∧
    (g .x0).setWidth rb = (s.gpr .x0).setWidth rb := by
  by_cases h0 : rb = 0
  · subst h0
    refine ⟨fun q => if q = .x0 then 0 else s.gpr q, ?_, fun q hq => by simp [hq], ?_⟩
    · simp [retFix, execBlock, isa, exec, addrs, State.write]
    · apply BitVec.eq_of_toNat_eq
      have h1 := ((((fun q => if q = .x0 then (0 : BitVec 64) else s.gpr q) .x0)).setWidth 0).isLt
      have h2 := ((s.gpr .x0).setWidth 0).isLt
      simp only [Nat.pow_zero] at h1 h2
      omega
  by_cases h32 : rb = 32
  · subst h32
    refine ⟨fun q => if q = .x0 then ((s.gpr .x0).setWidth 32 + 0).setWidth 64 else s.gpr q, ?_,
      fun q hq => by simp [hq], ?_⟩
    · simp [retFix, execBlock, isa, exec, addrs, State.write, State.read]
    · simp
  · have : retFix rb = [] := by
      unfold retFix; split <;> simp_all
    exact ⟨s.gpr, by rw [this]; rfl, fun _ _ => rfl, rfl⟩

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- Clearing what `x0` holds beyond the result keeps code verified. -/
theorem Verified.withRet {c : Prog isa}
    (h : Verified target c (sig.contract abi pre post wa stack leak)) :
    Verified target (withRet (sig.retBits abi.ptrBits) c) (sig.contract abi pre post wa stack leak) := by
  obtain ⟨hcor, hct, hsat⟩ := h
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, ha, hq⟩ := hcor s hs
    obtain ⟨g, hb, hg, hx⟩ := retFix_run (sig.retBits abi.ptrBits) s'
    refine ⟨_, _, Exec.seq he (Exec.block hb), ⟨fun q hq' => ?_, ha.2.1, ha.2.2⟩, ?_⟩
    · have : q ≠ .x0 := by rintro rfl; simp [preserved] at hq'
      show g q = s.gpr q
      rw [hg q this]; exact ha.1 q hq'
    · revert hq
      simp only [Sig.contract]
      split
      · exact id
      · intro hq
        have hr : (abi.ret { s' with gpr := g }).setWidth (sig.retBits abi.ptrBits) =
            (abi.ret s').setWidth (sig.retBits abi.ptrBits) := hx
        have hm : abi.mem { s' with gpr := g } = abi.mem s' := rfl
        rw [hm, hr]; exact hq
  · cases e₁ with
    | seq a₁ b₁ =>
    cases e₂ with
    | seq a₂ b₂ =>
    cases b₁ with
    | block hb₁ =>
    cases b₂ with
    | block hb₂ =>
    obtain ⟨_, hr₁, -, -⟩ := retFix_run (sig.retBits abi.ptrBits) _
    obtain ⟨_, hr₂, -, -⟩ := retFix_run (sig.retBits abi.ptrBits) _
    rw [hr₁] at hb₁; rw [hr₂] at hb₂
    cases hb₁; cases hb₂
    rw [hct _ _ _ _ _ _ h₁ h₂ hp a₁ a₂]

end

end VG.AArch64.RTaintF
