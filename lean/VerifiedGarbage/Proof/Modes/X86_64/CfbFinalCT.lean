module

public import VerifiedGarbage.Proof.Modes.X86_64.CfbFinal
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Modes.X86_64.CfbFinalSteps
import VerifiedGarbage.Proof.Framework.X86_64.InlineCalls
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-!
# CFB of a message's last piece on x86-64: in constant time

`cfbFinal_rel`: two runs of `cfbFinal a whole enc` whose public arguments
agree leak the same trace. The taint analysis cannot check the whole
function at once: the inlined functions save and restore the callee-saved
registers through memory that it forgets, so the public values `cfbFinal`
keeps there (the rest's address and length) would be secret after them.
Runs are related piece by piece instead (`Eq2`, from states the correctness
proof describes in each run): the frame is pushed and popped at `rsp`, the
same in both runs; each straight-line block and the XOR loop by the taint
analysis, from the registers the correctness proof pins to the same values
in both runs; and the inlined functions by their own constant-time proofs
(`relCT_inline`).
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (movR)

/-- Two runs from `σ₁` and `σ₂`. -/
abbrev Eq2 (σ₁ σ₂ : State) (a b : State) : Prop := a = σ₁ ∧ b = σ₂

/-- Nothing is required of the final states. -/
abbrev TT (_ _ : State) : Prop := True

/-- Then: the next piece, from the states the correctness proofs describe. -/
theorem rel_seq {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- Code the taint analysis checks, from registers the two runs agree on. -/
theorem rel_regs {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r)
    (hc : ∃ hc, (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa (Eq2 σ₁ σ₂) c TT := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s₁ s₂ h => by
    obtain ⟨rfl, rfl⟩ := h; exact Taint.agree_ofRegs hr) hc

/-- An empty block. -/
theorem rel_skip {σ₁ σ₂ : State} : RelCT isa (Eq2 σ₁ σ₂) (.block []) TT := by
  intro x y t₁ t₂ x' y' _ e₁ e₂
  cases e₁ with
  | block h₁ =>
    cases e₂ with
    | block h₂ =>
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
      obtain ⟨rfl, rfl⟩ := h₁; obtain ⟨rfl, rfl⟩ := h₂
      exact ⟨rfl, trivial⟩

/-- A frame pushed at the same `rsp` in both runs. -/
theorem rel_frame {rs : List Reg} {r : Reg} {k : Nat} {body : Prog isa} {σ₁ σ₂ : State}
    (hsp : σ₁.gpr .rsp = σ₂.gpr .rsp) (hb : RelCT isa (Eq2 (pushed rs σ₁) (pushed rs σ₂)) body TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.frame (.push rs) body (.pop r k)) TT :=
  RelCT.frame (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact hsp)
    (hb.mono (fun _ _ ⟨s₁, s₂, ⟨e₁, e₂⟩, hx, hy⟩ => by subst e₁ e₂; exact ⟨hx, hy⟩) fun _ _ h => h)

/-- Constant time, from runs related from any two states the precondition
holds in with the same public data. -/
theorem ct_of {pre : State → Prop} {pub : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, pre σ₁ → pre σ₂ → pub σ₁ σ₂ → RelCT isa (Eq2 σ₁ σ₂) c TT) : ConstantTime isa pre pub c :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hp e₁ e₂ => (h s₁ s₂ h₁ h₂ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- A call of code verified against `k` and constant time under it is
constant time under `calledK k`. -/
theorem called_ct {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) : ConstantTime isa (calledK k).pre (calledK k).pub (.call n c) :=
  ct_of fun σ₁ σ₂ p₁ p₂ hq => RelCT.callEx hv hct fun x₁ x₂ ⟨e₁, e₂⟩ => by
    subst e₁ e₂
    exact ⟨x₁.rd, x₁.wr, x₂.rd, x₂.wr, p₁.1, p₂.1, hq.1, Covers.refl _, Covers.refl _, Covers.refl _,
      Covers.refl _, hq.2⟩

/-- Inlined verified code, constant time from its contract, narrowed in each
run to regions the run's permit. -/
theorem rel_inline {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {u₁ u₂ : State} {r₁ w₁ r₂ w₂ : List Region}
    (p₁ : k.pre (u₁.withRegions r₁ w₁)) (p₂ : k.pre (u₂.withRegions r₂ w₂))
    (hp : k.pub (u₁.withRegions r₁ w₁) (u₂.withRegions r₂ w₂))
    (c₁ : Covers (r₁ ++ w₁) (u₁.rd ++ u₁.wr)) (cw₁ : Covers w₁ u₁.wr)
    (c₂ : Covers (r₂ ++ w₂) (u₂.rd ++ u₂.wr)) (cw₂ : Covers w₂ u₂.wr) :
    RelCT isa (Eq2 u₁ u₂) c TT :=
  regionModel.relCT_inline (c := c) (Pre := k.pre) (Post := k.post) (Pub := k.pub)
    (fun s hs => let ⟨t, s', e, _, p⟩ := hv s hs; ⟨t, s', e, p⟩) hct fun x₁ x₂ ⟨e₁, e₂⟩ => by
      subst e₁ e₂; exact ⟨_, _, _, _, p₁, p₂, hp, c₁, cw₁, c₂, cw₂⟩

/-- The data's address and length in `s₀`'s arguments. -/
abbrev dataOf (a : FinalArgs) (s₀ : State) : Addr := s₀.gpr (a.arg a.dataIx)
abbrev lenOf (a : FinalArgs) (s₀ : State) : Nat := (s₀.gpr (a.arg a.lenIx)).toNat

/-- What `cfbFinal_wp` asks of a state `s₀`, for the inlined functions'
contracts `kW` and `kE` narrowed to `rdW s₀`, `wrW s₀` and `rdE s₀`,
`wrE s₀`. -/
structure FinalHyps (a : FinalArgs) (whole : Prog isa) (kW kE : Contract isa)
    (rdW wrW rdE wrE : State → List Region) (s₀ : State) : Prop where
  h80 : 80 ≤ (s₀.gpr .rsp).toNat
  hwD : (⟨dataOf a s₀, lenOf a s₀⟩ : Region) ∈ s₀.wr
  hfitD : (dataOf a s₀).toNat + lenOf a s₀ ≤ 2 ^ 64
  hDF : Region.Disjoint ⟨dataOf a s₀, lenOf a s₀⟩ (frameRegion s₀)
  preW : ∀ u, Call₁ a s₀ (lenOf a s₀) u →
    kW.pre (u.withRegions (rdW s₀) (wrW s₀)) ∧ Covers (rdW s₀ ++ wrW s₀) (u.rd ++ u.wr) ∧ Covers (wrW s₀) u.wr
  slotsW : ∀ r ∈ wrW s₀, r.Disjoint (slotsRegion s₀)
  preE : ∀ u₁' v u, After₁ a s₀ (lenOf a s₀) kW (rdW s₀) (wrW s₀) whole.x86_64Depth u₁' → v.mem = u₁'.mem →
    v.rd = u₁'.rd → v.wr = u₁'.wr → Call₂ a s₀ v u →
    kE.pre (u.withRegions (rdE s₀) (wrE s₀)) ∧ Covers (rdE s₀ ++ wrE s₀) (u.rd ++ u.wr) ∧ Covers (wrE s₀) u.wr
  slotsE : ∀ r ∈ wrE s₀, r.Disjoint (slotsRegion s₀)

theorem lenOf_eq (a : FinalArgs) (s₀ : State) : s₀.gpr (a.arg a.lenIx) = BitVec.ofNat 64 (lenOf a s₀) :=
  ((BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)).symm

/-- `cfbFinal`'s pieces between the inlined functions, as the taint analysis
checks them: `entry ++ toBlocks` and `rest`, which access no memory; the
second function's arguments, from `rsp`; and, after it, the XOR loop and the
wipes, from `rsp` and the registers that hold the rest's address and
length; and `exit`, from `rsp`. -/
structure FinalTaint (a : FinalArgs) : Prop where
  entry : ∃ hc, (taint.check (Taint.ofRegs []) (.block (a.entry ++ a.toBlocks)) hc).isSome = true
  rest : ∃ hc, (taint.check (Taint.ofRegs []) (.block a.rest) hc).isSome = true
  setup : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block (a.zeroBlock ++ a.oneBlock)) hc).isSome = true
  tail : ∃ hc, (taint.check (Taint.ofRegs [.rsp, FinalArgs.saved a.dataIx, FinalArgs.saved a.lenIx])
    (.seq (.block [.mov .rax (.reg .rsp), .alu .add .rax (.imm 8)])
      (.seq (.loop (.block a.xorByte) .ne) (.block a.zeroBlock))) hc).isSome = true
  exit : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block FinalArgs.exit) hc).isSome = true

/-- `cfbFinal a whole enc` is constant time, for inlined functions constant
time from their contracts, where `P`'s states meet `cfbFinal_wp`'s
hypotheses (`FinalHyps`) and `Pub` pins `rsp` and the arguments, from which
the inlined functions' public data follows (`pubW`, `pubE`). -/
theorem cfbFinal_ct {a : FinalArgs} (ha : FinalOk a) {whole enc : Prog isa} {kW kE : Contract isa}
    (hW : ∀ s, kW.pre s → ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ kW.post s s')
    (hE : ∀ s, kE.pre s → ∃ t s', Exec isa enc s t s' ∧ abiPreserved s s' ∧ kE.post s s')
    (spW : SpSafe whole) (spE : SpSafe enc) (dW : whole.x86_64Depth + 80 ≤ 2 ^ 64)
    (dE : enc.x86_64Depth + 80 ≤ 2 ^ 64)
    (cW : ConstantTime isa kW.pre kW.pub whole) (cE : ConstantTime isa kE.pre kE.pub enc) (ht : FinalTaint a)
    {rdW wrW rdE wrE : State → List Region} {P : State → Prop} {Pub : State → State → Prop}
    (hP : ∀ s, P s → FinalHyps a whole kW kE rdW wrW rdE wrE s)
    (hpub : ∀ s₁ s₂, P s₁ → P s₂ → Pub s₁ s₂ →
      s₁.gpr .rsp = s₂.gpr .rsp ∧ ∀ i < a.regs.length, s₁.gpr (a.arg i) = s₂.gpr (a.arg i))
    (pubW : ∀ s₁ s₂ u₁ u₂, P s₁ → P s₂ → Pub s₁ s₂ → Call₁ a s₁ (lenOf a s₁) u₁ → Call₁ a s₂ (lenOf a s₂) u₂ →
      kW.pub (u₁.withRegions (rdW s₁) (wrW s₁)) (u₂.withRegions (rdW s₂) (wrW s₂)))
    (pubE : ∀ s₁ s₂ v₁ v₂ u₁ u₂, P s₁ → P s₂ → Pub s₁ s₂ → Call₂ a s₁ v₁ u₁ → Call₂ a s₂ v₂ u₂ →
      kE.pub (u₁.withRegions (rdE s₁) (wrE s₁)) (u₂.withRegions (rdE s₂) (wrE s₂))) :
    ConstantTime isa P Pub (cfbFinal a whole enc) := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have h₁ := hP σ₁ p₁
  have h₂ := hP σ₂ p₂
  obtain ⟨hsp, hargs⟩ := hpub σ₁ σ₂ p₁ p₂ hq
  have hlen6 := ha.length
  have dD6 : a.dataIx < 6 := by have := ha.data; omega
  have dL6 : a.lenIx < 6 := by have := ha.len; omega
  have hlg1 : 1 ≤ a.lg := by rcases ha.lg with h | h <;> omega
  have hlg2 : a.lg ≤ 63 := by rcases ha.lg with h | h <;> omega
  have hlen : lenOf a σ₁ = lenOf a σ₂ := by simp only [lenOf, hargs _ ha.len]
  have hDa : dataOf a σ₁ = dataOf a σ₂ := hargs _ ha.data
  have hfs : frameSp σ₁ = frameSp σ₂ := by simp only [frameSp, hsp]
  have hlt : ∀ σ : State, lenOf a σ < 2 ^ 64 := fun σ => (σ.gpr (a.arg a.lenIx)).isLt
  unfold cfbFinal
  refine rel_frame hsp ?_
  -- `entry ++ toBlocks`.
  obtain ⟨u₁, e₁, hu₁⟩ := entry_ok ha (lenOf_eq a σ₁) (hlt σ₁) h₁.h80
  obtain ⟨u₂, e₂, hu₂⟩ := entry_ok ha (lenOf_eq a σ₂) (hlt σ₂) h₂.h80
  have mx₁ : u₁.mxcsr = σ₁.mxcsr := by rw [runBlock_mxcsr _ _ _ (entry_mxcsr a) e₁, pushed_mxcsr]
  have mx₂ : u₂.mxcsr = σ₂.mxcsr := by rw [runBlock_mxcsr _ _ _ (entry_mxcsr a) e₂, pushed_mxcsr]
  refine rel_seq (F₁ := (· = u₁)) (F₂ := (· = u₂)) (rel_regs [] (fun _ h => absurd h List.not_mem_nil) ht.entry)
    (WP.of_runBlock ⟨u₁, e₁, rfl⟩) (WP.of_runBlock ⟨u₂, e₂, rfl⟩) fun τ₁ τ₂ hτ₁ hτ₂ => ?_
  subst τ₁ τ₂
  -- The first function.
  obtain ⟨pW₁, cW₁, wW₁⟩ := h₁.preW _ hu₁
  obtain ⟨pW₂, cW₂, wW₂⟩ := h₂.preW _ hu₂
  refine rel_seq (rel_inline hW cW pW₁ pW₂ (pubW _ _ _ _ p₁ p₂ hq hu₁ hu₂) cW₁ wW₁ cW₂ wW₂)
    (whole_wp ha hW spW dW h₁.slotsW hu₁ mx₁ pW₁ cW₁ wW₁) (whole_wp ha hW spW dW h₂.slotsW hu₂ mx₂ pW₂ cW₂ wW₂)
    fun x₁ x₂ hA₁ hA₂ => ?_
  -- `rest`.
  have dl : FinalArgs.saved a.dataIx ≠ FinalArgs.saved a.lenIx := fun h => ha.dl (saved_inj _ dD6 _ dL6 h)
  obtain ⟨v₁, ev₁, vD₁, vL₁, vz₁, vo₁, vm₁, vrd₁, vwr₁⟩ := rest_ok x₁ hlg1 hlg2 dl (saved_scratch _ dD6).1
    (saved_scratch _ dL6).1 (hA₁.saved _ ha.data) (by rw [hA₁.saved _ ha.len]; exact lenOf_eq a σ₁) (hlt σ₁)
  obtain ⟨v₂, ev₂, vD₂, vL₂, vz₂, vo₂, vm₂, vrd₂, vwr₂⟩ := rest_ok x₂ hlg1 hlg2 dl (saved_scratch _ dD6).1
    (saved_scratch _ dL6).1 (hA₂.saved _ ha.data) (by rw [hA₂.saved _ ha.len]; exact lenOf_eq a σ₂) (hlt σ₂)
  have hblk : a.blk = 2 ^ a.lg := rfl
  rw [← hblk] at vD₁ vL₁ vz₁ vD₂ vL₂ vz₂
  refine rel_seq (F₁ := (· = v₁)) (F₂ := (· = v₂)) (rel_regs [] (fun _ h => absurd h List.not_mem_nil) ht.rest)
    (WP.of_runBlock ⟨v₁, ev₁, rfl⟩) (WP.of_runBlock ⟨v₂, ev₂, rfl⟩) fun y₁ y₂ hy₁ hy₂ => ?_
  subst y₁ y₂
  have vsp₁ : v₁.gpr .rsp = frameSp σ₁ := by
    rw [vo₁ _ (by decide) (saved_ne_rsp _ dD6).symm (saved_ne_rsp _ dL6).symm, hA₁.rsp]
  have vsp₂ : v₂.gpr .rsp = frameSp σ₂ := by
    rw [vo₂ _ (by decide) (saved_ne_rsp _ dD6).symm (saved_ne_rsp _ dL6).symm, hA₂.rsp]
  have vS : ∀ {σ x v : State}, After₁ a σ (lenOf a σ) kW (rdW σ) (wrW σ) whole.x86_64Depth x →
      (∀ y, y ≠ .rax → y ≠ FinalArgs.saved a.dataIx → y ≠ FinalArgs.saved a.lenIx → v.gpr y = x.gpr y) →
      ∀ i < a.regs.length, i ≠ a.lenIx → i ≠ a.dataIx → v.gpr (FinalArgs.saved i) = σ.gpr (a.arg i) :=
    fun hA vo i hi h1 h2 => by
      rw [vo _ (saved_scratch i (by omega)).1 (fun e' => h2 (saved_inj _ (by omega) _ dD6 e'))
        (fun e' => h1 (saved_inj _ (by omega) _ dL6 e')), hA.saved i hi]
  have hfr₁ : frameRegion σ₁ ∈ v₁.wr := by rw [vwr₁, hA₁.wr]; exact List.mem_cons_self
  have hfr₂ : frameRegion σ₂ ∈ v₂.wr := by rw [vwr₂, hA₂.wr]; exact List.mem_cons_self
  -- After the branch, before `exit`: the frame's `rsp`.
  have ite_wp : ∀ {σ x v : State}, FinalHyps a whole kW kE rdW wrW rdE wrE σ →
      After₁ a σ (lenOf a σ) kW (rdW σ) (wrW σ) whole.x86_64Depth x →
      v.gpr (FinalArgs.saved a.dataIx) = restAddr a (dataOf a σ) (lenOf a σ) →
      v.gpr (FinalArgs.saved a.lenIx) = BitVec.ofNat 64 (lenOf a σ % a.blk) →
      v.zf = some (decide (lenOf a σ % a.blk = 0)) →
      (∀ y, y ≠ .rax → y ≠ FinalArgs.saved a.dataIx → y ≠ FinalArgs.saved a.lenIx → v.gpr y = x.gpr y) →
      v.mem = x.mem → v.rd = x.rd → v.wr = x.wr → v.gpr .rsp = frameSp σ →
      WP isa (.ite .e (.block []) (a.tail enc)) v fun w => w.gpr .rsp = frameSp σ :=
    by
    intro σ x v h hA vD vL vz vo vm vrd vwr vsp
    exact WP.ite (decide (lenOf a σ % a.blk = 0)) (by simp [X86_64.eval, vz])
      (fun _ => WP.block_nil vsp) (fun hb => by
        have hr : lenOf a σ % a.blk ≠ 0 := by simpa using hb
        exact WP.mono (tail_wp ha hE spE dE hr h.hwD h.hfitD h.hDF h.h80 vD vL (vS hA vo) vsp
          (by rw [vrd, hA.rd]) (by rw [vwr, hA.wr]) (fun j hj => by rw [vm, hA.slots j hj])
          (fun u hu => h.preE x v u hA vm vrd vwr hu) h.slotsE) fun w d => d.rsp)
  refine rel_seq (RelCT.ite (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; simp [X86_64.eval, vz₁, vz₂, hlen]) ?_ ?_)
    (ite_wp h₁ hA₁ vD₁ vL₁ vz₁ vo₁ vm₁ vrd₁ vwr₁ vsp₁) (ite_wp h₂ hA₂ vD₂ vL₂ vz₂ vo₂ vm₂ vrd₂ vwr₂ vsp₂)
    fun w₁ w₂ hw₁ hw₂ => rel_regs [.rsp] (by simp [hw₁, hw₂, hfs]) ht.exit
  · exact rel_skip.mono (fun _ _ h => h.1) fun _ _ h => h
  · -- The tail.
    refine RelCT.mono (P := Eq2 v₁ v₂) ?_ (fun _ _ h => h.1) fun _ _ h => h
    obtain ⟨z₁, ez₁, hz₁, hsav₁⟩ := tailSetup_ok ha (vS hA₁ vo₁) vsp₁ hfr₁
    obtain ⟨z₂, ez₂, hz₂, hsav₂⟩ := tailSetup_ok ha (vS hA₂ vo₂) vsp₂ hfr₂
    refine rel_seq (F₁ := (· = z₁)) (F₂ := (· = z₂)) (rel_regs [.rsp] (by simp [vsp₁, vsp₂, hfs]) ht.setup)
      (WP.of_runBlock ⟨z₁, ez₁, rfl⟩) (WP.of_runBlock ⟨z₂, ez₂, rfl⟩) fun t₁ t₂ ht₁ ht₂ => ?_
    subst t₁ t₂
    obtain ⟨pE₁, cE₁, wE₁⟩ := h₁.preE x₁ v₁ z₁ hA₁ vm₁ vrd₁ vwr₁ hz₁
    obtain ⟨pE₂, cE₂, wE₂⟩ := h₂.preE x₂ v₂ z₂ hA₂ vm₂ vrd₂ vwr₂ hz₂
    have pins : ∀ {σ v z : State}, Call₂ a σ v z → (∀ i < 6, z.gpr (FinalArgs.saved i) = v.gpr (FinalArgs.saved i)) →
        v.gpr (FinalArgs.saved a.dataIx) = restAddr a (dataOf a σ) (lenOf a σ) →
        v.gpr (FinalArgs.saved a.lenIx) = BitVec.ofNat 64 (lenOf a σ % a.blk) →
        kE.pre (z.withRegions (rdE σ) (wrE σ)) → Covers (rdE σ ++ wrE σ) (z.rd ++ z.wr) → Covers (wrE σ) z.wr →
        WP isa enc z fun y => y.gpr .rsp = frameSp σ ∧
          y.gpr (FinalArgs.saved a.dataIx) = restAddr a (dataOf a σ) (lenOf a σ) ∧
          y.gpr (FinalArgs.saved a.lenIx) = BitVec.ofNat 64 (lenOf a σ % a.blk) :=
      by
      intro σ v z hz hsav vD vL pE cE wE
      exact WP.inlineF hE spE (by omega) pE cE wE fun y _ _ ab _ _ _ =>
        ⟨by rw [ab.1 _ (by decide), hz.rsp], by rw [ab.1 _ (saved_mem _ dD6), hsav _ dD6, vD],
          by rw [ab.1 _ (saved_mem _ dL6), hsav _ dL6, vL]⟩
    refine rel_seq (rel_inline hE cE pE₁ pE₂ (pubE _ _ _ _ _ _ p₁ p₂ hq hz₁ hz₂) cE₁ wE₁ cE₂ wE₂)
      (pins hz₁ hsav₁ vD₁ vL₁ pE₁ cE₁ wE₁) (pins hz₂ hsav₂ vD₂ vL₂ pE₂ cE₂ wE₂) fun y₁ y₂ hy₁ hy₂ => ?_
    refine rel_regs [.rsp, FinalArgs.saved a.dataIx, FinalArgs.saved a.lenIx] ?_ ht.tail
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨by rw [hy₁.1, hy₂.1, hfs], by rw [hy₁.2.1, hy₂.2.1, hDa, hlen], by rw [hy₁.2.2, hy₂.2.2, hlen]⟩

end VG.Proof.Modes.X86_64
