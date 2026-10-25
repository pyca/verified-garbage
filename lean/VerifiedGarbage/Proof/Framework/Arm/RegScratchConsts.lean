module

import VerifiedGarbage.Proof.Framework.Arm.RegScratchWipe
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.Arm.RegScratch
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-!
# A scratch buffer in a register, wiped after use, for code that reads tables of constants (ARMv7)

`Verified.regScratchWipedC`: `Verified.regScratchWiped` for contracts under
`abi.withConsts K`, whose readable regions end with the tables `K`. The code
runs from `narrowR s`, which keeps the readable regions of `s`, the tables'
among them: without them (`stripConsts`) it is `narrowR` of the state without
them (`stripConsts_narrowR`), which satisfies the contract under `abi`
(`pre_consts`), so the lemmas of `RegScratch.lean` apply to it. The tables lie
outside the frame, which is within the stack the contract reserves, so
`narrowR s` holds them as `s` does (`narrowR_consts`).
-/

@[expose] public section

namespace VG.Arm

open VG.Impl.StackScratch.Arm VG.Arm.FrameStack

section
variable {sig : Sig} {nm : String} {e : Elem} {n : Nat}
  {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits} {wa : Bool}
  {stack bytes words : Nat} {r : Reg} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

theorem narrowR_syms (s : State) : (narrowR e n bytes r s).syms = s.syms := rfl

theorem stripConsts_narrowR (K : List (String × List (BitVec 64))) (s : State) :
    stripConsts K (narrowR e n bytes r s) = narrowR e n bytes r (stripConsts K s) := rfl

/-- The stack below `sp` that a contract with `stack + bytes` bytes of stack
reserves, from its precondition under `abi.withConsts`. -/
theorem sp_bound_consts (hb : FitsR bytes e n) {s : State}
    (hs : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true) : stack + bytes ≤ s.sp.toNat := by
  have hs' := (pre_consts.mp hs).1
  rw [pre_arm hl] at hs'
  obtain ⟨⟨hst, -⟩, -⟩ := hs'
  simp only [stripConsts_sp] at hst
  have := hb.1
  omega_arith

/-- What the calling convention says of the tables holds in `narrowR s`, with
`stack` bytes of stack, if it does in `s` with `stack + bytes`. -/
theorem narrowR_consts {K : List (String × List (BitVec 64))} (hb : FitsR bytes e n) {s : State}
    (hsb : stack + bytes ≤ s.sp.toNat) (h : ConstsOk K (stack + bytes) s) :
    ConstsOk K stack (narrowR e n bytes r s) := by
  obtain ⟨hd, hh, ht⟩ := h
  obtain ⟨hb0, -, -, -, hb4⟩ := hb
  have hsp : State.addr (s.sp - BitVec.ofNat 32 bytes) = State.addr s.sp - BitVec.ofNat 64 bytes :=
    addr_sub' (by omega_arith)
  have htR : ∀ t ∈ constRegs K s, ∀ {a k : Nat}, a ≤ stack + bytes → stack + bytes - a + k ≤ stack + bytes →
      t.Disjoint ⟨State.addr s.sp - BitVec.ofNat 64 a, k⟩ := fun t ht' _ _ ha hk =>
    ((ht t ht').2.2 _ (reserved_below (by omega_arith) s)).sub_right (Offset.sub_below _ ha hk)
  refine ⟨hd, hh, fun t ht' => ⟨(ht t ht').1, fun q hq => ?_, fun q hq => ?_⟩⟩
  · rcases List.mem_append.mp hq with hq | hq
    · exact (ht t ht').2.1 q hq
    · simp only [List.mem_singleton] at hq; subst hq
      rw [hsp]; exact htR t ht' (by omega_arith) (by omega_arith)
  · have hq' : q ∈ stackBelow (State.addr (s.sp - BitVec.ofNat 32 bytes)) stack := hq
    rw [hsp, stackBelow_sub] at hq'
    by_cases h0 : stack = 0
    · simp [h0] at hq'
    · simp only [h0, ite_false, List.mem_singleton] at hq'; subst hq'
      exact htR t ht' (by omega_arith) (by omega_arith)

/-- The precondition under `abi.withConsts` gives the one with the buffer in
`narrowR`. -/
theorem narrowR_preC (hcl : ScratchInReg sig r) (hloc : (locs sig).all (Loc.avoids r) = true)
    (hb : FitsR bytes e n) {s : State}
    (hs : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pre s)
    (hl : Sig.noLists sig.params = true) :
    (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack leak).pre
      (narrowR e n bytes r s) := by
  obtain ⟨hs', hc⟩ := pre_consts.mp hs
  refine pre_consts.mpr ⟨?_, narrowR_consts hb (sp_bound_consts hb hs hl) hc⟩
  rw [stripConsts_narrowR]
  exact narrowR_pre hcl hloc hb hs' hl

/-- A run of the code from `narrowR s` is a run of `withRegScratch` from `s`
(`withRegScratch_run`, for any stack pointer above the frame). -/
theorem withRegScratchC_run {c : Prog isa} (hcl : ScratchInReg sig r) (hb : FitsR bytes e n)
    {s : State} (hsb : stack + bytes ≤ s.sp.toNat) {t : List Leak} {s₃ : State}
    (he : Exec isa c (narrowR e n bytes r s) t s₃) (ha : abiPreserved (narrowR e n bytes r s) s₃) :
    Exec isa (withRegScratch bytes r c) s t (popState bytes s s₃) ∧
      abiPreserved s (popState bytes s s₃) ∧ (popState bytes s s₃).mem = s₃.mem ∧
      (popState bytes s s₃).gpr = s₃.gpr := by
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hb
  have hpush : isa.push (.alloc bytes) s = some (allocState bytes s) := by
    simp only [isa, push]
    exact ite_eq_left ⟨hb0, hb1, hb2, hb3, by omega_arith⟩
  have hblk : Exec isa (.block [.addSp r 0]) (allocState bytes s) [] (regState bytes r s) :=
    .block (by simp only [execBlock, isa, exec, show (0 : Nat) < 256 by decide, ite_true,
      Option.map_some, addrs, List.map_nil, List.append_nil, regState])
  have hcov : Covers (s.wr ++ [⟨State.addr (s.sp - BitVec.ofNat 32 bytes), n * e.size⟩])
      (⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr) :=
    Covers.append_left (Covers.of_mem fun r hr => List.mem_cons_of_mem _ hr)
      (Covers.one ⟨_, List.mem_cons_self .., by
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith⟩)
  have hw := Exec.widen he (rd := s.rd) (wr := ⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr)
    (by simpa using Covers.append (Covers.refl s.rd) hcov) (by simpa using hcov)
  rw [show (narrowR e n bytes r s).withRegions s.rd
      (⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr) = regState bytes r s from rfl] at hw
  have hsp₃ : s₃.sp = s.sp - BitVec.ofNat 32 bytes := ha.2.trans (narrowR_sp s)
  have hpop : isa.pop (.free bytes) (allocState bytes s)
      (s₃.withRegions s.rd (⟨State.addr (s.sp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr)) =
      some (popState bytes s s₃) := by
    simp only [isa, pop, State.withRegions_sp, State.withRegions_wr, allocState_sp, allocState_wr,
      hsp₃, List.head?_cons, hb0, hb1, hb2, hb3, and_self, ite_true, List.tail_cons,
      BitVec.sub_add_cancel]
    rfl
  have hex := Exec.frame hpush (Exec.seq hblk hw) hpop
  simp only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] at hex
  refine ⟨hex, ⟨fun q hq => ?_, rfl⟩, rfl, rfl⟩
  have hpa : ∀ q ∈ preserved, q ∉ argRegs := by decide
  have hqr : q ≠ r := fun h => hpa q hq (h ▸ hcl.1)
  show s₃.gpr q = s.gpr q
  rw [ha.1 q hq, narrowR_gpr]
  simp only [hqr, ↓reduceIte]

/-- Code verified for a function whose last argument, in a register `r`, is a
scratch buffer, and which reads the tables `c₀ :: cs`, is verified for the
function without it (`Verified.regScratchWiped`, under
`abi.withConsts (c₀ :: cs)`). -/
theorem Verified.regScratchWipedC {c : Prog isa}
    (h : Verified target c (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack leak))
    (hcl : ScratchInReg sig r) (hloc : (locs sig).all (Loc.avoids r) = true) (hb : FitsR bytes e n)
    (hw : 4 * words ≤ n * e.size)
    (hpost : ∀ vs m m₁ m₂ ret, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ ret →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ ret)
    (hsat : ∃ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes)).pre s)
    (hl : Sig.noLists sig.params = true := by decide) :
    Verified target (withRegScratchWiped bytes r words c)
      (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak) := by
  obtain ⟨hcor, hct, -⟩ := h
  have hlen := armArgs_length sig
  -- The buffer is below the stack the contract without it reserves, so apart
  -- from its buffers.
  have hdisj : ∀ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pre s →
      ∀ b ∈ Sig.bufs sig.params (armArgs sig s),
        b.1.Disjoint ⟨State.addr (s.sp - BitVec.ofNat 32 bytes), n * e.size⟩ := by
    intro s hs b hb'
    have h0 := sp_bound_consts hb hs hl
    have hs' := (pre_consts.mp hs).1
    rw [pre_arm hl] at hs'
    obtain ⟨-, -, -, -, hres, -, -⟩ := hs'
    simp only [stripConsts_sp] at hres
    rw [allRegions, argArea_eq_nil hcl.2.1, List.append_nil] at hres
    rw [addr_sub' (by omega_arith)]
    exact (Region.Disjoint.symm (hres _ (reserved_below (by have := hb.1; omega_arith) s) b hb')).sub_right
      (Offset.sub_below _ (by omega_arith) (by have := hb.2.2.2.2; omega_arith))
  -- Every run is the code's run from `narrowR`, then the wipe.
  have hrun : ∀ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pre s →
      ∃ t s₃ s₄,
      Exec isa c (narrowR e n bytes r s) t s₃ ∧
      (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack leak).post
        (narrowR e n bytes r s) s₃ ∧
      Frame [⟨State.addr (s.sp - BitVec.ofNat 32 bytes), n * e.size⟩] s₃.mem s₄.mem ∧
      s₃.sp = s.sp - BitVec.ofNat 32 bytes ∧
      Exec isa (withRegScratchWiped bytes r words c) s (t ++ wipeTrace s₃.sp words)
        (popState bytes s s₄) ∧
      abiPreserved s (popState bytes s s₄) ∧ (popState bytes s s₄).mem = s₄.mem ∧
      (popState bytes s s₄).gpr .r0 = s₃.gpr .r0 ∧ (popState bytes s s₄).gpr .r1 = s₃.gpr .r1 := by
    intro s hs
    obtain ⟨t, s₃, he, ha, hq⟩ := hcor _ (narrowR_preC hcl hloc hb hs hl)
    have hsp₃ : s₃.sp = s.sp - BitVec.ofNat 32 bytes := ha.2.trans (narrowR_sp s)
    have hwr₃ : s₃.wr = (narrowR e n bytes r s).wr := (Exec.rdwr he).2.1
    have h0 := sp_bound_consts hb hs hl
    have hn := hb.2.2.2.2
    obtain ⟨m', hblk, hfr⟩ := wipe_run ⟨State.addr (s.sp - BitVec.ofNat 32 bytes), n * e.size⟩ s₃ words
      (by rw [hwr₃, narrowR_wr]; simp) (by have := hb.2.1; omega_arith)
      (fun k hk' => by
        rw [hsp₃, addr_add (by rw [sub_toNat' (by omega_arith)]; have := s.sp.isLt; omega_arith)]
        exact Offset.contains_base _ (by omega_arith) (by omega_arith))
    have he' := Exec.seq he (Exec.block hblk)
    have ha' : abiPreserved (narrowR e n bytes r s)
        { (s₃.setReg .r12 (s₃.sp + BitVec.ofNat 32 0)).setReg .r2 0 with mem := m' } := by
      refine ⟨fun q hq => ?_, ha.2⟩
      have h12 : q ≠ .r12 := by rintro rfl; simp [preserved] at hq
      have h2 : q ≠ .r2 := by rintro rfl; simp [preserved] at hq
      simp only [State.setReg, h12, h2, ↓reduceIte]
      exact ha.1 q hq
    obtain ⟨hex, habi, hm, hg⟩ := withRegScratchC_run hcl hb h0 he' ha'
    refine ⟨t, s₃, _, he, hq, hfr, hsp₃, hex, habi, hm, ?_, ?_⟩
    · rw [hg]; simp [State.setReg]
    · rw [hg]; simp [State.setReg]
  -- The public data in `narrowR`.
  have hpub : ∀ s₁ s₂,
      (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + bytes) leak).pub s₁ s₂ →
      (Sig.scratchContract (abi.withConsts (c₀ :: cs)) sig nm e n pre post wa stack leak).pub
        (narrowR e n bytes r s₁) (narrowR e n bytes r s₂) := by
    intro s₁ s₂ hp
    obtain ⟨hp', hsy⟩ := pub_consts.mp hp
    exact pub_consts.mpr ⟨narrowR_pub hcl hloc hp' hl, hsy⟩
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s₃, s₄, -, hq, hfr, -, hex, ha, hm, hr0, hr1⟩ := hrun s hs
    refine ⟨t ++ _, _, hex, ha, ?_⟩
    rw [post_consts, post_arm]
    have hq' := (post_arm (sig := sig.withScratch nm e n)
      (pre := Curry.withScratch abi.ptrBits nm e n sig.params pre)
      (post := Curry.withScratch abi.ptrBits nm e n sig.params post)).mp (post_consts.mp hq)
    rw [narrowR_armArgs hcl hloc] at hq'
    rw [hm, hr0, hr1]
    have h₃ := Eq.mp (congrFun (congrFun (congrFun (Curry.apply_withScratch abi.ptrBits nm e n sig.params
      post _ _ (hlen s)) s.mem) s₃.mem) _) hq'
    refine hpost _ _ _ _ _ (hlen s) (fun b hb' a ha' => ?_) h₃
    exact (hfr a fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdisj s hs b hb' a ha').symm
  · obtain ⟨u₁, _, _, f₁, _, _, p₁, x₁, _⟩ := hrun s₁ h₁
    obtain ⟨u₂, _, _, f₂, _, _, p₂, x₂, _⟩ := hrun s₂ h₂
    rw [(Exec.det e₁ x₁).1, (Exec.det e₂ x₂).1, p₁, p₂, ((pubL_arm hl).mp (pub_consts.mp hp).1).1.1,
      hct _ _ _ _ _ _ (narrowR_preC hcl hloc hb h₁ hl) (narrowR_preC hcl hloc hb h₂ hl)
        (hpub s₁ s₂ hp) f₁ f₂]

end

end VG.Arm
