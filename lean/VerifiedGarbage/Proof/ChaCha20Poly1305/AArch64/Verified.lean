import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Open
import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.RelCT

/-!
# ChaCha20-Poly1305 on AArch64: `Verified`

Correctness (`Correct.lean`, and `Stitched/` for the eight-block stream's
own code), constant time, and a state satisfying the precondition: of the
code with its working space as its last argument (`sealScratchContract`,
`openScratchContract`), and then of the functions, which allocate it in a
frame of 768 bytes on the stack and wipe it after the code
(`Verified.stackScratchWiped`).

The taint analysis runs through the callees' code: it knows `x21`–`x25`
(the context, the data, the additional data and their lengths) for public
after each call because no callee writes them (unlike `x19` and `x20`, which
`vg_chacha20_xor` restores from memory, and which the analysis therefore
treats as secret afterwards). The address of `tag`, which no register can
keep through the eight-block stream's code, is saved in the context, so the
analysis, which knows nothing of memory, checks the code up to the tag
(`sealMainCode`, `openMainCode`) and the rest (`sealTail`, `openTail`)
separately: between them, correctness says that both runs load the same
address, from the same place (`MainS`, `MainO`), and the rest is checked with
it public.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64

/-! ## Relating two runs -/

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
theorem rel_taint {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (hsp : σ₁.sp = σ₂.sp)
    (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r) (hc : ∃ h, (taint.check (Taint.ofRegs rs) c h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) c TT := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) _ (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab
    exact ⟨hsp, fun r h => hr r (VG.AArch64.Taint.mem_ofRegs.mp h)⟩) hc

/-! ## Correctness -/

theorem sealCode_eq (c : Impl.ChaCha20.AArch64.XorCallee) (stitched : Bool) :
    sealCode c stitched = .seq (sealMainCode c stitched) sealTail := by
  cases stitched <;> rfl

theorem openCode_eq (c : Impl.ChaCha20.AArch64.XorCallee) (stitched : Bool) :
    openCode c stitched = .seq (openMainCode c stitched) openTail := by
  cases stitched <;> rfl

theorem sealMainCode_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre true s₀) :
    WP isa (sealMainCode v.callee v.stitched) s₀ (MainS s₀) := by
  unfold sealMainCode
  split
  · exact sealStitchedMain_ok v hp
  · exact sealMain_ok v hp

theorem openMainCode_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre false s₀) :
    WP isa (openMainCode v.callee v.stitched) s₀ (MainO s₀) := by
  unfold openMainCode
  split
  · exact openStitchedMain_ok v hp
  · exact openMain_ok v hp

theorem seal_ok (v : Proof.ChaCha20.AArch64.XorImpl) (s : State) (hs : sealAArch64.pre s) :
    ∃ t s', Exec isa (sealCode v.callee v.stitched) s t s' ∧
      abiPreserved s s' ∧ sealAArch64.post s s' := by
  rw [sealCode_eq]
  exact WP.seq (WP.mono (sealMainCode_ok v (APre.of s hs)) fun _ h => sealTail_ok (APre.of s hs) h)

theorem open_ok (v : Proof.ChaCha20.AArch64.XorImpl) (s : State) (hs : openAArch64.pre s) :
    ∃ t s', Exec isa (openCode v.callee v.stitched) s t s' ∧
      abiPreserved s s' ∧ openAArch64.post s s' := by
  rw [openCode_eq]
  exact WP.seq (WP.mono (openMainCode_ok v (APre.of s hs)) fun _ h => openTail_ok (APre.of s hs) h)

/-! ## Constant time -/

theorem sealLoad_taint : ∃ h, (taint.check (Taint.ofRegs [.x21])
    (.block [.ldr .x .x2 .x21 624]) h).isSome = true := ⟨_, by taint_decide⟩

theorem sealRest_taint : ∃ h, (taint.check (Taint.ofRegs [.x2, .x21])
    (.seq finalizeTag (.block restore)) h).isSome = true := ⟨_, by taint_decide⟩

theorem openLoad_taint : ∃ h, (taint.check (Taint.ofRegs [.x21])
    (.block [.ldr .x .x12 .x21 624]) h).isSome = true := ⟨_, by taint_decide⟩

theorem openRest_taint : ∃ h, (taint.check (Taint.ofRegs [.x12, .x21])
    (.block (compare ++ restore)) h).isSome = true := ⟨_, by taint_decide⟩

theorem pub_regs {s₁ s₂ : State} (hq : pubAArch64 s₁ s₂) :
    ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], s₁.gpr r = s₂.gpr r := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, -⟩ := hq
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem seal_ct (v : Proof.ChaCha20.AArch64.XorImpl) : ConstantTime isa sealAArch64.pre sealAArch64.pub
    (sealCode v.callee v.stitched) := by
  rw [sealCode_eq]
  intro σ₁ σ₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  have hp₁ := APre.of _ h₁
  have hp₂ := APre.of _ h₂
  obtain ⟨-, -, -, -, -, -, p6, p7, psp⟩ := id hq
  refine (rel_seq (rel_taint _ psp (pub_regs hq) v.sealTaint) (sealMainCode_ok v hp₁)
    (sealMainCode_ok v hp₂) (fun τ₁ τ₂ m₁ m₂ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1
  have sp : τ₁.sp = τ₂.sp := by rw [m₁.inv.sp, m₂.inv.sp, psp]
  refine rel_seq (rel_taint [.x21] sp (by
      simp only [List.mem_singleton, forall_eq, m₁.inv.x21, m₂.inv.x21, cx, p7]) sealLoad_taint)
    (tagPtr_ok hp₁ m₁.inv.x21 m₁.inv.saved m₁.inv.rd m₁.inv.wr (by decide))
    (tagPtr_ok hp₂ m₂.inv.x21 m₂.inv.saved m₂.inv.rd m₂.inv.wr (by decide))
    fun u₁ u₂ ⟨x2₁, k₁⟩ ⟨x2₂, k₂⟩ => rel_taint [.x2, .x21] (by rw [k₁.sp, k₂.sp, sp]) ?_ sealRest_taint
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [x2₁, x2₂, tp, tp, p6]
  · rw [k₁.cs _ (pres .x21) (pres30 .x21), k₂.cs _ (pres .x21) (pres30 .x21), m₁.inv.x21, m₂.inv.x21, cx,
      cx, p7]

theorem open_ct (v : Proof.ChaCha20.AArch64.XorImpl) : ConstantTime isa openAArch64.pre openAArch64.pub
    (openCode v.callee v.stitched) := by
  rw [openCode_eq]
  intro σ₁ σ₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  have hp₁ := APre.of _ h₁
  have hp₂ := APre.of _ h₂
  obtain ⟨-, -, -, -, -, -, p6, p7, psp⟩ := id hq
  refine (rel_seq (rel_taint _ psp (pub_regs hq) v.openTaint) (openMainCode_ok v hp₁)
    (openMainCode_ok v hp₂) (fun τ₁ τ₂ m₁ m₂ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1
  have sp : τ₁.sp = τ₂.sp := by rw [m₁.inv.sp, m₂.inv.sp, psp]
  refine rel_seq (rel_taint [.x21] sp (by
      simp only [List.mem_singleton, forall_eq, m₁.inv.x21, m₂.inv.x21, cx, p7]) openLoad_taint)
    (tagPtr_ok hp₁ m₁.inv.x21 m₁.inv.saved m₁.inv.rd m₁.inv.wr (by decide))
    (tagPtr_ok hp₂ m₂.inv.x21 m₂.inv.saved m₂.inv.rd m₂.inv.wr (by decide))
    fun u₁ u₂ ⟨x12₁, k₁⟩ ⟨x12₂, k₂⟩ => rel_taint [.x12, .x21] (by rw [k₁.sp, k₂.sp, sp]) ?_ openRest_taint
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [x12₁, x12₂, tp, tp, p6]
  · rw [k₁.cs _ (pres .x21) (pres30 .x21), k₂.cs _ (pres .x21) (pres30 .x21), m₁.inv.x21, m₂.inv.x21, cx,
      cx, p7]

/-! ## `Verified` -/

/-- A state satisfying `seal`'s precondition (with no additional data and no
data). -/
def sealSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x1100 | .x2 => 0x2000 | .x4 => 0x2100 | .x6 => 0x3000 | .x7 => 0x4000
    | _ => 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x2100, 0⟩, ⟨0x3000, 16⟩, ⟨0x4000, 760⟩]

/-- A state satisfying `open`'s precondition (as `sealSat`, with `tag` read). -/
def openSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x1100 | .x2 => 0x2000 | .x4 => 0x2100 | .x6 => 0x3000 | .x7 => 0x4000
    | _ => 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x3000, 16⟩]
  wr := [⟨0x2100, 0⟩, ⟨0x4000, 760⟩]

theorem seal_verified (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target (sealCode v.callee v.stitched) (sealScratchContract AArch64.abi 95) :=
  Verified.of_correct (seal_ok v) (seal_ct v) (by
    sig_implies [Proof.ChaCha20Poly1305.sealScratchContract, Proof.ChaCha20Poly1305.sealScratchSig,
      Spec.ChaCha20Poly1305.sealPost, Proof.ChaCha20Poly1305.sealAArch64,
      Proof.ChaCha20Poly1305.preAArch64, Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi, AArch64.argRegs]
      [sealSat] using sealSat)

/-- The postconditions match on `decrypt` through different auxiliary
functions, so the implication splits on it. -/
theorem open_verified (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target (openCode v.callee v.stitched) (openScratchContract AArch64.abi 95) :=
  Verified.of_correct (open_ok v) (open_ct v)
    { pre := by
        sig_implies_pre [Proof.ChaCha20Poly1305.openScratchContract,
          Proof.ChaCha20Poly1305.openScratchSig, Spec.ChaCha20Poly1305.openPost,
          Proof.ChaCha20Poly1305.openAArch64, Proof.ChaCha20Poly1305.preAArch64,
          Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi, AArch64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Proof.ChaCha20Poly1305.openScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openPost, AArch64.abi, AArch64.argRegs]
        simp only [Proof.ChaCha20Poly1305.openAArch64] at h
        -- The two `decrypt` terms are equal only up to unfolding numerals.
        split at h
        next _ pt e₁ =>
          split
          next _ pt' e₂ =>
            obtain rfl := Option.some.inj (e₁.symm.trans e₂)
            exact h
          next _ e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
        next _ e₁ =>
          split
          next _ pt' e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
          next _ e₂ => exact h
      pub := by
        sig_implies_pub [Proof.ChaCha20Poly1305.openScratchContract,
          Proof.ChaCha20Poly1305.openScratchSig, Spec.ChaCha20Poly1305.openPost,
          Proof.ChaCha20Poly1305.openAArch64, Proof.ChaCha20Poly1305.preAArch64,
          Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi, AArch64.argRegs]
      sat := by
        sig_implies_sat [Proof.ChaCha20Poly1305.openScratchContract,
          Proof.ChaCha20Poly1305.openScratchSig, Spec.ChaCha20Poly1305.openPost,
          Proof.ChaCha20Poly1305.openAArch64, Proof.ChaCha20Poly1305.preAArch64,
          Proof.ChaCha20Poly1305.pubAArch64, AArch64.abi, AArch64.argRegs]
          [openSat] using openSat }

/-! ## The frame -/

/-- A state satisfying `seal`'s precondition, without the working space. -/
def sealFrameSat : State := { sealSat with wr := [⟨0x2100, 0⟩, ⟨0x3000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.sealContract AArch64.abi 768).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
    Spec.ChaCha20Poly1305.sealPost, AArch64.abi, AArch64.argRegs] [sealFrameSat, sealSat]
    using sealFrameSat

theorem seal_framed (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratchWiped 768 .x7 95 (sealCode v.callee v.stitched))
      (Spec.ChaCha20Poly1305.sealContract AArch64.abi 768) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.ChaCha20Poly1305.sealSig) (nm := "work") (e := .u64)
    (n := 95) (post := Spec.ChaCha20Poly1305.sealPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 768) (words := 95) (seal_verified v) (by decide) (by decide) (by decide)
    (sealPost_out _) sealFrameSat_pre

/-- A state satisfying `open`'s precondition, without the working space. -/
def openFrameSat : State := { openSat with wr := [⟨0x2100, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.openContract AArch64.abi 768).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.openContract, Spec.ChaCha20Poly1305.openSig,
    Spec.ChaCha20Poly1305.openPost, AArch64.abi, AArch64.argRegs] [openFrameSat, openSat]
    using openFrameSat

theorem open_framed (v : Proof.ChaCha20.AArch64.XorImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratchWiped 768 .x7 95 (openCode v.callee v.stitched))
      (Spec.ChaCha20Poly1305.openContract AArch64.abi 768) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.ChaCha20Poly1305.openSig) (nm := "work") (e := .u64)
    (n := 95) (post := Spec.ChaCha20Poly1305.openPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 768) (words := 95) (open_verified v) (by decide) (by decide) (by decide)
    (openPost_out _) openFrameSat_pre

end VG.Proof.ChaCha20Poly1305.AArch64
