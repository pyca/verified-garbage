import VerifiedGarbage.Proof.CmacAes.Stream.X86.Init
import VerifiedGarbage.Proof.CmacAes.Stream.X86.AbsorbCorrect
import VerifiedGarbage.Proof.CmacAes.Stream.X86.Finish
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Cmac.Contract
import VerifiedGarbage.Proof.CmacAes.Stream.X86.Absorb

section

/-!
# Streaming AES-CMAC on x86: `vg_cmac_aes_absorb` is constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`): the taint analysis covers the code between the calls, from
`esp`, the stack arguments and `ebp`, which the correctness proof pins to a
value of the public arguments (`AAft`), and each call of `vg_cmac_aes_update`,
in its frame, is constant time by its own proof (`upd_rel`), its arguments
pinned by `AMid₁` and `AMid₂`.
-/

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86

variable (v : Proof.Aes.X86.Ctr32Impl)

theorem absorb_rel {s₀ s₀' : State} (h0 : absorbX86.pre s₀) (h0' : absorbX86.pre s₀')
    (hq : absorbX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (absorb v.callee v.suffix) fun _ _ => True := by
  have hp := APre.of h0
  have hp' := APre.of h0'
  obtain ⟨qE, qa⟩ := hq
  have eSt : aSt s₀ = aSt s₀' := qa 0 (by decide)
  have eR : aR s₀ = aR s₀' := by rw [aR, aR, qa 1 (by decide)]
  have eC : aC s₀ = aC s₀' := by rw [aC, aC, countX86, countX86, qa 2 (by decide), qa 3 (by decide)]
  have eD : aD s₀ = aD s₀' := qa 4 (by decide)
  have eL : aL s₀ = aL s₀' := by rw [aL, aL, qa 5 (by decide)]
  have eS : aSc s₀ = aSc s₀' := qa 6 (by decide)
  have e2 : d2Of s₀ = d2Of s₀' := by rw [d2Of, d2Of, eC, eL, eSt, eD]
  have ag : ∀ {rs : List Reg} {a b : State}, Pt 7 s₀ a → Pt 7 s₀' b → (∀ r ∈ rs, a.gpr r = b.gpr r) →
      VG.X86.Taint.Agree (argTaint rs (4 + 4 * 7)) a b :=
    fun h₁ h₂ hr => Pt.agree qE qa hp.argsOut hp'.argsOut h₁ h₂ hr
  have bp : ∀ {v v' : Nat} {a b : State}, v = v' → AAft s₀ v a → AAft s₀' v' b → ∀ r ∈ [Reg.ebp], a.gpr r = b.gpr r :=
    fun e h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ebp, h₂.ebp, e]
  have a := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 7))
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ag (Pt.refl _ _) (Pt.refl _ _) fun r hr => by simp at hr)
    (c := absorbPre) (by taint_decide)).wp (F₁ := AMid₁ s₀) (F₂ := AMid₁ s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨absorbPre_wp hp, absorbPre_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have c₁ := ((upd_rel v (E := aE s₀) (P := fun a b => AMid₁ s₀ a ∧ AMid₁ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [eSt, eS, eR, eC, eL]; exact h.2.args, h.1.ctx.esp,
        by rw [h.2.ctx.esp]; exact qE.symm⟩).wp
      (F₁ := AAft s₀ (fOf (aC s₀) (aL s₀))) (F₂ := AAft s₀' (fOf (aC s₀') (aL s₀')))
      fun _ _ h => ⟨(call1_after v) hp h.1, (call1_after v) hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have m := ((RelCT.taint (A := taint) (P := fun a b => AAft s₀ (fOf (aC s₀) (aL s₀)) a ∧
      AAft s₀' (fOf (aC s₀') (aL s₀')) b) (argTaint [.ebp] (4 + 4 * 7))
    (fun _ _ h => ag h.1.ctx.pt h.2.ctx.pt (bp (by rw [eC, eL]) h.1 h.2))
    (c := chain2) (by taint_decide)).wp (F₁ := AMid₂ s₀) (F₂ := AMid₂ s₀')
    fun _ _ h => ⟨WP.mono (chain2_mid hp h.1) fun _ h => h.1, WP.mono (chain2_mid hp' h.2) fun _ h => h.1⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have c₂ := ((upd_rel v (E := aE s₀) (P := fun a b => AMid₂ s₀ a ∧ AMid₂ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [eSt, eS, eR, eC, eL, e2]; exact h.2.args, h.1.aft.ctx.esp,
        by rw [h.2.aft.ctx.esp]; exact qE.symm⟩).wp
      (F₁ := AAft s₀ (fOf (aC s₀) (aL s₀) + 16 * nbOf (aC s₀) (aL s₀)))
      (F₂ := AAft s₀' (fOf (aC s₀') (aL s₀') + 16 * nbOf (aC s₀') (aL s₀')))
      fun _ _ h => ⟨(call2_after v) hp h.1, (call2_after v) hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have p := RelCT.taint (A := taint) (P := fun a b => AAft s₀ (fOf (aC s₀) (aL s₀) + 16 * nbOf (aC s₀) (aL s₀)) a ∧
      AAft s₀' (fOf (aC s₀') (aL s₀') + 16 * nbOf (aC s₀') (aL s₀')) b) (argTaint [.ebp] (4 + 4 * 7))
    (fun _ _ h => ag h.1.ctx.pt h.2.ctx.pt (bp (by rw [eC, eL]) h.1 h.2)) (c := absorbPost) (by taint_decide)
  exact a.seq (c₁.seq (m.seq (c₂.seq p)))

theorem absorb_ct : ConstantTime isa absorbX86.pre absorbX86.pub (absorb v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => ((absorb_rel v) h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.X86

end

/-!
# Streaming AES-CMAC on x86: `Verified`

Correctness and constant time, a state satisfying each precondition, and the
shared contracts of `Spec/Cmac/Contract.lean`, with 48 bytes of stack for
`init` (a call of `vg_cmac_aes_subkeys`: its four arguments, the return
address, and its call of `vg_aes_ctr32`) and 56 for `absorb` and `finish` (as
`init`, with six arguments).
-/

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86

variable (v : Proof.Aes.X86.Ctr32Impl)

theorem init_spSafe :
    (init v.expand v.callee v.suffix).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [init, call4, Code.all, v.expandSpSafe, Proof.CmacAes.X86.subkeys_spSafe v]
  decide +kernel

theorem absorb_spSafe :
    (absorb v.callee v.suffix).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [absorb, absorbPre, absorbPost, call6, countHeld, held, fill, copy,
    chain1, chain2, Code.all, Proof.CmacAes.X86.update_spSafe v]
  decide +kernel

theorem finish_spSafe :
    (finish v.callee v.suffix).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [finish, finPre, call6, countHeld, held, Code.all, Proof.CmacAes.X86.finalize_spSafe v]
  decide +kernel

/-- A state satisfying `vg_cmac_aes_init`'s precondition: the state at
`0x1000`, a key of 16 bytes at `0x3000` and the scratch buffer at `0x4000`,
as stack arguments at `0x8004`. -/
def initSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x30 else if a = 0x800c then 16
    else if a = 0x8011 then 0x40 else 0
  rd := [⟨0x3000, 16⟩, ⟨0x8004, 16⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem init_verified : Verified X86.target (init v.expand v.callee v.suffix) (Spec.Cmac.aesInitContract X86.abi 48) :=
  Verified.of_correct (fun _ hs => (init_wp v) hs) (init_ct v) (by
    have a0 : arg initSat 0 = 0x1000 := by decide
    have a1 : arg initSat 1 = 0x3000 := by decide
    have a2 : arg initSat 2 = 16 := by decide
    have a3 : arg initSat 3 = 0x4000 := by decide
    have e : argAddr initSat 0 = 0x8004 := by decide
    have esp : initSat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, initX86] [a0, a1, a2, a3, e, esp] using initSat)

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition: the state at
`0x1000`, 10 rounds, `count` 0, no data at `0x3000` and the scratch buffer
at `0x4000`, as stack arguments at `0x8004`. -/
def absorbSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10
    else if a = 0x8015 then 0x30 else if a = 0x801d then 0x40 else 0
  rd := [⟨0x3000, 0⟩, ⟨0x8004, 28⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem absorb_verified : Verified X86.target (absorb v.callee v.suffix) (Spec.Cmac.aesAbsorbContract X86.abi 56) :=
  Verified.of_correct (fun _ hs => (absorb_wp v) hs) (absorb_ct v) (by
    have a0 : arg absorbSat 0 = 0x1000 := by decide
    have a1 : arg absorbSat 1 = 10 := by decide
    have a2 : arg absorbSat 2 = 0 := by decide
    have a3 : arg absorbSat 3 = 0 := by decide
    have a4 : arg absorbSat 4 = 0x3000 := by decide
    have a5 : arg absorbSat 5 = 0 := by decide
    have a6 : arg absorbSat 6 = 0x4000 := by decide
    have e : argAddr absorbSat 0 = 0x8004 := by decide
    have esp : absorbSat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, absorbX86, countX86] [a0, a1, a2, a3, a4, a5, a6, e, esp] using absorbSat)

/-- A state satisfying `vg_cmac_aes_finish`'s precondition: the state at
`0x1000`, 10 rounds, `count` 0, `out` at `0x2000` and the scratch buffer at
`0x4000`, as stack arguments at `0x8004`. -/
def finishSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10
    else if a = 0x8015 then 0x20 else if a = 0x8019 then 0x40 else 0
  rd := [⟨0x8004, 24⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩, ⟨0x4000, 2304⟩]

theorem finish_verified : Verified X86.target (finish v.callee v.suffix) (Spec.Cmac.aesFinishContract X86.abi 56) :=
  Verified.of_correct (fun _ hs => (finish_wp v) hs) (finish_ct v) (by
    have a0 : arg finishSat 0 = 0x1000 := by decide
    have a1 : arg finishSat 1 = 10 := by decide
    have a2 : arg finishSat 2 = 0 := by decide
    have a3 : arg finishSat 3 = 0 := by decide
    have a4 : arg finishSat 4 = 0x2000 := by decide
    have a5 : arg finishSat 5 = 0x4000 := by decide
    have e : argAddr finishSat 0 = 0x8004 := by decide
    have esp : finishSat.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.Cmac.aesFinishContract, Spec.Cmac.aesFinishSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, finishX86, countX86] [a0, a1, a2, a3, a4, a5, e, esp] using finishSat)

end VG.Proof.CmacAes.Stream.X86
