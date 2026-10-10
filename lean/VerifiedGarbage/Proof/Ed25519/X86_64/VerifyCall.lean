import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyVerified
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified

/-!
# Verification calling the point functions: `Verified`

Untrusted: everything here is checked by Lean. The registered code,
`verifyEquation fld win'`, calls the point functions (`Point64.calls`); its
calls run as their bodies would inlined (`Code.inline`), which gives
`verifyEquationWith fld (Point64.bodies fld) win` for the windows `win` that
`win'` inlines to (`verifyEquation_inline`), the code `VerifyVerified.lean`
proves correct and constant time. `Verified.of_inline` moves the proof to the
calls, with 8 bytes of stack for their return address, which no buffer
overlaps (`Sig.clear_of_pre_consts`); the postcondition reads only `rax`.
`verify_ok_calls` is the same for a caller of the checker, which provides the
8 bytes (`verifyLocal8`).
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld] {win : Prog isa} [EdWindows win]

theorem restores_inline {a b : Prog isa} (h : restores a b = true) : restores a.inline b.inline = true := by
  unfold restores at h
  split at h
  · simp only [Code.inline]
    unfold restores
    simpa only [Code.allInstrs_inline] using h
  · cases h

/-- Code that restores MXCSR around every load of it does so with its calls inlined. -/
theorem ctlOk_inline : ∀ {c : Prog isa}, ctlOk c = true → ctlOk c.inline = true
  | .block _, h => h
  | .seq a b, h => by
    simp only [ctlOk, Bool.or_eq_true, Bool.and_eq_true] at h
    simp only [Code.inline, ctlOk, Bool.or_eq_true, Bool.and_eq_true]
    rcases h with h | ⟨ha, hb⟩
    · exact .inl (restores_inline h)
    · exact .inr ⟨ctlOk_inline ha, ctlOk_inline hb⟩
  | .ite _ t e, h => by
    simp only [ctlOk, Bool.and_eq_true] at h
    simp only [Code.inline, ctlOk, Bool.and_eq_true]
    exact ⟨ctlOk_inline h.1, ctlOk_inline h.2⟩
  | .loop b _, h => ctlOk_inline (c := b) h
  | .call _ b, h => h
  | .frame i b j, h => by
    simp only [ctlOk, Bool.and_eq_true] at h
    simp only [Code.inline, ctlOk, Bool.and_eq_true]
    exact ⟨⟨h.1.1, ctlOk_inline h.1.2⟩, h.2⟩

omit [EdArith fld] [EdWindows win] in
/-- The registered code, its calls inlined. -/
theorem verifyEquation_inline {win' : Prog isa} (h : win'.inline = win) :
    (verifyEquation fld win').inline = verifyEquationWith fld (Point64.bodies fld) win := by
  subst h; rfl

/-- `verifyLocal`, with the 8 bytes below `rsp` apart from every region: room for a call's return
address. -/
def verifyLocal8 : Contract isa where
  pre s := verifyLocal.pre s ∧ Clear (hole (s.gpr .rsp)) s
  post := verifyLocal.post
  pub := verifyLocal.pub

/-- The registered code meets `verifyLocal8`. -/
theorem verify_ok_calls {win' : Prog isa} (hinl : win'.inline = win)
    (hok : (verifyEquation fld win').InlineOk = true)
    (hmx : MxcsrOk (verifyEquationWith fld (Point64.bodies fld) win)) (s : State) (hs : verifyLocal8.pre s) :
    ∃ t s', Exec isa (verifyEquation fld win') s t s' ∧ abiPreserved s s' ∧ verifyLocal8.post s s' := by
  obtain ⟨t, b, he, ha, hp⟩ := verify_ok hmx s hs.1
  rw [← verifyEquation_inline hinl] at he
  obtain ⟨hv, u, ta, ha', _, _⟩ := Exec.of_inline hok he hs.2
  exact ⟨ta, _, ha', abiPreserved_patch hv u ha, hp⟩

/-- The registered code is constant time under `verifyLocal8`. -/
theorem verify_ct_calls {win' : Prog isa} (hinl : win'.inline = win)
    (hok : (verifyEquation fld win').InlineOk = true)
    (hmx : MxcsrOk (verifyEquationWith fld (Point64.bodies fld) win)) :
    ConstantTime isa verifyLocal8.pre verifyLocal8.pub (verifyEquation fld win') := by
  have e := verifyEquation_inline (fld := fld) hinl
  refine ConstantTime.of_inline hok (fun s hs => ?_) (fun _ h => h.2) (fun _ _ _ _ hp => hp.1) ?_
  · obtain ⟨t, s', he, -⟩ := verify_ok hmx s hs.1
    exact ⟨t, s', e ▸ he⟩
  · rw [e]
    exact fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => verify_ct s₁ s₂ t₁ t₂ s₁' s₂' h₁.1 h₂.1 hp e₁ e₂

/-- The shared contract's precondition with 8 bytes of stack, from its facts. -/
theorem verify_spec_pre8 {s : State}
    (hrd : s.rd = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rsi, 64⟩, ⟨s.gpr .rdx, 64⟩, ⟨s.syms baseOddSym, 16384⟩])
    (hw : s.wr = [⟨s.gpr .rcx, 8192⟩]) (hsp : 8 ≤ (s.gpr .rsp).toNat)
    (h1 : Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rcx, 8192⟩)
    (h2 : Region.Disjoint ⟨s.gpr .rsi, 64⟩ ⟨s.gpr .rcx, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .rdx, 64⟩ ⟨s.gpr .rcx, 8192⟩)
    (r1 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 32⟩) (r2 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 64⟩)
    (r3 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 64⟩) (r4 : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rcx, 8192⟩)
    (q1 : Region.Disjoint ⟨s.gpr .rsp - 8, 8⟩ ⟨s.gpr .rdi, 32⟩)
    (q2 : Region.Disjoint ⟨s.gpr .rsp - 8, 8⟩ ⟨s.gpr .rsi, 64⟩)
    (q3 : Region.Disjoint ⟨s.gpr .rsp - 8, 8⟩ ⟨s.gpr .rdx, 64⟩)
    (q4 : Region.Disjoint ⟨s.gpr .rsp - 8, 8⟩ ⟨s.gpr .rcx, 8192⟩)
    (f0 : (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64) (f1 : (s.gpr .rsi).toNat + 64 ≤ 2 ^ 64)
    (f2 : (s.gpr .rdx).toNat + 64 ≤ 2 ^ 64) (f3 : (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64)
    (held : ∀ i < 2048,
      s.mem.readW (s.syms baseOddSym + BitVec.ofNat 64 (8 * i)) 64 = baseOddWords.getD i 0)
    (fit : (s.syms baseOddSym).toNat + 16384 ≤ 2 ^ 64)
    (td : Region.Disjoint ⟨s.syms baseOddSym, 16384⟩ ⟨s.gpr .rcx, 8192⟩)
    (tr : Region.Disjoint ⟨s.syms baseOddSym, 16384⟩ ⟨s.gpr .rsp, 8⟩)
    (tq : Region.Disjoint ⟨s.syms baseOddSym, 16384⟩ ⟨s.gpr .rsp - 8, 8⟩) :
    (Spec.Ed25519.verifyEquationContract (X86_64.abi.withConsts baseOddConsts) 8).pre s := by
  sig_pre [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
    Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, baseOddConsts_eq, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow, baseOddWords_length]
  exact ⟨hsp, by rw [hrd]; rfl, held, fit, by rw [hw]; simp only [List.mem_singleton, forall_eq]; exact td, tr, tq,
    by rw [hrd]; rfl, hw, h1, h2, h3, r1, r2, r3, r4, q1, q2, q3, q4, f0, f1, f2, f3⟩

theorem verify_sat8 :
    (Spec.Ed25519.verifyEquationContract (X86_64.abi.withConsts baseOddConsts) 8).pre verifySatState :=
  verify_spec_pre8 rfl rfl (by decide) (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (by decide) (by decide) (by decide) (by decide)
    verifySatMem_held (by decide) (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide))

/-- The registered code, calling the point functions, against the shared contract with 8 bytes of
stack. -/
theorem verify_verified8 {win' : Prog isa} (hinl : win'.inline = win)
    (hok : (verifyEquation fld win').InlineOk = true)
    (hmx : MxcsrOk (verifyEquationWith fld (Point64.bodies fld) win)) :
    Verified X86_64.target (verifyEquation fld win')
      (Spec.Ed25519.verifyEquationContract (X86_64.abi.withConsts baseOddConsts) 8) := by
  have e := verifyEquation_inline (fld := fld) hinl
  refine Verified.of_inline hok (k₀ := verifyLocal) (fun s hs => e ▸ verify_ok hmx s hs) (e ▸ verify_ct)
    (verify_implies.stack8 ⟨verifySatState, verify_sat8⟩) (fun _ h => Sig.clear_of_pre_consts h)
    (fun _ _ _ _ _ hp => hp) fun s₁ s₂ _ _ hp => ?_
  sig_pub [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
    Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, baseOddConsts_eq, Abi.withConsts] at hp
  exact hp.1

/-- What a caller of the checker `verifyEquation fld win'` needs of its code: the windows `win` its
calls inline to, with their proofs, the inlining's condition and MXCSR's restores. Decided for each
checker in the registration file. -/
structure CallCode (fld : Arith) (win' : Prog isa) : Prop where
  ok : ∃ win : Prog isa, EdWindows win ∧ win'.inline = win ∧ (verifyEquation fld win').InlineOk = true ∧
    MxcsrOk (verifyEquationWith fld (Point64.bodies fld) win)

theorem CallCode.verified {win' : Prog isa} (h : CallCode fld win') :
    (∀ s, verifyLocal8.pre s → ∃ t s', Exec isa (verifyEquation fld win') s t s' ∧ abiPreserved s s' ∧
      verifyLocal8.post s s') ∧
    ConstantTime isa verifyLocal8.pre verifyLocal8.pub (verifyEquation fld win') := by
  obtain ⟨win, hw, hinl, hok, hmx⟩ := h.ok
  exact ⟨verify_ok_calls (win := win) hinl hok hmx, verify_ct_calls (win := win) hinl hok hmx⟩

end VG.Proof.Ed25519.X86_64
