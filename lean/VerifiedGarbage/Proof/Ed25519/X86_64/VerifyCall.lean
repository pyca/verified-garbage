module

public import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyVerified
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Ed25519.X86_64.BaseHeld
import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Spec.Ed25519.Contract

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

@[expose] public section

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
  | .icall .., h => h

omit [EdArith fld] [EdWindows win] in
/-- The registered code, its calls inlined. -/
theorem verifyEquation_inline {win' : Prog isa} (h : win'.inline = win) :
    (verifyEquation fld win').inline = verifyEquationWith fld (Point64.bodies fld) win := by
  subst h
  have hr : (rootPower2 fld).inline = rootPower2 fld := by unfold rootPower2; split <;> rfl
  have hd : (decodePowers fld).inline = decodePowers fld := by
    change Code.seq _ (.seq _ (.seq _ (.seq _ (.seq (rootPower2 fld).inline _)))) = _
    rw [hr]; rfl
  change Code.seq (.block verifySetup) (Code.seq (Code.seq (.block verifyScalar)
    (Code.ite .b (Code.seq (decodePowers fld).inline (decodeAThen fld (Point64.calls fld) win').inline)
      recoverInvalid.inline)) (.block _)) = _
  rw [hd]; rfl

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
