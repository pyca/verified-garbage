module

public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll

/-!
# Scrubbing code without frames that states what it writes (AArch64)

`Scrub.withScrubAll` leaves as it is a registration that states how much
of a buffer its code writes (`Registration.written`). For code without
frames, `scrubAll 0` adds only the clearing of registers, which writes no
memory: the memory on return is the code's, so what the registration states
of `written` still holds (`scrubAll0_mem`). `withScrubAllW` is
`withScrubAll` for such code, keeping `written`.
-/

@[expose] public section

namespace VG.AArch64.Scrub

open VG.AArch64 VG.Impl.Scrub.AArch64

theorem retFix_mem {rb : Nat} (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64) {s s' : State} {t : List Leak}
    (h : execBlock isa (retFix rb) s = some (s', t)) : s'.mem = s.mem := by
  obtain ⟨g, hg, -⟩ := retFix_hi hrb s
  rw [hg] at h
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
  rfl

/-- A run of `scrubAll 0 rb cl c` ends with the memory of a run of `c`. -/
theorem scrubAll0_mem {c : Prog isa} {rb : Nat} {cl : Clear} (hwf : cl.WF) (hrb : rb = 0 ∨ rb = 32 ∨ rb = 64)
    {s s' : State} {t : List Leak} (he : Exec isa (scrubAll 0 rb cl c) s t s') :
    ∃ t' u, Exec isa c s t' u ∧ s'.mem = u.mem := by
  change Exec isa (.seq (.seq c (.block (clearsOf cl))) (.block (retFix rb))) s t s' at he
  cases he with
  | seq a r =>
  cases a with
  | seq c₁ l =>
  cases l with
  | block hl =>
  cases r with
  | block hr =>
  rw [clears_run hwf] at hl
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hl)
  exact ⟨_, _, c₁, (retFix_mem hrb hr).trans rfl⟩

theorem writtenWithin_of_mem {A : Abi isa} {sig : Sig} {w : List (String × Nat)} {s u s' : State}
    (hm : A.mem s' = A.mem u) (h : Sig.writtenWithin A sig w s u) : Sig.writtenWithin A sig w s s' := by
  cases w with
  | nil => trivial
  | cons x xs =>
    simp only [Sig.writtenWithin, hm] at h ⊢
    exact h

/-- `withScrubAll`'s clearing of the registers for code without frames
(`r.stack = 0`), keeping what `r` states of `written`; otherwise `r` itself. -/
def withScrubAllW {api : Api} (r : Unscrubbed api target) (hok : ScrubAllOk r.contract r.stack (retBitsOf r)) :
    Registration api target :=
  if h : r.stack = 0 ∧ r.code.aarch64Depth = 0 ∧ r.code.all (fun i => !i.writesDit) = true ∧
      (retBitsOf r = 0 ∨ retBitsOf r = 32 ∨ retBitsOf r = 64) then
    { suffix := r.suffix
      tables := r.tables
      code := scrubAll 0 (retBitsOf r) (Clear.of r.code) r.code
      contract := r.contract
      verified := .scrubbed <| .abi ⟨Verified.scrubAll0 (Clear.of_wf _) r.verified h.2.2.2 (h.1 ▸ hok),
        noResidue_scrubAll0 (Clear.of_wf _) (Clear.of_keeps _) r.verified h.2.1 h.2.2.1 h.2.2.2⟩
      consts := r.consts
      stack := r.stack
      ofApi := r.ofApi
      ofSig := r.ofSig
      spSafe := all_spSafe _
      written := r.written
      writtenOk := fun s t s' hs he => by
        obtain ⟨t', u, hc, hm⟩ := scrubAll0_mem (Clear.of_wf _) h.2.2.2 he
        exact writtenWithin_of_mem hm (r.writtenOk s t' u hs hc)
      extra := r.extra
      vendor := r.vendor
      notWith := r.notWith }
  else r.registration

end VG.AArch64.Scrub
