module

public import VerifiedGarbage.Impl.AesGcm.X86_64.FastSeal
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Mid
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.SealEnd
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT

/-!
# AES-GCM `seal`'s path for TLS records

Untrusted: everything here is checked by Lean. With a prepared key context,
`FastSeal.run` is `Short.sealLong` with `Fast.aad`, which leaves what
`oneAad` does (`Fast.aad_mid`) and branches alike in two runs
(`Fast.aad_rel`), and `Short.finishP`, which ends as `Short.finishWith` does
(`Fast.finOk_finishP`), so it leaves what `sealRunW_ok` does
(`Fast.sealRunFin_ok`), and does it in two runs with the same addresses and
branches (`Fast.sealRunP_rel`); so `FastSeal.sel`
does, with `other` for the inputs `Fast.cond` turns away: `sealSel_ok`,
`sealSel_rel`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.FastSeal

variable {np : Nat} {hnp : 8 ≤ np ∧ np ≤ 24}

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts KsOk KsRel SealLongOk SealLongRel rel_next condS_of)
open VG.Proof.AesGcm.X86_64.Fast (IsFast aad_mid condE_ok finOk_finishP sealRunFin_ok sealRunP_rel)

variable {any : Bool}

/-- `sel`: this path for the inputs it takes, `other` for the rest. -/
theorem sealSel_ok (hF : ShortFacts) (v : GcmImpl) (B : BlkFn (CtxMode.preparedN np hnp)) {ks : Prog isa} (hks : KsOk ks)
    {other : Prog isa} (ho : SealLongOk (CtxMode.preparedN np hnp) other) :
    SealLongOk (CtxMode.preparedN np hnp) (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) other ks any) := by
  intro s s₁ Ctx W SP Np A D nl al n C X E hNp hnl hal
  unfold Impl.AesGcm.X86_64.FastSeal.sel
  refine WP.seq (WP.mono (condE_ok C E hnl hal) fun s₃ ⟨hz, E₃, _⟩ => ?_)
  refine WP.ite (decide ¬IsFast nl al n any) (eval_e hz) (fun _ => ho C X E₃ hNp hnl hal) fun h => ?_
  obtain ⟨h12, h17, -⟩ : IsFast nl al n any := Decidable.not_not.mp (of_decide_eq_false h)
  subst h12
  exact sealRunFin_ok B (finOk_finishP hF hks) C X hal (aad_mid hF C X E₃ hNp hnl hal (by omega))

/-- `sel` in two runs: the same path, and on it the same addresses and
branches. -/
theorem sealSel_rel (hF : ShortFacts) (v : GcmImpl) (B : BlkFn (CtxMode.preparedN np hnp)) {ks : Prog isa} (hks : KsOk ks)
    (hkr : KsRel ks) {other : Prog isa} (ho : SealLongRel (CtxMode.preparedN np hnp) other) :
    SealLongRel (CtxMode.preparedN np hnp) (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) other ks any) := by
  intro s₀ s₀' Ctx W SP Np A D nl al n R C C' X X' hNp hnl hal hR hNp' hnl' hal' hR'
  have hlt := C.data.ok.lt
  unfold Impl.AesGcm.X86_64.FastSeal.sel
  have hw : ∀ {s₀ : State} {Np : Addr} (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n), (s₀.gpr .rcx).toNat = nl →
      (s₀.gpr .r9).toNat = al → ∀ s, OneEntry s₀ Ctx W SP A D n s →
      WP isa (Impl.AesGcm.X86_64.Fast.cond any) s fun u => u.zf = some (decide ¬IsFast nl al n any) ∧
        OneEntry s₀ Ctx W SP A D n u :=
    fun C hnl hal s h => WP.mono (condE_ok C h hnl hal) fun _ ⟨z, E, _⟩ => ⟨z, E⟩
  have c := rel_next (Fast.cond_rel (F₁ := OneEntry s₀ Ctx W SP A D n) (F₂ := OneEntry s₀' Ctx W SP A D n)
      (fun _ h => condS_of h hnl hal) (fun _ h => condS_of h hnl' hal')
      (by rw [← hnl]; exact BitVec.isLt _) (by rw [← hal]; exact BitVec.isLt _) (by omega))
    (hw C hnl hal) (hw C' hnl' hal')
  refine RelCT.seq c (rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1])
    ((ho C C' X X' hNp hnl hal hR hNp' hnl' hal' hR').mono
      (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h) ?_)
  by_cases hs : IsFast nl al n any
  · obtain ⟨h12, h17, -⟩ := hs
    subst h12
    have L := C.lay
    exact (sealRunP_rel hks hkr B C C' X X' hNp hnl hal hR hNp' hnl' hal' hR'
      ((Fast.aad_rel L C.dE (M := (CtxMode.preparedN np hnp)) (R := R) (Np := Np) (A := A) (al := al) (by omega)).mono
        (P' := fun (s₁ s₂ : State) => OneEntry s₀ Ctx W SP A D n s₁ ∧ OneEntry s₀' Ctx W SP A D n s₂)
        (fun _ _ g => ⟨g.1.aadPre C X hNp hnl hal hR, g.2.aadPre C' X' hNp' hnl' hal' hR'⟩) fun _ _ _ => trivial)
      (fun _ h => aad_mid hF C X h hNp hnl hal (by omega))
      (fun _ h => aad_mid hF C' X' h hNp' hnl' hal' (by omega))).mono
      (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h
  · exact RelCT.of_false fun _ _ h => by have := h.1.1.1.symm.trans h.2; simp [hs] at this

end VG.Proof.AesGcm.X86_64.FastSeal
