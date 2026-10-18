module

public import VerifiedGarbage.Impl.AesGcm.X86_64.FastSeal
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Mid
public import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks

/-!
# AES-GCM `seal`'s path for TLS records

Untrusted: everything here is checked by Lean. With a prepared key context,
`FastSeal.run` is `Short.sealLong` with `Fast.aad`, which leaves what
`oneAad` does (`Fast.aad_mid`) and branches alike in two runs
(`Fast.aad_rel`), so it leaves what `sealRunW_ok` does, and does it in two
runs with the same addresses and branches (`sealRunW_rel`); so `FastSeal.sel`
does, with `other` for the inputs `Fast.cond` turns away: `sealSel_ok`,
`sealSel_rel`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.FastSeal

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts SealLongOk SealLongRel sealRunW_ok sealRunW_rel finKs_ksOk finKs_rel
  rel_next condS_of)
open VG.Proof.AesGcm.X86_64.Fast (IsFast aad_mid condE_ok)

/-- `sel`: this path for the inputs it takes, `other` for the rest. -/
theorem sealSel_ok (hF : ShortFacts) (v : GcmImpl) (B : BlkFn CtxMode.prepared) {other : Prog isa}
    (ho : SealLongOk CtxMode.prepared other) :
    SealLongOk CtxMode.prepared (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) other) := by
  intro s s₁ Ctx W SP Np A D nl al n C X E hNp hnl hal
  unfold Impl.AesGcm.X86_64.FastSeal.sel
  refine WP.seq (WP.mono (condE_ok C E hnl hal) fun s₃ ⟨hz, E₃, _⟩ => ?_)
  refine WP.ite (decide ¬IsFast nl al n) (eval_e hz) (fun _ => ho C X E₃ hNp hnl hal) fun h => ?_
  obtain ⟨h12, h17, -⟩ : IsFast nl al n := Decidable.not_not.mp (of_decide_eq_false h)
  subst h12
  exact sealRunW_ok hF finKs_ksOk B C X hal (aad_mid hF C X E₃ hNp hnl hal (by omega))

/-- `sel` in two runs: the same path, and on it the same addresses and
branches. -/
theorem sealSel_rel (hF : ShortFacts) (v : GcmImpl) (B : BlkFn CtxMode.prepared) {other : Prog isa}
    (ho : SealLongRel CtxMode.prepared other) :
    SealLongRel CtxMode.prepared (Impl.AesGcm.X86_64.FastSeal.sel (v.withBlk B) other) := by
  intro s₀ s₀' Ctx W SP Np A D nl al n R C C' X X' hNp hnl hal hR hNp' hnl' hal' hR'
  have hlt := C.data.ok.lt
  unfold Impl.AesGcm.X86_64.FastSeal.sel
  have hw : ∀ {s₀ : State} {Np : Addr} (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n), (s₀.gpr .rcx).toNat = nl →
      (s₀.gpr .r9).toNat = al → ∀ s, OneEntry s₀ Ctx W SP A D n s →
      WP isa Impl.AesGcm.X86_64.Fast.cond s fun u => u.zf = some (decide ¬IsFast nl al n) ∧
        OneEntry s₀ Ctx W SP A D n u :=
    fun C hnl hal s h => WP.mono (condE_ok C h hnl hal) fun _ ⟨z, E, _⟩ => ⟨z, E⟩
  have c := rel_next (Fast.cond_rel (F₁ := OneEntry s₀ Ctx W SP A D n) (F₂ := OneEntry s₀' Ctx W SP A D n)
      (fun _ h => condS_of h hnl hal) (fun _ h => condS_of h hnl' hal')
      (by rw [← hnl]; exact BitVec.isLt _) (by rw [← hal]; exact BitVec.isLt _) (by omega))
    (hw C hnl hal) (hw C' hnl' hal')
  refine RelCT.seq c (rel_ite_e (fun _ _ h => by rw [h.1.1, h.2.1])
    ((ho C C' X X' hNp hnl hal hR hNp' hnl' hal' hR').mono
      (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h) ?_)
  by_cases hs : IsFast nl al n
  · obtain ⟨h12, h17, -⟩ := hs
    subst h12
    have L := C.lay
    exact (sealRunW_rel hF finKs_ksOk finKs_rel B C C' X X' hNp hnl hal hR hNp' hnl' hal' hR'
      ((Fast.aad_rel L C.dE (M := CtxMode.prepared) (R := R) (Np := Np) (A := A) (al := al) (by omega)).mono
        (P' := fun (s₁ s₂ : State) => OneEntry s₀ Ctx W SP A D n s₁ ∧ OneEntry s₀' Ctx W SP A D n s₂)
        (fun _ _ g => ⟨g.1.aadPre C X hNp hnl hal hR, g.2.aadPre C' X' hNp' hnl' hal' hR'⟩) fun _ _ _ => trivial)
      (fun _ h => aad_mid hF C X h hNp hnl hal (by omega))
      (fun _ h => aad_mid hF C' X' h hNp' hnl' hal' (by omega))).mono
      (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩) fun _ _ h => h
  · exact RelCT.of_false fun _ _ h => by have := h.1.1.1.symm.trans h.2; simp [hs] at this

end VG.Proof.AesGcm.X86_64.FastSeal
