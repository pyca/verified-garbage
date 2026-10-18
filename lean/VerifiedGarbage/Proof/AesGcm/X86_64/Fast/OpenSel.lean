module

import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Mid
public import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.OpenTag
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Main
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks

/-!
# AES-GCM `open`'s path for TLS records: after the entry

Untrusted: everything here is checked by Lean. With a prepared key context,
`FastOpen.run` is `Short.openLong` with `Fast.aad`, which leaves what
`oneAad` does (`Fast.aad_mid`), and `tagP`, which leaves what `oneTag 112`
does (`tagP_ok`), so it leaves what `openOk_ok` does (`openOkW_ok`), and
`FastOpen.sel` too, with `other` for the inputs `Fast.cond` turns away:
`openSel_ok`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.FastOpen

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts KsOk LongOk)
open VG.Proof.AesGcm.X86_64.Fast (IsFast aad_mid condE_ok)

variable {any : Bool}

theorem tagP_mx : (Impl.AesGcm.X86_64.FastOpen.tagP : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel
theorem tagPA_mx :
    (Impl.AesGcm.X86_64.FastOpen.tagP Impl.AesGcm.X86_64.Short.finKsA : Prog isa).allInstrs (fun i => !loadsMxcsr i) =
      true := by
  decide +kernel
theorem tagPA_spSafe :
    (Impl.AesGcm.X86_64.FastOpen.tagP Impl.AesGcm.X86_64.Short.finKsA : Prog isa).all
      (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel
theorem tagPA_xdepth : (Impl.AesGcm.X86_64.FastOpen.tagP Impl.AesGcm.X86_64.Short.finKsA : Prog isa).x86_64Depth = 0 := by
  decide +kernel
theorem tagP_spSafe : (Impl.AesGcm.X86_64.FastOpen.tagP : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel
theorem tagP_xdepth : (Impl.AesGcm.X86_64.FastOpen.tagP : Prog isa).x86_64Depth = 0 := by decide +kernel

/-- `sel`: this path for the inputs it takes, `other` for the rest. -/
theorem openSel_ok (hF : ShortFacts) (v : GcmImpl) (B : BlkFn CtxMode.prepared) {ks : Prog isa} (hks : KsOk ks)
    {other : Prog isa} (ho : LongOk CtxMode.prepared other) :
    LongOk CtxMode.prepared (Impl.AesGcm.X86_64.FastOpen.sel (v.withBlk B) other ks any) := by
  intro s s₂ Ctx W SP Np A D T nl al n t C X E hNp hnl hal hTa hTar hTr oT oA htl hok
  unfold Impl.AesGcm.X86_64.FastOpen.sel
  refine WP.seq (WP.mono (condE_ok C E hnl hal) fun s₃ ⟨hz, E₃, K⟩ => ?_)
  rw [← K.mem] at htl
  refine WP.ite (decide ¬IsFast nl al n any) (eval_e hz) (fun _ => ho C X E₃ hNp hnl hal hTa hTar hTr oT oA htl hok)
    fun h => ?_
  obtain ⟨h12, h17, -⟩ : IsFast nl al n any := Decidable.not_not.mp (of_decide_eq_false h)
  subst h12
  exact openOkW_ok v B (tagP_ok hF hks) C X hal hTa hTar hTr oT oA htl hok (aad_mid hF C X E₃ hNp hnl hal (by omega))

/-- `openFin lng`, for `lng` that leaves what `openOk_ok` does. -/
theorem openFinW_wp {M : CtxMode} {lng : Prog isa} (hlng : LongOk M lng) {s : State}
    (hp : (Proof.AesGcm.openX86_64M M).pre s) :
    WP isa (Impl.AesGcm.X86_64.FastOpen.openFin lng) s fun s' =>
      gprPreserved s s' ∧ Proof.AesGcm.openX86_64.post s s' :=
  openM_of hp fun C X E hNp hnl hal _ hTa hTar hTr oT oA htl hok => hlng C X E hNp hnl hal hTa hTar hTr oT oA htl hok

end VG.Proof.AesGcm.X86_64.FastOpen
