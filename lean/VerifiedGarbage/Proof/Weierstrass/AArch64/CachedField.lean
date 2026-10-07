import VerifiedGarbage.Impl.Weierstrass.AArch64.CachedJac
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Jacobian
import VerifiedGarbage.Impl.Ecdsa.P256.AArch64
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd

namespace VG.Proof.Weierstrass.AArch64.CachedField
open VG VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64
open Spec.Weierstrass

def K : WinCfg := VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg p256
def head : List FOp := VG.Impl.Weierstrass.CachedJac.head K.S K.R K.E
def tail : List FOp := jacTail K.S K.R K.E K.D

theorem head_lit : head=[.mul 800 576 576,.mul 864 512 5400,.mul 896 704 800,
  .mul 928 544 5432,.mul 960 736 576,.mul 960 960 800,
  .sub 896 896 864,.sub 960 960 928] := rfl

theorem tail_lit : tail=[.mul 800 896 896,.mul 832 800 896,.mul 864 864 800,.mul 608 960 960,
  .sub 608 608 832,.sub 608 608 864,.sub 608 608 864,
  .sub 640 864 608,.mul 640 960 640,.mul 928 928 832,.sub 640 640 928,
  .mul 672 576 768,.mul 672 672 896] := rfl

section
variable {F : Type} [Lean.Grind.CommRing F]

theorem head_values (E : Nat → F)
    (h2 : E 5400=E 768*E 768) (h3 : E 5432=E 768*(E 768*E 768)) :
    runOps head E 896=E 704*(E 576*E 576)-E 512*(E 768*E 768) ∧
    runOps head E 960=E 736*E 576*(E 576*E 576)-E 544*E 768*(E 768*E 768) := by
  rw [head_lit]
  simp only [runOps,List.foldl_cons,List.foldl_nil,FOp.run,Function.update_apply]
  simp only [ite_true,h2,h3]
  constructor <;> grind

theorem full_values (E : Nat → F)
    (h2 : E 5400=E 768*E 768) (h3 : E 5432=E 768*(E 768*E 768)) :
    (runOps (head++tail) E 608,runOps (head++tail) E 640,runOps (head++tail) E 672)=
      jacAddF (E 512) (E 544) (E 576) (E 704) (E 736) (E 768) := by
  rw [head_lit,tail_lit]
  simp only [List.cons_append,List.nil_append,runOps,List.foldl_cons,List.foldl_nil,FOp.run,Function.update_apply]
  simp only [ite_true,h2,h3,jacAddF,Prod.mk.injEq]
  constructor
  · grind
  constructor <;> grind

end
end VG.Proof.Weierstrass.AArch64.CachedField
