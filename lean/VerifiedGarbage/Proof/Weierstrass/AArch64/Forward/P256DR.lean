import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
import VerifiedGarbage.Impl.Ecdsa.P256.AArch64
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Jacobian
import VerifiedGarbage.Impl.Weierstrass.AArch64.Forward
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Literal

namespace VG.Proof.Weierstrass.AArch64.Forward.P256DR
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Weierstrass.AArch64.Forward


def K := VG.Impl.Ecdsa.Verify.AArch64.Cfg.jacWinCfg VG.Impl.Ecdsa.AArch64.p256

def original := fprog K.M (dblJMul K.S K.D K.R)
def optimized := VG.Impl.Weierstrass.AArch64.Forward.optimize original
forward_state bundle :=
  let ns := (buildPair 8192 original optimized).getD ⟨.empty,.empty⟩
  (ns, evalData (certDom ns) 8192 original initialEnv,
       evalData (certDom ns) 8192 optimized initialEnv)
noncomputable def nodes := bundle.1
noncomputable def leftData := bundle.2.1
noncomputable def rightData := bundle.2.2
theorem original_lit : original=P256Bounds.leftDR.lit := P256Bounds.leftDR.lit_eq
theorem optimized_lit : optimized=P256Bounds.rightDR.lit := P256Bounds.rightDR.lit_eq

theorem valid : CertValid nodes := by decide +kernel

theorem inputs : Inputs nodes 8192 := by
  have h : ∀ i : Fin 1024,nodes.nodes.lookup (i.val+1)=some (.input (8*i.val)) := by decide +kernel
  intro off ha hb
  have ho : off=8*(off/8) := by omega
  simpa only [←ho] using h ⟨off/8,by omega⟩

noncomputable def left : Env Nat := fromData initialEnv (leftData.getD (.empty, .empty, none))
noncomputable def right : Env Nat := fromData initialEnv (rightData.getD (.empty, .empty, none))

private theorem some_getD {α : Type} {o : Option α} (d : α) (h : o.isSome=true) :
    o=some (o.getD d) := by cases o <;> simp_all

theorem evalLeft : eval (certDom nodes) 8192 original initialEnv=some left := by
  rw [original_lit]
  exact eval_of_data (d := leftData.getD (.empty, .empty, none)) (by kernel_rfl)

theorem evalRight : eval (certDom nodes) 8192 optimized initialEnv=some right := by
  rw [optimized_lit]
  exact eval_of_data (d := rightData.getD (.empty, .empty, none)) (by kernel_rfl)

theorem same : ∀ off,off%8=0 → off+8≤8192 → left.slot off=right.slot off := by
  have h : ∀ i : Fin 1024,left.slot (8*i.val)=right.slot (8*i.val) := by decide +kernel
  intro off ha hb
  have ho : off=8*(off/8) := by omega
  simpa only [←ho] using h ⟨off/8,by omega⟩

noncomputable def checked : Checked 8192 original optimized where
  nodes := nodes
  valid := valid
  inputs := inputs
  left := left
  right := right
  evalLeft := evalLeft
  evalRight := evalRight
  same := same
  boundLeft := by rw [original_lit]; decide +kernel
  boundRight := by rw [optimized_lit]; decide +kernel

end VG.Proof.Weierstrass.AArch64.Forward.P256DR
