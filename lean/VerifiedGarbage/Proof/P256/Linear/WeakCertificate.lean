import VerifiedGarbage.Proof.P256.Linear.WeakReference
import VerifiedGarbage.Impl.P256.Linear
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Checked
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Literal
import VerifiedGarbage.Proof.Framework.AArch64.Taint

namespace VG.Proof.P256.Linear.WeakCertificate
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Weierstrass.AArch64.Forward

def original := Weak.reference 864 512 800
def optimized := VG.Impl.P256.Linear.weakAdd 864 512 800
materialize_value leftCode := original
materialize_value rightCode := optimized
certificate_value nodes := (buildPair 8192 original optimized).getD ⟨.empty,.empty⟩
theorem original_lit : original=leftCode.lit := leftCode.lit_eq
theorem optimized_lit : optimized=rightCode.lit := rightCode.lit_eq

theorem valid : CertValid nodes := by decide +kernel

theorem inputs : Inputs nodes 8192 := by
  have h : ∀ i : Fin 1024,nodes.nodes.lookup (i.val+1)=some (.input (8*i.val)) := by decide +kernel
  intro off ha hb
  have ho : off=8*(off/8) := by omega
  simpa only [←ho] using h ⟨off/8,by omega⟩

noncomputable def left : Env Nat := (eval (certDom nodes) 8192 leftCode.lit initialEnv).getD initialEnv
noncomputable def right : Env Nat := (eval (certDom nodes) 8192 rightCode.lit initialEnv).getD initialEnv

private theorem some_getD {α : Type} {o : Option α} (d : α) (h : o.isSome=true) :
    o=some (o.getD d) := by cases o <;> simp_all

theorem evalLeft : eval (certDom nodes) 8192 original initialEnv=some left := by
  rw [original_lit]
  exact some_getD initialEnv (by decide +kernel)

theorem evalRight : eval (certDom nodes) 8192 optimized initialEnv=some right := by
  rw [optimized_lit]
  exact some_getD initialEnv (by decide +kernel)

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

end VG.Proof.P256.Linear.WeakCertificate
