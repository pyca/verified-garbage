import VerifiedGarbage.Impl.P256.EcdhDouble
import VerifiedGarbage.Proof.P256.VerifyAllocated.Case
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Literal
import VerifiedGarbage.Proof.Framework.AArch64.Taint

namespace VG.Proof.P256.EcdhDouble.Certificate
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Weierstrass.AArch64.Forward

def original := VG.Impl.P256.EcdhDouble.raw
def optimized := VG.Impl.P256.EcdhDouble.code
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

def observe := VG.Proof.P256.VerifyAllocated.observe .doubleRR
instance (off : Nat) : Decidable (observe off) := by unfold observe; infer_instance

theorem same : ∀ off,observe off → off%8=0 → off+8≤8192 → left.slot off=right.slot off := by
  have h : ∀ i : Fin 1024,observe (8*i.val) → left.slot (8*i.val)=right.slot (8*i.val) := by decide +kernel
  intro off hv ha hb
  have ho : off=8*(off/8) := by omega
  have hh := h ⟨off/8,by omega⟩
  simpa only [←ho] using hh (by simpa only [←ho] using hv)

noncomputable def checked : CheckedObserved 8192 observe original optimized where
  nodes := nodes
  valid := valid
  initial := initialEnv
  left := left
  right := right
  evalLeft := evalLeft
  evalRight := evalRight
  same := same

theorem leftBound : ∀ i∈original,instrBound i≤8192 := by
  have h : leftCode.lit.all (fun i => decide (instrBound i≤8192))=true := by decide +kernel
  rw [original_lit]
  intro i hi
  exact of_decide_eq_true ((List.all_eq_true.mp h) i hi)

theorem rightBound : ∀ i∈optimized,instrBound i≤8192 := by
  have h : rightCode.lit.all (fun i => decide (instrBound i≤8192))=true := by decide +kernel
  rw [optimized_lit]
  intro i hi
  exact of_decide_eq_true ((List.all_eq_true.mp h) i hi)

theorem clob : ∀ r∈optimized.flatMap instrClob,
    r∈VG.Proof.Weierstrass.AArch64.allocatedRegs := by
  rw [optimized_lit]
  decide +kernel

theorem writes : ∀ w∈optimized.flatMap instrWrites,
    ∃ w'∈VG.Proof.P256.VerifyAllocated.work,w'.1≤w.1 ∧ w.1+w.2≤w'.1+w'.2 := by
  rw [optimized_lit]
  decide +kernel

open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass.AArch64

theorem refine {base : Addr} {s : State} (hs : Scr s base 8192) {Q : State → Prop}
    (hq : WP isa (.block original) s Q) :
    WP isa Impl.P256.EcdhDouble.program s fun t => ∃ u,Q u ∧
      (∀ off,observe off → off%8=0 → off+8≤8192 →
        word t.mem base off=word u.mem base off) ∧
      AllocatedFrame allocatedRegs base VerifyAllocated.work s t := by
  exact WP.mono (checked.refine (word s.mem base) (by decide) hs (initial_rel inputs s base)
    leftBound rightBound hq) fun _ ⟨u,hu,hw,hk,hm⟩ => ⟨u,hu,hw,hk.mono clob,hm.cover writes⟩

theorem ct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
    Impl.P256.EcdhDouble.program := by
  change ConstantTime isa _ _ (.block optimized)
  rw [optimized_lit]
  exact VG.Taint.constantTime (A:=taint) (hc:=.block (List.replicate 5 (Taint.ofRegs [.x0])))
    (Taint.ofRegs [.x0]) (fun _ _ _ _ h => h) (by decide +kernel)

end VG.Proof.P256.EcdhDouble.Certificate
