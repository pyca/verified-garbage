import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Build
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Double

/-!
The scheduler is untrusted. A certificate runs both instruction lists through
an abstract interpreter whose scalar steps are proved against the AArch64 ISA.
Matching final word identifiers establishes equality of all final memory;
separate register and memory frames retain the existing field contracts.

The certificate extent is independent of the caller's writable-region extent.
Every actual instruction access must separately fit that region. This allows
the same concrete certificate to serve the generic point-arithmetic lemmas
without enlarging their memory preconditions.
-/

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

/-- The certificate names each incoming scratch word; this condition contains
no assumptions about its value. -/
def Inputs (nodes : Certificate) (size : Nat) : Prop :=
  ∀ off,off%8=0 → off+8≤size → nodes.nodes.lookup (off/8+1)=some (.input off)

theorem initial_rel {nodes : Certificate} {size : Nat} (hi : Inputs nodes size)
    (s : State) (base : Addr) :
    Rel (nodeVal nodes (word s.mem base)) base size initialEnv s := by
  refine ⟨?_,?_,?_⟩
  · intro r a h; cases h
  · intro off ha hb
    change (nodeVal nodes (word s.mem base) (off/8+1)).1=_
    rw [nodeVal,hi off ha hb]
  · intro a h; cases h

/-- A reusable, untrusted certificate checked entirely inside the proof. -/
structure Checked (size : Nat) (original optimized : List Instr) where
  nodes : Certificate
  valid : CertValid nodes
  inputs : Inputs nodes size
  left : Env Nat
  right : Env Nat
  evalLeft : eval (certDom nodes) size original initialEnv=some left
  evalRight : eval (certDom nodes) size optimized initialEnv=some right
  same : ∀ off,off%8=0 → off+8≤size → left.slot off=right.slot off
  boundLeft : ∀ w∈original.flatMap instrWrites,w.1+w.2≤size
  boundRight : ∀ w∈optimized.flatMap instrWrites,w.1+w.2≤size

 theorem Checked.refine {size : Nat} {original optimized : List Instr}
    (cert : Checked size original optimized) (ha : size%8=0) (hsize : size≤2^64)
    {s : State} {base : Addr} {cap : Nat} (hs : Scr s base cap)
    (hci : ∀ i∈original,instrBound i≤cap) (hcj : ∀ i∈optimized,instrBound i≤cap) {Q : State → Prop}
    (hq : WP isa (.block original) s Q) :
    WP isa (.block optimized) s fun t => ∃ u,Q u ∧ t.mem=u.mem ∧
      KeepRegs (optimized.flatMap instrClob) s t :=
  refine_wp (certDom_sound cert.valid _) hs ha hsize (initial_rel cert.inputs s base)
    cert.evalLeft cert.evalRight cert.same cert.boundLeft cert.boundRight hci hcj hq

end VG.Proof.Weierstrass.AArch64.Forward
