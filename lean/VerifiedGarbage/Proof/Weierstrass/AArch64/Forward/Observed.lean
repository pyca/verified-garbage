import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Checked

/-! Register allocation can discard dead scratch words and introduce spills.
Its certificate therefore compares exactly the words the caller observes,
while deriving register and memory frames from the executed instructions. -/
namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

/-- A checked certificate for an arbitrary initialized environment. Inputs are
interpreted by the caller, which must establish the initial state relation. -/
structure CheckedObserved (size : Nat) (observe : Nat → Prop)
    (original optimized : List Instr) where
  nodes : Certificate
  valid : CertValid nodes
  initial : Env Nat
  left : Env Nat
  right : Env Nat
  evalLeft : eval (certDom nodes) size original initial=some left
  evalRight : eval (certDom nodes) size optimized initial=some right
  same : ∀ off,observe off → off%8=0 → off+8≤size → left.slot off=right.slot off

 theorem CheckedObserved.refine {size : Nat} {observe : Nat → Prop}
    {original optimized : List Instr}
    (cert : CheckedObserved size observe original optimized)
    (input : Nat → BitVec 64) (hsize : size≤2^64)
    {s : State} {base : Addr} {cap : Nat} (hs : Scr s base cap)
    (he : Rel (nodeVal cert.nodes input) base size cert.initial s)
    (hci : ∀ i∈original,instrBound i≤cap)
    (hcj : ∀ i∈optimized,instrBound i≤cap) {Q : State → Prop}
    (hq : WP isa (.block original) s Q) :
    WP isa (.block optimized) s fun t => ∃ u,Q u ∧
      (∀ off,observe off → off%8=0 → off+8≤size →
        word t.mem base off=word u.mem base off) ∧
      KeepRegs (optimized.flatMap instrClob) s t ∧
      Unch base (optimized.flatMap instrWrites) s.mem t.mem := by
  have hd := certDom_sound cert.valid input
  obtain ⟨u,hu,heu,_,_,_⟩ := eval_sound hsize hd hs he cert.evalLeft hci
  obtain ⟨t,ht,het,_,hkt,hmt⟩ := eval_sound hsize hd hs he cert.evalRight hcj
  apply WP.of_runBlock
  refine ⟨t,ht,u,post_of_runBlock hq hu,?_,hkt,hmt⟩
  intro off ho ha hb
  exact (het.slot off ha hb).symm.trans
    ((congrArg (fun z => (nodeVal cert.nodes input z).1)
      (cert.same off ho ha hb).symm).trans (heu.slot off ha hb))

/-- Build a pair from an explicitly supplied common input environment. The
returned data is untrusted until the evaluations above have been checked. -/
def buildPairFrom (size : Nat) (original optimized : List Instr)
    (nodes : Array Node) (initial : Env Nat) : Option Certificate := do
  let (ns,_) ← build size original nodes initial
  let (ns,_) ← build size optimized ns initial
  return toCertificate ns

end VG.Proof.Weierstrass.AArch64.Forward
