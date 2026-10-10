import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.DeadOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.WellFormed
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Checked

/-! `optimize` is proved correct once, for every block the interpreter over
concrete words runs: the optimized block runs too and leaves the same word in
every slot. A block refines to its optimization when it passes the syntactic
check `wfK` and both blocks' accesses fit the scratch area, all evaluated in
time linear in the block, with no certificate to build or check. -/

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Impl.Weierstrass.AArch64.Forward

theorem optimize_ok {size : Nat} {is : List Instr} {e l : Env CVal} (h : eval concDom size is e=some l) :
    ∃ r,eval concDom size (optimize is) e=some r ∧ ∀ off,(l.slot off).1=(r.slot off).1 := by
  obtain ⟨r₁,h₁,e₁⟩ := forward_ok h
  obtain ⟨r₂,h₂,e₂⟩ := foldMoves_ok (forward is) ⟨fun _ _ => rfl,fun _ => rfl,rfl⟩ h₁
  obtain ⟨r₃,h₃,e₃⟩ := deadStores_ok h₂
  exact ⟨r₃,h₃,fun off => (e₁.slot off).trans ((e₂.slot off).trans (e₃ off))⟩

/-- `optimized` is `optimize original`, which the interpreter runs, and both
blocks' accesses fit `size` bytes. -/
structure OptChecked (size : Nat) (original optimized : List Instr) : Prop where
  opt : optimized=optimize original
  wf : wfK size original (RegSet.empty,false)=true
  boundLeft : ∀ w∈original.flatMap instrWrites,w.1+w.2≤size
  boundRight : ∀ w∈optimized.flatMap instrWrites,w.1+w.2≤size

theorem OptChecked.refine {size : Nat} {original optimized : List Instr}
    (cert : OptChecked size original optimized) (ha : size%8=0) (hsize : size≤2^64)
    {s : State} {base : Addr} {cap : Nat} (hs : Scr s base cap)
    (hci : ∀ i∈original,instrBound i≤cap) (hcj : ∀ i∈optimized,instrBound i≤cap) {Q : State → Prop}
    (hq : WP isa (.block original) s Q) :
    WP isa (.block optimized) s fun t => ∃ u,Q u ∧ t.mem=u.mem ∧
      KeepRegs (optimized.flatMap instrClob) s t := by
  obtain ⟨l,hl⟩ := eval_of_wfK original cert.wf (e := concEnv s base)
    ⟨fun _ h => absurd h (RegSet.not_mem_empty _),fun h => by cases h⟩
  obtain ⟨r,hr,hsl⟩ := optimize_ok hl
  rw [← cert.opt] at hr
  exact refine_words concDom_sound hs ha hsize (concEnv_rel s base size) hl hr
    (fun off _ _ => hsl off) cert.boundLeft cert.boundRight hci hcj hq

end VG.Proof.Weierstrass.AArch64.Forward
