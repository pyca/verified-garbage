module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafTiming
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNaf16Timing
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInvariant
public import VerifiedGarbage.Impl.Weierstrass.X86_64.Joint
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafPrep

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont

/-- The timing checks of the generator's recoder, of its width (`Joint.Cfg.gw`). -/
def JointPrepGChecks (c : Joint.Cfg) (u : Nat) : Prop :=
  if c.gw=9 then FastPrepChecks16 c.K.M.n u c.gBits else FastPrepChecks c.K.M.n u c.gBits 7

theorem jointPrep_relCT {c : Joint.Cfg} {base : Addr} {size u v : Nat} (hn : c.K.M.n=4 ∨ c.K.M.n=6 ∨ c.K.M.n=9)
    (hu : u+8*c.K.M.n≤size) (hv : v+8*c.K.M.n≤size) (hg : c.gBits+jointGSpan c≤size)
    (hq : c.K.bits+64*c.K.M.n+8≤size)
    (hvs : v+8*c.K.M.n≤c.gBits ∨ c.gBits+jointGSpan c≤v)
    (hcG : JointPrepGChecks c u) (hcQ : FastPrepChecks c.K.M.n v c.K.bits 5) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      wordsVal s.mem base u c.K.M.n=wordsVal t.mem base u c.K.M.n ∧
      wordsVal s.mem base v c.K.M.n=wordsVal t.mem base v c.K.M.n)
      (Joint.prep c u v) (fun _ _ => True) := by
  have gen : RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      wordsVal s.mem base u c.K.M.n=wordsVal t.mem base u c.K.M.n)
      (if c.gw=9 then Impl.Weierstrass.X86_64.FastNaf.prepN16 c.K.M.n u c.gBits else
        Impl.Weierstrass.X86_64.FastNaf.prepN c.K.M.n u c.gBits 7) (fun _ _ => True) := by
    by_cases h9 : c.gw=9
    · simp only [jointGSpan,h9,ite_true] at hg
      simp only [JointPrepGChecks,h9,ite_true] at hcG
      simpa only [h9,ite_true] using fastPrep16_relCT (base:=base) hn hu hg hcG
    · simp only [jointGSpan,h9,ite_false] at hg
      simp only [JointPrepGChecks,h9,ite_false] at hcG
      simpa only [h9,ite_false] using fastPrep_relCT (base:=base) hn (Or.inr rfl) hu hg hcG
  have hgs := hg
  have first := gen.mono
    (P':=fun (s t : State) => Scr s base size ∧ Scr t base size ∧
      wordsVal s.mem base u c.K.M.n=wordsVal t.mem base u c.K.M.n ∧
      wordsVal s.mem base v c.K.M.n=wordsVal t.mem base v c.K.M.n)
    (fun _ _ h => ⟨h.1,h.2.1,h.2.2.1⟩) (fun _ _ h => h)
  have framed := first.wpDep (F:=fun (s t : State) => Scr t base size ∧
    wordsVal t.mem base v c.K.M.n=wordsVal s.mem base v c.K.M.n) (by
      intro s t ⟨ss,st,_,_⟩
      have stage (a : State) (sa : Scr a base size) :
          WP isa (if c.gw=9 then Impl.Weierstrass.X86_64.FastNaf.prepN16 c.K.M.n u c.gBits else
            Impl.Weierstrass.X86_64.FastNaf.prepN c.K.M.n u c.gBits 7) a (fun b =>
            Scr b base size ∧ wordsVal b.mem base v c.K.M.n=wordsVal a.mem base v c.K.M.n) := by
        by_cases h9 : c.gw=9
        · simp only [jointGSpan,h9,ite_true] at hgs hvs
          simpa only [h9,ite_true] using
            WP.mono (fastPrepDigits16_ok hn sa hu hgs) (fun _ ⟨_,hk,ho⟩ =>
              ⟨sa.of_keepRegs hk (notin_clobN (by decide) (by decide)),
                ho.wordsVal hvs (by have := sa.nowrap; omega)⟩)
        · simp only [jointGSpan,h9,ite_false] at hgs hvs
          simpa only [h9,ite_false] using
            WP.mono (fastPrepDigits_ok hn (Or.inr rfl) sa hu hgs) (fun _ ⟨_,hk,ho⟩ =>
              ⟨sa.of_keepRegs hk (notin_clobN (by decide) (by decide)),
                ho.wordsVal hvs (by have := sa.nowrap; omega)⟩)
      exact ⟨stage s ss,stage t st⟩)
  apply RelCT.seq (framed.mono
    (Q':=fun (s t : State) => Scr s base size ∧ Scr t base size ∧
      wordsVal s.mem base v c.K.M.n=wordsVal t.mem base v c.K.M.n)
    (fun _ _ h => h)
    (fun _ _ ⟨_,_,_,hp,ps,pt⟩ => ⟨ps.1,pt.1,ps.2.trans (hp.2.2.2.trans pt.2.symm)⟩))
  exact fastPrep_relCT hn (Or.inl rfl) hv hq hcQ

end VG.Proof.Weierstrass.X86_64
