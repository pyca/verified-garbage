import VerifiedGarbage.Proof.Weierstrass.X86_64.JointPrep
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafTiming
import VerifiedGarbage.Proof.Framework.X86_64.Syms

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont

theorem jointPrep_relCT {c : Joint.Cfg} {base : Addr} {size u v : Nat}
    (hu : u+32≤size) (hv : v+32≤size) (hg : c.gBits+264≤size) (hq : c.K.bits+264≤size)
    (hvs : v+32≤c.gBits ∨ c.gBits+264≤v)
    (hcG : FastPrepChecks u c.gBits 7) (hcQ : FastPrepChecks v c.K.bits 5) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧
      wordsVal s.mem base u 4=wordsVal t.mem base u 4 ∧
      wordsVal s.mem base v 4=wordsVal t.mem base v 4)
      (Joint.prep c u v) (fun _ _ => True) := by
  have first := (fastPrep_relCT (base:=base) (Or.inr rfl) hu hg hcG).mono
    (P':=fun (s t : State) => Scr s base size ∧ Scr t base size ∧
      wordsVal s.mem base u 4=wordsVal t.mem base u 4 ∧
      wordsVal s.mem base v 4=wordsVal t.mem base v 4)
    (fun _ _ h => ⟨h.1,h.2.1,h.2.2.1⟩) (fun _ _ h => h)
  have framed := first.wpDep (F:=fun (s t : State) => Scr t base size ∧
    wordsVal t.mem base v 4=wordsVal s.mem base v 4) (by
      intro s t ⟨ss,st,_,_⟩
      have stage (a : State) (sa : Scr a base size) :
          WP isa (Impl.Weierstrass.X86_64.FastNaf.prep u c.gBits 7) a (fun b =>
            Scr b base size ∧ wordsVal b.mem base v 4=wordsVal a.mem base v 4) :=
        WP.mono (fastPrepDigits_ok (Or.inr rfl) sa hu hg) (fun _ ⟨_,hk,ho⟩ =>
          ⟨sa.of_keepRegs hk (by decide),ho.wordsVal hvs (by have := sa.nowrap; omega)⟩)
      exact ⟨stage s ss,stage t st⟩)
  apply RelCT.seq (framed.mono
    (Q':=fun (s t : State) => Scr s base size ∧ Scr t base size ∧ wordsVal s.mem base v 4=wordsVal t.mem base v 4)
    (fun _ _ h => h)
    (fun _ _ ⟨_,_,_,hp,ps,pt⟩ => ⟨ps.1,pt.1,ps.2.trans (hp.2.2.2.trans pt.2.symm)⟩))
  exact fastPrep_relCT (Or.inl rfl) hv hq hcQ

end VG.Proof.Weierstrass.X86_64
