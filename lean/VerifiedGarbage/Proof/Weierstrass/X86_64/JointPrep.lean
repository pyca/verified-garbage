import VerifiedGarbage.Impl.Weierstrass.X86_64.Joint
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafPrep
import VerifiedGarbage.Proof.Weierstrass.Unch

/-! Both scalar recoders retain the second input and the first digit buffer. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont

def jointPrepRanges (c : Joint.Cfg) : List (Nat×Nat) :=
  [(c.gBits,64*c.K.M.n+8),(c.K.bits,64*c.K.M.n+8)]

theorem jointPrep_ok {c : Joint.Cfg} {s : State} {base : Addr} {size u v : Nat}
    (hn : c.K.M.n=4 ∨ c.K.M.n=6 ∨ c.K.M.n=9)
    (hs : Scr s base size) (hu : u+8*c.K.M.n≤size) (hv : v+8*c.K.M.n≤size)
    (hg : c.gBits+64*c.K.M.n+8≤size) (hq : c.K.bits+64*c.K.M.n+8≤size)
    (hsep : c.gBits+64*c.K.M.n+8≤c.K.bits ∨ c.K.bits+64*c.K.M.n+8≤c.gBits)
    (hvs : v+8*c.K.M.n≤c.gBits ∨ c.gBits+64*c.K.M.n+8≤v) :
    WP isa (Joint.prep c u v) s fun t => Scr t base size ∧
      (∀ j<64*c.K.M.n+1,t.mem (off base (c.gBits+j))=
        FastNaf.byte 7 (wordsVal s.mem base u c.K.M.n) j) ∧
      (∀ j<64*c.K.M.n+1,t.mem (off base (c.K.bits+j))=
        FastNaf.byte 5 (wordsVal s.mem base v c.K.M.n) j) ∧
      KeepRegs (nafPrepClobN c.K.M.n) s t ∧ Unch base (jointPrepRanges c) s.mem t.mem := by
  refine WP.seq (WP.mono (fastPrepDigits_ok hn (Or.inr rfl) hs hu hg) fun a ⟨da,ka,oa⟩ => ?_)
  have sa := hs.of_keepRegs ka (notin_clobN (by decide) (by decide))
  have va : wordsVal a.mem base v c.K.M.n=wordsVal s.mem base v c.K.M.n :=
    oa.wordsVal hvs (by have := hs.nowrap; omega)
  refine WP.mono (fastPrepDigits_ok hn (Or.inl rfl) sa hv hq) fun t ⟨dt,kt,ot⟩ => ?_
  refine ⟨sa.of_keepRegs kt (notin_clobN (by decide) (by decide)),?_,?_,ka.trans kt,oa.unch.trans ot.unch⟩
  · intro j hj
    rw [ot.unch.byte (by
      intro w hw; rw [List.mem_singleton.mp hw]; dsimp only; omega)
      (by have := hs.nowrap; omega)]
    exact da j hj
  · rw [va] at dt
    exact dt

end VG.Proof.Weierstrass.X86_64
