import VerifiedGarbage.Impl.Weierstrass.X86_64.Joint
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafPrep
import VerifiedGarbage.Proof.Weierstrass.Unch

/-! Both scalar recoders retain the second input and the first digit buffer. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont

def jointPrepRanges (c : Joint.Cfg) : List (Nat×Nat) := [(c.gBits,264),(c.K.bits,264)]

theorem jointPrep_ok {c : Joint.Cfg} {s : State} {base : Addr} {size u v : Nat}
    (hs : Scr s base size) (hu : u+32≤size) (hv : v+32≤size)
    (hg : c.gBits+264≤size) (hq : c.K.bits+264≤size)
    (hsep : c.gBits+264≤c.K.bits ∨ c.K.bits+264≤c.gBits)
    (hvs : v+32≤c.gBits ∨ c.gBits+264≤v) :
    WP isa (Joint.prep c u v) s fun t => Scr t base size ∧
      (∀ j<257,t.mem (off base (c.gBits+j))=FastNaf.byte 7 (wordsVal s.mem base u 4) j) ∧
      (∀ j<257,t.mem (off base (c.K.bits+j))=FastNaf.byte 5 (wordsVal s.mem base v 4) j) ∧
      KeepRegs nafPrepClob s t ∧ Unch base (jointPrepRanges c) s.mem t.mem := by
  refine WP.seq (WP.mono (fastPrepDigits_ok (Or.inr rfl) hs hu hg) fun a ⟨da,ka,oa⟩ => ?_)
  have sa := hs.of_keepRegs ka (by decide)
  have va : wordsVal a.mem base v 4=wordsVal s.mem base v 4 :=
    oa.wordsVal hvs (by have := hs.nowrap; omega)
  refine WP.mono (fastPrepDigits_ok (Or.inl rfl) sa hv hq) fun t ⟨dt,kt,ot⟩ => ?_
  refine ⟨sa.of_keepRegs kt (by decide),?_,?_,ka.trans kt,oa.unch.trans ot.unch⟩
  · intro j hj
    rw [ot.unch.byte (by
      intro w hw; rw [List.mem_singleton.mp hw]; dsimp only; omega)
      (by have := hs.nowrap; omega)]
    exact da j hj
  · rw [va] at dt
    exact dt

end VG.Proof.Weierstrass.X86_64
