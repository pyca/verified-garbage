module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.Joint
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNafPrep
import VerifiedGarbage.Proof.Weierstrass.X86_64.FastNaf16
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInvariant
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Weierstrass.FastNaf
public import VerifiedGarbage.Proof.Weierstrass.X86_64.NafPrep
import VerifiedGarbage.Proof.Framework.Mem

/-! Both scalar recoders retain the second input and the first digit buffer. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont

def jointPrepRanges (c : Joint.Cfg) : List (Nat×Nat) :=
  [(c.gBits,jointGSpan c),(c.K.bits,64*c.K.M.n+8)]

/-- The recoders call nothing: their inlined code is their code. -/
theorem jointPrep_inline (c : Joint.Cfg) (u v : Nat) : (Joint.prep c u v).inline=Joint.prep c u v := by
  unfold Joint.prep
  split
  · rfl
  · split <;> rfl

/-- What the recoders leave, of the state `s` before them. -/
def JointPrepPost (c : Joint.Cfg) (base : Addr) (size u v : Nat) (s t : State) : Prop :=
  Scr t base size ∧
    (∀ j<jointGLen c,t.mem (off base (c.gBits+j))=
      jointGByte c (wordsVal s.mem base u c.K.M.n) j) ∧
    (∀ j<64*c.K.M.n+1,t.mem (off base (c.K.bits+j))=
      FastNaf.byte 5 (wordsVal s.mem base v c.K.M.n) j) ∧
    KeepRegs (nafPrepClobN c.K.M.n) s t ∧ Unch base (jointPrepRanges c) s.mem t.mem

/-- The generator's recoder and then the peer's, of what each leaves. -/
theorem jointPrepOf_ok {c : Joint.Cfg} {pG pQ : Prog isa} {s : State} {base : Addr} {size u v : Nat}
    (hs : Scr s base size) (hv : v+8*c.K.M.n≤size)
    (hg : c.gBits+jointGSpan c≤size) (hq : c.K.bits+64*c.K.M.n+8≤size)
    (hsep : c.gBits+jointGSpan c≤c.K.bits ∨ c.K.bits+64*c.K.M.n+8≤c.gBits)
    (hvs : v+8*c.K.M.n≤c.gBits ∨ c.gBits+jointGSpan c≤v)
    (first : WP isa pG s fun a =>
      (∀ j<jointGLen c,a.mem (off base (c.gBits+j))=jointGByte c (wordsVal s.mem base u c.K.M.n) j) ∧
      KeepRegs (nafPrepClobN c.K.M.n) s a ∧ Outside base c.gBits (jointGSpan c) s.mem a.mem)
    (second : ∀ a : State,Scr a base size → WP isa pQ a fun t =>
      (∀ j<64*c.K.M.n+1,t.mem (off base (c.K.bits+j))=
        FastNaf.byte 5 (wordsVal a.mem base v c.K.M.n) j) ∧
      KeepRegs (nafPrepClobN c.K.M.n) a t ∧ Outside base c.K.bits (64*c.K.M.n+8) a.mem t.mem) :
    WP isa (.seq pG pQ) s (JointPrepPost c base size u v s) := by
  have hgl := jointGLen_lt_span c
  have hq' := hq
  refine WP.seq (WP.mono first fun a ⟨da,ka,oa⟩ => ?_)
  have sa := hs.of_keepRegs ka (notin_clobN (by decide) (by decide))
  have va : wordsVal a.mem base v c.K.M.n=wordsVal s.mem base v c.K.M.n :=
    oa.wordsVal hvs (by have := hs.nowrap; omega_using [hv, this])
  refine WP.mono (second a sa) fun t ⟨dt,kt,ot⟩ => ?_
  refine ⟨sa.of_keepRegs kt (notin_clobN (by decide) (by decide)),?_,?_,ka.trans kt,oa.unch.trans ot.unch⟩
  · intro j hj
    rw [ot.unch.byte (by
      intro w hw; rw [List.mem_singleton.mp hw]; dsimp only; omega_using [hsep, hgl, hj])
      (by have := hs.nowrap; omega_using [hg, hgl, hj, this])]
    exact da j hj
  · rw [va] at dt
    exact dt

/-- What `Joint.prepB`, the recoders without branches on the scalars' bits, leaves. -/
theorem jointPrepB_ok {c : Joint.Cfg} {s : State} {base : Addr} {size u v : Nat}
    (hn : c.K.M.n=4 ∨ c.K.M.n=6 ∨ c.K.M.n=9) (h9 : c.gw=9)
    (hs : Scr s base size) (hu : u+8*c.K.M.n≤size) (hv : v+8*c.K.M.n≤size)
    (hg : c.gBits+jointGSpan c≤size) (hq : c.K.bits+64*c.K.M.n+8≤size)
    (hsep : c.gBits+jointGSpan c≤c.K.bits ∨ c.K.bits+64*c.K.M.n+8≤c.gBits)
    (hvs : v+8*c.K.M.n≤c.gBits ∨ c.gBits+jointGSpan c≤v) :
    WP isa (Joint.prepB c u v) s (JointPrepPost c base size u v s) := by
  have first : WP isa (FastNaf.prepB16 c.K.M.n u c.gBits) s fun a =>
      (∀ j<jointGLen c,a.mem (off base (c.gBits+j))=jointGByte c (wordsVal s.mem base u c.K.M.n) j) ∧
      KeepRegs (nafPrepClobN c.K.M.n) s a ∧ Outside base c.gBits (jointGSpan c) s.mem a.mem := by
    have hg' := hg
    simp only [jointGSpan,h9,ite_true] at hg'
    simpa only [jointGLen,jointGSpan,jointGByte,h9,ite_true] using fastPrepDigitsB16_ok hn hs hu hg'
  exact jointPrepOf_ok hs hv hg hq hsep hvs first
    (fun a sa => fastPrepDigitsB_ok hn sa hv hq)

theorem jointPrep_ok {c : Joint.Cfg} {s : State} {base : Addr} {size u v : Nat}
    (hn : c.K.M.n=4 ∨ c.K.M.n=6 ∨ c.K.M.n=9)
    (hs : Scr s base size) (hu : u+8*c.K.M.n≤size) (hv : v+8*c.K.M.n≤size)
    (hg : c.gBits+jointGSpan c≤size) (hq : c.K.bits+64*c.K.M.n+8≤size)
    (hsep : c.gBits+jointGSpan c≤c.K.bits ∨ c.K.bits+64*c.K.M.n+8≤c.gBits)
    (hvs : v+8*c.K.M.n≤c.gBits ∨ c.gBits+jointGSpan c≤v) (hB : c.recodeB=true → c.gw=9) :
    WP isa (Joint.prep c u v) s fun t => Scr t base size ∧
      (∀ j<jointGLen c,t.mem (off base (c.gBits+j))=
        jointGByte c (wordsVal s.mem base u c.K.M.n) j) ∧
      (∀ j<64*c.K.M.n+1,t.mem (off base (c.K.bits+j))=
        FastNaf.byte 5 (wordsVal s.mem base v c.K.M.n) j) ∧
      KeepRegs (nafPrepClobN c.K.M.n) s t ∧ Unch base (jointPrepRanges c) s.mem t.mem := by
  rw [Joint.prep]
  by_cases hr : c.recodeB=true
  · simp only [hr,ite_true]
    exact jointPrepB_ok hn (hB hr) hs hu hv hg hq hsep hvs
  simp only [hr,Bool.false_eq_true,ite_false]
  have first : WP isa (if c.gw=9 then FastNaf.prepN16 c.K.M.n u c.gBits else
      FastNaf.prepN c.K.M.n u c.gBits 7) s fun a =>
      (∀ j<jointGLen c,a.mem (off base (c.gBits+j))=jointGByte c (wordsVal s.mem base u c.K.M.n) j) ∧
      KeepRegs (nafPrepClobN c.K.M.n) s a ∧ Outside base c.gBits (jointGSpan c) s.mem a.mem := by
    by_cases h9 : c.gw=9
    · simp only [jointGSpan,h9,ite_true] at hg
      simpa only [jointGLen,jointGSpan,jointGByte,h9,ite_true] using fastPrepDigits16_ok hn hs hu hg
    · simp only [jointGSpan,h9,ite_false] at hg
      simpa only [jointGLen,jointGSpan,jointGByte,h9,ite_false] using
        fastPrepDigits_ok hn (Or.inr rfl) hs hu hg
  exact jointPrepOf_ok hs hv hg hq hsep hvs first
    (fun a sa => fastPrepDigits_ok hn (Or.inl rfl) sa hv hq)

end VG.Proof.Weierstrass.X86_64
