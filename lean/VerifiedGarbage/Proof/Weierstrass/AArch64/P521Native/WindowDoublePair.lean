module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowDoubleStep
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-! Two ordinary doubles alternate the buffers and return to the accumulator. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native (callNormalDouble outerBlock138 outerBlock139)
open VG.Proof.Weierstrass (dblJF)

def windowDbl (P : Fin fieldPrime×Fin fieldPrime×Fin fieldPrime) := dblJF P.1 P.2.1 P.2.2

def WindowWorkFrame (base : Addr) (m m' : Mem) : Prop :=
  ∀x,(ofs base x<1072 ∨ 1504≤ofs base x) →
    (ofs base x<4080 ∨ 4584≤ofs base x) → m' x=m x

 theorem WindowWorkFrame.trans {base : Addr} {m m' m'' : Mem}
    (h : WindowWorkFrame base m m') (k : WindowWorkFrame base m' m'') : WindowWorkFrame base m m'' :=
  fun x a b => (k x a b).trans (h x a b)

 theorem DoubleFrame.window {base : Addr} {o : Nat} {m m' : Mem} (h : DoubleFrame base o m m')
    (lo : 1072≤o) (hi : o+216≤1504) : WindowWorkFrame base m m' := by
  intro x a b
  exact h x (by omega_arith) b

def windowDoublePair : Prog isa :=
  .seq (.seq (.block outerBlock138) callNormalDouble) (.seq (.block outerBlock139) callNormalDouble)

 theorem window_double_pair_ok {s : State} {W : Nat}
    (hs : Scr s (s.gpr .x0) W) (room : 4584≤W)
    (bound : canonicalPoint s.mem (s.gpr .x0) 1072) :
    WP isa windowDoublePair s fun t =>
      canonicalPoint t.mem (s.gpr .x0) 1072 ∧
      ordinaryPoint t.mem (s.gpr .x0) 1072=windowDbl (windowDbl (ordinaryPoint s.mem (s.gpr .x0) 1072)) ∧
      WindowWorkFrame (s.gpr .x0) s.mem t.mem ∧ WindowStable s t := by
  rw [windowDoublePair,WP.seq_iff]
  refine WP.mono (window_double_step_ok hs room double_layout_forward bound (window_args_forward s))
    fun u ⟨bu,pu,fu,ku⟩ => ?_
  have hu := ku.scr hs
  have hb : canonicalPoint u.mem (u.gpr .x0) 1288 := by rw [ku.base]; exact bu
  refine WP.mono (window_double_step_ok hu room double_layout_backward hb (window_args_backward u))
    fun t ⟨bt,pt,ft,kt⟩ => ?_
  rw [ku.base] at bt pt ft
  refine ⟨bt,?_,WindowWorkFrame.trans (DoubleFrame.window fu (by decide) (by decide)) (DoubleFrame.window ft (by decide) (by decide)),ku.trans kt⟩
  change ordinaryPoint t.mem (s.gpr .x0) 1072=windowDbl (ordinaryPoint u.mem (s.gpr .x0) 1288) at pt
  rw [pt,pu]
  rfl

end VG.Proof.Weierstrass.AArch64.P521Native
