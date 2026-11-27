module

import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP384r1Literals
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP384r1Literals
meta import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP384r1.AArch64.Joint
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP384r1.AArch64.Joint
public import VerifiedGarbage.Impl.NatPairs
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.State
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Points
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Front
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.Math
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointAll

/-! ### `Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Points`, which this module and modules that import it used -/

section

/-!
# Joint radix-four verification over this curve on AArch64: the points

What other modules use of `Proof/Ecdsa/Verify/AArch64/JointAll.lean` at the
curve's kit (`Joint/State.lean`), for the curve's own programs
(`Impl/Ecdsa/Verify/BrainpoolP384r1/AArch64/Joint.lean`), which are the kit's by definition.
-/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdsa.Verify.AArch64 (U V RM')
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Proof.Ed25519.AArch64 (Keeps)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

abbrev gSource : Pt := cfg.pt GX GY ONEP
abbrev qSource : Pt := cfg.pt PX PY ONEP
abbrev arithmeticWork : List (Nat × Nat) := JointKit.arithmeticWork cfg
abbrev Inputs (base : Addr) (P Q : Point C) (s : State) : Prop := JointKit.Inputs cfg base P Q s
abbrev Bits (base : Addr) (u v : Nat) (s : State) : Prop := JointKit.Bits cfg base u v s
abbrev digitPair (u v j : Nat) : Nat := JointKit.digitPair u v j
abbrev Table (base : Addr) (P Q : Point C) (m : Nat) (s : State) : Prop := JointKit.Table cfg base P Q m s
abbrev Running (base : Addr) (P Q : Point C) (u v j : Nat) (s : State) : Prop :=
  JointKit.Running cfg base P Q u v j s

theorem Changes.of_keeps {base : Addr} {W : List (Nat × Nat)} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (h0 : .x0 ∉ rs) : Changes base W s t :=
  JointKit.Changes.of_keeps h h0

theorem loopWork_sub : ∀ w ∈ loopWork,w ∈ arithmeticWork :=
  JointKit.loopWork_sub (c := cfg)

theorem double_points {base : Addr} {P Q A : Point C} {s : State}
    (hc : BaseCfgOk cfg) (hC : Law C) (hI : Inputs base P Q s)
    (hA : onCurve C A = true) (hp : PointAt base s resultPt A) :
    WP isa double s fun t => Changes base loopWork s t ∧ Inputs base P Q t ∧
      PointAt base t resultPt (add A A) ∧ t.gpr .x19 = s.gpr .x19 :=
  JointKit.double_points (c := cfg) hc hC hI hA hp

theorem digit_ok {base : Addr} {s : State} (hs : Scr s base 8192) {u v j : Nat}
    (hb : Bits base u v s) (hj : j < 192) (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (.block digit) s fun t =>
      t.gpr .x2=BitVec.ofNat 64 (digitPair u v j) ∧ Keeps [.x2,.x4,.x6,.x16] s t :=
  JointKit.digit_ok (c := cfg) hs hb hj h19

theorem step_ok {base : Addr} {P Q : Point C} {u v j : Nat} {s : State}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (h1 : 1 ≤ j) (h256 : j ≤ 192) (h : Running base P Q u v j s) :
    WP isa step s fun t => Changes base loopWork s t ∧ Running base P Q u v (j-1) t :=
  JointKit.step_ok (c := cfg) hc hC hP hQ h1 (Nat.le_trans h256 (by decide)) h

theorem setup_ok {base : Addr} {s₀ s : State} {g : Reg → BitVec 64} {P : Point C}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hM : Mid cfg s₀ base g s)
    (hrep : Rep C (val base s qSource.x) (val base s qSource.y) (val base s qSource.z) P) :
    WP isa setup s fun t => Changes base work s t ∧
      Running base (G C) P (sv cfg base s U) (sv cfg base s V) 192 t :=
  JointKit.setupCompact_ok (c := cfg) rounds hc hC hP hM hrep

theorem points_ok {base : Addr} {s₀ s : State} {g : Reg → BitVec 64} {P : Point C}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hM : Mid cfg s₀ base g s)
    (hrep : Rep C (val base s qSource.x) (val base s qSource.y) (val base s qSource.z) P) :
    WP isa points s fun t => FinalState cfg s₀ base g t ∧
      Rep C (val base t resultPt.x) (val base t resultPt.y) (val base t resultPt.z)
        (add (mul (sv cfg base s U) (G C)) (mul (sv cfg base s V) P)) :=
  JointKit.pointsCompact_ok (c := cfg) rounds hc hC hP hM hrep

end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

end

end

/-! ### `Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Main`, which this module and modules that import it used -/

section

/-! ### `Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Math`, which this module and modules that import it used -/

section

/-! Curve-independent radix-four group identities, shared with Brainpool. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
export VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint
  (pair pair_curve pair_add pair_zero shift_radix stage at_step at_zero at_top
   pair_generator pair_peer previous previous_lt table_step point_comm)
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

end

end

/-! Full ECDSA verification correctness with the joint public multiplier. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (U V)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

theorem verify_ok (hc : BaseCfgOk cfg) (hC : Law C) {s₀ : State} (hp : FrontPre cfg s₀) :
    WP isa verify s₀ fun s' => (∀ r ∈ Cfg.saved.map Prod.fst,s'.gpr r=s₀.gpr r) ∧ VPost cfg s₀ s' :=
  JointKit.verifyWith_ok (fun hP hM hrep => points_ok hc hC hP hM hrep) hc hC hp
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

end

end

/-! Fixed-address initialization up to the joint public multiplication. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

def beforeCode : Prog isa :=
  .seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.args cfg)) <|
  .seq (Impl.Ecdh.AArch64.Cfg.prefixWith cfg (some D)) <|
  .seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.loadS cfg)) <|
  .seq (.block (Impl.Ecdh.AArch64.Cfg.peer cfg)) <|
  .seq (Impl.Ecdh.AArch64.Cfg.validate cfg) <|
  .seq (Impl.Ecdsa.Verify.AArch64.Cfg.scalars cfg) <| .seq cfg.nPow <|
  .seq (Impl.Ecdsa.Verify.AArch64.Cfg.uv cfg) (.block [])

def afterCode : Prog isa := Impl.Ecdsa.Verify.AArch64.Cfg.tail cfg

/-- The literals of `BrainpoolP384r1Literals`, under the terms this code has: `cfg`
is an abbreviation, and `materialize_code` finds a literal by its term. -/
private noncomputable abbrev validateCode.lit := BrainpoolP384r1Literals.validate.lit
private theorem validateCode.lit_eq : Impl.Ecdh.AArch64.Cfg.validate cfg = validateCode.lit :=
  BrainpoolP384r1Literals.validate.lit_eq
private noncomputable abbrev nPowCode.lit := BrainpoolP384r1Literals.nPow.lit
private theorem nPowCode.lit_eq : cfg.nPow = nPowCode.lit := BrainpoolP384r1Literals.nPow.lit_eq

materialize_code beforeCode
materialize_code afterCode

theorem prefix_ok (hc : BaseCfgOk cfg) {s : State} (hp : FrontPre cfg s) :
    WP isa beforeCode s fun t => ∃ g,Mid cfg s (s.gpr .x3) g t :=
  front_ok hc hp fun g _ _ hF => mid_ok hc hF fun _ hM => WP.block_nil ⟨g,hM⟩

theorem prefix_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3])) beforeCode :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x1,.x2,.x3])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem suffix_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0])) afterCode :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem verify_cut {s s' : State} {t : List Leak} (he : Exec isa verify s t s') :
    ∃ a b tp tc ts, Exec isa beforeCode s tp a ∧ Exec isa points a tc b ∧
      Exec isa afterCode b ts s' ∧ t=tp++tc++ts := by
  cases he with
  | seq e0 h => cases h with
    | seq e1 h => cases h with
      | seq e2 h => cases h with
        | seq e3 h => cases h with
          | seq e4 h => cases h with
            | seq e5 h => cases h with
              | seq e6 h => cases h with
                | seq e7 h => cases h with
                  | seq ec es =>
                    have nil : ∀ a : State, Exec isa (.block []) a [] a := fun _ => .block rfl
                    have ep := Exec.seq e0 (.seq e1 (.seq e2 (.seq e3 (.seq e4
                      (.seq e5 (.seq e6 (.seq e7 (nil _))))))))
                    exact ⟨_,_,_,_,_,ep,ec,es,by simp only [List.append_nil,List.append_assoc]⟩
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
