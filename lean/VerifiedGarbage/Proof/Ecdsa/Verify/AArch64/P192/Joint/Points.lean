module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Joint.State
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointAll

/-!
# Joint radix-four verification over this curve on AArch64: the points

What other modules use of `Proof/Ecdsa/Verify/AArch64/JointAll.lean` at the
curve's kit (`Joint/State.lean`), for the curve's own programs
(`Impl/Ecdsa/Verify/P192/AArch64/Joint.lean`), which are the kit's by definition.
-/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P192.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdsa.Verify.AArch64 (U V RM')
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Proof.Ed25519.AArch64 (Keeps)
open VG.Impl.Ecdsa.Verify.AArch64.P192.Joint

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
    (hb : Bits base u v s) (hj : j < 128) (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (.block digit) s fun t =>
      t.gpr .x2=BitVec.ofNat 64 (digitPair u v j) ∧ Keeps [.x2,.x4,.x6,.x16] s t :=
  JointKit.digit_ok (c := cfg) hs hb hj h19

theorem step_ok {base : Addr} {P Q : Point C} {u v j : Nat} {s : State}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (h1 : 1 ≤ j) (h256 : j ≤ 96) (h : Running base P Q u v j s) :
    WP isa step s fun t => Changes base loopWork s t ∧ Running base P Q u v (j-1) t :=
  JointKit.step_ok (c := cfg) hc hC hP hQ h1 (Nat.le_trans h256 (by decide)) h

theorem setup_ok {base : Addr} {s₀ s : State} {g : Reg → BitVec 64} {P : Point C}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hM : Mid cfg s₀ base g s)
    (hrep : Rep C (val base s qSource.x) (val base s qSource.y) (val base s qSource.z) P) :
    WP isa setup s fun t => Changes base work s t ∧
      Running base (G C) P (sv cfg base s U) (sv cfg base s V) 96 t :=
  JointKit.setup_ok (c := cfg) rounds hc hC hP hM hrep

theorem points_ok {base : Addr} {s₀ s : State} {g : Reg → BitVec 64} {P : Point C}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hM : Mid cfg s₀ base g s)
    (hrep : Rep C (val base s qSource.x) (val base s qSource.y) (val base s qSource.z) P) :
    WP isa points s fun t => FinalState cfg s₀ base g t ∧
      Rep C (val base t resultPt.x) (val base t resultPt.y) (val base t resultPt.z)
        (add (mul (sv cfg base s U) (G C)) (mul (sv cfg base s V) P)) :=
  JointKit.points_ok (c := cfg) rounds hc hC hP hM hrep

end VG.Proof.Ecdsa.Verify.AArch64.P192.Joint
