module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.WindowAll
public import VerifiedGarbage.Impl.Ecdsa.P521.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.Window3
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521

/-!
# `[k]P` by windows on PPC64LE, P-521

The curve's kit for `Proof/Ecdsa/PPC64LE/WindowAll.lean`: P-521's field, of nine words,
whose `a` is `-3` (`WAll.AKit.am3`: `rcb3`, `dblJ`, `b` at slot 40),
and three-bit windows (`WAll.Kit.w3`). Then what that proof gives of the windows on
P-521, as other modules use it: `mul_ok`, `R = [k]P` for `P` at ECDH's slots of the peer's
point and `k`'s bits in the table of bits (`MPre`), on the curve's own statements of a point in slots
(`PtOk`) and of the constants (`KC`).
-/

@[expose] public section

set_option exponentiation.threshold 1024

namespace VG.Proof.Ecdsa.PPC64LE.Window.P521

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Ecdsa.PPC64LE.Window
open VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Impl.Weierstrass.PPC64LE.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Proof.Weierstrass.PPC64LE.Point (KeepR tmv)
open VG.Spec.Weierstrass (Point Fe mul onCurve)
open VG.Proof.Ecdsa.PPC64LE (p521_ok)

/-- P-521. -/
abbrev W : Spec.Weierstrass.Curve := Spec.P521.curve

theorem am3 : AM3 W := by unfold AM3; decide

/-- A point's slots hold numbers below `p` that represent `P`. -/
structure PtOk (base : Addr) (s : State) (p : Pt) (P : Point W) : Prop where
  rep : Rep W (tmv W 9 base s p.x) (tmv W 9 base s p.y) (tmv W 9 base s p.z) P
  x : wordsVal s.mem base p.x 9 < W.p
  y : wordsVal s.mem base p.y 9 < W.p
  z : wordsVal s.mem base p.z 9 < W.p

theorem PtOk.of_eq {base : Addr} {s s' : State} {p : Pt} {P : Point W} (h : PtOk base s p P)
    (ex : wordsVal s'.mem base p.x 9 = wordsVal s.mem base p.x 9)
    (ey : wordsVal s'.mem base p.y 9 = wordsVal s.mem base p.y 9)
    (ez : wordsVal s'.mem base p.z 9 = wordsVal s.mem base p.z 9) : PtOk base s' p P :=
  ⟨by simp only [tmv]; rw [ex, ey, ez]; exact h.rep, by rw [ex]; exact h.x, by rw [ey]; exact h.y,
    by rw [ez]; exact h.z⟩

/-- The constants the windows read: `a` and `b` in Montgomery's form (`b` at
the slot `bp`), zero and Montgomery's one. -/
structure KC (bp : Nat) (base : Addr) (s : State) : Prop where
  ap : wordsVal s.mem base (p521.sl AP) 9 = W.a * 2 ^ 576 % W.p
  bp : wordsVal s.mem base (p521.sl bp) 9 = W.b * 2 ^ 576 % W.p
  zero : wordsVal s.mem base (p521.sl ZERO) 9 = 0
  onep : wordsVal s.mem base (p521.sl ONEP) 9 = 2 ^ 576 % W.p

/-- `P`'s slots: ECDH's peer point, with `Z = 1`. -/
abbrev gPt : Pt := p521.pt Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY ONEP

/-- The table of `k`'s bits, one byte each at `4096`. -/
abbrev Bits (base : Addr) (s : State) (k : Nat) : Prop :=
  ∀ t < 576, s.mem (off base (4096 + t)) = if k.testBit t then 1 else 0

/-- What `mul` writes. -/
abbrev mulW : List (Nat × Nat) := [(1072, 1080), (3520, 576), (5824, 1728)]

/-- What `mul` reads: the constants, `Q` at the peer point's slots, and the
table of `k`'s bits. -/
structure MPre (base : Addr) (s : State) (Q : Point W) (k : Nat) : Prop where
  ws : WsReg s base
  kc : KC BPs base s
  g : PtOk base s gPt Q
  on : onCurve W Q = true
  bits : Bits base s k
  lt : k < 2 ^ 528

theorem lok : CfgOk p521 := p521_ok

/-- The curve's kit. -/
def kit : WAll.Kit p521 := WAll.Kit.w3 (WAll.AKit.am3 lok am3) (Cfg.windows3 p521) (by decide) (by decide)

/-- `R = [k]Q`. -/
theorem mul_ok (hL : Law W) {base : Addr} {s : State} {Q : Point W} {k : Nat} (hp : MPre base s Q k) :
    WP isa (Window.Cfg.mul3 p521 Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY BPs) s fun s' =>
      Rk powClob s s' ∧ Unch base mulW s.mem s'.mem ∧ PtOk base s' (Cfg.rPt p521) (mul k Q) :=
  WP.mono (WAll.mul_ok kit hL ⟨hp.ws, ⟨hp.kc.ap, hp.kc.bp, hp.kc.zero, hp.kc.onep⟩,
    ⟨hp.g.rep, hp.g.x, hp.g.y, hp.g.z⟩, hp.on, hp.bits, hp.lt⟩)
    fun _ ⟨hk, hu, hr⟩ => ⟨hk, hu, ⟨hr.rep, hr.x, hr.y, hr.z⟩⟩

end VG.Proof.Ecdsa.PPC64LE.Window.P521
