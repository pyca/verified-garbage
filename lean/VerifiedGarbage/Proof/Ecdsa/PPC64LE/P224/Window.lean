module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.WindowAll
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P256.Window
public import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LE
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224

/-!
# `[k]P` by windows on PPC64LE, P-224

The curve's kit for `Proof/Ecdsa/PPC64LE/WindowAll.lean`: P-224's field, of four words,
whose `a` is `-3` (`WAll.AKit.am3`: `rcb3`, `dblJ`, `b` at slot 40),
and four-bit windows (`WAll.Kit.w4`). Then what that proof gives of the windows on
P-224, as other modules use it: `mul_ok`, `R = [k]P` for `P` at ECDH's slots of the peer's
point and `k`'s bits in the table of bits (`MPre`), on the curve's own statements of a point in slots
(`PtOk`) and of the constants (`KC`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE.Window.P224

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Ecdsa.PPC64LE.Window
open VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Impl.Weierstrass.PPC64LE.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Proof.Weierstrass.PPC64LE.Point (KeepR tmv)
open VG.Spec.Weierstrass (Point Fe mul onCurve)
open VG.Proof.Ecdsa.PPC64LE (p224_ok)

/-- P-224. -/
abbrev W : Spec.Weierstrass.Curve := Spec.P224.curve

theorem am3 : AM3 W := by unfold AM3; decide

/-- A point's slots hold numbers below `p` that represent `P`. -/
structure PtOk (base : Addr) (s : State) (p : Pt) (P : Point W) : Prop where
  rep : Rep W (tmv W 4 base s p.x) (tmv W 4 base s p.y) (tmv W 4 base s p.z) P
  x : wordsVal s.mem base p.x 4 < W.p
  y : wordsVal s.mem base p.y 4 < W.p
  z : wordsVal s.mem base p.z 4 < W.p

theorem PtOk.of_eq {base : Addr} {s s' : State} {p : Pt} {P : Point W} (h : PtOk base s p P)
    (ex : wordsVal s'.mem base p.x 4 = wordsVal s.mem base p.x 4)
    (ey : wordsVal s'.mem base p.y 4 = wordsVal s.mem base p.y 4)
    (ez : wordsVal s'.mem base p.z 4 = wordsVal s.mem base p.z 4) : PtOk base s' p P :=
  ⟨by simp only [tmv]; rw [ex, ey, ez]; exact h.rep, by rw [ex]; exact h.x, by rw [ey]; exact h.y,
    by rw [ez]; exact h.z⟩

/-- The constants the windows read: `a` and `b` in Montgomery's form (`b` at
the slot `bp`), zero and Montgomery's one. -/
structure KC (bp : Nat) (base : Addr) (s : State) : Prop where
  ap : wordsVal s.mem base (p224.sl AP) 4 = W.a * 2 ^ 256 % W.p
  bp : wordsVal s.mem base (p224.sl bp) 4 = W.b * 2 ^ 256 % W.p
  zero : wordsVal s.mem base (p224.sl ZERO) 4 = 0
  onep : wordsVal s.mem base (p224.sl ONEP) 4 = 2 ^ 256 % W.p

/-- `P`'s slots: ECDH's peer point, with `Z = 1`. -/
abbrev gPt : Pt := p224.pt Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY ONEP

/-- What `mul` writes. -/
abbrev mulW : List (Nat × Nat) := [(512, 480), (3840, 256), (4864, 1536)]

/-- What `mul` reads: the constants, `Q` at the peer point's slots, and the
table of `k`'s bits. -/
structure MPre (base : Addr) (s : State) (Q : Point W) (k : Nat) : Prop where
  ws : WsReg s base
  kc : KC BPs base s
  g : PtOk base s gPt Q
  on : onCurve W Q = true
  bits : Bits base s k
  lt : k < 2 ^ 256

theorem lok : CfgOk p224 := p224_ok

/-- The curve's kit. -/
def kit : WAll.Kit p224 := WAll.Kit.w4 (WAll.AKit.am3 lok am3) (by decide)

/-- `R = [k]Q`. -/
theorem mul_ok (hL : Law W) {base : Addr} {s : State} {Q : Point W} {k : Nat} (hp : MPre base s Q k) :
    WP isa (Cfg.mul p224 Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY BPs) s fun s' =>
      Rk powClob s s' ∧ Unch base mulW s.mem s'.mem ∧ PtOk base s' (Cfg.rPt p224) (mul k Q) :=
  WP.mono (WAll.mul_ok kit hL ⟨hp.ws, ⟨hp.kc.ap, hp.kc.bp, hp.kc.zero, hp.kc.onep⟩,
    ⟨hp.g.rep, hp.g.x, hp.g.y, hp.g.z⟩, hp.on, hp.bits, hp.lt⟩)
    fun _ ⟨hk, hu, hr⟩ => ⟨hk, hu, ⟨hr.rep, hr.x, hr.y, hr.z⟩⟩

end VG.Proof.Ecdsa.PPC64LE.Window.P224
