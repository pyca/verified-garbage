module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.WindowAll
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.WindowA
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.PPC64LE
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP320r1

/-!
# `[k]P` by windows on PPC64LE, brainpoolP320r1

The curve's kit for `Proof/Ecdsa/PPC64LE/WindowAll.lean`: brainpoolP320r1's field, of five words,
whose `a` is any (`WAll.AKit.anyA`: `rcb`, `dblJa`, `3 b` at `B3P`),
and four-bit windows (`WAll.Kit.w4`). Then what that proof gives of the windows on
brainpoolP320r1, as other modules use it: `mul_ok`, `R = [k]P` for `P` at ECDH's slots of the peer's
point and `k`'s bits in the table of bits (`MPre`), on the curve's own statements of a point in slots
(`PtOk`) and of the constants (`KC`).
-/

@[expose] public section

set_option exponentiation.threshold 512

namespace VG.Proof.Ecdsa.PPC64LE.Window.BrainpoolP320r1

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Ecdsa.PPC64LE.Window
open VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Impl.Weierstrass.PPC64LE.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Proof.Weierstrass.PPC64LE.Point (KeepR tmv)
open VG.Spec.Weierstrass (Point Fe mul onCurve)
open VG.Proof.Ecdsa.PPC64LE (brainpoolp320r1_ok)

/-- brainpoolP320r1. -/
abbrev W : Spec.Weierstrass.Curve := Spec.BrainpoolP320r1.curve

/-- A point's slots hold numbers below `p` that represent `P`. -/
structure PtOk (base : Addr) (s : State) (p : Pt) (P : Point W) : Prop where
  rep : Rep W (tmv W 5 base s p.x) (tmv W 5 base s p.y) (tmv W 5 base s p.z) P
  x : wordsVal s.mem base p.x 5 < W.p
  y : wordsVal s.mem base p.y 5 < W.p
  z : wordsVal s.mem base p.z 5 < W.p

theorem PtOk.of_eq {base : Addr} {s s' : State} {p : Pt} {P : Point W} (h : PtOk base s p P)
    (ex : wordsVal s'.mem base p.x 5 = wordsVal s.mem base p.x 5)
    (ey : wordsVal s'.mem base p.y 5 = wordsVal s.mem base p.y 5)
    (ez : wordsVal s'.mem base p.z 5 = wordsVal s.mem base p.z 5) : PtOk base s' p P :=
  ⟨by simp only [tmv]; rw [ex, ey, ez]; exact h.rep, by rw [ex]; exact h.x, by rw [ey]; exact h.y,
    by rw [ez]; exact h.z⟩

/-- The constants the windows read: `a` and `3 b` in Montgomery's form (`3 b` at
the slot `bp`), zero and Montgomery's one. -/
structure KC (bp : Nat) (base : Addr) (s : State) : Prop where
  ap : wordsVal s.mem base (brainpoolp320r1.sl AP) 5 = W.a * 2 ^ 320 % W.p
  bp : wordsVal s.mem base (brainpoolp320r1.sl bp) 5 = 3 * W.b * 2 ^ 320 % W.p
  zero : wordsVal s.mem base (brainpoolp320r1.sl ZERO) 5 = 0
  onep : wordsVal s.mem base (brainpoolp320r1.sl ONEP) 5 = 2 ^ 320 % W.p

/-- The slot of `3 b`: the signature's (`B3P`). -/
abbrev B3s : Nat := B3P

/-- `P`'s slots: ECDH's peer point, with `Z = 1`. -/
abbrev gPt : Pt := brainpoolp320r1.pt Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY ONEP

/-- The table of `k`'s bits, one byte each at `4096`. -/
abbrev Bits (base : Addr) (s : State) (k : Nat) : Prop :=
  ∀ t < 320, s.mem (off base (4096 + t)) = if k.testBit t then 1 else 0

/-- What `mul` writes. -/
abbrev mulW : List (Nat × Nat) := [(624, 600), (3776, 320), (5056, 1920)]

/-- What `mul` reads: the constants, `Q` at the peer point's slots, and the
table of `k`'s bits. -/
structure MPre (base : Addr) (s : State) (Q : Point W) (k : Nat) : Prop where
  ws : WsReg s base
  kc : KC B3s base s
  g : PtOk base s gPt Q
  on : onCurve W Q = true
  bits : Bits base s k
  lt : k < 2 ^ 320

theorem lok : CfgOk brainpoolp320r1 := brainpoolp320r1_ok

/-- The curve's kit. -/
def kit : WAll.Kit brainpoolp320r1 := WAll.Kit.w4 (WAll.AKit.anyA lok) (by decide)

/-- `R = [k]Q`. -/
theorem mul_ok (hL : Law W) {base : Addr} {s : State} {Q : Point W} {k : Nat} (hp : MPre base s Q k) :
    WP isa (WindowA.Cfg.mul brainpoolp320r1 Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY B3s) s fun s' =>
      Rk powClob s s' ∧ Unch base mulW s.mem s'.mem ∧ PtOk base s' (Cfg.rPt brainpoolp320r1) (mul k Q) :=
  WP.mono (WAll.mul_ok kit hL ⟨hp.ws, ⟨hp.kc.ap, hp.kc.bp, hp.kc.zero, hp.kc.onep⟩,
    ⟨hp.g.rep, hp.g.x, hp.g.y, hp.g.z⟩, hp.on, hp.bits, hp.lt⟩)
    fun _ ⟨hk, hu, hr⟩ => ⟨hk, hu, ⟨hr.rep, hr.x, hr.y, hr.z⟩⟩

end VG.Proof.Ecdsa.PPC64LE.Window.BrainpoolP320r1
