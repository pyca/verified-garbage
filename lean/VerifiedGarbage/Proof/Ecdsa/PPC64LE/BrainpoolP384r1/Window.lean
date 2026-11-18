module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.WindowAll
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.WindowA
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.PPC64LE
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP384r1

/-!
# `[k]P` by windows on PPC64LE, brainpoolP384r1

The curve's kit for `Proof/Ecdsa/PPC64LE/WindowAll.lean`: brainpoolP384r1's field, of six words,
whose `a` is any (`WAll.AKit.anyA`: `rcb`, `dblJa`, `3 b` at `B3P`),
and four-bit windows (`WAll.Kit.w4`). Then what that proof gives of the windows on
brainpoolP384r1, as other modules use it: `mul_ok`, `R = [k]P` for `P` at ECDH's slots of the peer's
point and `k`'s bits in the table of bits (`MPre`), on the curve's own statements of a point in slots
(`PtOk`) and of the constants (`KC`).
-/

@[expose] public section

set_option exponentiation.threshold 512

namespace VG.Proof.Ecdsa.PPC64LE.Window.BrainpoolP384r1

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Ecdsa.PPC64LE.Window
open VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Impl.Weierstrass.PPC64LE.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Proof.Weierstrass.PPC64LE.Point (KeepR tmv)
open VG.Spec.Weierstrass (Point Fe mul onCurve)
open VG.Proof.Ecdsa.PPC64LE (brainpoolp384r1_ok)

/-- brainpoolP384r1. -/
abbrev W : Spec.Weierstrass.Curve := Spec.BrainpoolP384r1.curve

/-- A point's slots hold numbers below `p` that represent `P`. -/
structure PtOk (base : Addr) (s : State) (p : Pt) (P : Point W) : Prop where
  rep : Rep W (tmv W 6 base s p.x) (tmv W 6 base s p.y) (tmv W 6 base s p.z) P
  x : wordsVal s.mem base p.x 6 < W.p
  y : wordsVal s.mem base p.y 6 < W.p
  z : wordsVal s.mem base p.z 6 < W.p

theorem PtOk.of_eq {base : Addr} {s s' : State} {p : Pt} {P : Point W} (h : PtOk base s p P)
    (ex : wordsVal s'.mem base p.x 6 = wordsVal s.mem base p.x 6)
    (ey : wordsVal s'.mem base p.y 6 = wordsVal s.mem base p.y 6)
    (ez : wordsVal s'.mem base p.z 6 = wordsVal s.mem base p.z 6) : PtOk base s' p P :=
  ⟨by simp only [tmv]; rw [ex, ey, ez]; exact h.rep, by rw [ex]; exact h.x, by rw [ey]; exact h.y,
    by rw [ez]; exact h.z⟩

/-- The constants the windows read: `a` and `3 b` in Montgomery's form (`3 b` at
the slot `bp`), zero and Montgomery's one. -/
structure KC (bp : Nat) (base : Addr) (s : State) : Prop where
  ap : wordsVal s.mem base (brainpoolp384r1.sl AP) 6 = W.a * 2 ^ 384 % W.p
  bp : wordsVal s.mem base (brainpoolp384r1.sl bp) 6 = 3 * W.b * 2 ^ 384 % W.p
  zero : wordsVal s.mem base (brainpoolp384r1.sl ZERO) 6 = 0
  onep : wordsVal s.mem base (brainpoolp384r1.sl ONEP) 6 = 2 ^ 384 % W.p

/-- The slot of `3 b`: the signature's (`B3P`). -/
abbrev B3s : Nat := B3P

/-- `P`'s slots: ECDH's peer point, with `Z = 1`. -/
abbrev gPt : Pt := brainpoolp384r1.pt Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY ONEP

/-- The table of `k`'s bits, one byte each at `4096`. -/
abbrev Bits (base : Addr) (s : State) (k : Nat) : Prop :=
  ∀ t < 384, s.mem (off base (4096 + t)) = if k.testBit t then 1 else 0

/-- What `mul` writes. -/
abbrev mulW : List (Nat × Nat) := [(736, 720), (3712, 384), (5248, 2304)]

/-- What `mul` reads: the constants, `Q` at the peer point's slots, and the
table of `k`'s bits. -/
structure MPre (base : Addr) (s : State) (Q : Point W) (k : Nat) : Prop where
  ws : WsReg s base
  kc : KC B3s base s
  g : PtOk base s gPt Q
  on : onCurve W Q = true
  bits : Bits base s k
  lt : k < 2 ^ 384

theorem lok : CfgOk brainpoolp384r1 := brainpoolp384r1_ok

/-- The curve's kit. -/
def kit : WAll.Kit brainpoolp384r1 := WAll.Kit.w4 (WAll.AKit.anyA lok) (by decide)

/-- `R = [k]Q`. -/
theorem mul_ok (hL : Law W) {base : Addr} {s : State} {Q : Point W} {k : Nat} (hp : MPre base s Q k) :
    WP isa (WindowA.Cfg.mul brainpoolp384r1 Impl.Ecdh.PPC64LE.PX Impl.Ecdh.PPC64LE.PY B3s) s fun s' =>
      Rk powClob s s' ∧ Unch base mulW s.mem s'.mem ∧ PtOk base s' (Cfg.rPt brainpoolp384r1) (mul k Q) :=
  WP.mono (WAll.mul_ok kit hL ⟨hp.ws, ⟨hp.kc.ap, hp.kc.bp, hp.kc.zero, hp.kc.onep⟩,
    ⟨hp.g.rep, hp.g.x, hp.g.y, hp.g.z⟩, hp.on, hp.bits, hp.lt⟩)
    fun _ ⟨hk, hu, hr⟩ => ⟨hk, hu, ⟨hr.rep, hr.x, hr.y, hr.z⟩⟩

end VG.Proof.Ecdsa.PPC64LE.Window.BrainpoolP384r1
