import VerifiedGarbage.Proof.Ecdh.AArch64.Window
import VerifiedGarbage.Impl.Ecdh.AArch64.WithMul

/-! The internal scalar-multiplication interface allows arbitrary invalid
scalars to execute safely; the existing final range check rejects them. -/
namespace VG.Proof.Ecdh.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64
open VG.Proof.Weierstrass Spec.Weierstrass VG.Proof.Ecdsa.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)

structure MulPost (c : Cfg) (base : Addr) (g : Reg → BitVec 64)
    (P : Point c.C) (k : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  fixed : Fixed c base g s'.mem
  extra : ∀ r ∈ [Reg.x26, .x27, .x28], s'.gpr r = s.gpr r
  x20 : s'.gpr .x20 = s.gpr .x20
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  flag : word s'.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG)
  d : sv c base s' D = sv c base s D
  q : 1 ≤ k → k < c.C.n → Rep c.C (tmv c.C c.n base s' (c.sl RX))
    (tmv c.C c.n base s' (c.sl RY)) (tmv c.C c.n base s' (c.sl RZ)) (mul k P)
  acc_lt : sv c base s' ACC < c.C.p
  acc : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) =
    tmv c.C c.n base s' (c.sl RZ) ^ (c.C.p - 2)
  rz_lt : sv c base s' RZ < c.C.p

def MulOk (c : Cfg) (mq : Prog isa) : Prop :=
  ∀ {base : Addr} {s : State}, Scr s base size →
    ∀ {g : Reg → BitVec 64}, Fixed c base g s.mem →
    ∀ {P : Point c.C}, onCurve c.C P = true → sv c base s PX < c.C.p → sv c base s PY < c.C.p →
    Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P →
    ∀ {rest : Prog isa} {R : State → Prop},
    (∀ s', MulPost c base g P (sv c base s K) s s' → WP isa rest s' R) →
    WP isa (.seq mq (.seq c.pPow rest)) s R

end VG.Proof.Ecdh.AArch64
