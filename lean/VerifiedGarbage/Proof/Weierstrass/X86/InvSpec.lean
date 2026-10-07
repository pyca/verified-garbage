import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.X86.InvState
import VerifiedGarbage.Proof.Weierstrass.InvToM
import VerifiedGarbage.Proof.Weierstrass.Law
import Mathlib.Data.Nat.Prime.Defs

/-! # The interface of the 256-bit divstep inversion -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.Impl.Weierstrass.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass

def invClob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi]

def invW (P : InvCfg) : List (Nat × Nat) :=
  [(P.tbl, 320), (P.out, 32), (P.M.tmp, 32), (P.wk, 68)]

structure InvOk (P : InvCfg) (p : Nat) : Prop where
  C : P.C = 2 ^ 40 * (2 ^ 256) ^ 3 % p
  Cpos : 0 < P.C
  Cn : P.Cn = p - P.C

def InvSound (p : Nat) [NeZero p] : Prop :=
  ∀ {P : InvCfg} {base : Addr} {size : Nat}, InvLay P size → 2 < p → UnitMod p (2 ^ 256) →
    ∀ {s : State}, Scr s base size → ModOkW P.M size p s.mem base → val32 s.mem base P.base 8 < p →
      InvOk P p → WP isa P.inv s fun z =>
        Keeps invClob s z ∧ Unch base (invW P) s.mem z.mem ∧ val32 z.mem base P.out 8 < p ∧
        toM p (2 ^ 256) (val32 z.mem base P.out 8) = toM p (2 ^ 256) (val32 s.mem base P.base 8) ^ (p - 2)

def InvSounds : Prop := ∀ {p : Nat} [NeZero p], p.Prime → InvSound p

structure HasLawInv (C : Spec.Weierstrass.Curve) : Type where
  law : Law C
  inv : InvSounds

theorem InvOk.ofMod {M : VG.Impl.Mont.Mod} {wk out base tbl p : Nat}
    (hC : 0 < (InvCfg.ofMod M wk out base tbl p).C) : InvOk (InvCfg.ofMod M wk out base tbl p) p :=
  ⟨rfl, hC, rfl⟩

end VG.Proof.Weierstrass.X86.Inv
