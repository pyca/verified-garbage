module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Core
public import VerifiedGarbage.Proof.Ed448.WnafWide.Group
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Negate
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.X448.AArch64.Base.AddDefs

/-! Conditional public negation preserves the point arithmetic invariant. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (slot)
open VG.Proof.X448.AArch64.Weak (Env)
open VG.Proof.X448.AArch64.Fast (Bnd Same)
open VG.Proof.Curve448.AArch64.Fast (Mb)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

def signedEnv (negative:Bool) (e:Env) : Env :=
  if negative then Function.update e 6 (0-e 6) else e

theorem negateIf_ok (negative:Bool) {s:State} {base:Addr} (h:Core base s)
    (hx:Bnd Mb s.mem base (slot 6))
    (h21:s.gpr .x21=BitVec.ofNat 64 (if negative then 1 else 0)) :
    WP isa (.ite (.nonzero .x .x21) negateSelected (.block [])) s fun t =>
      Core base t ∧ PointKeep base s t ∧ Same base [6] s.mem t.mem ∧
      EV t.mem base=signedEnv negative (EV s.mem base) := by
  cases negative
  · have he:isa.eval (.nonzero .x .x21) s=some false:=by
      simp only [eval,State.read,BitVec.setWidth_eq,h21]
      rfl
    refine VG.WP.ite false he (fun h => Bool.noConfusion h) fun _ => WP.block_nil ?_
    exact ⟨h,PointKeep.refl _ _,fun _ _ _ _ => rfl,rfl⟩
  · have he:isa.eval (.nonzero .x .x21) s=some true:=by
      simp only [eval,State.read,BitVec.setWidth_eq,h21]
      rfl
    refine VG.WP.ite true he (fun _ => ?_) (fun h => Bool.noConfusion h)
    refine WP.mono (negateSelected_ok h.scr h.env (VG.Proof.X448.AArch64.Base.zero_env h.zero).2 hx)
      fun t ⟨tk,tb,ts,te⟩ => ?_
    have kp:=PointKeep.of_field tk
    refine ⟨h.unchanged kp tb ts (by decide) (by decide) (by decide),kp,ts,?_⟩
    rw [te,(VG.Proof.X448.AArch64.Base.zero_env h.zero).1]
    rfl

theorem signedEnv_point (negative:Bool) (e:Env) :
    VG.Proof.X448.AArch64.Base.pt (signedEnv negative e) 6 7 8=
      VG.Proof.Ed448.WnafWide.signedPoint negative (VG.Proof.X448.AArch64.Base.pt e 6 7 8):=by
  cases negative <;> rfl

end VG.Proof.Ed448.AArch64.Sparse
