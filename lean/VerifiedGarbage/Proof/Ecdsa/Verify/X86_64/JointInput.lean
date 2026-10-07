import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Scalars
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInvariant

/-! The ordinary verifier's scalar stage supplies the joint window's field input. -/
namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 Spec.Weierstrass
open VG.Impl.Ecdh.X86_64 (PX PY BP)

theorem jointMid_field {c : Cfg} {j : Joint.Cfg} (hc : CfgOk c)
    (hK : j.K=c.winCfg PX PY BP) (hnp : c.C.n≤c.C.p)
    {s₀ s : State} {base : Addr} {g : Reg → BitVec 64} (h : Mid c s₀ base g s) :
    Inv j.K.M base size c.C.p (·∈nafSlots j.K) (winRo j.K) (tmv c.C j.K.M.n base s) s := by
  rw [hK]
  refine ⟨h.scr,modP_of hc h.fixed.mp,fun _ hx => List.mem_append_left _ (List.mem_append_left _ hx),?_,fun _ _ => rfl⟩
  intro x hx
  simp only [winRo,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
  · exact lt_of_eq_of_lt h.fixed.ap (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne c.C.p)))
  · exact Nat.lt_of_lt_of_le h.em_lt hnp
  · exact lt_of_eq_of_lt h.fixed.zero (Nat.pos_of_ne_zero (NeZero.ne c.C.p))
  · exact h.px_lt
  · exact h.py_lt
  · exact lt_of_eq_of_lt h.fixed.onep (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne c.C.p)))

theorem jointMid_zero {c : Cfg} {j : Joint.Cfg}
    (hK : j.K=c.winCfg PX PY BP)
    {s₀ s : State} {base : Addr} {g : Reg → BitVec 64} (h : Mid c s₀ base g s) :
    tmv c.C j.K.M.n base s j.K.zero=0 := by
  rw [hK]
  change toM c.C.p (2^(64*c.n)) (wordsVal s.mem base (c.sl ZERO) c.n)=0
  rw [h.fixed.zero]
  exact toM_zero _ _

theorem jointMid_point {c : Cfg} {j : Joint.Cfg} (hc : CfgOk c) (hC : Law c.C)
    (hK : j.K=c.winCfg PX PY BP) {Q : Point c.C}
    {s₀ s : State} {base : Addr} {g : Reg → BitVec 64} (h : Mid c s₀ base g s)
    (hp : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) Q) :
    InvJ c.C (tmv c.C j.K.M.n base s j.K.P.x) (tmv c.C j.K.M.n base s j.K.P.y)
      (tmv c.C j.K.M.n base s j.K.P.z) Q := by
  have one : tmv c.C c.n base s (c.sl ONEP)=1 := by
    change toM c.C.p (2^(64*c.n)) (wordsVal s.mem base (c.sl ONEP) c.n)=1
    rw [h.fixed.onep]
    exact toM_one (unitMod_pow_two hc.p_odd _)
  rw [hK]
  change InvJ c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
    (tmv c.C c.n base s (c.sl ONEP)) Q
  rw [one]
  have hj := InvJ.of_rep hC hp
  simpa only [one,Lean.Grind.Semiring.mul_one] using hj

end VG.Proof.Ecdsa.Verify.X86_64
