import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointInput
import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointGeneratorTable

/-! Reuse the verifier contract's existing width-seven comb table and certificate. -/
namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 Spec.Weierstrass
open VG.Impl.Ecdh.X86_64 (PX PY BP)

def jointCombRow {c : Cfg} {j : Joint.Cfg} {d : CombData} (hc : CfgOk c) (hC : Law c.C)
    (hT : CombTbls c) (hcd : c.comb=some d) (hw : d.w=7) :
    JointGeneratorRow j.K.M.n c.C (G c.C) :=
  combGeneratorRow j.K.M.n (unitMod_pow_two hc.p_odd (64*j.K.M.n)) hC
    (by simpa only [hw] using (hT d hcd).1)
    (by rw [Cfg.combJ]; have := hc.n0; omega)

theorem jointMid_generator {c : Cfg} {j : Joint.Cfg} {d : CombData}
    (hc : CfgOk c) (hC : Law c.C) (hT : CombTbls c)
    (hcd : c.comb=some d) (hw : d.w=7) (hsym : j.tsym=d.tsym)
    (hK : j.K=c.winCfg PX PY BP)
    {s₀ s : State} {g : Reg → BitVec 64} (hp : VPre c s₀) (h : Mid c s₀ (s₀.gpr .rcx) g s) :
    JointGenerator j c.C (s₀.gpr .rcx) (s₀.syms d.tsym) size
      (jointCombRow (j:=j) hc hC hT hcd hw) s := by
  have hjn : j.K.M.n=c.n := by rw [hK]; rfl
  have table := tbl_of_held hcd hp.tbls (by rw [hp.wr]; simp)
    (s:=s) (fun r hr => by rw [h.rd,hp.rd]; simp [hr]) h.unch
  have ws : c.combWords d=tcombWords j.K.M.n (2^(64*j.K.M.n)) c.C.p d.tbl := by
    simp only [Cfg.combWords,Cfg.R,hjn]
  have hpn : c.C.p<2^(64*j.K.M.n) := by rw [hjn]; exact hc.p_lt
  unfold jointCombRow
  apply jointGenerator_of_table (unitMod_pow_two hc.p_odd (64*j.K.M.n)) hC hpn
  · rw [←ws]
    exact table.1
  · rw [←ws]
    exact table.2
  · rw [hsym,h.syms]

end VG.Proof.Ecdsa.Verify.X86_64
