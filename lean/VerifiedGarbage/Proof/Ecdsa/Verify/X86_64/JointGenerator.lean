module

import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointGeneratorTable
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Scalars

/-! Reuse the verifier contract's existing width-seven comb table and certificate. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 Spec.Weierstrass
open VG.Impl.Ecdh.X86_64 (PX PY BP)

/-- The joint loop's table of `[m]G`: `d`, one of the curve's tables of
constants, of `J` rows, whose first row holds `[m]G` for `m = 1 … 2^(d.w-1)`,
past the largest magnitude of the generator's digits: the comb's, or the
verifier's own (`Cfg.gtab`). -/
structure JointGTable (c : Cfg) (j : Joint.Cfg) (d : CombData) (J : Nat) : Prop where
  mem : (d.tsym,c.combWords d)∈c.combConsts
  ok : CombOkW c.C d.w J d.tbl d.start
  pos : 0<J
  top : jointGTop j<2^(d.w-1)
  sym : j.tsym=d.tsym

theorem JointGTable.ofComb {c : Cfg} {j : Joint.Cfg} {d : CombData} {J : Nat}
    (hcd : c.comb=some d) (hT : CombOkW c.C d.w J d.tbl d.start) (hJ : 0<J)
    (ht : jointGTop j<2^(d.w-1)) (hs : j.tsym=d.tsym) : JointGTable c j d J :=
  ⟨comb_mem_consts hcd,hT,hJ,ht,hs⟩

theorem JointGTable.ofGTab {c : Cfg} {j : Joint.Cfg} {d : CombData} {J : Nat}
    (hcd : c.gtab=some d) (hT : CombOkW c.C d.w J d.tbl d.start) (hJ : 0<J)
    (ht : jointGTop j<2^(d.w-1)) (hs : j.tsym=d.tsym) : JointGTable c j d J :=
  ⟨gtab_mem_consts hcd,hT,hJ,ht,hs⟩

def jointCombRow {c : Cfg} {j : Joint.Cfg} {d : CombData} {J : Nat} (hc : BaseCfgOk c) (hC : Law c.C)
    (hG : JointGTable c j d J) : JointGeneratorRow j.K.M.n c.C (G c.C) (jointGTop j) :=
  combGeneratorRow j.K.M.n (unitMod_pow_two hc.p_odd (64*j.K.M.n)) hC hG.ok hG.pos hG.top

theorem jointMid_generator {c : Cfg} {j : Joint.Cfg} {d : CombData} {J : Nat}
    (hc : BaseCfgOk c) (hC : Law c.C) (hG : JointGTable c j d J)
    (hK : j.K=c.winCfg PX PY BP)
    {s₀ s : State} {g : Reg → BitVec 64} (hp : VPre c s₀) (h : Mid c s₀ (s₀.gpr .rcx) g s) :
    JointGenerator j c.C (s₀.gpr .rcx) (s₀.syms d.tsym) size
      (jointCombRow (j:=j) hc hC hG) s := by
  have hjn : j.K.M.n=c.n := by rw [hK]; rfl
  have table := tbl_of_held_mem hG.mem hp.tbls (by rw [hp.wr]; simp)
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
  · rw [hG.sym,h.syms]

end VG.Proof.Ecdsa.Verify.X86_64
