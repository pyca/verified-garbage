import VerifiedGarbage.Impl.Ecdh.X86.WinJac
import VerifiedGarbage.Proof.Weierstrass.X86.WinJacBuildState
import VerifiedGarbage.Proof.Ecdsa.X86.Lays

/-! The five-bit ECDH window fits the existing P-256 scratch layout. -/
namespace VG.Proof.Ecdh.X86
open VG VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Ecdsa.X86
open VG.Impl.Ecdsa.X86
variable {c : Impl.Ecdsa.X86.Cfg}

private theorem listLay {M : Mod} {sz : Nat} {xs : List Nat}
    (hle : xs.all (fun x => decide (x+8*M.n≤sz))=true)
    (hap : xs.all (fun x => xs.all (fun y => decide (x≠y → x+8*M.n≤y ∨ y+8*M.n≤x)))=true)
    (hmo : xs.all (fun x => decide (x+8*M.n≤M.mo ∨ M.mo+8*M.n≤x))=true)
    (htmp : xs.all (fun x => decide (x+8*M.n≤M.tmp ∨ M.tmp+8*M.n≤x))=true) :
    Lay M sz (·∈xs) := by
  refine ⟨fun x hx => ?_,fun x y hx hy => ?_,fun x hx => ?_,fun x hx => ?_⟩
  · exact of_decide_eq_true (List.all_eq_true.mp hle x hx)
  · exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hap x hx) y hy)
  · exact of_decide_eq_true (List.all_eq_true.mp hmo x hx)
  · exact of_decide_eq_true (List.all_eq_true.mp htmp x hx)

macro "jwin_layout" h:term : tactic => `(tactic|
  (simp only [Impl.Ecdh.X86.Cfg.jwinCfg,Impl.Ecdsa.X86.Cfg.MP',
    Impl.Ecdsa.X86.Cfg.rcbSlots,Impl.Ecdsa.X86.Cfg.pt,Impl.Ecdsa.X86.Cfg.sl,
    slot,($h),JWin.slots,JWin.ro,JWin.work,JWin.temps,JacWinCfg.E,JacWinCfg.z2,JacWinCfg.z3,
    List.cons_append,List.nil_append,Impl.Ecdh.X86.Cfg.windowBits,
    Mont.own,Spec.Weierstrass.Mont.ownAt,Spec.Weierstrass.Mont.ownBytes,VG.Impl.Mont.X86.words,
    List.forall_mem_cons,List.forall_mem_nil,List.forall_mem_append] <;> decide))

theorem jwinLay (h4 : c.n=4) :
    JWin.Layout (Impl.Ecdh.X86.Cfg.jwinCfg c) size (Mont.own c.n) := by
  refine ⟨?_,by decide,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · jwin_layout h4
  · apply listLay
    all_goals jwin_layout h4
  all_goals jwin_layout h4

theorem jwinWk (hc : CfgOk c) (h4 : c.n=4) :
    WkOk c.SP (Impl.Ecdh.X86.Cfg.jwinCfg c).M c.C.p size (Mont.own c.n)
      (·∈JWin.slots (Impl.Ecdh.X86.Cfg.jwinCfg c)) := by
  refine ⟨⟨hc.fp.2.2,hc.fp.1,hc.fp.2.1,rfl,rfl⟩,?_,?_,?_⟩
  all_goals jwin_layout h4

end VG.Proof.Ecdh.X86
