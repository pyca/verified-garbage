import VerifiedGarbage.Proof.Ecdsa.Verify.X86.WindowLayout
import VerifiedGarbage.Proof.Weierstrass.X86.NafFinish
import VerifiedGarbage.Proof.Weierstrass.X86.NafPrep

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86 VG.Impl.Ecdsa.Verify.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.X86
variable {c : Impl.Ecdsa.X86.Cfg}

private theorem listLay {M : Mod} {sz : Nat} {xs : List Nat}
    (hle : xs.all (fun x => decide (x + 8 * M.n ≤ sz)) = true)
    (hap : xs.all (fun x => xs.all (fun y => decide
      (x ≠ y → x + 8 * M.n ≤ y ∨ y + 8 * M.n ≤ x))) = true)
    (hmo : xs.all (fun x => decide (x + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ x)) = true)
    (htmp : xs.all (fun x => decide (x + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ x)) = true) :
    Lay M sz (· ∈ xs) := by
  refine ⟨fun x hx => ?_, fun x y hx hy => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · exact of_decide_eq_true (List.all_eq_true.mp hle x hx)
  · exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hap x hx) y hy)
  · exact of_decide_eq_true (List.all_eq_true.mp hmo x hx)
  · exact of_decide_eq_true (List.all_eq_true.mp htmp x hx)

macro "naf_layout" h:term : tactic => `(tactic|
  (simp only [Impl.Ecdsa.Verify.X86.Cfg.nafQ, Impl.Ecdsa.Verify.X86.Cfg.windowQ,
    Impl.Ecdh.X86.Cfg.windowCfg, Impl.Ecdsa.X86.Cfg.MP',
    Impl.Ecdsa.X86.Cfg.rcbSlots, Impl.Ecdsa.X86.Cfg.pt, Impl.Ecdsa.X86.Cfg.sl,
    slot, ($h), nafSlots, nafWrites, nafTblSlots, winRo, winOther, rcbW,
    List.map_append, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    Impl.Ecdh.X86.Cfg.windowBits, Mont.outW, Mont.own, Spec.Weierstrass.Mont.ownAt,
    Spec.Weierstrass.Mont.ownBytes, words, List.forall_mem_cons, List.forall_mem_nil,
    List.forall_mem_append, List.forall_mem_map] <;> decide))

theorem nafQLay (h4 : c.n=4) : NafLay (Impl.Ecdsa.Verify.X86.Cfg.nafQ c) size := by
  refine ⟨by decide,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · naf_layout h4
  · apply listLay
    all_goals naf_layout h4
  all_goals naf_layout h4

theorem nafQWk (hc : CfgOk c) (h4 : c.n=4) :
    WkOk c.SP (Impl.Ecdsa.Verify.X86.Cfg.nafQ c).M c.C.p size (Mont.own c.n)
      (·∈nafSlots (Impl.Ecdsa.Verify.X86.Cfg.nafQ c)) := by
  refine ⟨⟨hc.fp.2.2,hc.fp.1,hc.fp.2.1,rfl,rfl⟩,?_,?_,?_⟩
  all_goals naf_layout h4

theorem nafQ_cover (h4 : c.n=4) :
    ∀ w∈nafTableWrites (Impl.Ecdsa.Verify.X86.Cfg.nafQ c) (Mont.own c.n),
      ∃ w'∈windowW c,w'.1≤w.1 ∧ w.1+w.2≤w'.1+w'.2 := by
  simp only [nafTableWrites,windowW,slW]
  naf_layout h4

end VG.Proof.Ecdsa.Verify.X86
