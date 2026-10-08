import VerifiedGarbage.Proof.Ecdh.X86.JacLayout
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.WindowLayout

/-! Memory written by the Jacobian ECDH multiplier. -/
namespace VG.Proof.Ecdh.X86
open VG VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Ecdsa.X86
open VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Ecdsa.Verify.X86
variable {c : Cfg}

abbrev jwinW (c : Cfg) : List (Nat × Nat) := windowW c ++ [(5200,2560)]

theorem jwinW_fixed (h4 : c.n=4) : FixedOk c (jwinW c) := by
  refine (windowW_fixed h4).append ?_
  intro w hw
  rw [List.mem_singleton] at hw
  subst w
  right
  rw [sl_eq,h4]
  decide

theorem jwinW_apart (h4 : c.n=4) {i : Nat} (hi : i<45) (hw : i∉windowSlots) :
    ∀ w∈jwinW c,c.sl i+8*c.n≤w.1 ∨ w.1+w.2≤c.sl i := by
  refine apart_append (windowW_apart h4 hi hw) ?_
  intro w hw
  rw [List.mem_singleton] at hw
  subst w
  left
  rw [sl_eq,h4]
  dsimp only
  omega

theorem jwinW_table (h4 : c.n=4) {t : Nat} (ht : t<64*c.n) :
    ∀ w∈jwinW c,bitsAt c.n 1+t+1≤w.1 ∨ w.1+w.2≤bitsAt c.n 1+t := by
  refine apart_append (windowW_table h4 ht) ?_
  intro w hw
  rw [List.mem_singleton] at hw
  subst w
  left
  rw [bitsAt_eq,h4]
  rw [h4] at ht
  dsimp only
  omega

theorem jwinW_cover (h4 : c.n=4) :
    ∀ w∈JWin.allW (Impl.Ecdh.X86.Cfg.jwinCfg c) (Mont.own c.n),
      ∃ w'∈jwinW c,w'.1≤w.1 ∧ w.1+w.2≤w'.1+w'.2 := by
  simp only [JWin.allW,JWin.loopW,progW,jwinW,windowW,slW,
    List.map_cons,List.map_nil,List.forall_mem_append,List.forall_mem_map,
    List.forall_mem_cons,Mont.outW]
  jwin_layout h4

end VG.Proof.Ecdh.X86
