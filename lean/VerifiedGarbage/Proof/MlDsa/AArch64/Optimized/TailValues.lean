import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TailBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TailRun

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def tailGroupSchedule (u : Nat) (root : Nat → Nat → Nat → Nat) (p : Fin 4 × Nat) : List Traversal.Op :=
  Traversal.packedSchedule (32*u+8*p.1.val) p.2 (root p.1.val p.2)

theorem tailValues_field (v : Vector (BitVec 128) 8) (w : Poly) (ps : List (Fin 4 × Nat))
    (hps : ∀ p∈ps,p.2=1 ∨ p.2=2) (root : Nat → Nat → Nat → Nat) {u : Nat} (hu : u<8) {b : Int}
    (hb : 0≤b) (hs : b+16760834*(ps.length : Int)<2147483648)
    (hv : BankBound v b) (hf : InnerBankField u v w) :
    BankBound (tailValues v (fun g len e => (zetaNat (root g len e) : Int)) ps)
      (b+16760834*(ps.length : Int)) ∧
    InnerBankField u (tailValues v (fun g len e => (zetaNat (root g len e) : Int)) ps)
      (Traversal.run (ps.flatMap (tailGroupSchedule u root)) w) := by
  induction ps generalizing v w b with
  | nil => simpa only [tailValues,List.length_nil,Int.natCast_zero,Int.mul_zero,Int.add_zero,
      List.flatMap_nil,Traversal.run,List.foldl_nil] using And.intro hv hf
  | cons p ps ih =>
    have hp := hps p (by simp)
    have hs' : b+16760834<2147483648 := by
      simp only [List.length_cons,Int.natCast_add,Int.natCast_one] at hs; omega
    have hb' := packedValues_bound v p.1.isLt hp (fun e => (zetaNat (root p.1.val p.2 e) : Int)) hb hs' hv
    have hf' := packedValues_field v w p.1.isLt hp hu (root p.1.val p.2) hb hs' hv hf
    have hh := ih _ (Traversal.run (tailGroupSchedule u root p) w)
      (fun a ha => hps a (by simp [ha])) (b := b+16760834) (by omega) (by
        simp only [List.length_cons,Int.natCast_add,Int.natCast_one] at hs
        omega) hb' hf'
    simpa only [tailValues,List.length_cons,Int.natCast_add,Int.natCast_one,List.flatMap_cons,
      Traversal.run_append,show b+16760834*((ps.length : Int)+1)=
        (b+16760834)+16760834*(ps.length : Int) by omega] using hh

end VG.Proof.MlDsa.AArch64.Optimized
