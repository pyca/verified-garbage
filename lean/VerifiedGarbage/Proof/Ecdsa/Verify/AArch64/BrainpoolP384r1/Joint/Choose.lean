module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Table
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP384r1.AArch64.Joint
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.Math
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint.State
public import VerifiedGarbage.Proof.Ed25519.AArch64.Step

/-! Selecting a short copy path using only the public table counter. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
open VG VG.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans read_x)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint

theorem choose_sub (s : State) {m : Nat} (hm : m < 4096) :
    WP isa (.block [.subImm .x .x2 .x19 m]) s fun t =>
      t.gpr .x2=s.gpr .x19-BitVec.ofNat 64 m ∧ Keeps [.x2] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,hm,ite_true,BitVec.setWidth_eq,
    RegUpd.gpr_write_self,Option.some.injEq,exists_eq_left']
  refine ⟨rfl,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

theorem choose_wp (f : Nat → Prog isa) {Q : State → Prop} :
    ∀ m,m ≤ 15 → ∀ {j : Nat} {s : State},1 ≤ j → j ≤ m →
      s.gpr .x19=BitVec.ofNat 64 j →
      (∀ t,Keeps [.x2] s t → WP isa (f j) t Q) → WP isa (choose f m) s Q
  | 0,_,_,_,hj,hjm,_,_ => False.elim (by omega)
  | m+1,hm,j,s,hj,hjm,h19,h => by
    rw [choose]
    refine WP.seq (WP.mono (choose_sub s (m:=m+1) (by omega)) fun t ⟨v,k⟩ => ?_)
    have z : (t.read .x .x2 == 0)=decide (j=m+1) := by
      rw [read_x,v,h19]
      by_cases e : j=m+1
      · rw [e,BitVec.sub_self]
        change true = decide (m+1=m+1)
        exact (decide_eq_true rfl).symm
      · rw [decide_eq_false e,beq_eq_false_iff_ne]
        intro hz
        have hh := congrArg BitVec.toNat hz
        rw [BitVec.toNat_sub,BitVec.toNat_ofNat,BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : j < 2^64),
          Nat.mod_eq_of_lt (by omega : m+1 < 2^64)] at hh
        change (2^64-(m+1)+j)%(2^64)=0 at hh
        omega
    apply WP.ite (decide (j=m+1)) (by change some (t.read .x .x2 == 0)=_; rw [z])
    · intro e
      rw [decide_eq_true_eq] at e
      subst j
      exact h t k
    · intro e
      rw [decide_eq_false_iff_not] at e
      exact choose_wp f m (by omega) hj (by omega) ((k.gpr _ (by decide)).trans h19)
        fun u ku => h u (k.trans ku)
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP384r1.Joint
