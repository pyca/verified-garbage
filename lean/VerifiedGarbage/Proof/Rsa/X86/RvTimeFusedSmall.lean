module

import VerifiedGarbage.Proof.Rsa.X86.RvTimeFusedCheck
public import VerifiedGarbage.Proof.Rsa.X86.RvTimeBase
import VerifiedGarbage.Proof.Framework.Cold
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
meta import VerifiedGarbage.Impl.Rsa.X86.RecoverRt
meta import VerifiedGarbage.Proof.Rsa.X86.RvTaint
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Rsa.X86.RvFusedSmall
meta import VerifiedGarbage.Proof.Rsa.X86.RvFusedSmall
import VerifiedGarbage.Proof.Rsa.X86.RvSlots
meta import VerifiedGarbage.Proof.Rsa.X86.RvSlots
public import Mathlib.Data.Int.ModEq

/-! Multiplication's loop count and dispatch depend only on the candidate index. -/
@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

structure FusedMulData (g : Geo) (n j : Nat) where
  s0 : State
  A : Nat → Nat
  AW : Nat → Nat
  V : Nat → Nat
  value : A mBase=n
  modulus : A aN=n
  zero : A aZ=0
  bound : n<2^(64*g.n)
  inverse : (n*V sInv+1)%2^32=0
  positive : 0<n
  xl : A mX<n
  candidate : V sCand=j
  limit : j<100

def FusedMulData.Pre {g : Geo} {n j : Nat} (C : FusedMulData g n j) (s : State) : Prop :=
  KS g C.s0 C.A fusedLive C.AW [wRc,wR] C.V fusedSlots s

theorem FusedMulData.smallStart_ok {g : Geo} {n j : Nat} (C : FusedMulData g n j)
    {s : State} (h : C.Pre s) : WP isa fusedSmallStart s
      (SmallI g C.s0 C.A C.AW C.V n (C.A mX) (j+2) 1) := by
  simpa only [C.candidate] using fusedSmallStart_ok h rfl C.xl

theorem fusedSmall_relCT {g : Geo} {n j : Nat} (pg : PubG g)
    (C D : FusedMulData g n j) :
    RelCT isa (fun s t => C.Pre s ∧ D.Pre t) VG.Impl.Rsa.X86.RecoverRt.fusedSmall
      (fun _ _ => True) := by
  unfold VG.Impl.Rsa.X86.RecoverRt.fusedSmall
  simp only [seqs]
  apply VG.RelCT.assoc
  refine VG.RelCT.seq (R := fun s t =>
    SmallI g C.s0 C.A C.AW C.V n (C.A mX) (j+2) 1 s ∧
    SmallI g D.s0 D.A D.AW D.V n (D.A mX) (j+2) 1 t)
    (pub_relCT (P := C.Pre) (Q := D.Pre)
      (P' := SmallI g C.s0 C.A C.AW C.V n (C.A mX) (j+2) 1)
      (Q' := SmallI g D.s0 D.A D.AW D.V n (D.A mX) (j+2) 1) pg fusedSmallStartCheck (fun _ h => KS.stage h) (fun _ h => KS.stage h)
      (fun _ h => C.smallStart_ok h) (fun _ h => D.smallStart_ok h)) ?_
  refine (fixedLoop_relCT
    (fun k s => SmallI g C.s0 C.A C.AW C.V n (C.A mX) (j+2) (k+1) s)
    (fun k t => SmallI g D.s0 D.A D.AW D.V n (D.A mX) (j+2) (k+1) t)
    (show 0<j+1 by omega)
    (fun _ _ _ _ _ _ _ _ ⟨hs,ht⟩ es et =>
      ⟨pub_trace pg fusedSmallStepCheck.choose_spec hs.1 ht.1 es et,trivial⟩)
    (fun k s hk hs => by
      simpa only [show j+2-(k+1+1)=j+1-(k+1) from by omega] using
        fusedSmallStep_ok hs C.value C.modulus C.zero C.bound C.inverse C.positive rfl C.xl
          (by omega) (by have := C.limit; omega))
    (fun k t hk ht => by
      simpa only [show j+2-(k+1+1)=j+1-(k+1) from by omega] using
        fusedSmallStep_ok ht D.value D.modulus D.zero D.bound D.inverse D.positive rfl D.xl
          (by omega) (by have := D.limit; omega))).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

theorem fusedMultiply_relCT {g : Geo} {n j : Nat} (pg : PubG g)
    (C D : FusedMulData g n j) :
    RelCT isa (fun s t => C.Pre s ∧ D.Pre t) VG.Impl.Rsa.X86.RecoverRt.fusedMultiply
      (fun _ _ => True) := by
  intro s t tr ur sf tf ⟨hs,ht⟩ es et
  cases es with
  | @seq _ _ _ u _ _ _ e1 e2 =>
  cases et with
  | @seq _ _ _ v _ _ _ f1 f2 =>
  have head : ∀ (E : FusedMulData g n j) (s : State), E.Pre s →
      WP isa (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc sCand)), .alu .sub .eax (.imm 14)]) s
        (fun t => E.Pre t ∧ t.cf=some (decide (j<14))) := by
    intro E s h
    refine wp_movS (h.readSlot (by decide)) fun u U _ => ?_
    have hu := h.of_rest U.keeps (by decide) U.mem
    refine wp_subS rfl fun v D cf => WP.block_nil ⟨hu.of_rest D.keeps (by decide) D.mem,?_⟩
    rw [cf,U.gpr,E.candidate,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := E.limit; omega)]
    rfl
  have check : (VG.Taint.check sseTaint τA
      (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc sCand)), .alu .sub .eax (.imm 14)])
      (VG.Taint.hintOf sseTaint τA
        (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc sCand)), .alu .sub .eax (.imm 14)]))).isSome=true := by
    taint_decide
  have eq1 := pub_trace pg check hs ht e1 f1
  obtain ⟨hu,cu⟩ := wp_result (head C s hs) e1
  obtain ⟨hv,cv⟩ := wp_result (head D t ht) f1
  have branch : RelCT isa (fun s t => C.Pre s ∧ D.Pre t ∧
      s.cf=some (decide (j<14)) ∧ t.cf=some (decide (j<14)))
      (.iteCold .ae VG.Impl.Rsa.X86.RecoverRt.fusedSmall7 VG.Impl.Rsa.X86.RecoverRt.fusedSmall)
      (fun _ _ => True) := by
    apply VG.RelCT.iteCold
    refine VG.RelCT.ite (fun s t ⟨_,_,cs,ct⟩ => by change s.cf.map (!·)=t.cf.map (!·); rw [cs,ct]) ?_ ?_
    · exact (pub_relCT' pg fusedSmall7Check.choose_spec (fun _ h => KS.stage h) (fun _ h => KS.stage h)).mono
        (fun _ _ h => ⟨h.1.1,h.1.2.1⟩) (fun _ _ _ => trivial)
    · exact (fusedSmall_relCT pg C D).mono
        (fun _ _ h => ⟨h.1.1,h.1.2.1⟩) (fun _ _ _ => trivial)
  have eq2 := (branch _ _ _ _ _ _ ⟨hu,hv,cu,cv⟩ e2 f2).1
  exact ⟨by rw [eq1,eq2],trivial⟩

end VG.Proof.Rsa.X86.Recover
