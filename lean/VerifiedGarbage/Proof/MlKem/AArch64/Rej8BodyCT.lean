module

public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8StepCT
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Body
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Choice
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Public
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Impl.MlKem.AArch64.Encode
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Lanes
import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Accept
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8BatchCT
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Decode
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Finish
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Invariant
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Loop
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Memory
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8ScalarCT
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Steps
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Zero
import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Impl.MlKem.AArch64.Encode
meta import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Lanes
meta import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
meta import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Accept
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Advance
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Decode
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Invariant
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Memory
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Steps
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Tail
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Vector
meta import VerifiedGarbage.Proof.MlKem.Compress

/-! # Paired executions choose the same rejection path and early exit -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

def BodyPairPostW (w16 : Bool) (initial : List Zq) (N : Nat) (B : Nat → Byte) (bP aP : Addr)
    (s₀ u₀ : State) (t : Nat) (s u : State) : Prop :=
  PairInvW w16 initial N B bP aP s₀ u₀ (t+4) s u ∨
    (ResultW w16 initial N B aP s₀ s ∧ ResultW w16 initial N B aP u₀ u ∧ s.gpr .x5=0 ∧ u.gpr .x5=0)

theorem choice_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [])) (.block choosePrefix) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs []) (fun _ _ _ _ h => h) (by taint_decide)

theorem choice_relCT {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ u₀ : State} (hsp : s₀.sp=u₀.sp) :
    RelCT isa (PairInvW w16 initial N B bP aP s₀ u₀ t) (.block choosePrefix)
      (fun s u => PairInvW w16 initial N B bP aP s₀ u₀ t s u ∧
        (s.gpr .x6 == 0)=(u.gpr .x6 == 0) ∧
        ((s.gpr .x6 == 0)=true ↔ 8≤(s.gpr .x4).toNat)) := by
  intro s u tr ur s' u' hp es eu
  have pub := inv_public hp.1 hp.2.1 hsp
  have htr := choice_ct s u tr ur s' u' trivial trivial ⟨pub.1,by simp [Taint.ofRegs,RegSet.mem_ofList]⟩ es eu
  obtain ⟨_,a,ea,ha,ca,fa⟩ := choosePrefix_ok hp.1 hp.2.2.1
  obtain ⟨_,b,eb,hb,cb,fb⟩ := choosePrefix_ok hp.2.1 hp.2.2.2
  obtain ⟨_,rfl⟩ := Exec.det es ea
  obtain ⟨_,rfl⟩ := Exec.det eu eb
  refine ⟨htr,⟨ha,hb,ca,cb⟩,?_,fa⟩
  apply Bool.eq_iff_iff.mpr
  rw [fa,fb,(inv_public ha hb hsp).2 .x4 (by simp)]

theorem stop_full_ok {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ s : State} (h : Scalar.InvW w16 initial N B bP aP s₀ t s) (hc : Constants s)
    (ht : t≤N) (hf : (Scalar.LA initial B t).length=256) :
    WP isa (.block [.movz .x .x5 0 0]) s fun u => ResultW w16 initial N B aP s₀ u ∧ u.gpr .x5=0 := by
  have heq := sampleAfter_full (show (Scalar.LA initial B t).length=n from hf) N ht
  have hw : WP isa (.block [.movz .x .x5 0 0]) s fun u =>
      Scalar.AccW w16 aP s₀ (Scalar.LA initial B N) u ∧ Keep Scalar.lRegs s₀ u ∧ u.gpr .x5=0 := by
    refine wp_movz fun u hu eu => wp_nil ⟨?_,(h.keep.trans hu.keep).mono (by decide),eu⟩
    rw [show Scalar.LA initial B N=Scalar.LA initial B t from heq]
    exact Scalar.acc_keep h.acc hu.keep hu.mem
  refine WP.mono (WP.keepV (by decide) hw) fun u ⟨⟨ac,ke,x5⟩,ve⟩ => ⟨⟨ac,ke,?_⟩,x5⟩
  exact ⟨by rw [ve]; exact hc.index,by rw [ve]; exact hc.mask,
    by simpa only [ve] using hc.q,by simpa only [ve] using hc.weights,
    by simpa only [ve] using hc.zero⟩

theorem stop_relCT {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ u₀ : State} (hsp : s₀.sp=u₀.sp) (ht : t+4≤N) :
    RelCT isa (PairInvW w16 initial N B bP aP s₀ u₀ (t+4))
      (.ite (.zero .x .x4) (.block [.movz .x .x5 0 0]) (.block []))
      (BodyPairPostW w16 initial N B bP aP s₀ u₀ t) := by
  refine RelCT.ite (fun s u hp => by rw [eval_zero,eval_zero,(inv_public hp.1 hp.2.1 hsp).2 .x4 (by simp)]) ?_ ?_
  · intro s u tr ur s' u' hp es eu
    have hf : (Scalar.LA initial B (t+4)).length=256 := by
      have hz := hp.2
      rw [eval_zero] at hz
      have hz' : (s.gpr .x4).toNat=0 := by simpa only [Option.some.injEq,eq_zero_iff,decide_eq_true_eq] using hz
      rw [hp.1.1.acc.x4] at hz'
      have := hp.1.1.acc.len
      omega
    have ct : ConstantTime isa (fun _ => True) (VG.AArch64.Taint.Agree (Taint.ofRegs []))
        (.block [.movz .x .x5 0 0]) :=
      VG.Taint.constantTime (A := taint) (Taint.ofRegs []) (fun _ _ _ _ h => h) (by taint_decide)
    have htr := ct s u tr ur s' u' trivial trivial
      ⟨(inv_public hp.1.1 hp.1.2.1 hsp).1,by simp [Taint.ofRegs,RegSet.mem_ofList]⟩ es eu
    obtain ⟨_,a,ea,ha,xa⟩ := stop_full_ok hp.1.1 hp.1.2.2.1 ht hf
    obtain ⟨_,b,eb,hb,xb⟩ := stop_full_ok hp.1.2.1 hp.1.2.2.2 ht hf
    obtain ⟨_,rfl⟩ := Exec.det es ea
    obtain ⟨_,rfl⟩ := Exec.det eu eb
    exact ⟨htr,Or.inr ⟨ha,hb,xa,xb⟩⟩
  · exact RelCT.block_nil (fun _ _ h => Or.inl h.1)

theorem body_relCT {w16 : Bool} {initial : List Zq} {N t : Nat} {B : Nat → Byte} {bP aP : Addr}
    {s₀ u₀ : State} (ps : EnvW w16 N B bP aP s₀) (pu : EnvW w16 N B bP aP u₀)
    (hsp : s₀.sp=u₀.sp) (htab : s₀.gpr .x16=u₀.gpr .x16) (ht : t+4≤N) :
    RelCT isa (PairInvW w16 initial N B bP aP s₀ u₀ t) (body w16)
      (BodyPairPostW w16 initial N B bP aP s₀ u₀ t) := by
  refine RelCT.seq (choice_relCT hsp) (RelCT.ite (fun s u hp => by
    rw [eval_zero,eval_zero,hp.2.1]) ?_ ?_)
  · intro s u tr ur s' u' hp es eu
    have hz : (s.gpr .x6 == 0)=true := by
      have hx := hp.2
      rw [eval_zero] at hx
      exact Option.some.inj hx
    have hr := hp.1.2.2.mp hz
    rw [hp.1.1.1.acc.x4] at hr
    have hlen := hp.1.1.1.acc.len
    obtain ⟨he,hp'⟩ := vectorStep_relCT ps pu hsp htab ht (by omega) s u tr ur s' u' hp.1.1 es eu
    exact ⟨he,Or.inl hp'⟩
  · exact RelCT.mono (RelCT.seq (scalarFour_relCT ps pu hsp ht) (stop_relCT hsp ht))
      (fun _ _ h => h.1.1) (fun _ _ h => h)

end VG.Proof.MlKem.AArch64.Rej8
