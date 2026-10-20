module

public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! The shared FFDH frame adds only fixed stack addresses to its body's trace. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm

theorem framed_ct {P : State → State → Prop} {body : Prog isa}
    (fits : ∀ s t, P s t → 128 ≤ s.sp.toNat ∧ 128 ≤ t.sp.toNat)
    (sp : ∀ s t, P s t → s.sp = t.sp)
    (ct : RelCT isa (fun a b => ∃ s t, P s t ∧ a = entered s ∧ b = entered t) body (fun _ _ => True)) :
    RelCT isa P (VG.Impl.Ffdh.Arm.framed body) (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.framed
  apply RelCT.frame sp
  intro s t tr1 tr2 u v hp e1 e2
  obtain ⟨s0, t0, related, ps, pt⟩ := hp
  have fit := fits s0 t0 related
  have ps' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) (by omega : 56 ≤ s0.sp.toNat)
  have pt' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) (by omega : 56 ≤ t0.sp.toNat)
  have es : pcPushed s0 = s := Option.some.inj (ps'.symm.trans ps)
  have et : pcPushed t0 = t := Option.some.inj (pt'.symm.trans pt)
  subst s; subst t
  have spPush : (pcPushed s0).sp = (pcPushed t0).sp := by
    change s0.sp - BitVec.ofNat 32 56 = t0.sp - BitVec.ofNat 32 56
    rw [sp s0 t0 related]
  have allocatedTrace : RelCT isa
      (fun a b => a = pcPushed s0 ∧ b = pcPushed t0)
      (.frame (.alloc 72) body (.free 72)) (fun _ _ => True) := by
    intro a b ta tb a' b' h ea eb
    rcases h with ⟨rfl, rfl⟩
    cases ea with
    | frame pa ba qa =>
      cases eb with
      | frame pb bb qb =>
        have roomS : 72 ≤ (pcPushed s0).sp.toNat := by
          change 72 ≤ (s0.sp - BitVec.ofNat 32 56).toNat
          rw [FrameStack.sub_toNat' (by omega : 56 ≤ s0.sp.toNat)]; omega
        have roomT : 72 ≤ (pcPushed t0).sp.toNat := by
          change 72 ≤ (t0.sp - BitVec.ofNat 32 56).toNat
          rw [FrameStack.sub_toNat' (by omega : 56 ≤ t0.sp.toNat)]; omega
        have allocS : isa.push (.alloc 72) (pcPushed s0) = some (entered s0) := by
          simp only [isa, push, roomS, Nat.reduceLT, Nat.reduceMod, encodable]
          rfl
        have allocT : isa.push (.alloc 72) (pcPushed t0) = some (entered t0) := by
          simp only [isa, push, roomT, Nat.reduceLT, Nat.reduceMod, encodable]
          rfl
        have eqS := Option.some.inj (pa.symm.trans allocS)
        have eqT := Option.some.inj (pb.symm.trans allocT)
        subst eqS; subst eqT
        have trace := (ct _ _ _ _ _ _ ⟨s0, t0, related, rfl, rfl⟩ ba bb).1
        exact ⟨by simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using trace, trivial⟩
  have allocatedSp := relCT_keep_sp allocatedTrace (fun _ _ h => by rcases h with ⟨rfl, rfl⟩; exact spPush)
  have restore : RelCT isa (fun a b => a.sp = b.sp) (.block VG.Impl.Bignum.Arm.PcFn.restore)
      (fun a b => a.sp = b.sp) := stackLoads_ct pcCalleeSaved
  exact ⟨(allocatedSp.seq restore _ _ _ _ _ _ ⟨rfl, rfl⟩ e1 e2).1, trivial⟩

end VG.Proof.Ffdh.Arm
