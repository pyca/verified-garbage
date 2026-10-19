module

import VerifiedGarbage.Proof.AesXts.Arm.Unit.Dec
meta import VerifiedGarbage.Proof.AesXts.Arm.Unit.Dec
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
public import VerifiedGarbage.Proof.AesXts.Arm.Unit.Enc
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Impl.Aes.Arm.Alloc
import VerifiedGarbage.Proof.Aes.Ct32.Layers
import VerifiedGarbage.Proof.AesGcm.Arm.Env
import VerifiedGarbage.Proof.AesGcm.Arm.Loops
import VerifiedGarbage.Proof.AesGcm.Arm.Run
import VerifiedGarbage.Proof.AesOcb.Arm.Contract
import VerifiedGarbage.Proof.AesOcb.Arm.Env
import VerifiedGarbage.Proof.AesXts.Alpha
import VerifiedGarbage.Proof.AesXts.Arm.Body
import VerifiedGarbage.Proof.AesXts.Arm.Steps
import VerifiedGarbage.Proof.AesXts.Arm.Unit.Steps
import VerifiedGarbage.Proof.AesXts.Arm.Verified
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.CmacAes.Arm.UpdateCorrect
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Spec.Ocb.Contract
meta import VerifiedGarbage.Impl.Aes.Arm.Alloc
meta import VerifiedGarbage.Proof.Aes.Ct32.Layers
meta import VerifiedGarbage.Proof.AesGcm.Arm.Env
meta import VerifiedGarbage.Proof.AesGcm.Arm.Loops
meta import VerifiedGarbage.Proof.AesGcm.Arm.Run
meta import VerifiedGarbage.Proof.AesOcb.Arm.Contract
meta import VerifiedGarbage.Proof.AesOcb.Arm.Env
meta import VerifiedGarbage.Proof.AesXts.Alpha
meta import VerifiedGarbage.Proof.AesXts.Arm.Body
meta import VerifiedGarbage.Proof.AesXts.Arm.Steps
meta import VerifiedGarbage.Proof.AesXts.Arm.Unit.Steps
meta import VerifiedGarbage.Proof.AesXts.Arm.Verified
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.CmacAes.Arm.UpdateCorrect
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Bytes
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Gcm.Stream
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Spec.Ocb.Contract

/-!
# XTS-AES of data units on ARMv7: constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`), from the correctness proof's states between the pieces: the
taint analysis covers the code between the calls (the swap's loop with
them), from the public arguments for the prologue and from the registers the
states pin to public values (`Inv.agree`) afterwards, each call is constant
time by its callee's proof (`xcall_rel`), and the one branch, on whether
there is a partial block, agrees in both runs.
-/

@[expose] public section

namespace VG.Proof.AesXts.Arm.Unit

open VG VG.Arm VG.Impl.AesXts.ArmUnit

theorem encCall_eq : encCall =
    .frame (.push [.r12, .lr]) (.call (xname true) (xcode true)) (.pop .r12 (4 * [Reg.r12, .lr].length)) := rfl

theorem decCall_eq : decCall =
    .frame (.push [.r12, .lr]) (.call (xname false) (xcode false)) (.pop .r12 (4 * [Reg.r12, .lr].length)) := rfl

/-- A call of a whole-block function, with the same arguments in both runs,
and what each run leaves. -/
theorem xcall_rel (enc : Bool) {P : State → State → Prop} {F₁ F₂ : State → Prop}
    (hx : ∀ s₁ s₂, P s₁ s₂ → ∃ W T D S : BitVec 32, ∃ N R : Nat,
      XPre s₁ W T D S N R ∧ XPre s₂ W T D S N R ∧ s₁.sp = s₂.sp)
    (hw : ∀ s₁ s₂, P s₁ s₂ →
      WP isa (.frame (.push [.r12, .lr]) (.call (xname enc) (xcode enc)) (.pop .r12 (4 * [Reg.r12, .lr].length)))
        s₁ F₁ ∧
      WP isa (.frame (.push [.r12, .lr]) (.call (xname enc) (xcode enc)) (.pop .r12 (4 * [Reg.r12, .lr].length)))
        s₂ F₂) :
    RelCT isa P (.frame (.push [.r12, .lr]) (.call (xname enc) (xcode enc)) (.pop .r12 (4 * [Reg.r12, .lr].length)))
      fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂ :=
  ((xts_rel enc hx).wp hw).mono (fun _ _ h => h) fun _ _ h => h.2

theorem XPre.of_eq {s : State} {W T D S W' T' D' S' : BitVec 32} {N R R' : Nat} (h : XPre s W' T' D' S' N R')
    (e₁ : W = W') (e₂ : T = T') (e₃ : D = D') (e₄ : S = S') (e₅ : R = R') : XPre s W T D S N R := by
  subst e₁ e₂ e₃ e₄ e₅; exact h

/-- The registers the states pin to public values. -/
abbrev pubRegs : List Reg := [.r4, .r5, .r7, .r8, .r9]

section
variable {s₀ s₀' : State} (hq : unitPub s₀ s₀')
include hq

theorem pub_sp : s₀.sp = s₀'.sp := hq.1
theorem pub_W : W s₀ = W s₀' := hq.2.1
theorem pub_K : K s₀ = K s₀' := hq.2.2.1
theorem pub_r2 : s₀.gpr .r2 = s₀'.gpr .r2 := hq.2.2.2.1
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_r2 hq]
theorem pub_D : D s₀ = D s₀' := hq.2.2.2.2.2.1
theorem pub_a1 : stackArg s₀ 1 = stackArg s₀' 1 := hq.2.2.2.2.2.2.1
theorem pub_S : S s₀ = S s₀' := hq.2.2.2.2.2.2.2
theorem pub_M : M s₀ = M s₀' := by rw [M, M, Len, Len, pub_a1 hq]
theorem pub_B : B s₀ = B s₀' := by rw [B, B, Len, Len, pub_a1 hq]
theorem pub_Lv : Lv s₀ = Lv s₀' := by rw [Lv, Lv, pub_D hq, pub_M hq]
theorem pub_Tv : Tv s₀ = Tv s₀' := by rw [Tv, Tv, pub_S hq]
theorem pub_Zv : Zv s₀ = Zv s₀' := by rw [Zv, Zv, pub_S hq]
theorem pub_So {o : Nat} : S s₀ + BitVec.ofNat 32 o = S s₀' + BitVec.ofNat 32 o := by rw [pub_S hq]

theorem Inv.agree {s₁ s₂ : State} (h₁ : Inv s₀ s₁) (h₂ : Inv s₀' s₂) : ∀ r ∈ pubRegs, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h₁.r4, h₂.r4, pub_W hq]
  · rw [h₁.r5, h₂.r5, pub_r2 hq]
  · rw [h₁.r7, h₂.r7, pub_a1 hq]
  · rw [h₁.r8, h₂.r8, pub_S hq]
  · rw [h₁.r9, h₂.r9, pub_D hq]

theorem Inv.sp_eq {s₁ s₂ : State} (h₁ : Inv s₀ s₁) (h₂ : Inv s₀' s₂) : s₁.sp = s₂.sp := by
  rw [h₁.sp, h₂.sp, pub_sp hq]

theorem Inv.agreeT {s₁ s₂ : State} (h₁ : Inv s₀ s₁) (h₂ : Inv s₀' s₂) :
    VG.Arm.Taint.Agree (Taint.ofRegs pubRegs) s₁ s₂ :=
  Taint.agree_ofRegs (Inv.agree hq h₁ h₂)

end

/-! ## Taint checks -/

theorem pro_taint : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] 12) (.block pro) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem argsAll_taint : ∃ h, (taint.check (Taint.ofRegs pubRegs) (.block argsAll) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem argsHead_taint : ∃ h, (taint.check (Taint.ofRegs pubRegs) (.block argsHead) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem split_taint : ∃ h, (taint.check (Taint.ofRegs pubRegs) (.block split) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem encLast_taint : ∃ h, (taint.check (Taint.ofRegs (([.r0, .r1] : List Reg) ++ pubRegs))
    (.seq (.seq (.block lastAddr) swap) (.block (argsL tO))) h).isSome = true := ⟨_, by taint_decide⟩

theorem decL1_taint : ∃ h, (taint.check (Taint.ofRegs pubRegs)
    (.block (nextT ++ split ++ argsL zO)) h).isSome = true := ⟨_, by taint_decide⟩

theorem decL3_taint : ∃ h, (taint.check (Taint.ofRegs pubRegs)
    (.seq (.seq (.block (split ++ lastAddr)) swap) (.block (argsL tO))) h).isSome = true := ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (taint.check (Taint.ofRegs [.r8]) (.block restore) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-! ## The two runs -/

section
variable {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : unitPub s₀ s₀')
include hp hp' hq

omit hp hp' hq in
theorem wfA {s : State} (h : UPre s) :
    s.sp.toNat + 12 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 12⟩ r := by
  have e : (⟨State.addr s.sp, 12⟩ : Region) = argsR s := by simp [stackArgAddr]
  refine ⟨h.sp_fit, ?_⟩
  rw [e, h.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact h.data_args.symm
  · exact h.scr_args.symm

theorem tweak_rel : RelCT isa (fun a b => a = s₀ ∧ b = s₀') tweak fun a b => TwPost s₀ a ∧ TwPost s₀' b := by
  have hsp := pub_sp hq
  have p := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := ProPost s₀) (G' := ProPost s₀')
    (argTaint [.r0, .r1, .r2, .r3] 12)
    (fun s s' e e' => by
      subst e e'
      refine agree_argTaint (fun r hr => ?_) hsp (wfA hp) (wfA hp')
        (argMem_of (j := 3) hsp hp.sp_fit fun i hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hq.2.1
        · exact hq.2.2.1
        · exact hq.2.2.2.1
        · exact hq.2.2.2.2.1
      · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
        · exact hq.2.2.2.2.2.1
        · exact hq.2.2.2.2.2.2.1
        · exact hq.2.2.2.2.2.2.2) pro_taint
    (fun s e => by rw [e]; exact pro_wp hp) (fun s e => by rw [e]; exact pro_wp hp')
  have c := xcall_rel true (P := fun a b => ProPost s₀ a ∧ ProPost s₀' b)
    (fun a b h => ⟨_, _, _, _, _, _, h.1.pre,
      h.2.pre.of_eq (pub_K hq) (pub_Zv hq) (pub_Tv hq) (pub_S hq) (pub_R hq), Inv.sp_eq hq h.1.inv h.2.inv⟩)
    (F₁ := TwPost s₀) (F₂ := TwPost s₀')
    (fun a b h => ⟨tcall_wp hp h.1, tcall_wp hp' h.2⟩)
  exact p.seq c

theorem blocks_rel (enc : Bool) {N N' : Nat} (hN : 16 * N ≤ Len s₀) (hN' : 16 * N' ≤ Len s₀') (hNN : N = N') :
    RelCT isa (fun a b => BlocksReady s₀ N a ∧ BlocksReady s₀' N' b)
      (.frame (.push [.r12, .lr]) (.call (xname enc) (xcode enc)) (.pop .r12 (4 * [Reg.r12, .lr].length)))
      fun a b => AllPost enc s₀ N a ∧ AllPost enc s₀' N' b :=
  xcall_rel enc
    (fun _ _ h => ⟨_, _, _, _, _, _, h.1.pre,
      (hNN ▸ h.2.pre).of_eq (pub_W hq) (pub_Tv hq) (pub_D hq) (pub_S hq) (pub_R hq),
      Inv.sp_eq hq h.1.tw.inv h.2.tw.inv⟩)
    fun _ _ h => ⟨blocks_call hp enc hN h.1.tw h.1.pre, blocks_call hp' enc hN' h.2.tw h.2.pre⟩

theorem restore_rel {enc : Bool} :
    RelCT isa (fun a b => Fin enc s₀ a ∧ Fin enc s₀' b) (.block restore) fun _ _ => True :=
  (rel_agree (F := Fin enc s₀) (F' := Fin enc s₀') (G := fun _ => True) (G' := fun _ => True)
    (Taint.ofRegs [.r8]) (fun a b h₁ h₂ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.inv.r8, h₂.inv.r8, pub_S hq])
    restore_taint (fun _ h => WP.mono (fin_wp hp h.inv) fun _ _ => trivial)
    (fun _ h => WP.mono (fin_wp hp' h.inv) fun _ _ => trivial)).mono
    (fun _ _ h => h) fun _ _ _ => trivial

omit hp hp' in
theorem eval_eq' {s₁ s₂ : State} (h₁ : s₁.z = decide (B s₀ = 0)) (h₂ : s₂.z = decide (B s₀' = 0)) :
    isa.eval .eq s₁ = isa.eval .eq s₂ := by
  rw [eval_b h₁, eval_b h₂, pub_B hq]

theorem encrypt_rel : RelCT isa (fun a b => a = s₀ ∧ b = s₀') Impl.AesXts.ArmUnit.encrypt fun _ _ => True := by
  have hM := pub_M hq
  have t := tweak_rel hp hp' hq
  have a := rel_agree (F := TwPost s₀) (F' := TwPost s₀') (G := BlocksReady s₀ (M s₀))
    (G' := BlocksReady s₀' (M s₀')) (Taint.ofRegs pubRegs) (fun _ _ h₁ h₂ => Inv.agreeT hq h₁.inv h₂.inv)
    argsAll_taint (fun _ h => argsAll_wp hp h) (fun _ h => argsAll_wp hp' h)
  have c := blocks_rel hp hp' hq true (by rw [len_eq s₀]; omega) (by rw [len_eq s₀']; omega) hM
  have sp := rel_agree (F := AllPost true s₀ (M s₀)) (F' := AllPost true s₀' (M s₀'))
    (G := SplitPost true s₀ (M s₀)) (G' := SplitPost true s₀' (M s₀')) (Taint.ofRegs pubRegs)
    (fun _ _ h₁ h₂ => Inv.agreeT hq h₁.inv h₂.inv) split_taint (fun _ h => splitAll_wp hp h)
    (fun _ h => splitAll_wp hp' h)
  have br : RelCT isa (fun a b => SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b)
      (.ite .eq (.block []) encSteal) fun a b => Fin true s₀ a ∧ Fin true s₀' b := by
    refine RelCT.ite (fun a b h => eval_eq' hq h.1.z h.2.z) ?_ ?_
    · refine RelCT.block_nil fun a b h => ?_
      have hb : B s₀ = 0 := by
        have := h.2; rw [eval_b h.1.1.z] at this; simpa using this
      exact ⟨whole_fin h.1.1.all hb, whole_fin h.1.2.all (by rw [← pub_B hq]; exact hb)⟩
    · refine (RelCT.exists_ (P := fun (_ : B s₀ ≠ 0) a b =>
          SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b) fun hB => ?_).mono
        (fun a b h => ⟨by have := h.2; rw [eval_b h.1.1.z] at this; simpa using this, h.1⟩)
        fun _ _ h => h
      have hB' : B s₀' ≠ 0 := by rw [← pub_B hq]; exact hB
      refine RelCT.assoc (RelCT.assoc ?_)
      have l := rel_agree (F := SplitPost true s₀ (M s₀)) (F' := SplitPost true s₀' (M s₀'))
        (G := EncLast s₀) (G' := EncLast s₀') (Taint.ofRegs (([.r0, .r1] : List Reg) ++ pubRegs))
        (fun _ _ h₁ h₂ => Taint.agree_ofRegs fun r hr => by
          rcases List.mem_append.mp hr with hr | hr
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · rw [h₁.r0, h₂.r0, hM]
            · rw [h₁.r1, h₂.r1, pub_B hq]
          · exact Inv.agree hq h₁.all.inv h₂.all.inv r hr)
        encLast_taint (fun _ h => encLast_wp hp h hB) (fun _ h => encLast_wp hp' h hB')
      have c := xcall_rel true (P := fun a b => EncLast s₀ a ∧ EncLast s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.choose_spec.2.pre,
          h.2.choose_spec.2.pre.of_eq (pub_W hq) (pub_So hq) (pub_Lv hq) (pub_S hq) (pub_R hq),
          Inv.sp_eq hq h.1.choose_spec.2.inv h.2.choose_spec.2.inv⟩)
        (F₁ := Fin true s₀) (F₂ := Fin true s₀')
        fun a b h => ⟨encLastCall_wp hp h.1.choose_spec.2 h.1.choose_spec.1 hB,
          encLastCall_wp hp' h.2.choose_spec.2 h.2.choose_spec.1 hB'⟩
      exact l.seq c
  exact t.seq (a.seq (c.seq (sp.seq (br.seq (restore_rel hp hp' hq)))))

theorem decrypt_rel : RelCT isa (fun a b => a = s₀ ∧ b = s₀') Impl.AesXts.ArmUnit.decrypt fun _ _ => True := by
  have hM := pub_M hq
  have t := tweak_rel hp hp' hq
  have sp := rel_agree (F := TwPost s₀) (F' := TwPost s₀')
    (G := fun s => TwPost s₀ s ∧ s.z = decide (B s₀ = 0)) (G' := fun s => TwPost s₀' s ∧ s.z = decide (B s₀' = 0))
    (Taint.ofRegs pubRegs) (fun _ _ h₁ h₂ => Inv.agreeT hq h₁.inv h₂.inv) split_taint
    (fun _ h => split_tw_wp hp h) (fun _ h => split_tw_wp hp' h)
  have br : RelCT isa (fun a b => (TwPost s₀ a ∧ a.z = decide (B s₀ = 0)) ∧
      (TwPost s₀' b ∧ b.z = decide (B s₀' = 0)))
      (.ite .eq (.seq (.block argsAll) decCall) decSteal) fun a b => Fin false s₀ a ∧ Fin false s₀' b := by
    refine RelCT.ite (fun a b h => eval_eq' hq h.1.2 h.2.2) ?_ ?_
    · refine (RelCT.exists_ (P := fun (_ : B s₀ = 0) a b => TwPost s₀ a ∧ TwPost s₀' b) fun hb => ?_).mono
        (fun a b h => ⟨by have := h.2; rw [eval_b h.1.1.2] at this; simpa using this,
          h.1.1.1, h.1.2.1⟩) fun _ _ h => h
      have hb' : B s₀' = 0 := by rw [← pub_B hq]; exact hb
      have a := rel_agree (F := TwPost s₀) (F' := TwPost s₀') (G := BlocksReady s₀ (M s₀))
        (G' := BlocksReady s₀' (M s₀')) (Taint.ofRegs pubRegs) (fun _ _ h₁ h₂ => Inv.agreeT hq h₁.inv h₂.inv)
        argsAll_taint (fun _ h => argsAll_wp hp h) (fun _ h => argsAll_wp hp' h)
      have c := blocks_rel hp hp' hq false (by rw [len_eq s₀]; omega) (by rw [len_eq s₀']; omega) hM
      exact a.seq (c.mono (fun _ _ h => h) fun _ _ h => ⟨whole_fin h.1 hb, whole_fin h.2 hb'⟩)
    · refine (RelCT.exists_ (P := fun (_ : B s₀ ≠ 0) a b => TwPost s₀ a ∧ TwPost s₀' b) fun hB => ?_).mono
        (fun a b h => ⟨by have := h.2; rw [eval_b h.1.1.2] at this; simpa using this,
          h.1.1.1, h.1.2.1⟩) fun _ _ h => h
      have hB' : B s₀' ≠ 0 := by rw [← pub_B hq]; exact hB
      have a := rel_agree (F := TwPost s₀) (F' := TwPost s₀') (G := BlocksReady s₀ (M s₀ - 1))
        (G' := BlocksReady s₀' (M s₀' - 1)) (Taint.ofRegs pubRegs) (fun _ _ h₁ h₂ => Inv.agreeT hq h₁.inv h₂.inv)
        argsHead_taint (fun _ h => argsHead_wp hp h) (fun _ h => argsHead_wp hp' h)
      have c₁ := blocks_rel hp hp' hq false (N := M s₀ - 1) (N' := M s₀' - 1) (by rw [len_eq s₀]; omega)
        (by rw [len_eq s₀']; omega) (by rw [hM])
      have l₁ := rel_agree (F := AllPost false s₀ (M s₀ - 1)) (F' := AllPost false s₀' (M s₀' - 1))
        (G := DecL1 s₀) (G' := DecL1 s₀') (Taint.ofRegs pubRegs) (fun _ _ h₁ h₂ => Inv.agreeT hq h₁.inv h₂.inv)
        decL1_taint (fun _ h => decL1_wp hp h) (fun _ h => decL1_wp hp' h)
      have c₂ := xcall_rel false (P := fun a b => DecL1 s₀ a ∧ DecL1 s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.pre,
          h.2.pre.of_eq (pub_W hq) (pub_Zv hq) (pub_Lv hq) (pub_S hq) (pub_R hq),
          Inv.sp_eq hq h.1.inv h.2.inv⟩)
        (F₁ := DecL2 s₀) (F₂ := DecL2 s₀') fun a b h => ⟨decL2_wp hp h.1, decL2_wp hp' h.2⟩
      have l₃ := rel_agree (F := DecL2 s₀) (F' := DecL2 s₀') (G := DecL3 s₀) (G' := DecL3 s₀')
        (Taint.ofRegs pubRegs) (fun _ _ h₁ h₂ => Inv.agreeT hq h₁.inv h₂.inv) decL3_taint
        (fun _ h => decL3_wp hp h hB) (fun _ h => decL3_wp hp' h hB')
      have c₃ := xcall_rel false (P := fun a b => DecL3 s₀ a ∧ DecL3 s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.choose_spec.2.pre,
          h.2.choose_spec.2.pre.of_eq (pub_W hq) (pub_So hq) (pub_Lv hq) (pub_S hq) (pub_R hq),
          Inv.sp_eq hq h.1.choose_spec.2.inv h.2.choose_spec.2.inv⟩)
        (F₁ := Fin false s₀) (F₂ := Fin false s₀')
        fun a b h => ⟨decLast_wp hp h.1.choose_spec.2 h.1.choose_spec.1 hB,
          decLast_wp hp' h.2.choose_spec.2 h.2.choose_spec.1 hB'⟩
      exact a.seq (c₁.seq (l₁.seq (c₂.seq (RelCT.assoc (RelCT.assoc (l₃.seq c₃))))))
  exact t.seq (sp.seq (br.seq (restore_rel hp hp' hq)))

end

theorem encrypt_ct : ConstantTime isa (unitArm true).pre (unitArm true).pub Impl.AesXts.ArmUnit.encrypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (encrypt_rel (UPre.of h₁) (UPre.of h₂) hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem decrypt_ct : ConstantTime isa (unitArm false).pre (unitArm false).pub Impl.AesXts.ArmUnit.decrypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (decrypt_rel (UPre.of h₁) (UPre.of h₂) hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesXts.Arm.Unit
