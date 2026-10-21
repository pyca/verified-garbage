module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckArgs
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckFrame
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Entry
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.InvokeTiming
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Finish
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Result
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallResult
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.DrawCT
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.FinishCT
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Generate
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.GenerateCT
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Public
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.SampledCT

/-! # The domain-checking branch and final cleanup have public control flow -/
@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.GenerateKey

structure CheckedState (I : State → Mem → Prop) (s t : State) : Prop where
  ready : Ready s t
  saved : Saved s t.mem
  used : slot t.mem (rBase s) oUsed = 0
  status : slot t.mem (rBase s) oStatus = 0
  zf : t.zf = some (!checked s)
  invariant : checked s = true → I s t.mem

theorem checkArgs_step {s t : State} (A : KeyABI s) (h : Ready s t) :
    WP isa (.block checkArgs) t fun u => Ready s u ∧ CheckCall.CallSlots s u := by
  change WP isa (.block (checkArgs ++ [])) t _
  refine CheckCall.checkArgs_ok A h fun u hu mu _ => WP.block_nil ⟨hu, ?_⟩
  intro i hi
  rw [mu]; exact CheckCall.argsMem_slots s _ _ i hi

theorem checked_step {I : State → Mem → Prop} (C : CheckInvoke I) {s₀ : State} (A : KeyABI s₀) :
    WP isa (.seq (.block (entry ++ checkArgs))
      (.seq C.code (.block [.alu .cmp .eax (.imm 0)])))
      (allocated KeyRandom.frameBytes s₀) (CheckedState I s₀) := by
  have h0 := alloc_ready A
  refine WP.seq (WP.block_append (WP.mono (entry_ok h0 (allocated_gpr _ _ (by decide))
    (allocated_gpr _ _ (by decide)) (allocated_gpr _ _ (by decide)) (allocated_gpr _ _ (by decide)))
    fun t ⟨ht, saved, used, status, _⟩ => ?_))
  change WP isa (.block (checkArgs ++ [])) t _
  refine CheckCall.checkArgs_ok A ht fun u hu mu ku => WP.block_nil ?_
  have ou := CheckCall.argsMem_outs s₀ t.mem
  rw [← mu] at ou
  have slots : CheckCall.CallSlots s₀ u := fun i hi => by rw [mu]; exact CheckCall.argsMem_slots s₀ _ _ i hi
  refine WP.seq (WP.mono (C.correct A hu slots) fun v ⟨hv, frame, _, eax, invariant⟩ => ?_)
  have low (d : Nat) (hd : 44 ≤ d) (hd' : d + 4 ≤ 120) :
      slot v.mem (rBase s₀) d = slot t.mem (rBase s₀) d := by
    rw [CheckCall.call_frame_slot A frame hd hd', outs_high ou (e := 44) (by decide) hd (by omega)]
  have savedV : Saved s₀ v.mem := saved.of_slots fun d hd hd' => low d hd (by omega)
  have usedV : slot v.mem (rBase s₀) oUsed = 0 := by rw [low _ (by decide) (by decide)]; exact used
  have statusV : slot v.mem (rBase s₀) oStatus = 0 := by rw [low _ (by decide) (by decide)]; exact status
  rw [checkResult_eq A hu] at eax invariant
  refine wp_cmpi fun w fw _ zw => WP.block_nil ?_
  have hw := hv.fupd fw
  have savedW : Saved s₀ w.mem := by rw [fw.mem]; exact savedV
  have usedW : slot w.mem (rBase s₀) oUsed = 0 := by rw [fw.mem]; exact usedV
  rw [eax] at zw
  refine ⟨hw, savedW, usedW, by rw [fw.mem]; exact statusV, ?_, by rw [fw.mem]; exact invariant⟩
  cases hc : checked s₀ <;> simp only [hc] at zw ⊢ <;> rw [zw] <;> rfl

theorem checked_branch {I : State → Mem → Prop} (D : DeriveInvoke I) (stable : StableScratch I) {s t : State} (A : KeyABI s) (h : CheckedState I s t) :
    WP isa (.ite .e (.block []) (generateWith D.code)) t (Fin s) := by
  cases hc : checked s with
  | true =>
    refine WP.ite false (by simp only [eval, h.zf, hc]; rfl) (fun e => Bool.noConfusion e) (fun _ => ?_)
    exact generateWith_ok D stable A h.ready hc h.saved h.used (h.invariant hc)
  | false =>
    refine WP.ite true (by simp only [eval, h.zf, hc]; rfl) (fun _ => WP.block_nil ?_) (fun e => Bool.noConfusion e)
    have R := result_eq A
    simp only [hc, Bool.false_eq_true, ite_false] at R
    exact ⟨h.ready, by rw [R]; exact h.used, by rw [R]; exact h.status,
      by rw [R]; intro e; contradiction, h.saved⟩

theorem bodyWith_ct {I : State → Mem → Prop} (C : CheckInvoke I) (D : DeriveInvoke I)
    (stable : StableScratch I) (ctC : CheckInvokeCT C) (ctD : DeriveInvokeCT D) {s₁ s₂ : State}
    (A₁ : KeyABI s₁) (A₂ : KeyABI s₂) (e : pubOf s₁ = pubOf s₂)
    (hk : keyLeak s₁ = keyLeak s₂) (hr : (rResult s₁).status = (rResult s₂).status)
    (ht : (rResult s₁).trace = (rResult s₂).trace)
    {tr₁ tr₂ : List Leak} {u₁ u₂ : State}
    (x₁ : Exec isa (bodyWith C.code D.code) (allocated KeyRandom.frameBytes s₁) tr₁ u₁)
    (x₂ : Exec isa (bodyWith C.code D.code) (allocated KeyRandom.frameBytes s₂) tr₂ u₂) :
    tr₁ = tr₂ := by
  have hkey : (rInput s₁).key = (rInput s₂).key :=
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hk
  have hcheck := checked_eq e hkey
  unfold bodyWith at x₁ x₂
  cases x₁ with | seq en₁ re₁ => cases re₁ with | seq cl₁ re₁ => cases re₁ with | seq cm₁ re₁ => cases re₁ with | seq br₁ fi₁ =>
  cases x₂ with | seq en₂ re₂ => cases re₂ with | seq cl₂ re₂ => cases re₂ with | seq cm₂ re₂ => cases re₂ with | seq br₂ fi₂ =>
  have cen : RelCT isa (Two (At Ready)) (.block (entry ++ checkArgs)) (fun _ _ => True) :=
    two_taint [.esp] (pins_at id fun _ _ _ h => h) (by taint_decide)
  have een := (cen _ _ _ _ _ _ ⟨pubOf s₁, ⟨s₁, A₁, rfl, alloc_ready A₁⟩, s₂, A₂, e.symm, alloc_ready A₂⟩ en₁ en₂).1
  have entrySlots {s : State} (A : KeyABI s) :
      WP isa (.block (entry ++ checkArgs)) (allocated KeyRandom.frameBytes s)
        fun t => Ready s t ∧ CheckCall.CallSlots s t := by
    refine WP.block_append (WP.mono (entry_ok (alloc_ready A) (allocated_gpr _ _ (by decide))
      (allocated_gpr _ _ (by decide)) (allocated_gpr _ _ (by decide)) (allocated_gpr _ _ (by decide)))
      fun t ⟨h, _⟩ => checkArgs_step A h)
  obtain ⟨r₁, sl₁⟩ := post_of_exec (entrySlots A₁) en₁
  obtain ⟨r₂, sl₂⟩ := post_of_exec (entrySlots A₂) en₂
  have ecl := (ctC _ _ _ _ _ _ ⟨s₁, s₂, A₁, A₂, e, hk, r₁, r₂, sl₁, sl₂⟩ cl₁ cl₂).1
  have ccm : RelCT isa (fun _ _ => True) (.block [.alu .cmp .eax (.imm 0)]) (fun _ _ => True) :=
    RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs (by simp)) (by taint_decide)
  have ecm := (ccm _ _ _ _ _ _ trivial cm₁ cm₂).1
  have cs₁ := post_of_exec (checked_step C A₁) (.seq en₁ (.seq cl₁ cm₁))
  have cs₂ := post_of_exec (checked_step C A₂) (.seq en₂ (.seq cl₂ cm₂))
  have sameBranch : ∀ {a b : State}, CheckedState I s₁ a → CheckedState I s₂ b → eval .e a = eval .e b := by
    intro a b ha hb; simp only [eval, ha.zf, hb.zf, hcheck]
  have branchCT : ∀ {a b u v : State} {ta tb : List Leak}, CheckedState I s₁ a → CheckedState I s₂ b →
      Exec isa (.ite .e (.block []) (generateWith D.code)) a ta u →
      Exec isa (.ite .e (.block []) (generateWith D.code)) b tb v → ta = tb := by
    intro a b u v ta tb ha hb xa xb
    cases xa with
    | iteT fa xa =>
      cases xb with
      | iteF fb _ => have bad := fa.symm.trans ((sameBranch ha hb).trans fb); cases bad
      | iteT _ xb => cases xa with | block xa => cases xa; cases xb with | block xb => cases xb; rfl
    | iteF fa xa =>
      cases xb with
      | iteT fb _ => have bad := fa.symm.trans ((sameBranch ha hb).trans fb); cases bad
      | iteF fb xb =>
        have hc₁ : checked s₁ = true := by
          have ff : (!checked s₁) = false := by simpa only [eval, ha.zf, Option.some.injEq] using fa
          cases he : checked s₁ with
          | false => rw [he] at ff; contradiction
          | true => rfl
        have hc₂ : checked s₂ = true := hcheck ▸ hc₁
        exact congrArg (fun tr => Leak.branch false :: tr)
          (generateWith_ct D stable ctD A₁ A₂ e hk hc₁ hc₂ hr ht ha.ready hb.ready ha.used hb.used (ha.invariant hc₁) (hb.invariant hc₂) xa xb)
  have ebr := branchCT cs₁ cs₂ br₁ br₂
  have F₁ := post_of_exec (checked_branch D stable A₁ cs₁) br₁
  have F₂ := post_of_exec (checked_branch D stable A₂ cs₂) br₂
  have efi := (finish_ct _ _ _ _ _ _ ⟨(pubOf s₁, (rResult s₁).status),
    ⟨s₁, A₁, rfl, F₁, rfl⟩, s₂, A₂, e.symm, F₂, hr.symm⟩ fi₁ fi₂).1
  simp only [een, ecl, ecm, ebr, efi]
theorem body_ct (C : CheckCall.CheckFn) (D : DeriveFn) {s₁ s₂ : State}
    (A₁ : KeyABI s₁) (A₂ : KeyABI s₂) (e : pubOf s₁ = pubOf s₂)
    (hk : keyLeak s₁ = keyLeak s₂) (hr : (rResult s₁).status = (rResult s₂).status)
    (ht : (rResult s₁).trace = (rResult s₂).trace)
    {tr₁ tr₂ : List Leak} {u₁ u₂ : State}
    (x₁ : Exec isa (body C.name D.name C.code D.code) (allocated KeyRandom.frameBytes s₁) tr₁ u₁)
    (x₂ : Exec isa (body C.name D.name C.code D.code) (allocated KeyRandom.frameBytes s₂) tr₂ u₂) :
    tr₁ = tr₂ :=
  bodyWith_ct C.invoke D.invoke (fun _ _ _ => trivial) C.invoke_ct D.invoke_ct
    A₁ A₂ e hk hr ht x₁ x₂

end VG.Proof.Dsa.X86.KeyRandom
