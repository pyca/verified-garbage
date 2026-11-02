module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.CheckCall
import VerifiedGarbage.Proof.Dsa.X86.Generation.TimingFlags
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Dsa.X86.Generation.ABIEnv
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Geo
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TimingBase
import VerifiedGarbage.Proof.Dsa.X86.Generation.HashCT
import VerifiedGarbage.Proof.Framework.X86.CallReturn
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words
public import VerifiedGarbage.Proof.Dsa.Contract

/-! # Two runs of the domain check of the same p||q||g leak the same -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation

/-- The check's writable regions, at the generator's stack pointer. -/
def chkWrSp (E : Env) : List Region :=
  [⟨off E.base sChk, 16 * E.pLen * 8⟩, ⟨(E.sp - 24#32).setWidth 64, 24⟩]

theorem chkWr_sp {E : Env} {t : State} (h : t.gpr .esp = E.sp) : chkWr E t = chkWrSp E := by
  simp only [chkWr, chkWrSp, h]

/-- Before the check: p||q||g. -/
def CIn (E : Env) (g : Geo) (b : List Byte) (s : State) : Prop :=
  Base E s ∧ Spec.Rsa.bytesAt s.mem (off E.base sPk) (2 * g.pLen + g.qLen) = b

theorem wp_of_seq_nil {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq c (.block [])) s Q) :
    WP isa c s Q := by
  obtain ⟨t, s', e, q⟩ := h
  cases e with
  | seq e₁ e₂ =>
    cases e₂ with
    | block h₂ =>
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₂
      obtain ⟨rfl, rfl⟩ := h₂
      exact ⟨_, _, e₁, q⟩

/-- The check's call keeps `esp` and `edi`. -/
theorem chkCall_regs {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen)
    {s t : State} (B : Base E s) (A : ChkArgs E g s t) :
    WP isa (.frame (.push [.ebp, .esi, .ebx, .edx, .ecx, .eax]) (.call g.checkName g.checkCode) (.pop .ecx 6)) t
      fun u => u.gpr .esp = t.gpr .esp ∧ u.gpr .edi = t.gpr .edi := by
  have low := v.low
  have cs := G.cStack
  have spT : t.gpr .esp = E.sp := by
    rw [A.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), B.sp]
  exact WP.of_syms (WP.callWithReturn G.cv.1 G.cNoSp (by decide) (by decide)
    (by rw [spT]; simp only [List.length_cons, List.length_nil]; omega) (chk_callPre G v hp hq B A)
    fun u _ _ csu _ _ _ => ⟨csu .esp (by decide), csu .edi (by decide)⟩)

/-- What the check sees: its arguments and p||q||g. -/
theorem chkEntry_facts {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) {s t : State} (B : Base E s) (A : ChkArgs E g s t) :
    ((pushed chkRegs t).callEntry.withRegions (chkRd E) (chkWrSp E)).gpr .esp = E.sp - 28#32 ∧
      arg ((pushed chkRegs t).callEntry.withRegions (chkRd E) (chkWrSp E)) 0 = s.gpr .edi + BitVec.ofNat 32 sPk ∧
      arg ((pushed chkRegs t).callEntry.withRegions (chkRd E) (chkWrSp E)) 1 =
        BitVec.ofNat 32 (2 * g.pLen + g.qLen) ∧
      arg ((pushed chkRegs t).callEntry.withRegions (chkRd E) (chkWrSp E)) 2 = BitVec.ofNat 32 g.pLen ∧
      arg ((pushed chkRegs t).callEntry.withRegions (chkRd E) (chkWrSp E)) 3 = BitVec.ofNat 32 g.qLen ∧
      arg ((pushed chkRegs t).callEntry.withRegions (chkRd E) (chkWrSp E)) 4 = s.gpr .edi + BitVec.ofNat 32 sChk ∧
      arg ((pushed chkRegs t).callEntry.withRegions (chkRd E) (chkWrSp E)) 5 = BitVec.ofNat 32 (16 * g.pLen) ∧
      Spec.Rsa.bytesAt ((pushed chkRegs t).callEntry.withRegions (chkRd E) (chkWrSp E)).mem
        ((s.gpr .edi + BitVec.ofNat 32 sPk).setWidth 64) (2 * g.pLen + g.qLen) =
        Spec.Rsa.bytesAt s.mem (off E.base sPk) (2 * g.pLen + g.qLen) := by
  have sz := v.size_ge
  have bd := G.bounds
  have low := v.low
  have spT : t.gpr .esp = E.sp := by
    rw [A.other _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), B.sp]
  have fitT : 28 ≤ (t.gpr .esp).toNat := by rw [spT]; omega
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := chkEntry_arg (E := E) (s := t) fitT
  have Fm := chkEntry_mem (E := E) (s := t) fitT
  simp only [chkEntry, chkWr_sp spT] at e0 e1 e2 e3 e4 e5 Fm
  rw [A.eax] at e0; rw [A.ecx] at e1; rw [A.edx] at e2; rw [A.ebx] at e3; rw [A.esi] at e4; rw [A.ebp] at e5
  refine ⟨?_, e0, e1, e2, e3, e4, e5, ?_⟩
  · change (pushed chkRegs t).callEntry.gpr .esp = _
    rw [callEntry_esp' chkRegs t, spT]; rfl
  · have pW := Scr.wide B.scr (d := sPk) (by simp only [sPk]; omega)
    rw [pW, ← A.mem]
    rw [spT] at Fm
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    simp only [List.mem_range] at hi
    refine Frame.bytes Fm (R := ⟨off E.base sPk, 2 * g.pLen + g.qLen⟩) ?_ (by show 2 * g.pLen + g.qLen ≤ 2 ^ 64; omega) hi
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact (v.scratchStack.sub_left (Offset.sub_base _ (by simp only [sPk]; omega))).sub_right
      (below_sub (by decide) (by omega))

theorem check_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen) :
    RelCT isa (Both (CIn E g)) (check g.pLen g.qLen (16 * g.pLen) g.checkName g.checkCode) fun _ _ => True := by
  have sz := v.size_ge
  have low := v.low
  unfold check
  show RelCT isa _ (Prog.chain [_, _, _] (.ite .e _ _)) _
  refine RelCT.chain (RelCT.seq (both_post (Ψ := fun b x => ∃ s, CIn E g b s ∧
      ChkMid E g (Spec.Dsa.checkParametersBytes g.pLen g.qLen b) s x) ?_
    fun b s h => checkMid_ok G v hp hq h.1 (P := .block []) fun x M => WP.block_nil ⟨s, h, by rw [← h.2]; exact M⟩) ?_)
  · -- The arguments.
    refine RelCT.seq (both_post (Ψ := fun b t => ∃ s, CIn E g b s ∧ ChkArgs E g s t)
      (both_agree [.esp, .edi] (fun _ => baseVal E) (fun _ _ h => base_pins h.1) ?_)
      fun b s h => wp_of_seq_nil (chkArgs_ok (rest := .block []) fun t A => WP.block_nil ⟨s, h, A⟩)) ?_
    · rcases G.lengths with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂] <;> exact tcheck _ _ (by decide +kernel)
    have pins : ∀ (b : List Byte) t, (∃ s, CIn E g b s ∧ ChkArgs E g s t) → ∀ r ∈ [Reg.esp, .edi],
        t.gpr r = baseVal E r := by
      rintro b t ⟨s, h, A⟩ r hr
      rw [A.other r (by simp at hr; rcases hr with rfl | rfl <;> decide)
        (by simp at hr; rcases hr with rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl <;> decide)
        (by simp at hr; rcases hr with rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl <;> decide)
        (by simp at hr; rcases hr with rfl | rfl <;> decide)]
      exact base_pins h.1 r hr
    let Pin : State → Prop := fun t => ∀ r ∈ [Reg.esp, .edi], t.gpr r = baseVal E r
    refine RelCT.seq (R := fun u₁ u₂ => Pin u₁ ∧ Pin u₂) ?_ ?_
    · -- The call.
      refine both_exists fun b => ?_
      refine ((callWithPop (rs := chkRegs) G.cv.1 G.cv.2.1 (chkRd E) (chkWrSp E) fun t₁ t₂ hp => ?_).wp
        (F₁ := Pin) (F₂ := Pin) fun t₁ t₂ h => ⟨?_, ?_⟩).mono (fun _ _ h => h) fun _ _ h => h.2
      · obtain ⟨⟨s₁, h₁, A₁⟩, ⟨s₂, h₂, A₂⟩⟩ := hp
        have sp₁ : t₁.gpr .esp = E.sp := pins b t₁ ⟨s₁, h₁, A₁⟩ _ (by simp)
        have sp₂ : t₂.gpr .esp = E.sp := pins b t₂ ⟨s₂, h₂, A₂⟩ _ (by simp)
        have c₁ := chk_callPre G v hp hq h₁.1 A₁
        have c₂ := chk_callPre G v hp hq h₂.1 A₂
        rw [chkWr_sp sp₁] at c₁
        rw [chkWr_sp sp₂] at c₂
        refine ⟨c₁, c₂, sp₁.trans sp₂.symm, ?_⟩
        obtain ⟨esp₁, a0₁, a1₁, a2₁, a3₁, a4₁, a5₁, by₁⟩ := chkEntry_facts G v h₁.1 A₁
        obtain ⟨esp₂, a0₂, a1₂, a2₂, a3₂, a4₂, a5₂, by₂⟩ := chkEntry_facts G v h₂.1 A₂
        generalize (pushed chkRegs t₁).callEntry.withRegions (chkRd E) (chkWrSp E) = w₁ at esp₁ a0₁ a1₁ a2₁ a3₁ a4₁ a5₁ by₁ ⊢
        generalize (pushed chkRegs t₂).callEntry.withRegions (chkRd E) (chkWrSp E) = w₂ at esp₂ a0₂ a1₂ a2₂ a3₂ a4₂ a5₂ by₂ ⊢
        sig_pub [chkContract, Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argSlots, argVal,
          argBytes]
        have l1 : (BitVec.ofNat 32 (2 * g.pLen + g.qLen)).toNat = 2 * g.pLen + g.qLen := by
          have := G.bounds; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        refine ⟨by rw [esp₁, esp₂], ?_, by rw [a0₁, a0₂, h₁.1.edi, h₂.1.edi], by rw [a1₁, a1₂],
          by rw [a2₁, a2₂], by rw [a3₁, a3₂], by rw [a4₁, a4₂, h₁.1.edi, h₂.1.edi], by rw [a5₁, a5₂]⟩
        rw [a0₁, a1₁, l1, by₁, a0₂, a1₂, l1, by₂, h₁.2, h₂.2]
      · obtain ⟨⟨s, h, A⟩, _⟩ := h
        exact WP.mono (chkCall_regs G v hp hq h.1 A) fun u ⟨e₁, e₂⟩ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [e₁]; exact pins b t₁ ⟨s, h, A⟩ _ (by simp)
          · rw [e₂]; exact pins b t₁ ⟨s, h, A⟩ _ (by simp)
      · obtain ⟨_, ⟨s, h, A⟩⟩ := h
        exact WP.mono (chkCall_regs G v hp hq h.1 A) fun u ⟨e₁, e₂⟩ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [e₁]; exact pins b t₂ ⟨s, h, A⟩ _ (by simp)
          · rw [e₂]; exact pins b t₂ ⟨s, h, A⟩ _ (by simp)
    · exact (tcheck [.esp, .edi] _ (by decide +kernel)).mono (fun s t h => agree_regs fun r hr =>
        (h.1 r hr).trans (h.2 r hr).symm) fun _ _ h => h
  refine both_ite (fun b => Spec.Dsa.checkParametersBytes g.pLen g.qLen b) (fun b x h => by
      obtain ⟨s, _, M⟩ := h; exact M.zf)
    (stImm_ct (fun b x h => by obtain ⟨⟨s, _, M⟩, _⟩ := h; exact M.base) _ _) (RelCT.block_nil fun _ _ _ => trivial)

end VG.Proof.Dsa.X86.Generation
