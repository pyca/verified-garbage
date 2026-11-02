module

public import VerifiedGarbage.Proof.Ed448.RISCV64.VMain
public import VerifiedGarbage.Proof.Ed448.RISCV64.VCT
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelBlock
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Proof.Ed448.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Ed448.RISCV64.VerifyEquation
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# `vg_ed448_verify_equation` on RISC-V, verified

The function meets `verifyRISCV64` (`VTiming.lean`), with no stack: the code
calls no function and writes only caller-saved registers (`WP.keep`), so the
ABI's obligations hold of every execution (`verifyEquation_ok`), and it is
constant time from its pointers and inputs (`verifyEquation_ct`).

Two runs from states with the same pointers and the same inputs leak the same
trace (`verifyEquation_rel`). Everything before the joint loop, its start,
`[4](R + (-R'))` and the end are constant time from the pointers
(`VCT.lean`). In the loop, both runs hold the same digits of the same `S`
and `k` (`pre_ok`, from the same inputs), so at each position both take the
same branches, and each branch is constant time from its digit
(`base_rel`, `key_rel`, `step_rel`, `loop_rel`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 (Rest)
open VG.Proof.Ed448.RISCV64.Comb (ptOf DQ)
open VG.Impl.Ed448.WnafWide (digitAt residual)
open VG.Impl.X448.RISCV64 (ACC)
open VG.Proof.Ed25519.RISCV64 (base)

/-! ## Relating two runs -/

/-- Two runs from `σ₁` and `σ₂`. -/
abbrev Eq2 (σ₁ σ₂ : State) (a b : State) : Prop := a = σ₁ ∧ b = σ₂

/-- Nothing is required of the final states. -/
abbrev TT (_ _ : State) : Prop := True

/-- Then: the next piece, from the states the correctness proofs describe. -/
theorem rel_seq {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- A branch both runs take the same way. -/
theorem rel_ite {c : Cond} {t e : Prog isa} {σ₁ σ₂ : State} {b : Bool} (e₁ : isa.eval c σ₁ = some b)
    (e₂ : isa.eval c σ₂ = some b) (ht : b = true → RelCT isa (Eq2 σ₁ σ₂) t TT)
    (hf : b = false → RelCT isa (Eq2 σ₁ σ₂) e TT) : RelCT isa (Eq2 σ₁ σ₂) (.ite c t e) TT := by
  refine RelCT.ite (fun a b' hab => by obtain ⟨rfl, rfl⟩ := hab; rw [e₁, e₂]) ?_ ?_
  · cases b
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h
    · exact (ht rfl).mono (fun _ _ h => h.1) fun _ _ h => h
  · cases b
    · exact (hf rfl).mono (fun _ _ h => h.1) fun _ _ h => h
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h

/-- Registers and stack pointers equal in two given states. -/
theorem eq2_regs {σ₁ σ₂ : State} {rs : List Reg} (hsp : σ₁.sp = σ₂.sp) (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r) :
    ∀ a b, Eq2 σ₁ σ₂ a b → a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r := fun a b ⟨ha, hb⟩ => by
  subst ha hb; exact ⟨hsp, hr⟩

section
variable {b : Addr}

/-! ## The digits' branches -/

theorem a5_digit {S K : Nat} {w z l : State} {t2v : BitVec 64} {m : Nat} (hm : m < 464)
    (hc : R64.Cur b w t2v (BitVec.ofNat 64 m) DQ (FS z.mem b) z) (hfx : JFix b S K w.mem) {e : Nat}
    (he : e = 2 ∨ e = 3)
    (h5 : l.gpr .a5 = BitVec.ofNat 64 (z.mem (b + BitVec.ofNat 64 (TB + (4 * m + e)))).toNat) :
    l.gpr .a5 = dByte (digitAt false (if e = 2 then S else K) m) := by
  have hA : ACC = 952 := rfl
  have hT : TB = 2104 := rfl
  rw [h5, byte_hi hc.stp.frame (by omega) (by omega), dig_byte hfx.1 (by omega) he]

theorem base_rel {S K : Nat} {w₁ w₂ z₁ z₂ : State} (hv₁ : VCtx b w₁) (hv₂ : VCtx b w₂)
    (hf₁ : JFix b S K w₁.mem) (hf₂ : JFix b S K w₂.mem) (hw : w₁.sp = w₂.sp) {m : Nat} (hm : m < 464)
    {a₁ a₂ : BitVec 64} (c₁ : R64.Cur b w₁ a₁ (BitVec.ofNat 64 m) DQ (FS z₁.mem b) z₁)
    (c₂ : R64.Cur b w₂ a₂ (BitVec.ofNat 64 m) DQ (FS z₂.mem b) z₂) :
    RelCT isa (Eq2 z₁ z₂) addBase TT := by
  have y₁ := vctx_cur hv₁ c₁
  have y₂ := vctx_cur hv₂ c₂
  unfold addBase
  refine rel_seq (load2_ct (eq2_regs (by rw [c₁.stp.rest.sp, c₂.stp.rest.sp, hw]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [y₁.a0, y₂.a0]
      · rw [c₁.t1, c₂.t1]))
    (loadDigit_ok y₁ (n := m) (e := 2) (by omega) (by decide) c₁.t1)
    (loadDigit_ok y₂ (n := m) (e := 2) (by omega) (by decide) c₂.t1) fun l₁ l₂ ⟨r₁, _, e₁⟩ ⟨r₂, _, e₂⟩ => ?_
  have d₁ := a5_digit hm c₁ hf₁ (.inl rfl) e₁
  have d₂ := a5_digit hm c₂ hf₂ (.inl rfl) e₂
  refine rel_ite (by rw [eval_nonzero, d₁]) (by rw [eval_nonzero, d₂]) (fun _ => baseBody_ct (eq2_regs
    (by rw [r₁.sp, r₂.sp, c₁.stp.rest.sp, c₂.stp.rest.sp, hw]) fun r hr => ?_))
    (fun _ => (relct_nil (P := Eq2 l₁ l₂)).mono (fun _ _ h => h) fun _ _ _ => trivial)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [r₁.gpr _ (by decide), r₂.gpr _ (by decide), y₁.a0, y₂.a0]
  · rw [r₁.gpr _ (by decide), r₂.gpr _ (by decide), y₁.ctx.a3, y₂.ctx.a3]
  · rw [d₁, d₂]

theorem key_rel {S K : Nat} {w₁ w₂ z₁ z₂ : State} (hv₁ : VCtx b w₁) (hv₂ : VCtx b w₂)
    (hf₁ : JFix b S K w₁.mem) (hf₂ : JFix b S K w₂.mem) (hw : w₁.sp = w₂.sp) {m : Nat} (hm : m < 464)
    {a₁ a₂ : BitVec 64} (c₁ : R64.Cur b w₁ a₁ (BitVec.ofNat 64 m) DQ (FS z₁.mem b) z₁)
    (c₂ : R64.Cur b w₂ a₂ (BitVec.ofNat 64 m) DQ (FS z₂.mem b) z₂) :
    RelCT isa (Eq2 z₁ z₂) addKey TT := by
  have y₁ := vctx_cur hv₁ c₁
  have y₂ := vctx_cur hv₂ c₂
  unfold addKey
  refine rel_seq (load3_ct (eq2_regs (by rw [c₁.stp.rest.sp, c₂.stp.rest.sp, hw]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [y₁.a0, y₂.a0]
      · rw [c₁.t1, c₂.t1]))
    (loadDigit_ok y₁ (n := m) (e := 3) (by omega) (by decide) c₁.t1)
    (loadDigit_ok y₂ (n := m) (e := 3) (by omega) (by decide) c₂.t1) fun l₁ l₂ ⟨r₁, _, e₁⟩ ⟨r₂, _, e₂⟩ => ?_
  have d₁ := a5_digit hm c₁ hf₁ (.inr rfl) e₁
  have d₂ := a5_digit hm c₂ hf₂ (.inr rfl) e₂
  refine rel_ite (by rw [eval_nonzero, d₁]) (by rw [eval_nonzero, d₂]) (fun _ => keyBody_ct (eq2_regs
    (by rw [r₁.sp, r₂.sp, c₁.stp.rest.sp, c₂.stp.rest.sp, hw]) fun r hr => ?_))
    (fun _ => (relct_nil (P := Eq2 l₁ l₂)).mono (fun _ _ h => h) fun _ _ _ => trivial)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [r₁.gpr _ (by decide), r₂.gpr _ (by decide), y₁.a0, y₂.a0]
  · rw [r₁.gpr _ (by decide), r₂.gpr _ (by decide), y₁.ctx.a3, y₂.ctx.a3]
  · rw [d₁, d₂]

/-! ## The loop -/

theorem step_rel {S K : Nat} {w₁ w₂ : State} (hv₁ : VCtx b w₁) (hv₂ : VCtx b w₂)
    (hf₁ : JFix b S K w₁.mem) (hf₂ : JFix b S K w₂.mem) (hw : w₁.sp = w₂.sp) {m : Nat} (hm : m < 464)
    {x₁ x₂ : State} (hx₁ : WInv b S K w₁ (m + 1) x₁) (hx₂ : WInv b S K w₂ (m + 1) x₂) :
    RelCT isa (Eq2 x₁ x₂) jointStep TT := by
  have hx₁' := hx₁
  have hx₂' := hx₂
  obtain ⟨⟨_, cx₁⟩, -, -⟩ := hx₁'
  obtain ⟨⟨_, cx₂⟩, -, -⟩ := hx₂'
  unfold jointStep
  refine rel_seq (dec_ct (eq2_regs (by rw [cx₁.stp.rest.sp, cx₂.stp.rest.sp, hw]) fun r hr => by
      rw [List.mem_singleton.mp hr, cx₁.t1, cx₂.t1]))
    (decStep_ok hm hx₁) (decStep_ok hm hx₂) fun y₁ y₂ ⟨⟨_, cy₁⟩, dy₁, ry₁⟩ ⟨⟨_, cy₂⟩, dy₂, ry₂⟩ => ?_
  refine rel_seq (dbl_ct (eq2_regs (by rw [cy₁.stp.rest.sp, cy₂.stp.rest.sp, hw]) fun r hr => by
      rw [List.mem_singleton.mp hr, cy₁.ctx.a3, cy₂.ctx.a3]))
    (dblStep_ok cy₁ dy₁ ry₁) (dblStep_ok cy₂ dy₂ ry₂) fun z₁ z₂ ⟨⟨_, cz₁⟩, dz₁, rz₁⟩ ⟨⟨_, cz₂⟩, dz₂, rz₂⟩ => ?_
  refine rel_seq (base_rel hv₁ hv₂ hf₁ hf₂ hw hm cz₁ cz₂) (addBase_ok hv₁ hf₁ hm cz₁ dz₁ rz₁)
    (addBase_ok hv₂ hf₂ hm cz₂ dz₂ rz₂) fun q₁ q₂ ⟨⟨_, cq₁⟩, _, _⟩ ⟨⟨_, cq₂⟩, _, _⟩ => ?_
  exact key_rel hv₁ hv₂ hf₁ hf₂ hw hm cq₁ cq₂

theorem loop_rel {S K : Nat} {w₁ w₂ : State} (hv₁ : VCtx b w₁) (hv₂ : VCtx b w₂)
    (hf₁ : JFix b S K w₁.mem) (hf₂ : JFix b S K w₂.mem) (hw : w₁.sp = w₂.sp)
    (h₁ : WInv b S K w₁ 464 w₁) (h₂ : WInv b S K w₂ 464 w₂) :
    RelCT isa (Eq2 w₁ w₂) (.loop jointStep (.nonzero .t1)) TT := by
  refine (RelCT.loop (Q := TT) (fun n a b' => 1 ≤ n ∧ n ≤ 464 ∧ WInv b S K w₁ n a ∧ WInv b S K w₂ n b') ?_
    464).mono (fun a b' ⟨ha, hb⟩ => by subst ha hb; exact ⟨by decide, le_refl _, h₁, h₂⟩) fun _ _ h => h
  intro n
  rcases n with _ | m
  · exact RelCT.of_false fun a b' h => absurd h.1 (by decide)
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hn1, hn2, hs₁, hs₂⟩ e₁ e₂
    have hm : m < 464 := by omega
    have r := ((step_rel hv₁ hv₂ hf₁ hf₂ hw hm hs₁ hs₂).wp
      (F₁ := fun (t : State) => WInv b S K w₁ m t ∧ (t.gpr .t1 != 0) = decide (m ≠ 0))
      (F₂ := fun (t : State) => WInv b S K w₂ m t ∧ (t.gpr .t1 != 0) = decide (m ≠ 0)) fun a b' ⟨ha, hb⟩ => by
        subst ha hb; exact ⟨jointStep_ok hv₁ hf₁ hm hs₁, jointStep_ok hv₂ hf₂ hm hs₂⟩)
      s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂
    obtain ⟨ht, -, ⟨g₁, z₁⟩, ⟨g₂, z₂⟩⟩ := r
    refine ⟨ht, ⟨by rw [eval_nonzero, eval_nonzero, z₁, z₂], fun _ => trivial, fun hc => ⟨m, by omega, ?_⟩⟩⟩
    rw [eval_nonzero, z₁] at hc
    have : m ≠ 0 := by simpa using hc
    exact ⟨by omega, by omega, g₁, g₂⟩

theorem jointLoop_rel {S K : Nat} (hS : S < Impl.Ed448.WnafWide.scalarLimit)
    (hK : K < Impl.Ed448.WnafWide.scalarLimit) {u₁ u₂ : State} (hv₁ : VCtx b u₁) (hv₂ : VCtx b u₂)
    (hf₁ : JFix b S K u₁.mem) (hf₂ : JFix b S K u₂.mem) (hd₁ : FS u₁.mem b DK = Spec.Ed448.d)
    (hd₂ : FS u₂.mem b DK = Spec.Ed448.d) (hu : u₁.sp = u₂.sp) :
    RelCT isa (Eq2 u₁ u₂) jointLoop TT := by
  have hRX : RX = 56 := rfl
  have hRY : RY = 0 := rfl
  have hRZ : RZ = 112 := rfl
  have hDK : DK = 336 := rfl
  unfold jointLoop
  refine rel_seq (init_ct (eq2_regs hu fun r hr => by rw [List.mem_singleton.mp hr, hv₁.ctx.a3, hv₂.ctx.a3]))
    (jointInit_ok hv₁) (jointInit_ok hv₂) fun w₁ w₂ ⟨vw₁, rw₁, fw₁, pw₁, tw₁⟩ ⟨vw₂, rw₂, fw₂, pw₂, tw₂⟩ => ?_
  have fa : ∀ {u w : State}, Frame (R3 b RX RY RZ) u.mem w.mem → Frame [FA b] u.mem w.mem := fun hf =>
    hf.sub fun r hr => ⟨FA b, by simp, by
      have hA : ACC = 952 := rfl
      simp only [R3, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Offset.sub_base _ (by omega)⟩
  have dk : ∀ {u w : State}, Frame (R3 b RX RY RZ) u.mem w.mem → FS w.mem b DK = FS u.mem b DK := fun hf =>
    fsD hf fun r hr => by
      simp only [R3, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by omega)
  have start : ∀ {w : State}, VCtx b w → ptOf (FS w.mem b) = Spec.Ed448.identity →
      w.gpr .t1 = BitVec.ofNat 64 464 → FS w.mem b DK = Spec.Ed448.d → WInv b S K w 464 w :=
    fun hv hp ht hd => ⟨⟨_, ⟨hv.ctx, R64.Stp.refl _ _, rfl, ht, fun _ _ => rfl⟩⟩, hd, fun a _ => by
      beta_reduce
      rw [hp, residual_464 hS, residual_464 hK]
      simpa only [Nat.cast_zero, zero_smul, add_zero] using Proof.Ed448.identity_rep⟩
  exact loop_rel vw₁ vw₂ (jfix_FA (fa fw₁) hf₁) (jfix_FA (fa fw₂) hf₂) (by rw [rw₁.sp, rw₂.sp, hu])
    (start vw₁ pw₁ tw₁ (by rw [dk fw₁, hd₁])) (start vw₂ pw₂ tw₂ (by rw [dk fw₂, hd₂]))

end

/-! ## The whole function -/

/-- `verifyEquationContract` by register. -/
def verifyRISCV64 : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .a0, 57⟩
    let sig : Region := ⟨s.gpr .a1, 114⟩
    let ch : Region := ⟨s.gpr .a2, 57⟩
    let ws : Region := ⟨s.gpr .a3, 8192⟩
    s.rd = [pk, sig, ch] ∧ s.wr = [ws] ∧ pk.Disjoint ws ∧ sig.Disjoint ws ∧ ch.Disjoint ws
  post s s' := (s'.gpr .a0).setWidth 32 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt s.mem (s.gpr .a0) 57)
    (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114) (Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57) then 1 else 0
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp ∧
    (Spec.Ed448.bytesAt s₁.mem (s₁.gpr .a0) 57 ++ Spec.Ed448.bytesAt s₁.mem (s₁.gpr .a1) 114 ++
      Spec.Ed448.bytesAt s₁.mem (s₁.gpr .a2) 57).map (·.toNat) =
    (Spec.Ed448.bytesAt s₂.mem (s₂.gpr .a0) 57 ++ Spec.Ed448.bytesAt s₂.mem (s₂.gpr .a1) 114 ++
      Spec.Ed448.bytesAt s₂.mem (s₂.gpr .a2) 57).map (·.toNat)


theorem bytes_parts {a₁ b₁ c₁ a₂ b₂ c₂ : List Byte} (ha : a₁.length = a₂.length) (hb : b₁.length = b₂.length)
    (h : (a₁ ++ b₁ ++ c₁).map (·.toNat) = (a₂ ++ b₂ ++ c₂).map (·.toNat)) : a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ := by
  have hi : Function.Injective (fun x : Byte => x.toNat) := fun x y hxy => BitVec.eq_of_toNat_eq hxy
  have e := List.map_injective_iff.mpr hi h
  obtain ⟨e1, e2⟩ := List.append_inj e (by simp [ha, hb])
  obtain ⟨e3, e4⟩ := List.append_inj e1 ha
  exact ⟨e3, e4, e2⟩

theorem verifyEquation_rel (hR : Proof.Ed448.RecoverOk) {σ₁ σ₂ : State} (h₁ : VPre σ₁) (h₂ : VPre σ₂)
    (hpub : verifyRISCV64.pub σ₁ σ₂) : RelCT isa (Eq2 σ₁ σ₂) verifyEquation TT := by
  obtain ⟨p0, p1, p2, p3, psp, pb⟩ := hpub
  obtain ⟨-, eS, eK⟩ := bytes_parts (by simp [Spec.Ed448.bytesAt]) (by simp [Spec.Ed448.bytesAt]) pb
  unfold verifyEquation
  refine rel_seq (prefix_ct (eq2_regs psp fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption))
    (pre_ok hR h₁) (pre_ok hR h₂) fun u₁ u₂ ⟨c₁, sp₁, f₁, d₁, _⟩ ⟨c₂, sp₂, f₂, d₂, _⟩ => ?_
  rw [← p3] at c₂ f₂ d₂
  rw [← eS, ← eK] at f₂
  have hl4 : (Spec.Ed448.bytesAt σ₁.mem (σ₁.gpr .a1) 114).length = 114 := by simp [Spec.Ed448.bytesAt]
  have hSl := limit_of (bs := (Spec.Ed448.bytesAt σ₁.mem (σ₁.gpr .a1) 114).drop 57) (by rw [List.length_drop, hl4])
  have hKl := limit_of (bs := Spec.Ed448.bytesAt σ₁.mem (σ₁.gpr .a2) 57) (by simp [Spec.Ed448.bytesAt])
  generalize base (σ₁.gpr .a3) = b at c₁ c₂ f₁ f₂ d₁ d₂
  have hu : u₁.sp = u₂.sp := by rw [sp₁, sp₂, psp]
  refine rel_seq (jointLoop_rel hSl hKl c₁ c₂ f₁ f₂ d₁ d₂ hu) (joint_ok hSl hKl c₁ f₁ d₁) (joint_ok hSl hKl c₂ f₂ d₂)
    fun v₁ v₂ ⟨L₁, vL₁, _, rL₁, ⟨⟨_, cv₁⟩, dv₁, _⟩⟩ ⟨L₂, vL₂, _, rL₂, ⟨⟨_, cv₂⟩, dv₂, _⟩⟩ => ?_
  have hv : v₁.sp = v₂.sp := by rw [cv₁.stp.rest.sp, cv₂.stp.rest.sp, rL₁.sp, rL₂.sp, hu]
  refine rel_seq (addNegR_ct (eq2_regs hv fun r hr => by
      rw [List.mem_singleton.mp hr, cv₁.ctx.a3, cv₂.ctx.a3]))
    (addNegR_ok vL₁ cv₁ dv₁) (addNegR_ok vL₂ cv₂ dv₂) fun t₁ t₂ ⟨ct₁, st₁, _⟩ ⟨ct₂, st₂, _⟩ => ?_
  refine vFinish_ct (eq2_regs (by rw [st₁.rest.sp, st₂.rest.sp, rL₁.sp, rL₂.sp, hu]) fun r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [ct₁.a0, ct₂.a0]
  · rw [ct₁.ctx.a3, ct₂.ctx.a3]

theorem verifyEquation_ct (hR : Proof.Ed448.RecoverOk) :
    ConstantTime isa verifyRISCV64.pre verifyRISCV64.pub verifyEquation :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hp e₁ e₂ =>
    (verifyEquation_rel hR (σ₁ := s₁) (σ₂ := s₂) ⟨h₁.1, h₁.2.1, h₁.2.2.1, h₁.2.2.2.1, h₁.2.2.2.2⟩
      ⟨h₂.1, h₂.2.1, h₂.2.2.1, h₂.2.2.2.1, h₂.2.2.2.2⟩ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1


/-! ## Correctness with the ABI -/

open VG VG.RISCV64


open VG VG.RISCV64

theorem verifyEquation_ok (hR : Proof.Ed448.RecoverOk) (s : State)
    (hs : verifyRISCV64.pre s) :
    ∃ t s', Exec isa Impl.Ed448.RISCV64.verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyRISCV64.post s s' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  obtain ⟨t, s', he, h, hk⟩ := WP.keep [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6]
    (verifyEquation_correct hR ⟨h1, h2, h3, h4, h5⟩) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), h⟩

end VG.Proof.Ed448.RISCV64
