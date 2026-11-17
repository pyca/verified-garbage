module

public import VerifiedGarbage.Proof.AesCbc.Arm.Groups
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.AesCbc.Arm.Groups
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# AES's modes on ARMv7, a group of blocks at a time: constant time

Two runs of `wholeG` from states that agree on the public arguments are
related piece by piece (`RelCT`), as those of `whole` are (`CT.lean`): the
taint analysis covers the code of a group before and after its call
(`LevelTaint`), from the registers the invariant pins (`WInv`), and the call
of the block function on the group is constant time by its own proof
(`blk_rel`); the levels' loops run as long in both runs, the number of blocks
being public. The blocks left and the epilogue are `whole`'s (`loop_ct`),
from the entry states with the groups' buffer as the groups left it
(`anch`), which agree on the public arguments as the entry states do.
`wholeG_ct`: `wholeG` is constant time if `body` is (`BodyCt`).
-/

@[expose] public section

namespace VG.Proof.AesCbc.Arm

open VG VG.Arm VG.Impl.AesCbc.Arm
open VG.Impl.CmacAes.Arm (save setup restore)
open VG.Proof.CmacAes.Arm (W R Dp N S argsR)
open VG.Proof.AesOcb.Arm (BlkFn BlkCall BlkPost blkFrame blk_call blk_rel)
open VG.Proof.MdStream.Arm (eval_eq eval_ne)

/-- The taint checks of the groups of `2 ^ lg` blocks: whether one is left,
from the number of blocks left; the code before the call, from the registers
the invariant pins; and the code after it, from `r6`, `r7`, `r8` and `r10`. -/
structure LevelTaint (gm : GMode) (lg : Nat) : Prop where
  head : ∃ h, (taint.check (Taint.ofRegs [.r8]) (.block (groupsLeft lg)) h).isSome = true
  pre : ∃ h, (taint.check (Taint.ofRegs vars)
    (.block (opsCode (gm.pre (2 ^ lg)) ++ gArgs gm.onW (2 ^ lg))) h).isSome = true
  post : ∃ h, (taint.check (Taint.ofRegs postVars)
    (.block (opsCode (gm.post (2 ^ lg)) ++ gAdvance lg)) h).isSome = true

theorem test_taint : ∃ h, (taint.check (Taint.ofRegs [.r8]) (.block [.cmp .r8 (.imm 0)]) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- Two runs of no instructions. -/
theorem relCT_nil {P : State → State → Prop} : RelCT isa P (.block []) P := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
  obtain ⟨rfl, rfl⟩ := e₁
  obtain ⟨rfl, rfl⟩ := e₂
  exact ⟨rfl, hp⟩

section
variable {M : Mode} {s₀ s₀' : State} (hq : (modeArm M).pub s₀ s₀')
include hq

theorem pub_gB (k : Nat) (onW : Bool) : gB s₀ k onW = gB s₀' k onW := by
  unfold gB; rw [pub_S hq, pub_D32 hq]

/-- The registers the invariant pins agree in both runs. -/
theorem WInv.agree {k : Nat} {s₁ s₂ : State} (h₁ : WInv M s₀ k s₁) (h₂ : WInv M s₀' k s₂) :
    ∀ r ∈ vars, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.regs.r4, h₂.regs.r4, pub_W hq]
  · rw [h₁.regs.r5, h₂.regs.r5, pub_r1 hq]
  · rw [h₁.regs.r6, h₂.regs.r6, pub_Iv hq]
  · rw [h₁.regs.r7, h₂.regs.r7, pub_D32 hq]
  · rw [h₁.r8, h₂.r8, pub_N hq]
  · rw [h₁.regs.r10, h₂.regs.r10, pub_S hq]

theorem WInv.agree8 {k : Nat} {s₁ s₂ : State} (h₁ : WInv M s₀ k s₁) (h₂ : WInv M s₀' k s₂) :
    VG.Arm.Taint.Agree (Taint.ofRegs [.r8]) s₁ s₂ :=
  Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; rw [h₁.r8, h₂.r8, pub_N hq]

end

/-! ## One group -/

/-- What is known between the code before the call and the call. -/
structure GMid (s₀ : State) (k : Nat) (onW : Bool) (G : Nat) (s : State) : Prop where
  pre : BlkCall s (W s₀) (gB s₀ k onW) (S s₀) (R s₀) G
  after : After s₀ k s

theorem gpre_mid {M : Mode} {F : BlkFn} {C : Nat → List Byte → Spec.Cbc.Cipher} {gm : GMode} {lg : Nat}
    (hl : LevelOk M F C gm lg) {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k + 2 ^ lg ≤ N s₀) {s : State}
    (h : WInv M s₀ k s) :
    WP isa (.block (opsCode (gm.pre (2 ^ lg)) ++ gArgs gm.onW (2 ^ lg))) s (GMid s₀ k gm.onW (2 ^ lg)) := by
  obtain hG : 0 < 2 ^ lg := Nat.two_pow_pos lg
  obtain lay : GLay (2 ^ lg) (D32 s₀ k) (S s₀) (Iv s₀) s.wr := by rw [h.regs.wr]; exact hp.glay hG hl.g5 hk
  rw [WP.block_append_iff]
  refine WP.mono (opsCode_wp lay h.regs.r7 h.regs.r10 h.regs.r6
    (b := fun x => Spec.Aes.bytesAt s.mem (gaddr (D32 s₀ k) (S s₀) (Iv s₀) x) 16) (fun _ _ => rfl) hl.pre)
    fun s₁ i₁ => ?_
  refine WP.mono (gArgs_wp hp hG hl.g5 hk hl.encG (h.regs.ofOps i₁.regs i₁.sp i₁.rd i₁.wr) gm.onW) fun s₂ a => ?_
  have g : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₂.gpr r = s.gpr r :=
    fun r h0 h1 h2 h3 h12 hlr => by rw [a.keep r h0 h1 h2 h3 h12, i₁.regs r h0 h1 h2 h3 h12 hlr]
  exact ⟨a.pre, ⟨by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.regs.r6],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.regs.r7],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r8],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.regs.r10],
    by rw [a.sp, i₁.sp, h.regs.sp]⟩⟩

theorem gafter {F : BlkFn} {s₀ : State} {k : Nat} {onW : Bool} {G : Nat} {s s' : State} (h : GMid s₀ k onW G s)
    (c : BlkPost F s (W s₀) (gB s₀ k onW) (S s₀) (R s₀) G s') : After s₀ k s' :=
  ⟨by rw [c.saved .r6 (by simp [preserved]) (by decide), h.after.r6],
    by rw [c.saved .r7 (by simp [preserved]) (by decide), h.after.r7],
    by rw [c.saved .r8 (by simp [preserved]) (by decide), h.after.r8],
    by rw [c.saved .r10 (by simp [preserved]) (by decide), h.after.r10], by rw [c.sp, h.after.sp]⟩

/-- The relation before a group of `2 ^ lg` blocks, in two runs. -/
def GRel (M : Mode) (lg : Nat) (s₀ s₀' : State) (k : Nat) (s₁ s₂ : State) : Prop :=
  (k + 2 ^ lg ≤ N s₀ ∧ WInv M s₀ k s₁) ∧ (k + 2 ^ lg ≤ N s₀' ∧ WInv M s₀' k s₂)

section
variable {M : Mode} {F : BlkFn} {C : Nat → List Byte → Spec.Cbc.Cipher} {gm : GMode} {s₀ s₀' : State}

/-- One group is constant time. -/
theorem gBody_ct {lg : Nat} (hl : LevelOk M F C gm lg) (ht : LevelTaint gm lg) (hp : UPre s₀) (hp' : UPre s₀')
    (hq : (modeArm M).pub s₀ s₀') (k : Nat) :
    RelCT isa (GRel M lg s₀ s₀' k) (gBody (blkFrame F) gm lg) fun _ _ => True := by
  obtain ⟨_, hB⟩ := ht.post
  have a := rel_agree (F := fun s => k + 2 ^ lg ≤ N s₀ ∧ WInv M s₀ k s)
    (F' := fun s => k + 2 ^ lg ≤ N s₀' ∧ WInv M s₀' k s)
    (G := GMid s₀ k gm.onW (2 ^ lg)) (G' := GMid s₀' k gm.onW (2 ^ lg)) (Taint.ofRegs vars)
    (fun _ _ h h' => Taint.agree_ofRegs (WInv.agree hq h.2 h'.2)) ht.pre
    (fun _ h => gpre_mid hl hp h.1 h.2) (fun _ h => gpre_mid hl hp' h.1 h.2)
  have c := rel_wp (F := GMid s₀ k gm.onW (2 ^ lg)) (F' := GMid s₀' k gm.onW (2 ^ lg)) (G := After s₀ k)
    (G' := After s₀' k)
    (blk_rel F fun s₁ s₂ h => ⟨W s₀, gB s₀ k gm.onW, S s₀, R s₀, 2 ^ lg, h.1.pre,
      by rw [pub_W hq, pub_gB hq, pub_S hq, pub_R hq]; exact h.2.pre,
      by rw [h.1.after.sp, h.2.after.sp, pub_sp hq]⟩)
    (fun _ h => WP.mono (blk_call F h.pre) fun _ hc => gafter h hc)
    (fun _ h => WP.mono (blk_call F h.pre) fun _ hc => gafter h hc)
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => After s₀ k s₁ ∧ After s₀' k s₂) (Taint.ofRegs postVars)
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [postVars, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.1.r6, h.2.r6, pub_Iv hq]
      · rw [h.1.r7, h.2.r7, pub_D32 hq]
      · rw [h.1.r8, h.2.r8, pub_N hq]
      · rw [h.1.r10, h.2.r10, pub_S hq]) hB
  exact a.seq ((c.mono (fun _ _ h => ⟨h.1, h.2⟩) fun _ _ h => ⟨h.1, h.2⟩).seq
    (b.mono (fun _ _ h => h) fun _ _ h => h))

/-! ## The levels -/

/-- The loop's relation at a level, with the number of blocks left. -/
def GLRel (M : Mode) (lg : Nat) (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ GRel M lg s₀ s₀' k s₁ s₂

/-- The relation between the levels: the invariant after as many blocks in
both runs. -/
def KRel (M : Mode) (s₀ s₀' : State) (s₁ s₂ : State) : Prop :=
  ∃ k, k ≤ N s₀ ∧ WInv M s₀ k s₁ ∧ WInv M s₀' k s₂

theorem gLoop_ct {lg : Nat} (hl : LevelOk M F C gm lg) (ht : LevelTaint gm lg) (hp : UPre s₀) (hp' : UPre s₀')
    (hq : (modeArm M).pub s₀ s₀') (n : Nat) :
    RelCT isa (GLRel M lg s₀ s₀' n) (.loop (gBody (blkFrame F) gm lg) .ne) (KRel M s₀ s₀') := by
  obtain hG : 0 < 2 ^ lg := Nat.two_pow_pos lg
  refine RelCT.loop (M := isa) (GLRel M lg s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : GLRel M lg s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  have ct := (gBody_ct hl ht hp hp' hq k).wp
    (F₁ := fun (s : State) => (WInv M s₀ (k + 2 ^ lg) s ∧
      s.z = decide ((N s₀ - (k + 2 ^ lg)) / 2 ^ lg = 0)) ∧ k + 2 ^ lg ≤ N s₀)
    (F₂ := fun (s : State) => WInv M s₀' (k + 2 ^ lg) s ∧ s.z = decide ((N s₀' - (k + 2 ^ lg)) / 2 ^ lg = 0))
    fun _ _ h => ⟨WP.mono (gBody_ok hl hp h.1.1 h.1.2) fun _ r => ⟨r, h.1.1⟩, gBody_ok hl hp' h.2.1 h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, ⟨⟨l₁, z₁⟩, hk⟩, ⟨l₂, z₂⟩⟩ => ?_
  have e₁ : isa.eval .ne s₁ = some !decide ((N s₀ - (k + 2 ^ lg)) / 2 ^ lg = 0) := by
    show VG.Arm.eval .ne s₁ = _; rw [eval_ne, z₁]
  have e₂ : isa.eval .ne s₂ = some !decide ((N s₀ - (k + 2 ^ lg)) / 2 ^ lg = 0) := by
    show VG.Arm.eval .ne s₂ = _; rw [eval_ne, z₂, ← hN]
  refine ⟨by rw [e₁, e₂], fun _ => ⟨k + 2 ^ lg, hk, l₁, l₂⟩, fun ht => ?_⟩
  rw [e₁] at ht
  have h0 : ¬ (N s₀ - (k + 2 ^ lg)) / 2 ^ lg = 0 := by simpa using ht
  rw [Nat.div_eq_zero_iff_lt hG] at h0
  exact ⟨N s₀ - (k + 2 ^ lg), by omega_using [hk, hG], k + 2 ^ lg, rfl, ⟨by omega_using [h0, hk], l₁⟩,
    ⟨by omega_using [hN, h0, hk], l₂⟩⟩

theorem gLevel_ct {lg : Nat} (hl : LevelOk M F C gm lg) (ht : LevelTaint gm lg) (hp : UPre s₀) (hp' : UPre s₀')
    (hq : (modeArm M).pub s₀ s₀') :
    RelCT isa (KRel M s₀ s₀') (gLevel (blkFrame F) gm lg) (KRel M s₀ s₀') := by
  obtain hG : 0 < 2 ^ lg := Nat.two_pow_pos lg
  have hN := pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : KRel M s₀ s₀' s₁ s₂) => h) fun _ _ h => h
  by_cases hk : k ≤ N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.1
  have head := rel_agree (F := fun s => WInv M s₀ k s) (F' := fun s => WInv M s₀' k s)
    (G := fun s => WInv M s₀ k s ∧ s.z = decide ((N s₀ - k) / 2 ^ lg = 0))
    (G' := fun s => WInv M s₀' k s ∧ s.z = decide ((N s₀' - k) / 2 ^ lg = 0)) (Taint.ofRegs [.r8])
    (fun _ _ h h' => WInv.agree8 hq h h') ht.head (fun _ h => ghead_wp hl.sh h) (fun _ h => ghead_wp hl.sh h)
  have ev {s : State} (h : s.z = decide ((N s₀ - k) / 2 ^ lg = 0)) :
      isa.eval .eq s = some (decide ((N s₀ - k) / 2 ^ lg = 0)) := by
    show VG.Arm.eval .eq s = _; rw [eval_eq, h]
  have ev' {s : State} (h : s.z = decide ((N s₀' - k) / 2 ^ lg = 0)) :
      isa.eval .eq s = some (decide ((N s₀ - k) / 2 ^ lg = 0)) := by
    show VG.Arm.eval .eq s = _; rw [eval_eq, h, hN]
  refine (head.mono (fun _ _ h => ⟨h.2.1, h.2.2⟩) fun _ _ h => h).seq ?_
  refine RelCT.ite (fun a b h => by rw [ev h.1.2, ev' h.2.2]) ?_ ?_
  · exact relCT_nil.mono (fun _ _ h => h) fun _ _ h => ⟨k, hk, h.1.1.1, h.1.2.1⟩
  · by_cases hz : (N s₀ - k) / 2 ^ lg = 0
    · refine RelCT.of_false fun a b h => ?_
      have := h.2; rw [ev h.1.1.2] at this
      simp [hz] at this
    · rw [Nat.div_eq_zero_iff_lt hG] at hz
      exact (gLoop_ct hl ht hp hp' hq (N s₀ - k)).mono
        (fun a b h => ⟨k, rfl, ⟨by omega_using [hz, hk], h.1.1.1⟩, ⟨by omega_using [hN, hz, hk], h.1.2.1⟩⟩)
        fun _ _ h => h

theorem gLevels_ct {lgs : List Nat} (hl : ∀ lg ∈ lgs, LevelOk M F C gm lg) (ht : ∀ lg ∈ lgs, LevelTaint gm lg)
    (hp : UPre s₀) (hp' : UPre s₀') (hq : (modeArm M).pub s₀ s₀') :
    RelCT isa (KRel M s₀ s₀') (gLevels (blkFrame F) gm lgs) (KRel M s₀ s₀') := by
  induction lgs with
  | nil => exact relCT_nil
  | cons lg lgs ih =>
    show RelCT isa _ (.seq (gLevel (blkFrame F) gm lg) (gLevels (blkFrame F) gm lgs)) _
    exact (gLevel_ct (hl lg List.mem_cons_self) (ht lg List.mem_cons_self) hp hp' hq).seq
      (ih (fun lg' h' => hl lg' (List.mem_cons_of_mem _ h')) fun lg' h' => ht lg' (List.mem_cons_of_mem _ h'))

/-! ## The whole function -/

/-- The blocks the groups left and the epilogue, in two runs. -/
theorem gtail_rel {body : Prog isa} (hb : BodyOk M body) (hc : BodyCt M body) (hp : UPre s₀) (hp' : UPre s₀')
    (hq : (modeArm M).pub s₀ s₀') :
    RelCT isa (KRel M s₀ s₀')
      (.seq (.block [.cmp .r8 (.imm 0)]) (.seq (.ite .eq (.block []) (.loop body .ne)) (.block restore)))
      fun _ _ => True := by
  have hN := pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : KRel M s₀ s₀' s₁ s₂) => h) fun _ _ h => h
  by_cases hk : k ≤ N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.1
  have test := rel_agree (F := fun s => WInv M s₀ k s) (F' := fun s => WInv M s₀' k s)
    (G := fun s => WInv M s₀ k s ∧ s.z = decide (N s₀ - k = 0))
    (G' := fun s => WInv M s₀' k s ∧ s.z = decide (N s₀' - k = 0)) (Taint.ofRegs [.r8])
    (fun _ _ h h' => WInv.agree8 hq h h') test_taint (fun _ h => gtest_wp h) (fun _ h => gtest_wp h)
  refine (test.mono (fun _ _ h => ⟨h.2.1, h.2.2⟩) fun _ _ h => h).seq ?_
  -- From here the runs are `whole`'s, from the entry states with the buffer as it is now.
  intro a b t₁ t₂ a' b' ⟨⟨ha, za⟩, ⟨hb', zb⟩⟩ e₁ e₂
  obtain hpa := hp.anch a.mem
  obtain hpb := hp'.anch b.mem
  obtain hLa := ha.toL hp
  obtain hLb := hb'.toL hp'
  have eNa := anch_N hp a.mem
  have eNb := anch_N hp' b.mem
  have hqa : (modeArm M).pub (anch s₀ a.mem) (anch s₀' b.mem) :=
    ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1,
      by rw [anch_arg hp _ (by decide), anch_arg hp' _ (by decide)]; exact hq.2.2.2.2.2.1,
      by rw [anch_arg hp _ (by decide), anch_arg hp' _ (by decide)]; exact hq.2.2.2.2.2.2⟩
  obtain ⟨_, hepi⟩ := epilogue_taint
  have eva : isa.eval .eq a = some (decide (N s₀ - k = 0)) := by
    show VG.Arm.eval .eq a = _; rw [eval_eq, za]
  have evb : isa.eval .eq b = some (decide (N s₀ - k = 0)) := by
    show VG.Arm.eval .eq b = _; rw [eval_eq, zb, hN]
  have mid : RelCT isa (fun x y => x = a ∧ y = b) (.ite .eq (.block []) (.loop body .ne))
      (fun x y => LInv M (anch s₀ a.mem) (N (anch s₀ a.mem)) x ∧
        LInv M (anch s₀' b.mem) (N (anch s₀' b.mem)) y) := by
    refine RelCT.ite (fun x y h => by obtain ⟨rfl, rfl⟩ := h; rw [eva, evb]) ?_ ?_
    · refine relCT_nil.mono (fun _ _ h => h) fun x y h => ?_
      obtain ⟨⟨rfl, rfl⟩, hc⟩ := h
      rw [eva] at hc
      have h0 : N s₀ - k = 0 := by simpa using hc
      obtain hkN : N s₀ = k := by omega_using [h0, hk]
      exact ⟨by rw [eNa, hkN]; exact hLa, by rw [eNb, ← hN, hkN]; exact hLb⟩
    · by_cases hz : N s₀ - k = 0
      · refine RelCT.of_false fun x y h => ?_
        obtain ⟨⟨rfl, rfl⟩, hc⟩ := h
        rw [eva] at hc
        simp [hz] at hc
      · exact (loop_ct hb hc hpa hpb hqa (N (anch s₀ a.mem) - k)).mono
          (fun x y h => by
            obtain ⟨⟨rfl, rfl⟩, _⟩ := h
            exact ⟨k, rfl, ⟨by rw [eNa]; omega_using [hz], hLa⟩, ⟨by rw [eNb]; omega_using [hN, hz], hLb⟩⟩)
          fun _ _ h => h
  have epi := RelCT.taint (A := taint)
    (P := fun x y => LInv M (anch s₀ a.mem) (N (anch s₀ a.mem)) x ∧ LInv M (anch s₀' b.mem) (N (anch s₀' b.mem)) y)
    (Taint.ofRegs [.r10]) (fun x y h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.r10, h.2.r10, anch_S hp, anch_S hp', pub_S hq]) hepi
  exact (mid.seq epi) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

/-- The whole function, in two runs. -/
theorem wholeG_rel {lgs : List Nat} {body : Prog isa} (hl : ∀ lg ∈ lgs, LevelOk M F C gm lg)
    (ht : ∀ lg ∈ lgs, LevelTaint gm lg) (hb : BodyOk M body) (hc : BodyCt M body)
    (h0 : (modeArm M).pre s₀) (h0' : (modeArm M).pre s₀') (hq : (modeArm M).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (wholeG (blkFrame F) gm lgs body) fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  exact ((prologue_rel h0 h0' hq).mono (fun _ _ h => h)
    fun a b h => ⟨0, Nat.zero_le _, h.1.1.toW, h.2.1.toW⟩).seq
      ((gLevels_ct hl ht hp hp' hq).seq (gtail_rel hb hc hp hp' hq))

/-- The whole function, in groups, is constant time. -/
theorem wholeG_ct {lgs : List Nat} {body : Prog isa} (hl : ∀ lg ∈ lgs, LevelOk M F C gm lg)
    (ht : ∀ lg ∈ lgs, LevelTaint gm lg) (hb : BodyOk M body) (hc : BodyCt M body) :
    ConstantTime isa (modeArm M).pre (modeArm M).pub (wholeG (blkFrame F) gm lgs body) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (wholeG_rel hl ht hb hc h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end

end VG.Proof.AesCbc.Arm
