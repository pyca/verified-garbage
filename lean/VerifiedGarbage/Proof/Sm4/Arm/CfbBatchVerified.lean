module

public import VerifiedGarbage.Proof.Sm4.Arm.BatchPrologue
public import VerifiedGarbage.Proof.Sm4.Arm.CfbLoop
import VerifiedGarbage.Proof.Sm4.Arm.Prologue
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Sm4.Arm.BatchCfb
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Sm4.Arm.BatchChain
public import VerifiedGarbage.Spec.Cfb
public import VerifiedGarbage.Spec.Sm4.Ctr
import VerifiedGarbage.Proof.Sm4.Arm.CfbGroup
public import VerifiedGarbage.Impl.Sm4.Arm.Prepared
import VerifiedGarbage.Proof.Sm4.Arm.CfbFill
import VerifiedGarbage.Proof.Sm4.Arm.BatchGroup
public import VerifiedGarbage.Proof.Sm4.Arm.PreparedBody
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Sm4.Prepared
import VerifiedGarbage.Proof.Sm4.Arm.BatchTaint
import VerifiedGarbage.Proof.Sm4.Arm.CfbTaint
import VerifiedGarbage.Proof.Sm4.Arm.BatchHead
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Sm4.FbScratch
public import VerifiedGarbage.Spec.Sm4.Cfb
meta import VerifiedGarbage.Spec.Sm4.Cfb
public import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sm4.FbScratch
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Sm4.Arm.CfbBody`, which only this module used -/

section

/-! # Functional composition of the prepared, eight-block SM4-CFB decryption implementation -/

@[expose] public section

namespace VG.Proof.Sm4.Arm.CfbBody

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb movR)
open VG.Proof.Sm4.Arm.BatchXor
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchEntry VG.Proof.Sm4.Arm.BatchChain
open VG.Proof.Sm4.Arm.BatchPrologue VG.Proof.Sm4.Arm.CfbLoop VG.Proof.Sm4.Arm.BatchGroup
open VG.Spec.Aes (bytesAt)

structure Post (s₀ s : State) : Prop where
  regs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  data : Spec.Cbc.blocksAt s.mem (State.addr (Dp s₀)) (N s₀) =
    Spec.Cfb.decrypt (Spec.Sm4.cipher (Spec.Sm4.scheduleAt s₀.mem (State.addr (Kp s₀))))
      (bytesAt s₀.mem (State.addr (Iv s₀)) 16) (Spec.Cbc.blocksAt s₀.mem (State.addr (Dp s₀)) (N s₀))
  iv : bytesAt s.mem (State.addr (Iv s₀)) 16 =
    Spec.Cbc.next (bytesAt s₀.mem (State.addr (Iv s₀)) 16)
      (Spec.Cbc.blocksAt s₀.mem (State.addr (Dp s₀)) (N s₀))
  sp : s.sp = s₀.sp

theorem body_wp {s₀ : State} (hp : Pre s₀) : WP isa BatchCfb.decrypt s₀ (Post s₀) := by
  have hw := hp.writable (r := wsR s₀) (by simp)
  have hd := hp.writable (r := dataR s₀) (by simp)
  have hi := hp.writable (r := ivR s₀) (by simp)
  refine WP.seq (WP.mono (prologue_wp hp) fun s₁ p => ?_)
  have blocks₁ : Spec.Cbc.blocksAt s₁.mem (State.addr (Dp s₀)) (N s₀) =
      Spec.Cbc.blocksAt s₀.mem (State.addr (Dp s₀)) (N s₀) := by
    unfold Spec.Cbc.blocksAt
    apply List.map_congr_left
    intro j hj
    apply bytes_frame (P := dataAddr (Dp s₀) j) p.frame
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.ds.sub_left (Offset.sub_base _ (by have := List.mem_range.mp hj; change 16 * j + 16 ≤ 16 * N s₀; omega_using [this]))
  refine WP.seq (WP.mono (loopOrEmpty_wp (s₀.gpr .r3).isLt p.base p.data p.left p.z hp.fitB hp.fitD
    (by rw [p.wr]; exact hw) (by rw [p.wr]; exact hd) hp.ds p.table p.counter) fun s₂ l => ?_)
  have base₂ : s₂.gpr sb = Sc s₀ := (l.regs _ (by simp [sb])).trans p.base
  have iv₂ : s₂.gpr .r5 = Iv s₀ := (l.regs _ (by simp)).trans p.iv
  have saved₂ := p.saved.frame mode_slots l.frame (fun r hr => by
    simp only [batchRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint_base _ (d := 1456) (n := 36) (k := 4 * slots) (by decide) (by decide)
    · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
    · exact hp.ds.symm.sub_left (Offset.sub_base _ (by decide)))
  have cp : ChainPre s₂ (Sc s₀) (Iv s₀) :=
    ⟨base₂, iv₂, hp.fitB, hp.fitI, by rw [l.wr, p.wr]; exact hw,
      by rw [l.wr, p.wr]; exact hi, hp.ivs⟩
  have output := loop_output l
  rw [blocks₁] at output
  apply (WP.block_append_iff (M := isa) (l₁ := BatchCtr.copyCounterOut)
    (l₂ := ([movR .r12 sb] : List Instr) ++ BatchCtr.restore)).mpr
  refine WP.mono (counterOut_wp cp) fun s₃ c => ?_
  have saved₃ := saved₂.frame mode_slots c.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.ivs.symm.sub_left (Offset.sub_base _ (by decide)))
  have blocks₃ : Spec.Cbc.blocksAt s₃.mem (State.addr (Dp s₀)) (N s₀) =
      Spec.Cbc.blocksAt s₂.mem (State.addr (Dp s₀)) (N s₀) := by
    unfold Spec.Cbc.blocksAt
    apply List.map_congr_left
    intro j hj
    apply bytes_frame (P := dataAddr (Dp s₀) j) c.frame
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.id.symm.sub_left (Offset.sub_base _ (by have := List.mem_range.mp hj; change 16 * j + 16 ≤ 16 * N s₀; omega_using [this]))
  refine WP.mono (restore_wp ((c.regs _ (by decide) (by decide)).trans base₂) hp.fitB
    (by rw [c.wr, l.wr, p.wr]; exact hw) saved₃) fun s₄ ⟨regs, mem, _, _, sp⟩ => ?_
  refine ⟨regs, ?_, ?_, sp.trans (c.sp.trans (l.sp.trans p.sp))⟩
  · rw [mem, blocks₃]; exact output
  · rw [mem, c.block, l.counter, chain_next, blocks₁]

end VG.Proof.Sm4.Arm.CfbBody

end

end

/-! ### `Sm4.Arm.CfbCT`, which only this module used -/

section

/-! ### `Sm4.Arm.CfbHead`, which only this module used -/

section

/-! # Public registers across SM4-CFB decryption's helper calls -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.CfbHead

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchGroup
open VG.Proof.Sm4.Arm.BatchPrologue VG.Proof.Sm4.Arm.BatchEntry
open VG.Proof.Sm4.Prepared (Holds)

def groupHead : Prog isa := .seq BatchCtr.count (.seq BatchCfb.fill BatchCtr.crypt)
def groupTail : Prog isa := .seq BatchCtr.xorGroup (.block [.subs .r7 .r7 (.reg .r11)])
structure HeadPre (B D : BitVec 32) (n : Nat) (s : State) : Prop where
  base : s.gpr sb = B
  left : s.gpr .r7 = BitVec.ofNat 32 n
  fit : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32
  writable : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr
  table : ∃ K, Holds layout s.mem (State.addr B) K .encrypt
  data : s.gpr .r6 = D
  fitD : D.toNat + 16 * n ≤ 2 ^ 32
  wdata : Covers [⟨State.addr D, 16 * n⟩] s.wr
  sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩

structure HeadPost (s : State) (n : Nat) (s' : State) : Prop where
  regs : ∀ r ∈ [.r6, .r7, .r8], s'.gpr r = s.gpr r
  group : s'.gpr .r11 = BitVec.ofNat 32 (min n 8)

theorem head_wp {s : State} {B D : BitVec 32} {n : Nat} (hn : 1 ≤ n) (hn32 : n < 2 ^ 32)
    (h : HeadPre B D n s) : WP isa groupHead s (HeadPost s n) := by
  have hg : 1 ≤ min n 8 := by omega_using [hn]
  have hg8 : min n 8 ≤ 8 := Nat.min_le_right _ _
  obtain ⟨K, hH⟩ := h.table
  refine WP.seq (WP.mono (count_wp h.left hn32) fun s₁ ⟨g₁, o₁, m₁, _, wr₁, _⟩ => ?_)
  have b₁ : s₁.gpr sb = B := (o₁ _ (by decide) (by decide)).trans h.base
  have table₁ : Holds layout s₁.mem (State.addr B) K .encrypt := by
    rw [m₁]; exact hH
  have d₁ : s₁.gpr .r6 = D := (o₁ _ (by decide) (by decide)).trans h.data
  have wd₁ : Covers [⟨State.addr D, 16 * min n 8⟩] s₁.wr := by
    rw [wr₁]
    apply Covers.trans (rs' := [⟨State.addr D, 16 * n⟩]) _ h.wdata
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 0, by rw [BitVec.add_zero],
      by change 0 + 16 * min n 8 ≤ 16 * n; have := Nat.min_le_left n 8; omega_using []⟩
  have fp : CfbFill.Pre B D (min n 8) s₁ := ⟨b₁, d₁, g₁, h.fit, by have := h.fitD; have := Nat.min_le_left n 8; omega_arith,
    by rw [wr₁]; exact h.writable, wd₁, h.sep.sub_left (Region.sub_prefix (by have := Nat.min_le_left n 8; omega_using []))⟩
  refine WP.seq (WP.mono (CfbFill.fill_wp fp hg hg8) fun s₂ f => ?_)
  have b₂ : s₂.gpr sb = B := (f.regs _ (by decide) (by decide)).trans b₁
  have table₂ : Holds layout s₂.mem (State.addr B) K .encrypt := table_frame table₁ f.frame fun r hr => by
    simp only [CfbFill.regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · apply Offset.disjoint (State.addr B)
      · right; change 4 * tailSlot + 16 * 0 + 128 ≤ 384; decide
      · decide
      · change 4 * tailSlot + 16 * 0 + 128 ≤ 2 ^ 64; rw [tailSlot]; omega_using []
    · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  have wc : Covers [⟨State.addr B, 4 * slots⟩] s₂.wr := by
    rw [f.wr, wr₁]
    simpa only [BitVec.add_zero] using workspace_part h.writable 0 (4 * slots)
      (by change 4 * slots ≤ 4 * BatchCtr.totalSlots; decide)
  refine WP.mono (BatchCalls.crypt_wp b₂ (by have := h.fit; change B.toNat + 1456 ≤ 2 ^ 32; change B.toNat + 1512 ≤ 2 ^ 32 at this; omega_using [this]) wc table₂)
    fun s₃ ⟨c, _, _⟩ => ?_
  refine ⟨fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [c.regs _ (by decide) (by decide), f.regs _ (by decide) (by decide), o₁ _ (by decide) (by decide)]
  · rw [c.regs _ (by decide) (by decide), f.regs _ (by decide) (by decide), g₁]


theorem loop_pre {s₀ s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n i : Nat}
    (_hn32 : n < 2 ^ 32) (hi : i < n) (hB : s₀.gpr sb = B)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (h : CfbLoop.LoopInv s₀ B D K t n i s) : HeadPre B (D + BitVec.ofNat 32 (16 * i)) (n - i) s := by
  let Di := D + BitVec.ofNat 32 (16 * i)
  have diNat : Di.toNat = D.toNat + 16 * i := offset_nat _ _ (by omega_using [hi, fitD])
  have diAddr : State.addr Di = State.addr D + BitVec.ofNat 64 (16 * i) := addr_add (by omega_using [hi, fitD])
  have subD : Region.Sub ⟨State.addr Di, 16 * (n - i)⟩ ⟨State.addr D, 16 * n⟩ := by
    rw [diAddr]; exact Offset.sub_base _ (by omega_using [hi])
  have wdi : Covers [⟨State.addr Di, 16 * (n - i)⟩] s.wr := by
    rw [h.wr]
    apply Covers.trans (rs' := [⟨State.addr D, 16 * n⟩]) _ wd
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 16 * i, diAddr, by change 16 * i + 16 * (n - i) ≤ 16 * n; omega_using [hi]⟩
  exact ⟨(h.regs _ (by simp [sb])).trans hB, h.left, fitB, by rw [h.wr]; exact hw,
    ⟨K, h.table⟩, h.data, by change Di.toNat + 16 * (n - i) ≤ 2 ^ 32; rw [diNat]; omega_using [hi, fitD], wdi, sep.sub_left subD⟩

end VG.Proof.Sm4.Arm.CfbHead

end

end


/-! # Constant-time composition for batched SM4-CFB decryption -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.CfbCT

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.CfbHead VG.Proof.Sm4.Arm.CfbLoop
open VG.Proof.Sm4.Arm.BatchPrologue VG.Proof.Sm4.Arm.BatchFill
open VG.Proof.Sm4.Arm.BatchHead (proHead_wp)
open VG.Proof.Sm4.Arm.CfbGroup

theorem append_eq {a b c d : List Leak} (h : a = b) (h' : c = d) : a ++ c = b ++ d := by rw [h, h']

/-- Functional postconditions hold of any execution, by determinism. -/
theorem result {c : Prog isa} {s s' : State} {t : List Leak} {Q : State → Prop}
    (h : WP isa c s Q) (e : Exec isa c s t s') : Q s' := by
  obtain ⟨_, _, e', h'⟩ := h
  obtain ⟨_, rfl⟩ := Exec.det e e'
  exact h'

theorem checked {rs : List Reg} {c : Prog isa}
    (hc : ∃ h, (taint.check (Taint.ofRegs rs) c h).isSome = true)
    {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}
    (hag : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (e₁ : Exec isa c s₁ t₁ s₁') (e₂ : Exec isa c s₂ t₂ s₂') : t₁ = t₂ := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taint (A := taint) (P := fun a b => ∀ r ∈ rs, a.gpr r = b.gpr r)
    (Taint.ofRegs rs) (fun _ _ h => Taint.agree_ofRegs h) hc) _ _ _ _ _ _ hag e₁ e₂).1

/-- Reassociate the existing group at the point where the helper returns. -/
theorem group_split {s s' : State} {t : List Leak} (e : Exec isa BatchCfb.group s t s') :
    ∃ m th tt, Exec isa groupHead s th m ∧ Exec isa groupTail m tt s' ∧ t = th ++ tt := by
  cases e with | seq a b =>
    cases b with | seq c d =>
      cases c with | seq f g =>
        cases g with | seq k x =>
          exact ⟨_, _, _, .seq a (.seq f k), .seq x d, by simp only [List.append_assoc]⟩

theorem group_ct {B D : BitVec 32} {n : Nat} (hn : 1 ≤ n) (hn32 : n < 2 ^ 32)
    {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}
    (h₁ : HeadPre B D n s₁) (h₂ : HeadPre B D n s₂) (hd : s₁.gpr .r6 = s₂.gpr .r6)
    (e₁ : Exec isa BatchCfb.group s₁ t₁ s₁') (e₂ : Exec isa BatchCfb.group s₂ t₂ s₂') : t₁ = t₂ := by
  obtain ⟨m₁, th₁, tt₁, eh₁, et₁, tr₁⟩ := group_split e₁
  obtain ⟨m₂, th₂, tt₂, eh₂, et₂, tr₂⟩ := group_split e₂
  have ht : th₁ = th₂ := checked CfbTaint.groupHead_check (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hd
    · rw [h₁.left, h₂.left]
    · exact h₁.base.trans h₂.base.symm) eh₁ eh₂
  have p₁ := result (head_wp hn hn32 h₁) eh₁
  have p₂ := result (head_wp hn hn32 h₂) eh₂
  have tt : tt₁ = tt₂ := checked BatchTaint.groupTail_check (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [p₁.regs _ (by simp), p₂.regs _ (by simp), hd]
    · rw [p₁.regs _ (by simp), p₂.regs _ (by simp), h₁.left, h₂.left]
    · rw [p₁.regs _ (by simp), p₂.regs _ (by simp)]; exact h₁.base.trans h₂.base.symm
    · rw [p₁.group, p₂.group]) et₁ et₂
  rw [tr₁, tr₂, ht, tt]

section
variable {s₀ s₀' : State} {B D : BitVec 32} {K K' : Spec.Sm4.Schedule} {t t' : List Byte} {n : Nat}
    (hn32 : n < 2 ^ 32) (hB : s₀.gpr sb = B) (hB' : s₀'.gpr sb = B)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (hw' : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀'.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (wd' : Covers [⟨State.addr D, 16 * n⟩] s₀'.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)

def LoopRel (s₀ s₀' : State) (B D : BitVec 32) (K K' : Spec.Sm4.Schedule) (t t' : List Byte)
    (n m : Nat) (a b : State) : Prop :=
  ∃ i, m = n - i ∧ i < n ∧ LoopInv s₀ B D K t n i a ∧ LoopInv s₀' B D K' t' n i b

include hn32 hB hB' fitB fitD hw hw' wd wd' sep in
 theorem loop_ct (m : Nat) :
    RelCT isa (LoopRel s₀ s₀' B D K K' t t' n m) (.loop BatchCfb.group .ne)
      (fun a b => LoopInv s₀ B D K t n n a ∧ LoopInv s₀' B D K' t' n n b) := by
  refine RelCT.loop (M := isa) (LoopRel s₀ s₀' B D K K' t t' n) (fun m => ?_) m
  intro a b ta tb a' b' ⟨i, hm, hi, l, l'⟩ ea eb
  have p := loop_pre hn32 hi hB fitB fitD hw wd sep l
  have p' := loop_pre hn32 hi hB' fitB fitD hw' wd' sep l'
  have eqtr := group_ct (by omega_arith) (by omega_arith) p p' (by rw [l.data, l'.data]) ea eb
  obtain ⟨la, za⟩ := result (loopInv_step hn32 hi hB fitB fitD hw wd sep l) ea
  obtain ⟨lb, zb⟩ := result (loopInv_step hn32 hi hB' fitB fitD hw' wd' sep l') eb
  have evA : isa.eval .ne a' = some !decide (i + min (n - i) 8 = n) := by
    change some (!a'.z) = _; rw [za]
  have evB : isa.eval .ne b' = some !decide (i + min (n - i) 8 = n) := by
    change some (!b'.z) = _; rw [zb]
  refine ⟨eqtr, by rw [evA, evB], ?_, ?_⟩
  · intro h
    rw [evA] at h
    have he : i + min (n - i) 8 = n := by simpa using h
    rw [he] at la lb
    exact ⟨la, lb⟩
  · intro h
    rw [evA] at h
    have he : i + min (n - i) 8 ≠ n := by simpa using h
    refine ⟨n - (i + min (n - i) 8), by omega_arith, i + min (n - i) 8, rfl, ?_, la, lb⟩
    have := la.bound
    omega_arith

include hn32 hB hB' fitB fitD hw hw' wd wd' sep in
 theorem dataLoop_ct :
    RelCT isa (fun a b => LoopInv s₀ B D K t n 0 a ∧ LoopInv s₀' B D K' t' n 0 b ∧
      a.z = decide (n = 0) ∧ b.z = decide (n = 0)) BatchCfb.dataLoop (fun _ _ => True) := by
  have ev {a : State} (h : a.z = decide (n = 0)) : isa.eval .eq a = some (decide (n = 0)) := by
    change some a.z = _; rw [h]
  refine RelCT.ite (fun a b h => by rw [ev h.2.2.1, ev h.2.2.2]) ?_ ?_
  · obtain ⟨_, hc⟩ := BatchTaint.nil_check
    exact RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (fun r hr => by simp at hr)) hc
  · refine (loop_ct (K := K) (K' := K') (t := t) (t' := t') hn32 hB hB' fitB fitD hw hw' wd wd' sep n).mono (fun a b h => ?_) (fun _ _ _ => trivial)
    have he := h.2
    rw [ev h.1.2.2.1] at he
    have hn : 0 < n := by
      have : n ≠ 0 := by simpa using he
      omega_arith
    exact ⟨0, by omega_arith, hn, h.1.1, h.1.2.1⟩

end

def Pub (s s' : State) : Prop :=
  s.sp = s'.sp ∧ s.gpr .r0 = s'.gpr .r0 ∧ s.gpr .r1 = s'.gpr .r1 ∧
  s.gpr .r2 = s'.gpr .r2 ∧ s.gpr .r3 = s'.gpr .r3 ∧ Sc s = Sc s'

theorem arg_wf {s : State} (h : Pre s) :
    s.sp.toNat + 4 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 4⟩ r := by
  refine ⟨h.spFit, ?_⟩
  intro r hr
  have he : (⟨State.addr s.sp, 4⟩ : Region) = argR s := by simp [argR, stackArgAddr]
  rw [he, h.wr] at *
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [h.ia.symm, h.da.symm, h.sa.symm]

theorem prologue_ct {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak}
    (h₁ : Pre s₁) (h₂ : Pre s₂) (hq : Pub s₁ s₂)
    (e₁ : Exec isa BatchCtr.prologue s₁ t₁ s₁') (e₂ : Exec isa BatchCtr.prologue s₂ t₂ s₂') : t₁ = t₂ := by
  cases e₁ with | seq a b =>
    cases b with | seq p u =>
      cases e₂ with | seq a' b' =>
        cases b' with | seq p' u' =>
          have eh := Exec.seq a p
          have eh' := Exec.seq a' p'
          have hag : VG.Arm.Taint.Agree (argTaint [.r0, .r1, .r2, .r3] 4) s₁ s₂ :=
            agree_argTaint (fun r hr => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl | rfl | rfl
              exacts [hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1]) hq.1 (arg_wf h₁) (arg_wf h₂)
              (argMem_of (j := 1) hq.1 h₁.spFit (fun i hi => by
                have he : i = 0 := by omega_arith
                subst i
                exact hq.2.2.2.2.2))
          obtain ⟨_, hc⟩ := BatchTaint.proHead_check
          have heq := ((RelCT.taint (A := taint) (P := fun a b => VG.Arm.Taint.Agree (argTaint [.r0, .r1, .r2, .r3] 4) a b)
            (argTaint [.r0, .r1, .r2, .r3] 4) (fun _ _ h => h) hc) _ _ _ _ _ _ hag eh eh').1
          obtain ⟨i, n, b⟩ := result (proHead_wp h₁) eh
          obtain ⟨i', n', b'⟩ := result (proHead_wp h₂) eh'
          have heq' := checked BatchTaint.setup_check (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl
            · rw [i, i']; exact hq.2.2.1
            · rw [n, n']; unfold N; rw [hq.2.2.2.2.1]
            · exact b.trans (hq.2.2.2.2.2.trans b'.symm)) u u'
          simpa only [List.append_assoc] using append_eq heq heq'

theorem initial {s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n : Nat}
    (hD : s.gpr .r6 = D) (hN : s.gpr .r7 = BitVec.ofNat 32 n)
    (hH : Proof.Sm4.Prepared.Holds layout s.mem (State.addr B) K .encrypt)
    (hC : Spec.Aes.bytesAt s.mem (counterAddr B) 16 = t) : LoopInv s B D K t n 0 s :=
  ⟨fun _ _ => rfl, by simpa only [Nat.mul_zero, BitVec.add_zero] using hD,
    by simpa only [Nat.sub_zero] using hN, by omega_arith, rfl, rfl, rfl, Frame.refl _ _, hH,
    by change Spec.Aes.bytesAt s.mem (counterAddr B) 16 = t; exact hC, fun _ h => by omega_arith⟩

theorem cfb_ct : ConstantTime isa Pre Pub BatchCfb.decrypt := by
  intro s₁ s₂ tr₁ tr₂ s₁' s₂' hp₁ hp₂ hq e₁ e₂
  have eB : Sc s₂ = Sc s₁ := hq.2.2.2.2.2.symm
  have eD : Dp s₂ = Dp s₁ := hq.2.2.2.1.symm
  have eN : N s₂ = N s₁ := by unfold N; rw [hq.2.2.2.2.1]
  have hw₁ := hp₁.writable (r := wsR s₁) (by simp)
  have hw₂ := hp₂.writable (r := wsR s₂) (by simp)
  have wd₁ := hp₁.writable (r := dataR s₁) (by simp)
  have wd₂ := hp₂.writable (r := dataR s₂) (by simp)
  cases e₁ with | seq pro rest =>
    cases rest with | seq dl fin =>
      cases e₂ with | seq pro' rest' =>
        cases rest' with | seq dl' fin' =>
          have eqP := prologue_ct hp₁ hp₂ hq pro pro'
          have p := result (prologue_wp hp₁) pro
          have p' := result (prologue_wp hp₂) pro'
          have pb' := p'.base
          have pd' := p'.data
          have pn' := p'.left
          have pt' := p'.table
          have pc' := p'.counter
          have pz' := p'.z
          rw [eB] at pb' pt' pc'
          rw [eD] at pd'
          rw [eN] at pn' pz'
          have ib := initial p.data p.left p.table p.counter
          have ib' := initial pd' pn' pt' pc'
          have w₁ := hw₁
          have w₂ := hw₂
          have d₁ := wd₁
          have d₂ := wd₂
          rw [← p.wr] at w₁ d₁
          rw [← p'.wr] at w₂ d₂
          change Covers [⟨State.addr (Sc s₂), 4 * BatchCtr.totalSlots⟩] _ at w₂
          change Covers [⟨State.addr (Dp s₂), 16 * N s₂⟩] _ at d₂
          rw [eB] at w₂
          rw [eD, eN] at d₂
          have rel := dataLoop_ct (K := Spec.Sm4.scheduleAt s₁.mem (State.addr (Kp s₁)))
            (K' := Spec.Sm4.scheduleAt s₂.mem (State.addr (Kp s₂)))
            (t := Spec.Aes.bytesAt s₁.mem (State.addr (Iv s₁)) 16)
            (t' := Spec.Aes.bytesAt s₂.mem (State.addr (Iv s₂)) 16)
            (s₁.gpr .r3).isLt p.base pb' hp₁.fitB hp₁.fitD w₁ w₂ d₁ d₂ hp₁.ds
          have eqL := (rel _ _ _ _ _ _ ⟨ib, ib', p.z, pz'⟩ dl dl').1
          have l := result (loopOrEmpty_wp (s₁.gpr .r3).isLt p.base p.data p.left p.z hp₁.fitB hp₁.fitD w₁ d₁ hp₁.ds p.table p.counter) dl
          have l' := result (loopOrEmpty_wp (s₁.gpr .r3).isLt pb' pd' pn' pz' hp₁.fitB hp₁.fitD w₂ d₂ hp₁.ds pt' pc') dl'
          have eqF := checked BatchTaint.finish_check (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · rw [l.regs _ (by simp), l'.regs _ (by simp), p.iv, p'.iv]; exact hq.2.2.1
            · rw [l.regs _ (by simp), l'.regs _ (by simp)]
              exact p.base.trans pb'.symm) fin fin'
          exact append_eq eqP (append_eq eqL eqF)

end VG.Proof.Sm4.Arm.CfbCT

end

end


/-! # Batched ARMv7 SM4-CFB decryption meets the public, wiped-stack contract -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.CfbBatchVerified

open VG VG.Arm VG.Impl.Sm4.Arm
open VG.Proof.Sm4.Arm.BatchPrologue VG.Proof.Sm4.Arm.CfbBody VG.Proof.Sm4.Arm.CfbCT

def cfbArm : Contract isa where
  pre := Pre
  post := Post
  pub := Pub

theorem correct (s : State) (h : cfbArm.pre s) :
    ∃ t s', Exec isa BatchCfb.decrypt s t s' ∧ abiPreserved s s' ∧ cfbArm.post s s' := by
  obtain ⟨t, s', e, p⟩ := body_wp h
  exact ⟨t, s', e, ⟨p.regs, p.sp⟩, p⟩

def satState : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 128⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0, 1512⟩]

theorem implies : cfbArm.Implies (Proof.Sm4.fbScratchContract Arm.abi 189 Proof.Sm4.cfbDecPost 0) where
  pre s h := by
    sig_pre [Proof.Sm4.fbScratchContract, Proof.Sm4.fbScratchSig, Spec.Sm4.ofbSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    rcases h with ⟨sp, rd, wr, ki, kd, ks, id, ivs, ia, ds, da, sa, fk, fi, fd, fb⟩
    rw [Nat.mul_comm] at wr kd id ds da fd
    exact ⟨sp, rd, wr, ki, kd, ks, id, ivs, ds, ia, da, sa, fk, fi, fd, fb⟩
  post s s' _ h := by
    sig_post [Proof.Sm4.fbScratchContract, Proof.Sm4.fbScratchSig, Proof.Sm4.cfbDecPost, Spec.Sm4.ofbSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact ⟨h.data, h.iv⟩
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Sm4.fbScratchContract, Proof.Sm4.fbScratchSig, Spec.Sm4.ofbSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h
  sat := by
    sig_implies_sat [Proof.Sm4.fbScratchContract, Proof.Sm4.fbScratchSig, Spec.Sm4.ofbSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr]
      [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

theorem verified : Verified Arm.target BatchCfb.decrypt (Proof.Sm4.fbScratchContract Arm.abi 189 Proof.Sm4.cfbDecPost 0) :=
  Verified.of_correct correct cfb_ct implies

def frameState : State := { satState with rd := [⟨0x1000, 128⟩], wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩] }

theorem frameSat : ∃ s, (Spec.Sm4.cfbDecryptContract Arm.abi 1520).pre s := by
  implies_sat [Spec.Sm4.cfbDecryptContract, Spec.Sm4.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, State.addr] [frameState, satState] using frameState

theorem framed : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratchWiped 1520 0 378 BatchCfb.decrypt)
    (Spec.Sm4.cfbDecryptContract Arm.abi 1520) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Sm4.cfbSig) (nm := "scratch") (e := .u64) (n := 189)
    (post := Proof.Sm4.cfbDecPost Arm.abi.ptrBits) (wa := true) (stack := 0) (m := 0) (bytes := 1520)
    verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm4.cfbDecPost_local _)
    (Proof.Sm4.cfbDecPostOut_local _) frameSat

end VG.Proof.Sm4.Arm.CfbBatchVerified
