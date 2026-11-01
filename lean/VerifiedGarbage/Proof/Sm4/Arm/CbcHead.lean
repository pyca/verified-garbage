module

public import VerifiedGarbage.Impl.Sm4.Arm.BatchCbc
public import VerifiedGarbage.Proof.Sm4.Arm.BatchPrologue
import VerifiedGarbage.Proof.Sm4.Arm.CbcPrepare
public import VerifiedGarbage.Proof.Sm4.Arm.CbcGroup
public import VerifiedGarbage.Proof.Sm4.Arm.CbcLoop
import VerifiedGarbage.Proof.Sm4.Arm.BatchGroup
import VerifiedGarbage.Proof.Sm4.Arm.BatchEntry
public import VerifiedGarbage.Proof.Sm4.Arm.PreparedBody
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Sm4.Prepared

/-! # Public registers across the CBC decryption cipher phase -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.CbcHead
open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchEntry VG.Proof.Sm4.Arm.BatchChain
open VG.Proof.Sm4.Arm.BatchGroup (count_wp table_frame)
open VG.Proof.Sm4.Arm.BatchPrologue
open VG.Proof.Sm4.Prepared (Holds)

def groupHead : Prog isa := .seq BatchCtr.count (.seq BatchCbc.fill BatchCtr.crypt)
def groupTail : Prog isa := .seq (BatchCbc.chooseXor 0 8)
  (.seq (.block BatchCtr.copyCounterIn) (.block BatchCbc.advance))
def proHead : Prog isa := .seq (.block BatchCtr.entry) BatchCbc.prepare

structure HeadPre (B I D : BitVec 32) (n : Nat) (s : State) : Prop extends CbcGroup.Pre B I D n s where
  table : ∃ K, Holds layout s.mem (State.addr B) K .decrypt

structure HeadPost (s : State) (n : Nat) (s' : State) : Prop where
  regs : ∀ r ∈ [.r5, .r6, .r7, .r8], s'.gpr r = s.gpr r
  group : s'.gpr .r11 = BitVec.ofNat 32 (min n 8)

theorem head_wp {s : State} {B I D : BitVec 32} {n : Nat} (hn : 1 ≤ n) (hn32 : n < 2 ^ 32)
    (h : HeadPre B I D n s) : WP isa groupHead s (HeadPost s n) := by
  have hgN : min n 8 ≤ n := Nat.min_le_left _ _
  have hg8 : min n 8 ≤ 8 := Nat.min_le_right _ _
  have hg : 1 ≤ min n 8 := by omega
  obtain ⟨K, hH⟩ := h.table
  refine WP.seq (WP.mono (count_wp h.left hn32) fun s₁ ⟨g₁, o₁, m₁, _, wr₁, _⟩ => ?_)
  have wd₁ : Covers [⟨State.addr D, 16 * min n 8⟩] s₁.wr := by
    rw [wr₁]
    apply Covers.trans (rs' := [⟨State.addr D, 16 * n⟩]) _ h.wd
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 0, by rw [BitVec.add_zero], by change 0 + 16 * min n 8 ≤ 16 * n; omega⟩
  have fp : CbcFill.Pre B I D (min n 8) s₁ := ⟨⟨(o₁ _ (by decide) (by decide)).trans h.base,
    (o₁ _ (by decide) (by decide)).trans h.data, g₁, h.fitB, by have := h.fitD; omega,
    by rw [wr₁]; exact h.hw, wd₁, h.db.sub_left (Region.sub_prefix (by omega))⟩,
    (o₁ _ (by decide) (by decide)).trans h.iv, h.fitI, by rw [wr₁]; exact h.hi,
    h.id.sub_right (Region.sub_prefix (by omega)), h.ib⟩
  have table₁ : Holds layout s₁.mem (State.addr B) K .decrypt := by rw [m₁]; exact hH
  refine WP.seq (WP.mono (CbcFill.fill_wp fp hg hg8) fun s₂ f => ?_)
  have b₂ : s₂.gpr sb = B := (f.kept.regs _ (by decide) (by decide)).trans fp.core.base
  have table₂ : Holds layout s₂.mem (State.addr B) K .decrypt := table_frame table₁ f.kept.frame fun r hr => by
    simp only [CbcFill.regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
    · exact h.ib.symm.sub_left (Offset.sub_base _ (by decide))
  have wc : Covers [⟨State.addr B, 4 * slots⟩] s₂.wr := by
    rw [f.kept.wr, wr₁]
    simpa only [BitVec.add_zero] using workspace_part h.hw 0 (4 * slots) (by decide)
  refine WP.mono (BatchCalls.crypt_wp b₂
    (by have := h.fitB; change B.toNat + 1456 ≤ 2 ^ 32; change B.toNat + 1512 ≤ 2 ^ 32 at this; omega)
    wc table₂) fun s₃ ⟨c, _, _⟩ => ?_
  refine ⟨fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [c.regs _ (by decide) (by decide), f.kept.regs _ (by decide) (by decide), o₁ _ (by decide) (by decide)]
  · rw [c.regs _ (by decide) (by decide), f.kept.regs _ (by decide) (by decide), g₁]

theorem proHead_wp {s : State} (hp : BatchPrologue.Pre s) : WP isa proHead s fun s' =>
    s'.gpr .r5 = Iv s ∧ s'.gpr .r7 = BitVec.ofNat 32 (N s) ∧ s'.gpr sb = Sc s := by
  have hw := hp.writable (r := wsR s) (by simp)
  have ha : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 4 :=
    ⟨argR s, List.mem_append_left _ (by rw [hp.rd]; simp), Region.contains_self _ _⟩
  refine WP.seq (WP.mono (entry_wp rfl ha rfl hp.fitB hw) fun s₁ e => ?_)
  have wc : Covers [⟨State.addr (Sc s), 4 * slots⟩] s₁.wr := by
    rw [e.wr]
    simpa only [BitVec.add_zero] using workspace_part hw 0 (4 * slots) (by decide)
  refine WP.mono (CbcPrepare.prepare_wp e.key e.base hp.fitK
    (by have := hp.fitB; change (Sc s).toNat + 1456 ≤ 2 ^ 32; change (Sc s).toNat + 1512 ≤ 2 ^ 32 at this; omega)
    (hp.ks.sub_right (Region.sub_prefix (by decide)))
    (by rw [e.rd, e.wr]; exact hp.key) wc) fun s₂ ⟨p, _⟩ => ?_
  refine ⟨(p.regs _ (by decide) (by decide)).trans e.iv, ?_, (p.regs _ (by decide) (by decide)).trans e.base⟩
  rw [p.regs _ (by decide) (by decide), e.left]
  exact (BitVec.ofNat_toNat 32 (s.gpr .r3)).symm

theorem loop_pre {s₀ s : State} {B I D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n i : Nat}
    (_hn32 : n < 2 ^ 32) (hi : i < n) (hB : s₀.gpr sb = B)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hI : s₀.gpr .r5 = I) (fitI : I.toNat + 16 ≤ 2 ^ 32)
    (hiv : Covers [⟨State.addr I, 16⟩] s₀.wr)
    (id : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr D, 16 * n⟩)
    (ib : Region.Disjoint ⟨State.addr I, 16⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (h : CbcLoop.LoopInv s₀ B I D K t n i s) : HeadPre B I (D + BitVec.ofNat 32 (16 * i)) (n - i) s := by
  let Di := D + BitVec.ofNat 32 (16 * i)
  have diNat : Di.toNat = D.toNat + 16 * i := offset_nat _ _ (by omega)
  have diAddr : State.addr Di = State.addr D + BitVec.ofNat 64 (16 * i) := addr_add (by omega)
  have subD : Region.Sub ⟨State.addr Di, 16 * (n - i)⟩ ⟨State.addr D, 16 * n⟩ := by
    rw [diAddr]; exact Offset.sub_base _ (by omega)
  have wdi : Covers [⟨State.addr Di, 16 * (n - i)⟩] s.wr := by
    rw [h.wr]
    apply Covers.trans (rs' := [⟨State.addr D, 16 * n⟩]) _ wd
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 16 * i, diAddr,
      by change 16 * i + 16 * (n - i) ≤ 16 * n; omega⟩
  exact ⟨⟨(h.regs _ (by simp [sb])).trans hB, (h.regs _ (by simp)).trans hI, h.data, h.left,
    fitB, fitI, by change Di.toNat + 16 * (n - i) ≤ 2 ^ 32; rw [diNat]; omega,
    by rw [h.wr]; exact hw, by rw [h.wr]; exact hiv, wdi,
    id.sub_right subD, ib, sep.sub_left subD⟩, ⟨K, h.table⟩⟩

end VG.Proof.Sm4.Arm.CbcHead
