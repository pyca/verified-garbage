module

public import VerifiedGarbage.Impl.Sm4.Arm.SerialCfb
public import VerifiedGarbage.Impl.Sm4.Arm.Prepared
import VerifiedGarbage.Proof.Sm4.Arm.CfbFill
public import VerifiedGarbage.Proof.Sm4.Arm.SerialCfbLoop
import VerifiedGarbage.Proof.Sm4.Arm.BatchPrologue
import VerifiedGarbage.Proof.Sm4.Arm.BatchCalls
import VerifiedGarbage.Proof.Sm4.Arm.BatchEntry
public import VerifiedGarbage.Proof.Sm4.Arm.PreparedBody
import VerifiedGarbage.Proof.Sm4.Arm.Keys
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Sm4.Prepared

/-! # Public registers across SM4-CFB encryption's helper calls -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.SerialCfbHead

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchGroup
open VG.Proof.Sm4.Arm.BatchPrologue VG.Proof.Sm4.Arm.BatchEntry
open VG.Proof.Sm4.Prepared (Holds)

def groupHead : Prog isa := .seq SerialCfb.count (.seq BatchCfb.fill BatchCtr.crypt)
def groupTail : Prog isa := .seq BatchCtr.xorGroup
  (.seq (.block SerialCfb.saveCipher) (.block [.subs .r7 .r7 (.reg .r11)]))
def proHead : Prog isa := .seq (.block BatchCtr.entry) BatchCtr.prepare

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
  group : s'.gpr .r11 = BitVec.ofNat 32 (1)

theorem count_wp (s : State) : WP isa SerialCfb.count s fun s' =>
    s'.gpr .r11 = (1 : BitVec 32) ∧
      (∀ r, r ≠ .r11 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s', e, g, o, m, rd, wr, sp⟩ := movImm_ok s .r11 1 (by decide)
  exact WP.seq (WP.of_runBlock ⟨s', e, WP.of_runBlock
    ⟨s', CfbFill.pad_run s', g, fun r hr _ => o r hr, m, rd, wr, sp⟩⟩)

theorem head_wp {s : State} {B D : BitVec 32} {n : Nat} (hn : 1 ≤ n) (_hn32 : n < 2 ^ 32)
    (h : HeadPre B D n s) : WP isa groupHead s (HeadPost s n) := by
  have hg : 1 ≤ 1 := by omega
  have hg8 : 1 ≤ 8 := by decide
  obtain ⟨K, hH⟩ := h.table
  refine WP.seq (WP.mono (count_wp s) fun s₁ ⟨g₁, o₁, m₁, _, wr₁, _⟩ => ?_)
  have b₁ : s₁.gpr sb = B := (o₁ _ (by decide) (by decide)).trans h.base
  have table₁ : Holds layout s₁.mem (State.addr B) K .encrypt := by
    rw [m₁]; exact hH
  have d₁ : s₁.gpr .r6 = D := (o₁ _ (by decide) (by decide)).trans h.data
  have wd₁ : Covers [⟨State.addr D, 16 * 1⟩] s₁.wr := by
    rw [wr₁]
    apply Covers.trans (rs' := [⟨State.addr D, 16 * n⟩]) _ h.wdata
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 0, by rw [BitVec.add_zero],
      by change 0 + 16 * 1 ≤ 16 * n; omega⟩
  have fp : CfbFill.Pre B D (1) s₁ := ⟨b₁, d₁, g₁, h.fit, by have := h.fitD; omega,
    by rw [wr₁]; exact h.writable, wd₁, h.sep.sub_left (Region.sub_prefix (by omega))⟩
  refine WP.seq (WP.mono (CfbFill.fill_wp fp hg hg8) fun s₂ f => ?_)
  have b₂ : s₂.gpr sb = B := (f.regs _ (by decide) (by decide)).trans b₁
  have table₂ : Holds layout s₂.mem (State.addr B) K .encrypt := table_frame table₁ f.frame fun r hr => by
    simp only [CfbFill.regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · apply Offset.disjoint (State.addr B)
      · right; change 4 * tailSlot + 16 * 0 + 128 ≤ 384; decide
      · decide
      · change 4 * tailSlot + 16 * 0 + 128 ≤ 2 ^ 64; rw [tailSlot]; omega
    · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  have wc : Covers [⟨State.addr B, 4 * slots⟩] s₂.wr := by
    rw [f.wr, wr₁]
    simpa only [BitVec.add_zero] using workspace_part h.writable 0 (4 * slots)
      (by change 4 * slots ≤ 4 * BatchCtr.totalSlots; decide)
  refine WP.mono (BatchCalls.crypt_wp b₂ (by have := h.fit; change B.toNat + 1456 ≤ 2 ^ 32; change B.toNat + 1512 ≤ 2 ^ 32 at this; omega) wc table₂)
    fun s₃ ⟨c, _, _⟩ => ?_
  refine ⟨fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [c.regs _ (by decide) (by decide), f.regs _ (by decide) (by decide), o₁ _ (by decide) (by decide)]
  · rw [c.regs _ (by decide) (by decide), f.regs _ (by decide) (by decide), g₁]; rfl


theorem loop_pre {s₀ s : State} {B D : BitVec 32} {K : Spec.Sm4.Schedule} {t : List Byte} {n i : Nat}
    (_hn32 : n < 2 ^ 32) (hi : i < n) (hB : s₀.gpr sb = B)
    (fitB : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32) (fitD : D.toNat + 16 * n ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s₀.wr)
    (wd : Covers [⟨State.addr D, 16 * n⟩] s₀.wr)
    (sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr B, 4 * BatchCtr.totalSlots⟩)
    (h : SerialCfbLoop.LoopInv s₀ B D K t n i s) : HeadPre B (D + BitVec.ofNat 32 (16 * i)) (n - i) s := by
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
    exact ⟨⟨State.addr D, 16 * n⟩, List.mem_singleton_self _, 16 * i, diAddr, by change 16 * i + 16 * (n - i) ≤ 16 * n; omega⟩
  exact ⟨(h.regs _ (by simp [sb])).trans hB, h.left, fitB, by rw [h.wr]; exact hw,
    ⟨K, h.table⟩, h.data, by change Di.toNat + 16 * (n - i) ≤ 2 ^ 32; rw [diNat]; omega, wdi, sep.sub_left subD⟩

end VG.Proof.Sm4.Arm.SerialCfbHead
