module

import VerifiedGarbage.Proof.Sm4.Arm.BatchGroup
public import VerifiedGarbage.Proof.Sm4.Arm.BatchPrologue
import VerifiedGarbage.Proof.Sm4.Arm.BatchCalls
import VerifiedGarbage.Proof.Sm4.Arm.BatchEntry
public import VerifiedGarbage.Proof.Sm4.Arm.PreparedBody
import VerifiedGarbage.Proof.Sm4.Arm.Core
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Sm4.Prepared

/-! # Public registers across SM4-CTR's helper calls -/

@[expose] public section
namespace VG.Proof.Sm4.Arm.BatchHead

open VG VG.Arm VG.Impl.Sm4.Arm VG.Proof.Sm4.Arm
open VG.Impl.Aes.Arm (sb)
open VG.Proof.Sm4.Arm.BatchFill VG.Proof.Sm4.Arm.BatchGroup
open VG.Proof.Sm4.Arm.BatchPrologue VG.Proof.Sm4.Arm.BatchEntry
open VG.Proof.Sm4.Prepared (Holds)

def groupHead : Prog isa := .seq BatchCtr.count (.seq BatchCtr.fill BatchCtr.crypt)
def groupTail : Prog isa := .seq BatchCtr.xorGroup (.block [.subs .r7 .r7 (.reg .r11)])
def proHead : Prog isa := .seq (.block BatchCtr.entry) BatchCtr.prepare

structure HeadPre (B : BitVec 32) (n : Nat) (s : State) : Prop where
  base : s.gpr sb = B
  left : s.gpr .r7 = BitVec.ofNat 32 n
  fit : B.toNat + 4 * BatchCtr.totalSlots ≤ 2 ^ 32
  writable : Covers [⟨State.addr B, 4 * BatchCtr.totalSlots⟩] s.wr
  table : ∃ K, Holds layout s.mem (State.addr B) K .encrypt

structure HeadPost (s : State) (n : Nat) (s' : State) : Prop where
  regs : ∀ r ∈ [.r6, .r7, .r8], s'.gpr r = s.gpr r
  group : s'.gpr .r11 = BitVec.ofNat 32 (min n 8)

theorem head_wp {s : State} {B : BitVec 32} {n : Nat} (hn : 1 ≤ n) (hn32 : n < 2 ^ 32)
    (h : HeadPre B n s) : WP isa groupHead s (HeadPost s n) := by
  have hg : 1 ≤ min n 8 := by omega
  have hg8 : min n 8 ≤ 8 := Nat.min_le_right _ _
  obtain ⟨K, hH⟩ := h.table
  refine WP.seq (WP.mono (count_wp h.left hn32) fun s₁ ⟨g₁, o₁, m₁, _, wr₁, _⟩ => ?_)
  have b₁ : s₁.gpr sb = B := (o₁ _ (by decide) (by decide)).trans h.base
  have table₁ : Holds layout s₁.mem (State.addr B) K .encrypt := by
    rw [m₁]; exact hH
  refine WP.seq (WP.mono (fill_wp hg hg8 b₁ g₁ h.fit (by rw [wr₁]; exact h.writable)) fun s₂ f => ?_)
  have b₂ : s₂.gpr sb = B := (f.regs _ (by decide) (by decide) (by decide) (by decide)).trans b₁
  have table₂ : Holds layout s₂.mem (State.addr B) K .encrypt := table_frame table₁ f.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · apply Offset.disjoint (State.addr B)
      · right; change 4 * tailSlot + 16 * 0 + 16 * min n 8 ≤ 384; rw [tailSlot]; omega
      · decide
      · change 4 * tailSlot + 16 * 0 + 16 * min n 8 ≤ 2 ^ 64; rw [tailSlot]; omega
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
      rw [c.regs _ (by decide) (by decide), f.regs _ (by decide) (by decide) (by decide) (by decide), o₁ _ (by decide) (by decide)]
  · rw [c.regs _ (by decide) (by decide), f.regs _ (by decide) (by decide) (by decide) (by decide), g₁]

theorem proHead_wp {s : State} (hp : Pre s) : WP isa proHead s fun s' =>
    s'.gpr .r5 = Iv s ∧ s'.gpr .r7 = BitVec.ofNat 32 (N s) ∧ s'.gpr sb = Sc s := by
  have hw := hp.writable (r := wsR s) (by simp)
  have ha : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 4 :=
    ⟨argR s, List.mem_append_left _ (by rw [hp.rd]; simp), Region.contains_self _ _⟩
  refine WP.seq (WP.mono (entry_wp rfl ha rfl hp.fitB hw) fun s₁ e => ?_)
  have wc : Covers [⟨State.addr (Sc s), 4 * slots⟩] s₁.wr := by
    rw [e.wr]
    simpa only [BitVec.add_zero] using workspace_part hw 0 (4 * slots) (by decide)
  refine WP.mono (BatchCalls.prepare_wp e.key e.base hp.fitK
    (by have := hp.fitB; change (Sc s).toNat + 1456 ≤ 2 ^ 32; change (Sc s).toNat + 1512 ≤ 2 ^ 32 at this; omega)
    (hp.ks.sub_right (Region.sub_prefix (by decide)))
    (by rw [e.rd, e.wr]; exact hp.key) wc) fun s₂ ⟨p, _⟩ => ?_
  refine ⟨(p.regs _ (by decide) (by decide)).trans e.iv, ?_, (p.regs _ (by decide) (by decide)).trans e.base⟩
  rw [p.regs _ (by decide) (by decide), e.left]
  exact (BitVec.ofNat_toNat 32 (s.gpr .r3)).symm

end VG.Proof.Sm4.Arm.BatchHead
