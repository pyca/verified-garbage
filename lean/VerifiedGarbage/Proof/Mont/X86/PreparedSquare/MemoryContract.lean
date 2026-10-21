module

public import VerifiedGarbage.Proof.Mont.X86.Compact.Entry
public import VerifiedGarbage.Spec.Rsa.Mont

public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Frame

import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.FrameArgs
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryMemory
import VerifiedGarbage.Proof.Mont.X86.Compact.Layout
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.RangeCover

/-! # The saved registers and symmetric product stay within prepared scratch -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Spec.Rsa.Mont

theorem entered_byte {s t : State} (A : Compact.Entry s) {rs : List Reg}
    (K : Keeps rs s t) (sp : .esp ∉ rs) {i : Nat} (index : i < Compact.lenOf s) :
    (entered t).mem (Compact.wsOf s + BitVec.ofNat 64 i) = t.mem (Compact.wsOf s + BitVec.ofNat 64 i) := by
  have es := K.1 .esp sp
  have saved := pushed_frame (rs := cacheRegisters) (s := t) (by decide) (by rw [es]; exact A.stackFit)
  exact saved _ fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    intro hc
    rw [es] at hc
    exact A.savedSeparate' _ hc (Offset.contains_base _ (by omega) (by have := A.bound; omega))

theorem entry_keeps {s t : State} (A : Compact.Entry s) {rs : List Reg}
    (K : Keeps rs s t) (sp : .esp ∉ rs)
    (cache : Outside (Compact.wsOf s) (arrAt (wOf s.mem (Compact.wsOf s)) 2) 16 s.mem t.mem)
    {m : Mem}
    (O : Outs (Compact.wsOf s)
      [(arrAt (wOf s.mem (Compact.wsOf s)) 2 + 16, 8 * (2 * wOf s.mem (Compact.wsOf s)) + 16),
       (arrAt (wOf s.mem (Compact.wsOf s)) (arg s 2).toNat, 4 * (2 * wOf s.mem (Compact.wsOf s)))]
      (entered t).mem m) :
    Spec.Rsa.Mont.Keeps (Compact.wsOf s) (arg s 1).toNat (wOf s.mem (Compact.wsOf s)) (arg s 2).toNat s.mem m := by
  intro i index far
  have two := far 2 (by change 2 ∈ [2, 3, (arg s 2).toNat]; simp)
  have three := far 3 (by change 3 ∈ [2, 3, (arg s 2).toNat]; simp)
  have output := far (arg s 2).toNat (by change (arg s 2).toNat ∈ [2, 3, (arg s 2).toNat]; simp)
  have oi : ofs (Compact.wsOf s) (Compact.wsOf s + BitVec.ofNat 64 i) = i :=
    ofs_off0 _ (by have := A.bound; omega)
  have keep := O (Compact.wsOf s + BitVec.ofNat 64 i) (by
    intro r hr
    rw [oi]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · dsimp only
      unfold arrAt hdrBytes at two three ⊢
      omega
    · dsimp only; omega)
  have cached : t.mem (Compact.wsOf s + BitVec.ofNat 64 i) = s.mem (Compact.wsOf s + BitVec.ofNat 64 i) := by
    apply cache
    rw [oi]
    unfold arrAt hdrBytes at two ⊢
    omega
  exact keep.trans ((entered_byte A K sp (by unfold Compact.lenOf; omega)).trans cached)

theorem return_word {s t : State} (A : Compact.Entry s) {rs : List Reg}
    (K : Keeps rs s t) (sp : .esp ∉ rs)
    (cache : Outs (Compact.wsOf s) [(0, Compact.lenOf s)] s.mem t.mem)
    {m : Mem} (O : Outs (Compact.wsOf s) [(0, Compact.lenOf s)] (entered t).mem m) :
    m.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
  have es := K.1 .esp sp
  have far := A.returnFar
  have keep : m.readW ((s.gpr .esp).setWidth 64) 32 = (entered t).mem.readW ((s.gpr .esp).setWidth 64) 32 :=
    Mem.readW_congr fun j hj => O _ fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      have := far j (by omega)
      right; simpa only [Nat.zero_add] using this
  have pushed : (entered t).mem.readW ((s.gpr .esp).setWidth 64) 32 = t.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
    have frame := pushed_frame (rs := cacheRegisters) (s := t) (by decide) (by rw [es]; exact A.stackFit)
    have separate : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (below (t.gpr .esp) 16) := by
      rw [es]
      unfold below
      rw [Taint.sub_setWidth A.stackFit]
      exact Offset.base_disjoint_below _ (by decide)
    exact frame.readW (Region.contains_self _ _) (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate) (by decide)
  refine keep.trans (pushed.trans ?_)
  exact Mem.readW_congr fun j hj => cache _ fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    have := far j (by omega)
    right; simpa only [Nat.zero_add] using this

end VG.Proof.Mont.X86.PreparedSquare
