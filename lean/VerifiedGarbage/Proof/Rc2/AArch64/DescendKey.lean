module

public import VerifiedGarbage.Proof.Rc2.AArch64.KeyLoop
public import VerifiedGarbage.Proof.Rc2.Expansion
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Rc2.AArch64.KeySteps
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Rc2.AArch64.KeyCompose`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.Impl.Rc2.AArch64

theorem fillKey_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (s.gpr .x21 + s.gpr .x23 - 1#64) 1)
    (readHi : InRegions (s.rd ++ s.wr) (s.gpr .x21 + (s.gpr .x23 - s.gpr .x20)) 1)
    (writable : InRegions s.wr (s.gpr .x21 + s.gpr .x23) 1) :
    WP isa (.block fillKey) s (fun s' =>
      s'.gpr .x23 = s.gpr .x23 + 1 ∧
      zeroFlag s' = some ((s.gpr .x23 + 1 - 128) == 0) ∧
      Keep keyTemps {s with
        mem := s.mem.writeW (s.gpr .x21 + s.gpr .x23)
          (Spec.Rc2.pi (s.mem (s.gpr .x21 + s.gpr .x23 - 1#64) +
          s.mem (s.gpr .x21 + (s.gpr .x23 - s.gpr .x20))))} s') := by
  rw [fillKey, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := fillInput_ok s readLo readHi
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  apply WP.mono (piLookup_ok s₁)
  intro s₂ h₂
  have k₁ : Keep keyTemps s s₁ := keep₁.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h <;> subst r <;> decide)
  have k₂ : Keep keyTemps s₁ s₂ := h₂.2.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h <;> subst r <;> decide)
  have keep := k₁.trans k₂
  have ptr := keep.reg .x21 (by decide)
  have index := (keep₁.reg .x23 (by decide)).trans rfl
  have index₂ : s₂.gpr .x23 = s.gpr .x23 := (h₂.2.reg .x23 (by decide)).trans index
  have write₂ : InRegions s₂.wr (s₂.gpr .x21 + s₂.gpr .x23) 1 := by
    rw [keep.wr, ptr, index₂]; exact writable
  obtain ⟨s₃, run₃, out₃, flag₃, keep₃⟩ := fillOutput_ok s₂ write₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  refine ⟨by rw [out₃, index₂], by rw [flag₃, index₂], ?_⟩
  constructor
  · intro r hr
    exact (keep₃.reg r hr).trans (keep.reg r hr)
  · rw [keep₃.mem, keep.mem, ptr, index₂, h₂.1, out₁]
    simp [BitVec.setWidth_add]
  · exact keep₃.rd.trans keep.rd
  · exact keep₃.wr.trans keep.wr

theorem piStore_ok (s : State) (writable : InRegions s.wr (s.gpr .x21 + s.gpr .x23) 1) :
    WP isa (.block (piLookup ++ storeKey)) s (fun s' =>
      s'.gpr .x23 = s.gpr .x23 ∧
      Keep keyTemps {s with
        mem := s.mem.writeW (s.gpr .x21 + s.gpr .x23) (Spec.Rc2.pi ((s.gpr .x8).setWidth 8))} s') := by
  rw [WP.block_append_iff]
  apply WP.mono (piLookup_ok s)
  intro s₁ h₁
  have ptr := h₁.2.reg .x21 (by decide)
  have index := h₁.2.reg .x23 (by decide)
  have valid : InRegions s₁.wr (s₁.gpr .x21 + s₁.gpr .x23) 1 := by
    rw [h₁.2.wr, ptr, index]; exact writable
  obtain ⟨s₂, run₂, index₂, keep₂⟩ := storeByte_ok s₁ valid
  refine WP.of_runBlock ⟨s₂, run₂, index₂.trans index, ?_⟩
  constructor
  · intro r hr
    rw [keep₂.reg r (by intro hm; simp only [List.mem_singleton] at hm; subst r; exact hr (by decide))]
    exact h₁.2.reg r (fun hm => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h <;> subst r <;> decide))
  · rw [keep₂.mem, h₁.2.mem, ptr, index, h₁.1]
    simp
  · exact keep₂.rd.trans h₁.2.rd
  · exact keep₂.wr.trans h₁.2.wr

theorem reduceKey_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .x21 + s.gpr .x23) 1)
    (writable : InRegions s.wr (s.gpr .x21 + s.gpr .x23) 1) :
    WP isa (.block reduceKey) s (fun s' => s'.gpr .x23 = s.gpr .x23 ∧
      Keep keyTemps {s with
        mem := s.mem.writeW (s.gpr .x21 + s.gpr .x23)
          (Spec.Rc2.pi (s.mem (s.gpr .x21 + s.gpr .x23) &&& (s.gpr .x2).setWidth 8))} s') := by
  rw [reduceKey, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := reduceInput_ok s readable
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have ptr := keep₁.reg .x21 (by decide)
  have index := keep₁.reg .x23 (by decide)
  have valid : InRegions s₁.wr (s₁.gpr .x21 + s₁.gpr .x23) 1 := by
    rw [keep₁.wr, ptr, index]; exact writable
  apply WP.mono (piStore_ok s₁ valid)
  intro s₂ h₂
  refine ⟨h₂.1.trans index, ?_⟩
  constructor
  · intro r hr
    exact (h₂.2.reg r hr).trans (keep₁.reg r (by
      intro hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h <;> subst r <;> exact hr (by decide)))
  · rw [h₂.2.mem, keep₁.mem, ptr, index, out₁]
    simp
  · exact h₂.2.rd.trans keep₁.rd
  · exact h₂.2.wr.trans keep₁.wr

theorem descendKey_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (s.gpr .x21 + (s.gpr .x23 - 1#64) + 1#64) 1)
    (readHi : InRegions (s.rd ++ s.wr) (s.gpr .x21 + (s.gpr .x23 - 1#64 + s.gpr .x24)) 1)
    (writable : InRegions s.wr (s.gpr .x21 + (s.gpr .x23 - 1#64)) 1) :
    WP isa (.block descendKey) s (fun s' =>
      s'.gpr .x23 = s.gpr .x23 - 1 ∧ zeroFlag s' = some ((s.gpr .x23 - 1) == 0) ∧
      Keep keyTemps {s with
        mem := s.mem.writeW (s.gpr .x21 + (s.gpr .x23 - 1#64))
          (Spec.Rc2.pi (s.mem (s.gpr .x21 + (s.gpr .x23 - 1#64) + 1#64) ^^^
            s.mem (s.gpr .x21 + (s.gpr .x23 - 1#64 + s.gpr .x24))))} s') := by
  rw [descendKey, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, index₁, out₁, keep₁⟩ := descendInput_ok s readLo readHi
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have ptr := keep₁.reg .x21 (by decide)
  have valid : InRegions s₁.wr (s₁.gpr .x21 + s₁.gpr .x23) 1 := by
    rw [keep₁.wr, ptr, index₁]; exact writable
  rw [← List.append_assoc, WP.block_append_iff]
  apply WP.mono (piStore_ok s₁ valid)
  intro s₂ h₂
  obtain ⟨s₃, run₃, flag₃, keep₃⟩ := cmpZero_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have index₂ := h₂.1.trans index₁
  refine ⟨(keep₃.reg .x23 (by decide)).trans index₂, by rw [flag₃, index₂], ?_⟩
  constructor
  · intro r hr
    exact ((keep₃.reg r (by intro hm; simp only [List.mem_singleton] at hm; subst r; exact hr (by decide))).trans (h₂.2.reg r hr)).trans (keep₁.reg r (fun hm => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h | h <;> subst r <;> decide)))
  · rw [keep₃.mem, h₂.2.mem, keep₁.mem, ptr, index₁, out₁]
    simp
  · exact keep₃.rd.trans (h₂.2.rd.trans keep₁.rd)
  · exact keep₃.wr.trans (h₂.2.wr.trans keep₁.wr)


end VG.Proof.Rc2.AArch64

end

end

/-! ### `Rc2.AArch64.FillKey`, which the modules that import this one used -/

section

/-! # Forward expansion to 128 bytes -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.Impl.Rc2.AArch64

theorem fillLoop_ok (s : State) (key : List Byte) (ht : 1 ≤ key.length) (ht' : key.length < 128)
    (len : s.gpr .x20 = BitVec.ofNat 64 key.length) (start : s.gpr .x23 = BitVec.ofNat 64 key.length)
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .x21 + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (s.gpr .x21) (fill key 0) key.length) :
    WP isa (.loop (.block fillKey) (.nonzero .x .x10)) s (fun s' =>
      s'.gpr .x23 = 128 ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (s.gpr .x21) (fill key (128 - key.length)) 128) := by
  let I (j : Nat) (s' : State) := s'.gpr .x23 = BitVec.ofNat 64 (key.length + j) ∧ KeyFrame s s' ∧
    BytesPrefix s'.mem (s.gpr .x21) (fill key j) (key.length + j)
  have finish : I (128 - key.length) = (fun s' => s'.gpr .x23 = 128 ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (s.gpr .x21) (fill key (128 - key.length)) 128) := by
    funext s'
    simp only [I, Nat.add_sub_of_le (Nat.le_of_lt ht')]
    rfl
  rw [← finish]
  apply forwardLoop (.block fillKey) I (128 - key.length) _ 0 (by omega_using [ht']) s
    ⟨start, KeyFrame.refl s, initialPrefix⟩
  intro j hj s₁ ⟨index₁, frame₁, prefix₁⟩
  have outPtr := frame₁.reg .x21 (by decide)
  have len₁ := (frame₁.reg .x20 (by decide)).trans len
  have loAddr : s₁.gpr .x21 + s₁.gpr .x23 - 1#64 =
      s.gpr .x21 + BitVec.ofNat 64 (key.length + j - 1) := by
    rw [outPtr, index₁]
    exact Offset.add_ofNat_sub _ (by omega_using [ht])
  have hiAddr : s₁.gpr .x21 + (s₁.gpr .x23 - s₁.gpr .x20) =
      s.gpr .x21 + BitVec.ofNat 64 j := by
    rw [outPtr, index₁, len₁, Offset.ofNat_sub_ofNat (by omega_using []), Nat.add_sub_cancel_left]
  have read₁ (i : Nat) (hi : i < 128) :
      InRegions (s₁.rd ++ s₁.wr) (s.gpr .x21 + BitVec.ofNat 64 i) 1 := by
    obtain ⟨r, hr, hc⟩ := writable i hi
    rw [frame₁.wr]
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have write₁ : InRegions s₁.wr (s₁.gpr .x21 + s₁.gpr .x23) 1 := by
    rw [frame₁.wr, outPtr, index₁]
    exact writable _ (by omega_using [hj])
  have readLo : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x21 + s₁.gpr .x23 - 1#64) 1 := by
    rw [loAddr]; exact read₁ _ (by omega_using [hj])
  have readHi : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x21 + (s₁.gpr .x23 - s₁.gpr .x20)) 1 := by
    rw [hiAddr]; exact read₁ _ (by omega_using [hj])
  apply WP.mono (fillKey_ok s₁ readLo readHi write₁)
  intro s₂ h₂
  let b := Spec.Rc2.pi ((fill key j).getD (key.length + j - 1) 0 + (fill key j).getD j 0)
  have keep₂ : Keep keyTemps {s₁ with
      mem := s₁.mem.writeW (s.gpr .x21 + BitVec.ofNat 64 (key.length + j)) b} s₂ := by
    have h := h₂.2.2
    rw [loAddr, hiAddr, prefix₁ _ (by omega_using [ht]), prefix₁ _ (by omega_using [ht]), outPtr, index₁] at h
    exact h
  constructor
  · refine ⟨?_, frame₁.step (key.length + j) (by omega_using [hj]) b keep₂, ?_⟩
    · rw [h₂.1, index₁, counter_add, Nat.add_assoc]
    · rw [keep₂.mem, fill_succ]
      have h := prefix₁.extend (show key.length + j < 128 by omega_using [hj]) b
      simpa only [fillStep, Nat.add_sub_cancel_left, Nat.add_assoc] using h
  · rw [h₂.2.1, index₁, counter_add]
    have he : key.length + j + 1 = 128 ↔ j + 1 = 128 - key.length := by omega_using []
    change some ((BitVec.ofNat 64 (key.length + j + 1) - BitVec.ofNat 64 128) == 0#64) = _
    rw [counter_eq _ _ (by omega_using [hj]) (by decide)]
    simp only [he]

end VG.Proof.Rc2.AArch64

end

end

/-! # The descending effective-key reduction loop -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.Impl.Rc2.AArch64

theorem descendLoop_ok (s : State) (l : KeyBytes) (t8 : Nat) (ht : 1 ≤ t8) (ht' : t8 < 128)
    (len : s.gpr .x24 = BitVec.ofNat 64 t8) (start : s.gpr .x23 = BitVec.ofNat 64 (128 - t8))
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .x21 + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (s.gpr .x21) l 128) :
    WP isa (.loop (.block descendKey) (.nonzero .x .x10)) s (fun s' =>
      s'.gpr .x23 = 0 ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (s.gpr .x21) (descend l t8 (128 - t8)) 128) := by
  let I (j : Nat) (s' : State) := s'.gpr .x23 = BitVec.ofNat 64 (128 - t8 - j) ∧ KeyFrame s s' ∧
    BytesPrefix s'.mem (s.gpr .x21) (descend l t8 j) 128
  have finish : I (128 - t8) = (fun s' => s'.gpr .x23 = 0 ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (s.gpr .x21) (descend l t8 (128 - t8)) 128) := by
    funext s'
    simp only [I, Nat.sub_self]
    rfl
  rw [← finish]
  apply forwardLoop (.block descendKey) I (128 - t8) _ 0 (by omega_using [ht']) s
    ⟨start, KeyFrame.refl s, initialPrefix⟩
  intro j hj s₁ ⟨index₁, frame₁, prefix₁⟩
  have outPtr := frame₁.reg .x21 (by decide)
  have len₁ := (frame₁.reg .x24 (by decide)).trans len
  have indexNew : s₁.gpr .x23 - 1#64 = BitVec.ofNat 64 (127 - t8 - j) := by
    rw [index₁, Offset.ofNat_sub_ofNat (show 1 ≤ 128 - t8 - j by omega_using [hj])]
    congr 1; omega_using []
  have loAddr : s₁.gpr .x21 + (s₁.gpr .x23 - 1#64) + 1#64 =
      s.gpr .x21 + BitVec.ofNat 64 (127 - t8 - j + 1) := by
    rw [outPtr, indexNew, BitVec.add_assoc]
    exact congrArg (s.gpr .x21 + ·) (counter_add _)
  have hiAddr : s₁.gpr .x21 + (s₁.gpr .x23 - 1#64 + s₁.gpr .x24) =
      s.gpr .x21 + BitVec.ofNat 64 (127 - t8 - j + t8) := by
    rw [outPtr, indexNew, len₁, ← BitVec.ofNat_add]
  have read₁ (i : Nat) (hi : i < 128) :
      InRegions (s₁.rd ++ s₁.wr) (s.gpr .x21 + BitVec.ofNat 64 i) 1 := by
    obtain ⟨r, hr, hc⟩ := writable i hi
    rw [frame₁.wr]
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have write₁ : InRegions s₁.wr (s₁.gpr .x21 + (s₁.gpr .x23 - 1#64)) 1 := by
    rw [frame₁.wr, outPtr, indexNew]
    exact writable _ (by omega_using [])
  have readLo : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x21 + (s₁.gpr .x23 - 1#64) + 1#64) 1 := by
    rw [loAddr]; exact read₁ _ (by omega_using [ht])
  have readHi : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x21 + (s₁.gpr .x23 - 1#64 + s₁.gpr .x24)) 1 := by
    rw [hiAddr]; exact read₁ _ (by omega_using [ht'])
  apply WP.mono (descendKey_ok s₁ readLo readHi write₁)
  intro s₂ h₂
  let b := Spec.Rc2.pi ((descend l t8 j).getD (127 - t8 - j + 1) 0 ^^^
    (descend l t8 j).getD (127 - t8 - j + t8) 0)
  have keep₂ : Keep keyTemps {s₁ with
      mem := s₁.mem.writeW (s.gpr .x21 + BitVec.ofNat 64 (127 - t8 - j)) b} s₂ := by
    have h := h₂.2.2
    rw [loAddr, hiAddr, prefix₁ _ (by omega_using [ht]), prefix₁ _ (by omega_using [ht']), outPtr, indexNew] at h
    exact h
  constructor
  · refine ⟨?_, frame₁.step (127 - t8 - j) (by omega_using []) b keep₂, ?_⟩
    · rw [h₂.1]
      change s₁.gpr .x23 - 1#64 = _
      rw [indexNew]
      congr 1; omega_using []
    · rw [keep₂.mem, descend_succ]
      exact prefix₁.write (by decide) (by omega_using []) b
  · rw [h₂.2.1]
    change some ((s₁.gpr .x23 - 1#64) == 0#64) = _
    rw [indexNew]
    have he : 127 - t8 - j = 0 ↔ j + 1 = 128 - t8 := by omega_using [hj]
    have eqZero := counter_eq (127 - t8 - j) 0 (by omega_using []) (by decide)
    simp only [BitVec.sub_zero] at eqZero
    rw [eqZero]
    simp only [he]

end VG.Proof.Rc2.AArch64
