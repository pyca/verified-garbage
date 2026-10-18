module

public import VerifiedGarbage.Proof.Dsa.X86.RunFrame

/-! # Preservation of caller bytes and untouched encoded intermediates -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem outs_bytes {m m' : Mem} {base p : Addr} {len : Nat} {ranges : List (Nat × Nat)}
    (O : Outs base ranges m m') (hl : len ≤ 2 ^ 64)
    (hb : ∀ r ∈ ranges, r.1 + r.2 ≤ 2 ^ 64)
    (apart : ∀ r ∈ ranges, Region.Disjoint ⟨p, len⟩ ⟨off base r.1, r.2⟩) :
    Spec.Rsa.bytesAt m' p len = Spec.Rsa.bytesAt m p len := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  have hilt := List.mem_range.mp hi
  apply O _
  intro r hr
  have inside : (⟨p, len⟩ : Region).Contains (p + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base p (by omega) (by omega)
  have outside := apart r hr _ inside
  have H := Offset.lt_iff (p + BitVec.ofNat 64 i) base (hb r hr)
  change ¬ ((p + BitVec.ofNat 64 i - off base r.1).toNat + 1 ≤ r.2) at outside
  change (p + BitVec.ofNat 64 i - off base r.1).toNat < r.2 ↔
    r.1 ≤ ofs base (p + BitVec.ofNat 64 i) ∧ ofs base (p + BitVec.ofNat 64 i) < r.1 + r.2 at H
  omega

theorem stackOuts_bytes {m m' : Mem} {base p : Addr} {len : Nat} {ranges : List (Nat × Nat)} {sp : BitVec 32}
    (O : StackOuts base sp ranges m m') (hl : len ≤ 2 ^ 64)
    (safe : ∀ x, (⟨p, len⟩ : Region).Contains x 1 → ofs base x < usedBytes ∨ ¬ (callStack sp).Contains x 1)
    (hb : ∀ r ∈ ranges, r.1 + r.2 ≤ 2 ^ 64)
    (apart : ∀ r ∈ ranges, Region.Disjoint ⟨p, len⟩ ⟨off base r.1, r.2⟩) :
    Spec.Rsa.bytesAt m' p len = Spec.Rsa.bytesAt m p len := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  have hilt := List.mem_range.mp hi
  apply O _ ?_ (safe _ (Offset.contains_base p (by omega) (by omega)))
  intro r hr
  have inside : (⟨p, len⟩ : Region).Contains (p + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base p (by omega) (by omega)
  have outside := apart r hr _ inside
  have H := Offset.lt_iff (p + BitVec.ofNat 64 i) base (hb r hr)
  change ¬ ((p + BitVec.ofNat 64 i - off base r.1).toNat + 1 ≤ r.2) at outside
  change (p + BitVec.ofNat 64 i - off base r.1).toNat < r.2 ↔
    r.1 ≤ ofs base (p + BitVec.ofNat 64 i) ∧ ofs base (p + BitVec.ofNat 64 i) < r.1 + r.2 at H
  omega

theorem runFrame_bytes {s t : State} {base p : Addr} {size len : Nat}
    (O : StackOuts base (s.gpr .esp) runRanges s.mem t.mem) (hs : usedBytes ≤ size) (hl : len ≤ 2 ^ 64)
    (apart : Region.Disjoint ⟨p, len⟩ ⟨base, size⟩)
    (stack : Region.Disjoint ⟨p, len⟩ (callStack (s.gpr .esp))) :
    Spec.Rsa.bytesAt t.mem p len = Spec.Rsa.bytesAt s.mem p len := by
  apply stackOuts_bytes O hl (fun x hx => .inr (stack x hx))
  · intro r hr
    simp only [runRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · intro r hr
    apply apart.sub_right
    apply Offset.sub_base
    simp only [runRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      change _ ≤ size <;> change 15712 ≤ size at hs <;>
      simp only [VG.Impl.Mont.X86.Dynamic.contextBytes, VG.Impl.Mont.X86.Dynamic.slot,
        VG.Impl.Mont.X86.Dynamic.stride, Layout.field, VG.Impl.Dsa.Layout.r, usedBytes] <;> omega

end VG.Proof.Dsa.X86
