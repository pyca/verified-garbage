module

import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
import VerifiedGarbage.Proof.Dsa.X86.Layout

/-! ### `Dsa.X86.RunFrame`, which this module and modules that import it used -/

section

/-! # Memory and pointer invariants across complete DSA arithmetic schedules -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

/-- Arithmetic scratch, the acceptance mask, and persistent intermediates. -/
def runRanges : List (Nat × Nat) :=
  [(0, contextBytes 48), (Layout.field .mask, 4), (r, usedBytes - r)]

def StablePointer : Pointer → Prop
  | .input f => f ≠ .mask
  | .local _ => True
  | .signatureS => True

instance (p : Pointer) : Decidable (StablePointer p) := by
  cases p <;> unfold StablePointer <;> infer_instance

theorem runFrame_field {s t : State} {base : Addr}
    (O : StackOuts base (s.gpr .esp) runRanges s.mem t.mem) {f : Field} (hf : f ≠ .mask) :
    t.mem.readW (off base (Layout.field f)) 32 = s.mem.readW (off base (Layout.field f)) 32 := by
  have lo := (VG.Proof.Dsa.X86.Layout.field_bounds f).1
  have hi : Layout.field f + 4 ≤ 8244 := by cases f <;> simp_all [Layout.field]
  apply BitVec.eq_of_toNat_eq
  have H : val32 t.mem base (Layout.field f) 1 = val32 s.mem base (Layout.field f) 1 := by
    apply O.val32
    · intro pair hp
      simp only [runRanges, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · change Layout.field f + 4 ≤ 0 ∨ 7048 ≤ Layout.field f
        omega_using [lo]
      · change Layout.field f + 4 ≤ 8244 ∨ 8248 ≤ Layout.field f
        omega_using [hi]
      · change Layout.field f + 4 ≤ 14720 ∨ 15712 ≤ Layout.field f
        omega_using [hi]
    · change _ ≤ 15712; omega_using [hi]
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using H

theorem runFrame_pointer {s t : State} {base : Addr} {rs : List Reg} {p : Pointer}
    (O : StackOuts base (s.gpr .esp) runRanges s.mem t.mem) (K : Keeps rs s t) (hdi : .edi ∉ rs) (hp : StablePointer p) :
    pointerValue base t p = pointerValue base s p := by
  cases p with
  | input f => exact runFrame_field O hp
  | «local» offset => simp only [pointerValue, K.1 _ hdi]
  | signatureS =>
    simp only [pointerValue, runFrame_field O (f := .signature) (by decide), runFrame_field O (f := .qLen) (by decide)]

end VG.Proof.Dsa.X86

end

end

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
    Offset.contains_base p (by omega_using [hilt]) (by omega_using [hl, hilt])
  have outside := apart r hr _ inside
  have H := Offset.lt_iff (p + BitVec.ofNat 64 i) base (hb r hr)
  change ¬ ((p + BitVec.ofNat 64 i - off base r.1).toNat + 1 ≤ r.2) at outside
  change (p + BitVec.ofNat 64 i - off base r.1).toNat < r.2 ↔
    r.1 ≤ ofs base (p + BitVec.ofNat 64 i) ∧ ofs base (p + BitVec.ofNat 64 i) < r.1 + r.2 at H
  omega_using [outside, H]

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
  apply O _ ?_ (safe _ (Offset.contains_base p (by omega_using [hilt]) (by omega_using [hl, hilt])))
  intro r hr
  have inside : (⟨p, len⟩ : Region).Contains (p + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base p (by omega_using [hilt]) (by omega_using [hl, hilt])
  have outside := apart r hr _ inside
  have H := Offset.lt_iff (p + BitVec.ofNat 64 i) base (hb r hr)
  change ¬ ((p + BitVec.ofNat 64 i - off base r.1).toNat + 1 ≤ r.2) at outside
  change (p + BitVec.ofNat 64 i - off base r.1).toNat < r.2 ↔
    r.1 ≤ ofs base (p + BitVec.ofNat 64 i) ∧ ofs base (p + BitVec.ofNat 64 i) < r.1 + r.2 at H
  omega_using [outside, H]

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
        VG.Impl.Mont.X86.Dynamic.stride, Layout.field, VG.Impl.Dsa.Layout.r, usedBytes] <;> omega_using [hs]

end VG.Proof.Dsa.X86
