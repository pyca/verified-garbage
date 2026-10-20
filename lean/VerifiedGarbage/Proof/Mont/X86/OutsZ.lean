module

import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.Words

/-! # Memory that changes in given ranges and in the stack a call uses

`OutsZ base sp rs m m'`: `m'` agrees with `m` but on the ranges `rs` of
offsets from `base` (as `Outs`) and on the 20 bytes below `sp`, where a call
of a function of four arguments writes them and its return address. The
working space lies apart from those bytes (`CallRoom`), so its numbers keep
their values as under `Outs` (`OutsZ.val32`). -/

@[expose] public section

namespace VG.Proof.Mont.X86

open VG VG.X86 VG.Proof.Mont

def OutsZ (base : Addr) (sp : BitVec 32) (rs : List (Nat × Nat)) (m m' : Mem) : Prop :=
  ∀ x, (∀ r ∈ rs, ofs base x < r.1 ∨ r.1 + r.2 ≤ ofs base x) → ¬ (below sp 20).Contains x 1 → m' x = m x

/-- The 40 bytes below `sp`, which a call and its callee use, are apart from
the working space. -/
structure CallRoom (sp : BitVec 32) (base : Addr) (size : Nat) : Prop where
  low : 40 ≤ sp.toNat
  apart : Region.Disjoint (below sp 40) ⟨base, size⟩

namespace OutsZ

variable {base : Addr} {sp : BitVec 32} {rs rs' : List (Nat × Nat)} {m₁ m₂ m₃ : Mem}

theorem refl (base : Addr) (sp : BitVec 32) (rs : List (Nat × Nat)) (m : Mem) : OutsZ base sp rs m m :=
  fun _ _ _ => rfl

theorem trans (h₁ : OutsZ base sp rs m₁ m₂) (h₂ : OutsZ base sp rs m₂ m₃) : OutsZ base sp rs m₁ m₃ :=
  fun x hx hz => (h₂ x hx hz).trans (h₁ x hx hz)

theorem mono (h : OutsZ base sp rs m₁ m₂) (hr : ∀ r ∈ rs, r ∈ rs' := by decide) : OutsZ base sp rs' m₁ m₂ :=
  fun x hx hz => h x (fun r h' => hx r (hr r h')) hz

theorem of_outs (h : Outs base rs m₁ m₂) : OutsZ base sp rs m₁ m₂ := fun x hx _ => h x hx

/-- Changes within some ranges, as changes within ranges covering them. -/
theorem widen (h : OutsZ base sp rs m₁ m₂)
    (hr : ∀ y : Nat, (∀ r ∈ rs', y < r.1 ∨ r.1 + r.2 ≤ y) → ∀ r ∈ rs, y < r.1 ∨ r.1 + r.2 ≤ y) :
    OutsZ base sp rs' m₁ m₂ :=
  fun x hx hz => h x (hr _ hx) hz

theorem of_outside {o n : Nat} (h : Outside base o n m₁ m₂) (hr : (o, n) ∈ rs) : OutsZ base sp rs m₁ m₂ :=
  of_outs (Outs.of_outside h hr)

end OutsZ

/-- Changes within some ranges, as changes within ranges covering them. -/
theorem Outs.widen {base : Addr} {rs rs' : List (Nat × Nat)} {m₁ m₂ : Mem} (h : Outs base rs m₁ m₂)
    (hr : ∀ y : Nat, (∀ r ∈ rs', y < r.1 ∨ r.1 + r.2 ≤ y) → ∀ r ∈ rs, y < r.1 ∨ r.1 + r.2 ≤ y) :
    Outs base rs' m₁ m₂ :=
  fun x hx => h x (hr _ hx)

/-- The zone a call writes lies apart from the working space. -/
theorem CallRoom.zone {sp : BitVec 32} {base : Addr} {size : Nat} (R : CallRoom sp base size) :
    Region.Disjoint (below sp 20) ⟨base, size⟩ :=
  fun x h₁ => R.apart x (below_sub (by decide) R.low x h₁)

/-- The return address lies above the zone a call writes. -/
theorem ret_zone {sp : BitVec 32} (h : 20 ≤ sp.toNat) :
    Region.Disjoint ⟨sp.setWidth 64, 4⟩ (below sp 20) := by
  simp only [below]
  rw [VG.X86.Taint.sub_setWidth h]
  exact Offset.base_disjoint_below _ (by decide)

/-- The stack a call uses is past the working space. -/
theorem CallRoom.zone_ofs {sp : BitVec 32} {base : Addr} {size : Nat} (R : CallRoom sp base size) {x : Addr} (hx : (below sp 20).Contains x 1) : size ≤ ofs base x := by
  have h40 := R.low
  have hsp := sp.isLt
  by_contra hc
  have hcx : (⟨base, size⟩ : Region).Contains x 1 := by
    simp only [Region.Contains, ofs] at hc ⊢; omega
  refine R.apart x ?_ hcx
  simp only [Region.Contains] at hx ⊢
  have e20 : ((sp - BitVec.ofNat 32 20).setWidth 64).toNat = sp.toNat - 20 := by
    rw [BitVec.toNat_setWidth, sub_toNat (by omega)]; exact Nat.mod_eq_of_lt (by omega)
  have e40 : ((sp - BitVec.ofNat 32 40).setWidth 64).toNat = sp.toNat - 40 := by
    rw [BitVec.toNat_setWidth, sub_toNat (by omega)]; exact Nat.mod_eq_of_lt (by omega)
  generalize ((sp - BitVec.ofNat 32 20).setWidth 64) = z at hx e20
  generalize ((sp - BitVec.ofNat 32 40).setWidth 64) = w at e40 ⊢
  bv_omega

/-- A number in the working space keeps its value. -/
theorem OutsZ.val32 {base : Addr} {sp : BitVec 32} {rs : List (Nat × Nat)} {m m' : Mem} {size : Nat}
    (h : OutsZ base sp rs m m') (R : CallRoom sp base size) (hn : base.toNat + size ≤ 2 ^ 32)
    {d k : Nat} (hd : ∀ r ∈ rs, d + 4 * k ≤ r.1 ∨ r.1 + r.2 ≤ d) (hs : d + 4 * k ≤ size) :
    val32 m' base d k = val32 m base d k :=
  val32_congr fun j hj => congrArg BitVec.toNat (Mem.readW_congr fun i hi => h _ (fun r hr => by
    have := hd r hr
    rw [ofs_off base (by omega)]; omega) fun hz => by
      have := R.zone_ofs hz
      rw [ofs_off base (by omega)] at this; omega)

theorem OutsZ.wordsVal {base : Addr} {sp : BitVec 32} {rs : List (Nat × Nat)} {m m' : Mem} {size : Nat}
    (h : OutsZ base sp rs m m') (R : CallRoom sp base size) (hn : base.toNat + size ≤ 2 ^ 32)
    {d k : Nat} (hd : ∀ r ∈ rs, d + 8 * k ≤ r.1 ∨ r.1 + r.2 ≤ d) (hs : d + 8 * k ≤ size) :
    wordsVal m' base d k = wordsVal m base d k := by
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  exact h.val32 R hn (fun r hr => by have := hd r hr; omega) (by omega)

theorem OutsZ.readW32 {base : Addr} {sp : BitVec 32} {rs : List (Nat × Nat)} {m m' : Mem} {size : Nat}
    (h : OutsZ base sp rs m m') (R : CallRoom sp base size) (hn : base.toNat + size ≤ 2 ^ 32)
    {d : Nat} (hd : ∀ r ∈ rs, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d) (hs : d + 4 ≤ size) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 :=
  Mem.readW_congr fun i hi => h _ (fun r hr => by
    have := hd r hr
    rw [ofs_off base (by omega)]; omega) fun hz => by
      have := R.zone_ofs hz
      rw [ofs_off base (by omega)] at this; omega

theorem OutsZ.w32 {base : Addr} {sp : BitVec 32} {rs : List (Nat × Nat)} {m m' : Mem} {size : Nat}
    (h : OutsZ base sp rs m m') (R : CallRoom sp base size) (hn : base.toNat + size ≤ 2 ^ 32)
    {d : Nat} (hd : ∀ r ∈ rs, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d) (hs : d + 4 ≤ size) :
    w32 m' base d = w32 m base d := by
  refine congrArg BitVec.toNat (Mem.readW_congr fun i hi => h _ (fun r hr => by
    have := hd r hr
    rw [ofs_off base (by omega)]; omega) fun hz => by
      have := R.zone_ofs hz
      rw [ofs_off base (by omega)] at this; omega)

end VG.Proof.Mont.X86
