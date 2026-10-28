module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # The stack below `esp` that the calls of `vg_rsa_keygen_inverse` use

The calls write the 52 bytes below `esp`: twelve of arguments, the return address and
the callee's frame. As a range of offsets from the workspace (`stackRange`), they lie
beyond it, so frames of the workspace's ranges take them in like any other range.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.KeyRt (RtWs)
open VG.Proof.Bignum.X86 (CallArgument)
open VG.Proof.RsaKeyGen.X86.KeyArgs (DeepStk)

def stackRange (B : Addr) (sp : BitVec 32) : Nat × Nat := (ofs B (below sp 52).base, 52)

theorem below52_toNat {sp : BitVec 32} (h : 52 ≤ sp.toNat) : (below sp 52).base.toNat = sp.toNat - 52 := by
  change ((sp - 52#32).setWidth 64).toNat = _
  rw [BitVec.toNat_setWidth, sub_toNat h]
  exact Nat.mod_eq_of_lt (by have := sp.isLt; omega)

/-- `x` is in the stack below `sp` exactly when its offset is in `stackRange`. -/
theorem stack_contains {sp : BitVec 32} {B : Addr} {Z : Nat} (D : DeepStk sp B Z)
    (nowrap : B.toNat + Z ≤ 2 ^ 32) (x : Addr) :
    (below sp 52).Contains x 1 ↔
      (stackRange B sp).1 ≤ ofs B x ∧ ofs B x < (stackRange B sp).1 + (stackRange B sp).2 := by
  obtain ⟨low, high, apart⟩ := D
  have b : (BitVec.setWidth 64 (sp - 52#32)).toNat = sp.toNat - 52 := below52_toNat low
  unfold stackRange ofs
  simp only [Region.Contains]
  rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_sub]
  change (2 ^ 64 - (BitVec.setWidth 64 (sp - 52#32)).toNat + _) % _ + 1 ≤ 52 ↔ _
  rw [b]
  have := x.isLt
  have := B.isLt
  omega

theorem stack_far {sp : BitVec 32} {B : Addr} {Z : Nat} (D : DeepStk sp B Z) (nowrap : B.toNat + Z ≤ 2 ^ 32) :
    Z ≤ (stackRange B sp).1 ∧ (stackRange B sp).1 + 52 ≤ 2 ^ 64 := by
  obtain ⟨low, high, apart⟩ := D
  have b := below52_toNat low
  unfold stackRange ofs
  rw [BitVec.toNat_sub, b]
  have := B.isLt
  constructor <;> omega

theorem outs_of_below {sp : BitVec 32} {B : Addr} {Z : Nat} {m m' : Mem} (D : DeepStk sp B Z)
    (nowrap : B.toNat + Z ≤ 2 ^ 32) (F : Frame [below sp 52] m m') : Outs B [stackRange B sp] m m' := by
  intro x hx
  apply F x
  intro r hr c
  obtain rfl := List.mem_singleton.mp hr
  have H := (stack_contains D nowrap x).mp c
  have := hx _ (List.mem_singleton_self _)
  omega

theorem frame_of_outs {sp : BitVec 32} {B : Addr} {Z : Nat} {m m' : Mem} {rs : List (Nat × Nat)}
    (D : DeepStk sp B Z) (nowrap : B.toNat + Z ≤ 2 ^ 32) (fits : ∀ r ∈ rs, r.1 + r.2 ≤ Z)
    (O : Outs B (rs ++ [stackRange B sp]) m m') : Frame [⟨B, Z⟩, below sp 52] m m' := by
  intro x hx
  have outside : Z ≤ ofs B x := by
    have H := hx ⟨B, Z⟩ List.mem_cons_self
    simp only [Region.Contains] at H
    unfold ofs
    omega
  have stack := hx (below sp 52) (List.mem_cons_of_mem _ List.mem_cons_self)
  apply O x
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · have := fits r hr
    omega
  · obtain rfl := List.mem_singleton.mp hr
    by_contra c
    exact stack ((stack_contains D nowrap x).mpr (by omega))

theorem argument_keepBelow {s t : State} {B : Addr} {Z i : Nat} {v : BitVec 32} {rs : List Reg}
    (A : CallArgument s B Z i v) (K : Keeps rs s t) (esp : .esp ∉ rs)
    (F : Frame [⟨B, Z⟩, below (s.gpr .esp) 52] s.mem t.mem) (low : 52 ≤ (s.gpr .esp).toNat) (fit : (s.gpr .esp).toNat + 8 + 4 * i ≤ 2 ^ 32) :
    CallArgument t B Z i v := by
  refine ⟨A.stack.keep K esp, ?_⟩
  have value : VG.Proof.Dsa.X86.stackValue t i = VG.Proof.Dsa.X86.stackValue s i := by
    unfold VG.Proof.Dsa.X86.stackValue
    rw [show VG.Proof.Dsa.X86.stackAddress t i = VG.Proof.Dsa.X86.stackAddress s i by
      simp only [VG.Proof.Dsa.X86.stackAddress, K.1 _ esp]]
    apply F.readW (Region.contains_self _ 4) _ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact A.stack.apart
    · have address : (VG.Proof.Dsa.X86.stackAddress s i).toNat = (s.gpr .esp).toNat + 4 + 4 * i := by
        simp only [VG.Proof.Dsa.X86.stackAddress, addr, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
        have := (s.gpr .esp).isLt
        omega
      have b : (below (s.gpr .esp) 52).base.toNat = (s.gpr .esp).toNat - 52 := below52_toNat low
      intro a ha hb
      simp only [Region.Contains, BitVec.toNat_sub] at ha hb
      rw [b] at hb
      rw [address] at ha
      have := a.isLt
      omega
  exact value.trans A.value

theorem rtWs_keepBelow {L : VG.Impl.Rsa.X86.KeyRt.Lay} {s t : State} {B : Addr} {Z len N : Nat}
    {rs : List Reg} (h : RtWs L s B Z len N) (K : Keeps rs s t) (edi : .edi ∉ rs) (esp : .esp ∉ rs)
    (F : Frame [⟨B, Z⟩, below (s.gpr .esp) 52] s.mem t.mem) (low : 52 ≤ (s.gpr .esp).toNat)
    (fitLen : (s.gpr .esp).toNat + 8 + 4 * L.len ≤ 2 ^ 32) (fitWs : (s.gpr .esp).toNat + 8 + 4 * L.ws ≤ 2 ^ 32) :
    RtWs L t B Z len N :=
  ⟨h.ws.rest K edi esp, h.lenArg.imp fun _ ⟨a, l, c⟩ => ⟨a, l, argument_keepBelow c K esp F low fitLen⟩,
    argument_keepBelow h.wsArg K esp F low fitWs, h.lenLe, h.layLen⟩

/-- `Ws.keep`, for code that also writes the stack below `esp` that a call uses. -/
theorem Ws.keepBelow {s t : State} {B : Addr} {Z n N : Nat} {rs : List Reg}
    (h : Ws s B Z n N) (K : Keeps rs s t) (F : Frame [⟨B, Z⟩, below (s.gpr .esp) 52] s.mem t.mem)
    (edi : .edi ∉ rs := by decide) (esp : .esp ∉ rs := by decide) : Ws t B Z n N := by
  obtain ⟨low, high, _⟩ := h.deep
  exact ⟨rtWs_keepBelow h.full K edi esp F low (by change _ + 8 + 4 * 7 ≤ _; omega) (by change _ + 8 + 4 * 20 ≤ _; omega),
    rtWs_keepBelow h.prime K edi esp F low (by change _ + 8 + 4 * 9 ≤ _; omega) (by change _ + 8 + 4 * 20 ≤ _; omega),
    rtWs_keepBelow h.exponent K edi esp F low (by change _ + 8 + 4 * 19 ≤ _; omega) (by change _ + 8 + 4 * 20 ≤ _; omega),
    h.width, h.size, by rw [K.1 .esp esp]; exact h.deep⟩

/-- The workspace is apart from the stack a call uses. -/
theorem deep_disjoint {sp : BitVec 32} {B : Addr} {Z : Nat} (D : DeepStk sp B Z) (nowrap : B.toNat + Z ≤ 2 ^ 32) :
    (⟨B, Z⟩ : Region).Disjoint (below sp 52) := by
  intro x hx hb
  have H : _ ≤ (x - B).toNat ∧ (x - B).toNat < _ := (stack_contains D nowrap x).mp hb
  have F := stack_far D nowrap
  have : (stackRange B sp).2 = 52 := rfl
  simp only [Region.Contains] at hx
  omega

/-! ## Changes in ranges of the workspace and in the stack a call uses -/

/-- `m'` agrees with `m` but on the ranges `rs` of offsets from `B` (as `Outs`) and on the 52
bytes below `sp` that a call of `vg_rsa_keygen_inverse` uses. -/
def OutsS (B : Addr) (sp : BitVec 32) (rs : List (Nat × Nat)) (m m' : Mem) : Prop :=
  ∀ x, (∀ r ∈ rs, ofs B x < r.1 ∨ r.1 + r.2 ≤ ofs B x) → ¬ (below sp 52).Contains x 1 → m' x = m x

namespace OutsS

variable {B : Addr} {sp : BitVec 32} {rs rs' : List (Nat × Nat)} {m₁ m₂ m₃ : Mem}

theorem trans (h₁ : OutsS B sp rs m₁ m₂) (h₂ : OutsS B sp rs m₂ m₃) : OutsS B sp rs m₁ m₃ :=
  fun x hx hz => (h₂ x hx hz).trans (h₁ x hx hz)

theorem mono (h : OutsS B sp rs m₁ m₂) (hr : ∀ r ∈ rs, r ∈ rs' := by decide) : OutsS B sp rs' m₁ m₂ :=
  fun x hx hz => h x (fun r h' => hx r (hr r h')) hz

theorem of_outs (h : Outs B rs m₁ m₂) : OutsS B sp rs m₁ m₂ := fun x hx _ => h x hx

theorem widen (h : OutsS B sp rs m₁ m₂)
    (hr : ∀ y : Nat, (∀ r ∈ rs', y < r.1 ∨ r.1 + r.2 ≤ y) → ∀ r ∈ rs, y < r.1 ∨ r.1 + r.2 ≤ y) :
    OutsS B sp rs' m₁ m₂ :=
  fun x hx hz => h x (hr _ hx) hz

/-- What `Outs` lets change within some ranges, it lets change within others: so does `OutsS`. -/
theorem lift (f : ∀ m m' : Mem, Outs B rs m m' → Outs B rs' m m') (h : OutsS B sp rs m₁ m₂) :
    OutsS B sp rs' m₁ m₂ := by
  intro x hx hz
  by_cases outside : ∀ r ∈ rs, ofs B x < r.1 ∨ r.1 + r.2 ≤ ofs B x
  · exact h x outside hz
  · exfalso
    have moved : Outs B rs m₁ (fun y => if y = x then m₁ x + 1 else m₁ y) := by
      intro y hy
      by_cases e : y = x
      · subst e
        exact absurd hy outside
      · simp only [e, ↓reduceIte]
    have := f _ _ moved x hx
    simp only [↓reduceIte] at this
    exact absurd this (by bv_omega)

/-- What `Outs` lets change within some regions, `OutsS` lets change within them and the stack. -/
theorem toFrame {R : List Region} (f : ∀ m m' : Mem, Outs B rs m m' → Frame R m m') (h : OutsS B sp rs m₁ m₂) :
    Frame (R ++ [below sp 52]) m₁ m₂ := by
  intro x hx
  have hz := hx _ (List.mem_append_right _ (List.mem_singleton_self _))
  by_cases outside : ∀ r ∈ rs, ofs B x < r.1 ∨ r.1 + r.2 ≤ ofs B x
  · exact h x outside hz
  · exfalso
    have moved : Outs B rs m₁ (fun y => if y = x then m₁ x + 1 else m₁ y) := by
      intro y hy
      by_cases e : y = x
      · subst e
        exact absurd hy outside
      · simp only [e, ↓reduceIte]
    have := f _ _ moved x (fun r hr => hx r (List.mem_append_left _ hr))
    simp only [↓reduceIte] at this
    exact absurd this (by bv_omega)

/-- Within the workspace, the changes are those of `Outs`. -/
theorem outs {Z : Nat} (h : OutsS B sp rs m₁ m₂) (D : DeepStk sp B Z) (nowrap : B.toNat + Z ≤ 2 ^ 32) :
    Outs B (rs ++ [(Z, 2 ^ 64 - Z)]) m₁ m₂ := by
  intro x hx
  apply h x (fun r hr => hx r (List.mem_append_left _ hr))
  intro hb
  have H : _ ≤ (x - B).toNat ∧ (x - B).toNat < _ := (stack_contains D nowrap x).mp hb
  have F := stack_far D nowrap
  have : (stackRange B sp).2 = 52 := rfl
  have far : (x - B).toNat < Z ∨ Z + (2 ^ 64 - Z) ≤ (x - B).toNat :=
    hx _ (List.mem_append_right _ (List.mem_singleton_self _))
  have := (x - B).isLt
  omega

/-- A frame of the workspace's ranges and the stack. -/
theorem frame {Z : Nat} (h : OutsS B sp rs m₁ m₂) (fits : ∀ r ∈ rs, r.1 + r.2 ≤ Z) :
    Frame [⟨B, Z⟩, below sp 52] m₁ m₂ := by
  intro x hx
  apply h x _ (hx _ (List.mem_cons_of_mem _ List.mem_cons_self))
  intro r hr
  have := fits r hr
  have H := hx _ List.mem_cons_self
  simp only [Region.Contains] at H
  unfold ofs
  omega

end OutsS

end VG.Proof.RsaKeyGen.X86.KeyRuntime
