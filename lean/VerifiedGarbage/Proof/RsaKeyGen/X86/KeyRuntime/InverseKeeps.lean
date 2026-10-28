module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StackRange
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseFrame
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseBridge

/-! # What a call of `vg_rsa_keygen_inverse` leaves in the workspace

`Key.inverse_preserves_num` and `Key.inverse_preserves_slot`, for the frame of a call
(`OutsS`): the stack it writes is beyond the workspace. -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Proof.RsaKeyGen.X86.Key (inverseRanges)

/-- A number in the workspace keeps its value. -/
theorem OutsS.val32_eq {B : Addr} {sp : BitVec 32} {rs : List (Nat × Nat)} {m m' : Mem} {Z : Nat}
    (h : OutsS B sp rs m m') (D : VG.Proof.RsaKeyGen.X86.KeyArgs.DeepStk sp B Z)
    (nowrap : B.toNat + Z ≤ 2 ^ 32) {d k : Nat} (hd : ∀ r ∈ rs, d + 4 * k ≤ r.1 ∨ r.1 + r.2 ≤ d)
    (hs : d + 4 * k ≤ Z) : val32 m' B d k = val32 m B d k := by
  apply (h.outs D nowrap).val32 _ (by omega)
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hd r hr
  · obtain rfl := List.mem_singleton.mp hr
    exact Or.inl hs

/-- The memory with the stack below `sp` as in `m₁`, the rest as in `m₂`: what `OutsS` changes as
`Outs` would. -/
def hyb (sp : BitVec 32) (m₁ m₂ : Mem) : Mem := fun x => if (below sp 52).Contains x 1 then m₁ x else m₂ x

theorem OutsS.outs_hyb {B : Addr} {sp : BitVec 32} {rs : List (Nat × Nat)} {m₁ m₂ : Mem}
    (h : OutsS B sp rs m₁ m₂) : Outs B rs m₁ (hyb sp m₁ m₂) := by
  intro x hx
  unfold hyb
  by_cases hz : (below sp 52).Contains x 1
  · simp only [hz, ↓reduceIte]
  · simp only [hz, ↓reduceIte]
    exact h x hx hz

/-- A number in the workspace changes as `Outs` lets it. -/
theorem OutsS.read {B : Addr} {sp : BitVec 32} {rs : List (Nat × Nat)} {m₁ m₂ : Mem} {Z : Nat}
    (h : OutsS B sp rs m₁ m₂) (D : VG.Proof.RsaKeyGen.X86.KeyArgs.DeepStk sp B Z)
    (nowrap : B.toNat + Z ≤ 2 ^ 32) {d k : Nat} (fit : d + 4 * k ≤ Z)
    (old : Outs B rs m₁ (hyb sp m₁ m₂) → val32 (hyb sp m₁ m₂) B d k = val32 m₁ B d k) :
    val32 m₂ B d k = val32 m₁ B d k := by
  rw [← old h.outs_hyb]
  have far := stack_far D nowrap
  have size : (stackRange B sp).2 = 52 := rfl
  refine val32_congr fun j hj => congrArg BitVec.toNat (Mem.readW_congr fun i hi => ?_)
  unfold hyb
  have notStack : ¬ (below sp 52).Contains (off B (d + 4 * j) + BitVec.ofNat 64 i) 1 := by
    intro c
    have H := (stack_contains D nowrap _).mp c
    rw [ofs_off B (by omega)] at H
    omega
  simp only [notStack, ↓reduceIte]

theorem Ws.read_num {s : State} {B : Addr} {Z n N j : Nat} (W : Ws s B Z n N) (hj : j < N)
    {rs : List (Nat × Nat)} {m₁ m₂ : Mem} (h : OutsS B (s.gpr .esp) rs m₁ m₂)
    (old : Outs B rs m₁ (hyb (s.gpr .esp) m₁ m₂) → num (hyb (s.gpr .esp) m₁ m₂) B n j = num m₁ B n j) :
    num m₂ B n j = num m₁ B n j :=
  h.read W.deep W.old.workspace.nowrap (by have := W.arr_fit hj; unfold S at this; omega) old

theorem Ws.read_val32 {s : State} {B : Addr} {Z n N d k : Nat} (W : Ws s B Z n N) (fit : d + 4 * k ≤ hdr)
    {rs : List (Nat × Nat)} {m₁ m₂ : Mem} (h : OutsS B (s.gpr .esp) rs m₁ m₂)
    (old : Outs B rs m₁ (hyb (s.gpr .esp) m₁ m₂) → val32 (hyb (s.gpr .esp) m₁ m₂) B d k = val32 m₁ B d k) :
    val32 m₂ B d k = val32 m₁ B d k :=
  h.read W.deep W.old.workspace.nowrap (Nat.le_trans fit W.hdr_le) old

theorem Ws.inverse_num {s : State} {B : Addr} {Z n N k j : Nat} {m m' : Mem} (h : Ws s B Z n N)
    (width : k ≤ n) (persistent : 15 ≤ j) (hj : j < N)
    (changed : OutsS B (s.gpr .esp) (inverseRanges k invSlots) m m') : num m' B n j = num m B n j := by
  have fit := h.arr_fit hj
  apply changed.val32_eq h.deep h.old.workspace.nowrap _ (by unfold S at fit; omega)
  intro r hr
  simp only [inverseRanges, invSlots, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · have endBound := VG.Proof.RsaKeyGen.X86.Key.inverse_end_le width persistent
    have endEq : arr k 15 = hdr + 4 * (15 * (k + 2)) := by unfold arr S; omega
    rw [endEq] at endBound
    exact Or.inr endBound
  all_goals have lower : hdr ≤ arr n j := Nat.le_add_right ..
  all_goals simp only [sOdd, sB, sC, hdr] at lower ⊢
  all_goals omega

theorem Ws.inverse_slot {s : State} {B : Addr} {Z n N k d : Nat} {m m' : Mem} (h : Ws s B Z n N)
    (bound : d + 4 ≤ 100) (changed : OutsS B (s.gpr .esp) (inverseRanges k invSlots) m m') :
    slot m' B d = slot m B d := by
  have header := h.hdr_le
  have value : val32 m' B d 1 = val32 m B d 1 := by
    apply changed.val32_eq h.deep h.old.workspace.nowrap _ (by unfold hdr at header; omega)
    intro r hr
    simp only [inverseRanges, invSlots, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    all_goals simp only [sOdd, sB, sC, hdr]
    all_goals omega
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using value

end VG.Proof.RsaKeyGen.X86.KeyRuntime
