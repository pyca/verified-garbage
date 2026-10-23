module
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Call
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Draw

import VerifiedGarbage.Proof.Framework.Offset

/-! # Saved registers and sampler state survive the derivation call -/

@[expose] public section

namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom

theorem outs_high {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m') {e : Nat}
    (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ e) {d : Nat} (hd : e ≤ d) (hd' : d + 4 < 2 ^ 64) :
    slot m' B d = slot m B d :=
  slot_outs h (fun r hr => .inr (Nat.le_trans (hrs r hr) hd)) hd'

theorem outs_low {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m') {e : Nat}
    (hrs : ∀ r ∈ rs, e ≤ r.1) {d : Nat} (hd : d + 4 ≤ e) (hd' : d + 4 < 2 ^ 64) :
    slot m' B d = slot m B d :=
  slot_outs h (fun r hr => .inl (Nat.le_trans hd (hrs r hr))) hd'

/-- The key-generation result for the original arguments and tape. -/
abbrev rResult (s₀ : State) : Spec.Dsa.GenerateKeyResult :=
  Spec.Dsa.generateKeyBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key (rInput s₀).rand

/-- The callee-saved registers, in their slots. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  slot m (rBase s₀) oSaveEbx = s₀.gpr .ebx ∧ slot m (rBase s₀) oSaveEsi = s₀.gpr .esi ∧
    slot m (rBase s₀) oSaveEdi = s₀.gpr .edi ∧ slot m (rBase s₀) oSaveEbp = s₀.gpr .ebp

theorem Saved.of_slots {s₀ : State} {m m' : Mem} (h : Saved s₀ m)
    (he : ∀ d, 44 ≤ d → d + 4 ≤ 60 → slot m' (rBase s₀) d = slot m (rBase s₀) d) : Saved s₀ m' :=
  ⟨(he _ (by decide) (by decide)).trans h.1, (he _ (by decide) (by decide)).trans h.2.1,
    (he _ (by decide) (by decide)).trans h.2.2.1, (he _ (by decide) (by decide)).trans h.2.2.2⟩

/-! ## What the call keeps -/

theorem self_contains (x : Addr) : (⟨x, 1⟩ : Region).Contains x 1 := by
  simp [Region.Contains]

/-- The frame above its argument words is apart from where the call writes. -/
theorem call_frame_byte {s₀ : State} (A : KeyABI s₀) {m m' : Mem} (hf : Frame (callWrites s₀) m m')
    {d : Nat} (h₁ : 44 ≤ d) (h₂ : d < 120) : m' (off (rBase s₀) d) = m (off (rBase s₀) d) := by
  rw [rBase_off, rLow_off]
  have hs : (rStack s₀).Contains (off (rCall s₀) (88 + (24 + d))) 1 := Offset.contains_base _ (by omega) (by omega)
  refine hf _ fun r hr => ?_
  simp only [callWrites, callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact A.stackOutWide _ hs
  · exact A.stackScratchWide _ hs
  · rw [rLow_off]
    exact (Offset.disjoint (rCall s₀) (d := 88 + (24 + d)) (n := 1) (e := 88 + 24) (k := 36) (by omega)
      (by omega) (by omega)) _ (self_contains _)
  · exact (Offset.disjoint_base (rCall s₀) (d := 88 + (24 + d)) (n := 1) (k := 112) (by omega) (by omega)) _
      (self_contains _)

theorem call_frame_slot {s₀ : State} (A : KeyABI s₀) {m m' : Mem} (hf : Frame (callWrites s₀) m m')
    {d : Nat} (h₁ : 44 ≤ d) (h₂ : d + 4 ≤ 120) : slot m' (rBase s₀) d = slot m (rBase s₀) d :=
  Mem.readW_congr fun i hi => by
    have : i < 4 := hi
    rw [show off (rBase s₀) d + BitVec.ofNat 64 i = off (rBase s₀) (d + i) by
      rw [off, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]]
    exact call_frame_byte A hf (by omega) (by omega)

/-- The call keeps the sampler's state. -/
theorem Smp.after_call {s₀ t u : State} (A : KeyABI s₀) {used d : Nat} (S : Smp s₀ used d t)
    (hr : Ready s₀ u) (hf : Frame (callWrites s₀) t.mem u.mem) : Smp s₀ used d u := by
  have hql := rQBytes_le A
  have hfit : rWidth s₀ ≤ (rQBytes s₀).length := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  refine ⟨hr, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, S.usedBound⟩
  · rw [call_frame_slot A hf (by decide) (by decide)]; exact S.q
  · rw [call_frame_slot A hf (by decide) (by decide)]; exact S.width
  · rw [call_frame_slot A hf (by decide) (by decide)]; exact S.mask
  · rw [call_frame_slot A hf (by decide) (by decide)]; exact S.usedW
  · rw [call_frame_slot A hf (by decide) (by decide)]; exact S.drawsW
  · rw [call_frame_byte A hf (by unfold oNonce; omega) (by unfold oNonce; omega)]; exact S.pad i hi

/-- The argument stores keep the sampler's state. -/
theorem Smp.after_args {s₀ t u : State} (A : KeyABI s₀) {used d : Nat} (S : Smp s₀ used d t)
    (hr : Ready s₀ u) (hm : Outs (rBase s₀) [(0, 36)] t.mem u.mem) : Smp s₀ used d u := by
  have hql := rQBytes_le A
  have hfit : rWidth s₀ ≤ (rQBytes s₀).length := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  have hs : ∀ d, 44 ≤ d → d + 4 ≤ 120 → slot u.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d h₁ h₂ =>
    slot_outs hm (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; right; change 0 + 36 ≤ d; omega) (by omega)
  refine ⟨hr, (hs _ (by decide) (by decide)).trans S.q, (hs _ (by decide) (by decide)).trans S.width,
    (hs _ (by decide) (by decide)).trans S.mask, (hs _ (by decide) (by decide)).trans S.usedW,
    (hs _ (by decide) (by decide)).trans S.drawsW, fun i hi => ?_, S.usedBound⟩
  rw [hm _ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [ofs_off0 _ (by unfold oNonce; omega)]; right; unfold oNonce; omega]
  exact S.pad i hi

end VG.Proof.Dsa.X86.KeyRandom
