module
public import VerifiedGarbage.Proof.Dsa.X86.RandomCall
public import VerifiedGarbage.Proof.Dsa.X86.RandomDraw

import VerifiedGarbage.Proof.Framework.Offset

/-!
# The signer's state between attempts (x86)

`Att`: the sampler's state, the attempts left, the callee-saved registers
in their slots, and how the rest of the specification's signing loop
(`randomSignRemaining`) gives the overall result (`rResult`). `Done`: the
loop's status and consumption, and the signature in `out` on success.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random

/-- The overall result. -/
abbrev rResult (s₀ : State) : Spec.Dsa.RandomSignResult :=
  Spec.Dsa.randomSignBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key (rInput s₀).digest
    (rInput s₀).rand

/-- The callee-saved registers, in their slots. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  slot m (rBase s₀) oSaveEbx = s₀.gpr .ebx ∧ slot m (rBase s₀) oSaveEsi = s₀.gpr .esi ∧
    slot m (rBase s₀) oSaveEdi = s₀.gpr .edi ∧ slot m (rBase s₀) oSaveEbp = s₀.gpr .ebp

theorem Saved.of_slots {s₀ : State} {m m' : Mem} (h : Saved s₀ m)
    (he : ∀ d, 44 ≤ d → d + 4 ≤ 60 → slot m' (rBase s₀) d = slot m (rBase s₀) d) : Saved s₀ m' :=
  ⟨(he _ (by decide) (by decide)).trans h.1, (he _ (by decide) (by decide)).trans h.2.1,
    (he _ (by decide) (by decide)).trans h.2.2.1, (he _ (by decide) (by decide)).trans h.2.2.2⟩

/-- The spec's signing from `used` on, with `fuel` attempts left, gives the
overall result. -/
abbrev RRel (s₀ : State) (used fuel : Nat) : Prop :=
  VG.Proof.Dsa.RandomSignResultRel (rInput s₀) 0 (rResult s₀) used fuel

/-- Between attempts. -/
structure Att (s₀ : State) (used fuel : Nat) (t : State) : Prop where
  smp : ∃ d, Smp s₀ used d t
  attempts : slot t.mem (rBase s₀) oAttempts = BitVec.ofNat 32 fuel
  saved : Saved s₀ t.mem
  rel : RRel s₀ used fuel

/-- After the attempts. -/
structure Done (s₀ : State) (t : State) : Prop where
  smp : ∃ d, Smp s₀ (rResult s₀).used d t
  status : slot t.mem (rBase s₀) oStatus = BitVec.ofNat 32 (rResult s₀).status
  out : (rResult s₀).status = 1 → Spec.Rsa.bytesAt t.mem (argumentPointer s₀ 0) (X86.arg s₀ 1).toNat =
    (rResult s₀).signature.getD (List.replicate (X86.arg s₀ 1).toNat 0)
  saved : Saved s₀ t.mem

/-! ## What the call keeps -/

theorem self_contains (x : Addr) : (⟨x, 1⟩ : Region).Contains x 1 := by
  simp [Region.Contains]

/-- The frame above its argument words is apart from where the call writes. -/
theorem call_frame_byte {s₀ : State} (A : RandomSignABI s₀) {m m' : Mem} (hf : Frame (callWrites s₀) m m')
    {d : Nat} (h₁ : 44 ≤ d) (h₂ : d < 120) : m' (off (rBase s₀) d) = m (off (rBase s₀) d) := by
  rw [rBase_off]
  have hs : (rStack s₀).Contains (off (rLow s₀) (24 + d)) 1 := Offset.contains_base _ (by omega) (by omega)
  refine hf _ fun r hr => ?_
  simp only [callWrites, callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact A.stackOut _ hs
  · exact A.stackScratch _ hs
  · exact (Offset.disjoint (rLow s₀) (d := 24 + d) (n := 1) (e := 24) (k := 44) (by omega) (by omega)
      (by omega)) _ (self_contains _)
  · exact (Offset.disjoint_base (rLow s₀) (d := 24 + d) (n := 1) (k := 24) (by omega) (by omega)) _
      (self_contains _)

theorem call_frame_slot {s₀ : State} (A : RandomSignABI s₀) {m m' : Mem} (hf : Frame (callWrites s₀) m m')
    {d : Nat} (h₁ : 44 ≤ d) (h₂ : d + 4 ≤ 120) : slot m' (rBase s₀) d = slot m (rBase s₀) d :=
  Mem.readW_congr fun i hi => by
    have : i < 4 := hi
    rw [show off (rBase s₀) d + BitVec.ofNat 64 i = off (rBase s₀) (d + i) by
      rw [off, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]]
    exact call_frame_byte A hf (by omega) (by omega)

/-- The call keeps the sampler's state. -/
theorem Smp.after_call {s₀ t u : State} (A : RandomSignABI s₀) {used d : Nat} (S : Smp s₀ used d t)
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
theorem Smp.after_args {s₀ t u : State} (A : RandomSignABI s₀) {used d : Nat} (S : Smp s₀ used d t)
    (hr : Ready s₀ u) (hm : Outs (rBase s₀) [(0, 44)] t.mem u.mem) : Smp s₀ used d u := by
  have hql := rQBytes_le A
  have hfit : rWidth s₀ ≤ (rQBytes s₀).length := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  have hs : ∀ d, 44 ≤ d → d + 4 ≤ 120 → slot u.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d h₁ h₂ =>
    slot_outs hm (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; right; exact h₁) (by omega)
  refine ⟨hr, (hs _ (by decide) (by decide)).trans S.q, (hs _ (by decide) (by decide)).trans S.width,
    (hs _ (by decide) (by decide)).trans S.mask, (hs _ (by decide) (by decide)).trans S.usedW,
    (hs _ (by decide) (by decide)).trans S.drawsW, fun i hi => ?_, S.usedBound⟩
  rw [hm _ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [ofs_off0 _ (by unfold oNonce; omega)]; right; unfold oNonce; omega]
  exact S.pad i hi

end VG.Proof.Dsa.X86
