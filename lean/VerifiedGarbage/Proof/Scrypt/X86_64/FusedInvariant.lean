import VerifiedGarbage.Proof.Scrypt.X86_64.FusedInit
namespace VG.Proof.Scrypt.X86_64.BlockMix.Fused
open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt)
open VG.Proof.Scrypt.X86_64.Retained (Words Meta memWords)

/-- The original BlockMix memory invariant, without its obsolete allocation
of public loop variables to the data registers. -/
structure Logical (s₀ : State) (k : Nat) (s : State) : Prop where
  le : k ≤ rr s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  frame : Frame [yR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  done : ∀ i < k, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)
  x : bytesAt s.mem (xP s₀ k) 64 = xBefore (B s₀) (rr s₀) (2 * k)

def view (s₀ : State) (k : Nat) (s : State) : State :=
  {s with gpr := fun r => match r with
    | .rbx => bB s₀ k | .rbp => yE s₀ k | .r12 => yO s₀ k
    | .r13 => sc s₀ | .r14 => BitVec.ofNat 64 (rr s₀ - k) | .r15 => xP s₀ k
    | _ => s.gpr r}

theorem Logical.old {s₀ s : State} {k : Nat} (h : Logical s₀ k s) :
    BlockMix.Inv s₀ k (view s₀ k s) :=
  ⟨h.le, h.rd, h.wr, h.rsp, rfl, rfl, rfl, rfl, rfl, rfl, h.frame, h.saved, h.done, h.x⟩

theorem Logical.of_old {s₀ s : State} {k : Nat} (h : BlockMix.Inv s₀ k s) : Logical s₀ k s :=
  ⟨h.k_le, h.rd, h.wr, h.rsp, h.frame, h.saved, h.done, h.x⟩

structure Inv (s₀ : State) (k : Nat) (s : State) : Prop extends Logical s₀ k s where
  words : Words (sc s₀) (memWords s.mem (xP s₀ k)) s
  metadata : Meta (sc s₀) (bB s₀ k) (yE s₀ k) (yO s₀ k) (BitVec.ofNat 64 (rr s₀ - k)) s.mem

theorem scratch_frame {s₀ : State} {m m' : Mem} (hf : Frame [⟨sc s₀, 64⟩] m m') :
    Frame [yR s₀, scR s₀, stkR s₀] m m' :=
  hf.sub fun R hR => by
    simp only [List.mem_singleton] at hR; subst R
    exact ⟨scR s₀, by simp, Region.sub_prefix (by decide)⟩

theorem scratch_oldframe {s₀ : State} {m m' : Mem} (hf : Frame [⟨sc s₀, 64⟩] m m') :
    Frame [slot s₀ 0, ⟨sc s₀, 64⟩, stkR s₀] m m' := hf.mono (by simp)

theorem x_s {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k ≤ rr s₀) :
    Region.Disjoint ⟨xP s₀ k, 64⟩ ⟨sc s₀, 64⟩ := by
  cases k with
  | zero =>
    exact (hp.b_s.sub_left (b_sub hp (by have := hp.pos; omega))).sub_right (Region.sub_prefix (by decide))
  | succ k => exact slot_s hp (by omega)

theorem Logical.scratch {s₀ s t : State} (hp : Pre s₀) {k : Nat} (h : Logical s₀ k s)
    (hf : Frame [⟨sc s₀, 64⟩] s.mem t.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (sp : t.gpr .rsp = s.gpr .rsp) : Logical s₀ k t := by
  have keep : ∀ a, Region.Disjoint ⟨a, 64⟩ ⟨sc s₀, 64⟩ → bytesAt t.mem a 64 = bytesAt s.mem a 64 :=
    fun a hd => Memory.frame_bytesAt hf (fun R hR => by
      simp only [List.mem_singleton] at hR; subst R; exact hd) (by decide)
  refine ⟨h.le, rd.trans h.rd, wr.trans h.wr, sp.trans h.rsp,
    h.frame.trans (scratch_frame hf), saved_keep hp (by have := hp.pos; omega) (scratch_oldframe hf) h.saved,
    fun i hi => ?_, ?_⟩
  · rw [keep (yE s₀ i) (slot_s hp (by have := h.le; omega)),
      keep (yO s₀ i) (slot_s hp (by have := h.le; omega))]
    exact h.done i hi
  · rw [keep (xP s₀ k) (x_s hp h.le), h.x]
end VG.Proof.Scrypt.X86_64.BlockMix.Fused
