module

public import VerifiedGarbage.Proof.Rsa.X86.RvBase

/-! # Preservation of narrow arrays, wide arrays and scalar slots -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

section
variable {g : Geo} {s0 s t : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

/-- The arrays read with `w` that a step with `w` words does not write. -/
theorem KS.arrs_w {js ds : List Nat} (h : KS g s0 A live AW liveW V ls s) (k : Keep g.B g.w js ds s.mem t.mem)
    (hl : ∀ j ∈ live, ∀ i ∈ js, i ≠ j) (hds : ∀ d ∈ ds, SlotOk d) : Arrs t.mem g.B g.w A live :=
  h.arrs.keepOf k hl (fun d hd => (hds d hd).2.1) fun j hj => h.ws.fit64 (h.live_lt j hj)

/-- The arrays read with `W` that a step with `w` words does not write. -/
theorem KS.arrsW_w {js ds : List Nat} (h : KS g s0 A live AW liveW V ls s) (k : Keep g.B g.w js ds s.mem t.mem)
    (hl : ∀ j ∈ liveW, ∀ i ∈ js, i / 2 ≠ j) (hds : ∀ d ∈ ds, SlotOk d) : Arrs t.mem g.B g.W AW liveW :=
  h.arrsW.keepOf k.toW (fun j hj i hi => by
      simp only [List.mem_map] at hi
      obtain ⟨i', hi', rfl⟩ := hi
      exact hl j hj i' hi') (fun d hd => (hds d hd).2.1) fun j hj => h.wsW.fit64 (h.liveW_lt j hj)

/-- The arrays read with `w` that a step with `W` words does not write. -/
theorem KS.arrs_W {js ds : List Nat} (h : KS g s0 A live AW liveW V ls s) (k : Keep g.B g.W js ds s.mem t.mem)
    (hl : ∀ j ∈ live, ∀ i ∈ js, j / 2 ≠ i) (hds : ∀ d ∈ ds, SlotOk d) : Arrs t.mem g.B g.w A live :=
  h.arrs.keepOf k.ofW (fun j hj i hi => by
      simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hi
      obtain ⟨i', hi', e⟩ := hi
      have := hl j hj i' hi'
      rcases e with rfl | rfl <;> omega) (fun d hd => (hds d hd).2.1) fun j hj => h.ws.fit64 (h.live_lt j hj)

/-- The arrays read with `W` that a step with `W` words does not write. -/
theorem KS.arrsW_W {js ds : List Nat} (h : KS g s0 A live AW liveW V ls s) (k : Keep g.B g.W js ds s.mem t.mem)
    (hl : ∀ j ∈ liveW, ∀ i ∈ js, i ≠ j) (hds : ∀ d ∈ ds, SlotOk d) : Arrs t.mem g.B g.W AW liveW :=
  h.arrsW.keepOf k hl (fun d hd => (hds d hd).2.1) fun j hj => h.wsW.fit64 (h.liveW_lt j hj)

/-- The header words a step does not write. -/
theorem KS.sl_keep {js ds : List Nat} {v : Nat} (h : KS g s0 A live AW liveW V ls s)
    (k : Keep g.B v js ds s.mem t.mem) (hl : ∀ d ∈ ls, ∀ e ∈ ds, d + 4 ≤ e ∨ e + 4 ≤ d) :
    ∀ d ∈ ls, slot t.mem g.B d = V d := fun d hd => by
  rw [k.slot (h.ls_ok d hd).2.1 (fun e he => hl d hd e he), h.sl d hd]

end
end VG.Proof.Rsa.X86.Recover
