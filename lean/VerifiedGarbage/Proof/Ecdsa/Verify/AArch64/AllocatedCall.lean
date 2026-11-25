module

public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Allocated
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedFrame
public import VerifiedGarbage.Proof.Ed25519.AArch64.Step
public import VerifiedGarbage.Proof.Mont.AArch64.Words
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Block

/-! Calls of the allocated point kernels preserve the same memory and public
counter contracts. Their link is saved in a vector lane the kernels never write. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.AllocatedCall
open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)
open VG.Impl.Ecdsa.Verify.AArch64.P256Allocated (pointFn)

/-- Point contracts depend on memory, the scratch pointer, the counter and symbols. -/
def Stable (P : State → Prop) : Prop :=
  ∀ {s t}, Keeps allocatedRegs s t → t.syms = s.syms → P s → P t

def saved (s : State) : State := s.setV .v31 (setLane (s.v .v31) 64 0 (s.gpr .x30))
def restored (s : State) : State := s.write .x .x30 (laneOf s .v31 0)

theorem entry_keeps (s : State) : Keeps allocatedRegs s s.callEntry :=
  ⟨fun r hr => State.callEntry_gpr s (by revert hr; cases r <;> decide), rfl, rfl, rfl, rfl⟩

theorem saved_keeps (s : State) : Keeps allocatedRegs s (saved s) :=
  ⟨fun _ _ => by rw [saved, gpr_setV], rfl, rfl, rfl, rfl⟩

theorem restored_keeps (s : State) : Keeps allocatedRegs s (restored s) :=
  ⟨fun r hr => gpr_write_of_ne s .x (laneOf s .v31 0) (by revert hr; cases r <;> decide), rfl, rfl, rfl, rfl⟩

theorem frame_of_keeps {s t : State} {base : Addr} {W : List (Nat × Nat)}
    (h : Keeps allocatedRegs s t) : AllocatedFrame allocatedRegs base W s t :=
  ⟨⟨h.gpr, h.rd, h.wr, h.sp⟩, by rw [h.mem]; exact Unch.refl _ _ _⟩

theorem saved_exec (s : State) :
    Exec isa (.block [.vop (.ins .d2 .v31 0 .x30)]) s [] (saved s) := by
  apply Exec.block
  have he : isa.exec (.vop (.ins .d2 .v31 0 .x30)) s = some (saved s) := exec_ins (s := s) (v := .v31) (r := .x30) (l := 0) (by decide)
  rw [execBlock, he]
  rfl

theorem restored_exec (s : State) :
    Exec isa (.block [.umov .x .x30 .v31 0]) s [] (restored s) := by
  apply Exec.block
  have he : isa.exec (.umov .x .x30 .v31 0) s = some (restored s) := exec_umov (s := s) (v := .v31) (r := .x30) (l := 0) (by decide)
  rw [execBlock, he]
  rfl

theorem saved_lane (s : State) : laneOf (saved s) .v31 0 = s.gpr .x30 := by
  rw [saved, laneOf_setV, ite_eq_left rfl, extract_setLane64 _ _ (by decide) (by decide), ite_eq_left rfl]

/-- Lift a point proof through its internal call, without an ABI assumption
on x26–x28 or x30, which the outer verifier saves and restores. -/
theorem call_wp {name : String} {body : Prog isa} {base : Addr} {W : List (Nat × Nat)}
    {P Q : State → Prop} (hp : Stable P) (hq : Stable Q)
    (hv : ∀ i ∈ instrs body, vdstOf i ≠ some .v31)
    (hb : ∀ s, P s → WP isa body s fun t => AllocatedFrame allocatedRegs base W s t ∧ Q t)
    {s : State} (hs : P s) :
    WP isa (.call name (pointFn body)) s fun t => AllocatedFrame allocatedRegs base W s t ∧ Q t := by
  let e := s.callEntry
  let a := saved e
  have ka : Keeps allocatedRegs s a := (entry_keeps s).trans (saved_keeps e)
  obtain ⟨tr, b, eb, kb, qb⟩ := hb a (hp ka rfl hs)
  have bv : b.v .v31 = a.v .v31 := Exec.vec hv eb
  have link : laneOf b .v31 0 = e.gpr .x30 := by
    rw [laneOf, bv]
    exact saved_lane e
  refine ⟨_, restored b, Exec.call (call_callEntry s)
    (.seq (saved_exec e) (.seq eb (restored_exec b))) ?_,
    (frame_of_keeps ka).trans (kb.trans (frame_of_keeps (restored_keeps b))), hq (restored_keeps b) rfl qb⟩
  simp only [isa, ret, restored, gpr_write_self, BitVec.setWidth_eq, link, e, eq_self, ite_true]

/-- Relations used by point timing proofs ignore the internal call registers. -/
def Stable₂ (P : State → State → Prop) : Prop :=
  ∀ {s₁ s₂ t₁ t₂}, Keeps allocatedRegs s₁ t₁ → Keeps allocatedRegs s₂ t₂ →
    t₁.syms = s₁.syms → t₂.syms = s₂.syms → P s₁ s₂ → P t₁ t₂

theorem call_relCT {name : String} {body : Prog isa} {P Q : State → State → Prop}
    (hp : Stable₂ P) (hq : Stable₂ Q) (hb : RelCT isa P body Q) :
    RelCT isa P (.call name (pointFn body)) Q := by
  have save : RelCT isa P (.block [.vop (.ins .d2 .v31 0 .x30)]) P := by
    intro s t ts tt s' t' h es et
    obtain ⟨rfl,rfl⟩ := Exec.det es (saved_exec s)
    obtain ⟨rfl,rfl⟩ := Exec.det et (saved_exec t)
    exact ⟨rfl,hp (saved_keeps s) (saved_keeps t) rfl rfl h⟩
  have restore : RelCT isa Q (.block [.umov .x .x30 .v31 0]) Q := by
    intro s t ts tt s' t' h es et
    obtain ⟨rfl,rfl⟩ := Exec.det es (restored_exec s)
    obtain ⟨rfl,rfl⟩ := Exec.det et (restored_exec t)
    exact ⟨rfl,hq (restored_keeps s) (restored_keeps t) rfl rfl h⟩
  have hfn := save.seq (hb.seq restore)
  intro s t ts tt s' t' h es et
  cases es with
  | call cs bs rs =>
    cases et with
    | call ct bt rt =>
      rw [call_callEntry,Option.some.injEq] at cs ct
      subst cs ct
      simp only [isa,ret] at rs rt
      split at rs <;> cases rs
      split at rt <;> cases rt
      simpa only [isa,List.map_nil,List.nil_append,List.append_nil] using
        hfn _ _ _ _ _ _ (hp (entry_keeps s) (entry_keeps t) rfl rfl h) bs bt

end VG.Proof.Ecdsa.Verify.AArch64.AllocatedCall
