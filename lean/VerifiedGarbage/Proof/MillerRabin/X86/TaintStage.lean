module

public import VerifiedGarbage.Proof.MillerRabin.X86.TaintInput
public import VerifiedGarbage.Proof.MillerRabin.X86.Snapshot

/-! # Correctness reestablishes public widths between borrowed arithmetic pieces -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Spec.Rsa.Mont (arrAt wOf)

theorem capacity_min {w bytes : Nat} (lower : 4 ≤ w) (fit : arrAt w 28 ≤ bytes) : 1600 ≤ bytes := by
  have mono : arrAt 4 28 ≤ arrAt w 28 :=
    Nat.add_le_add_left (Nat.mul_le_mul_left 28 (Nat.mul_le_mul_left 8
      (Nat.add_le_add_right lower 2))) 256
  exact Nat.le_trans (by decide : 1600 ≤ arrAt 4 28) (mono.trans fit)

namespace PieceInput

theorem of_stage {σ s : State} {base : Addr} {bytes w : Nat} {sp len : BitVec 32}
    (initial : PieceInput base bytes w sp len σ) (facts : RoundFacts σ base bytes w)
    (h : Stage base bytes w σ s) : PieceInput base bytes w sp len s := by
  refine ⟨h.context, h.room, h.wr.trans initial.wr, h.stack.trans initial.stack, initial.capacity,
    h.width facts.fit initial.width, ?_⟩
  rw [← initial.stack]
  exact (h.read_stack32 facts.fit (by decide) (.inl (by decide))).trans
    (by rw [initial.stack]; exact initial.length)

theorem of_snapshot {s σ : State} (A : RoundABI s) (ready : SnapshotReady s σ) :
    PieceInput (wsOf s) (bytesOf s) (wOf s.mem (wsOf s))
      ((allocFrame VG.Impl.MillerRabin.X86.frameBytes s).gpr .esp) (arg s 1) σ := by
  have facts := round_facts_of (bytes := bytesOf s) rfl ready.width ready.layout ready.prepared ready.length
  refine ⟨ready.context, ready.room, ?_, ready.sp, ?_, facts.width, ?_⟩
  · rw [ready.wr, allocFrame_wr, A.wr]
    rfl
  · exact capacity_min facts.lower facts.fit
  · rw [← ready.sp]
    exact ready.length

theorem pieces_ct {σ₁ σ₂ : State} {base : Addr} {bytes w : Nat} {sp len : BitVec 32} {c : Prog isa}
    (initial₁ : PieceInput base bytes w sp len σ₁) (initial₂ : PieceInput base bytes w sp len σ₂)
    (facts₁ : RoundFacts σ₁ base bytes w) (facts₂ : RoundFacts σ₂ base bytes w)
    (cert : PieceCert c) :
    RelCT isa (fun s t => Stage base bytes w σ₁ s ∧ Stage base bytes w σ₂ t) c (fun _ _ => True) := by
  obtain ⟨hc, checked⟩ := cert
  exact RelCT.taint (A := taint) pieceTaint (fun _ _ ⟨h₁, h₂⟩ =>
    (initial₁.of_stage facts₁ h₁).agree (initial₂.of_stage facts₂ h₂)) checked

end PieceInput
end VG.Proof.MillerRabin.X86
