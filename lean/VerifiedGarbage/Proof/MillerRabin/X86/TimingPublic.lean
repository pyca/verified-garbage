module

public import VerifiedGarbage.Proof.MillerRabin.X86.ArithmeticTiming
public import VerifiedGarbage.Proof.MillerRabin.X86.EntryTiming

/-! # Only pointers, lengths and limb counts are shared between timing runs -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Spec.Rsa.Mont (wOf)

structure RoundPublic (s t : State) : Prop where
  stack : s.gpr .esp = t.gpr .esp
  args : ∀ i, i < 2 → arg s i = arg t i
  width : wOf s.mem (wsOf s) = wOf t.mem (wsOf t)

namespace RoundPublic

theorem workspace {s t : State} (P : RoundPublic s t) : wsOf s = wsOf t :=
  congrArg (BitVec.setWidth 64) (P.args 0 (by decide))

theorem bytes {s t : State} (P : RoundPublic s t) : bytesOf s = bytesOf t :=
  congrArg (fun x : BitVec 32 => x.toNat * 8) (P.args 1 (by decide))

theorem allocated_sp {s t : State} (P : RoundPublic s t) :
    (allocFrame 1132 s).gpr .esp = (allocFrame 1132 t).gpr .esp := by
  simp only [allocFrame_esp, P.stack]

theorem entry_input {s t u : State} (P : RoundPublic s t) (B : RoundABI t) (entry : EntryReady t u) :
    PieceInput (wsOf s) (bytesOf s) (wOf s.mem (wsOf s)) ((allocFrame 1132 s).gpr .esp) (arg s 1) u := by
  have second := PieceInput.of_entry B entry
  have width := P.width
  rw [← P.workspace] at second width
  rw [← width, ← P.bytes, ← P.allocated_sp, ← P.args 1 (by decide)] at second
  exact second

theorem snapshot_context {s t σ₁ σ₂ : State} (P : RoundPublic s t) (A : RoundABI s) (B : RoundABI t)
    (ready₁ : SnapshotReady s σ₁) (ready₂ : SnapshotReady t σ₂) :
    TimingContext σ₁ σ₂ (wsOf s) (bytesOf s) (wOf s.mem (wsOf s))
      ((allocFrame 1132 s).gpr .esp) (arg s 1) := by
  have initial₂ := PieceInput.of_snapshot B ready₂
  simp only [VG.Impl.MillerRabin.X86.frameBytes] at initial₂
  have facts₁ := round_facts_of (bytes := bytesOf s) rfl ready₁.width ready₁.layout ready₁.prepared ready₁.length
  have facts₂ := round_facts_of (bytes := bytesOf t) rfl ready₂.width ready₂.layout ready₂.prepared ready₂.length
  have width := P.width
  rw [← P.workspace] at initial₂ facts₂ width
  rw [← width, ← P.bytes, ← P.allocated_sp, ← P.args 1 (by decide)] at initial₂
  rw [← width, ← P.bytes] at facts₂
  exact ⟨PieceInput.of_snapshot A ready₁, initial₂, facts₁, facts₂, rfl⟩

theorem tail_second {s t σ : State} (P : RoundPublic s t) (ready : SnapshotReady t σ) :
    σ.mem.readW (off (wsOf s) (Spec.Rsa.Mont.arrAt (wOf s.mem (wsOf s)) 27 + 8 * wOf s.mem (wsOf s))) 64 =
      BitVec.twoPow 64 ((Spec.Rsa.splitTwos (val32 σ.mem (wsOf s) 256 (2 * wOf s.mem (wsOf s)) - 1)).1 % 64) := by
  have tail := prepared_tail ready.width ready.prepared
  have width := P.width
  rw [← P.workspace] at tail width
  rw [← width] at tail
  exact tail

end RoundPublic
end VG.Proof.MillerRabin.X86
