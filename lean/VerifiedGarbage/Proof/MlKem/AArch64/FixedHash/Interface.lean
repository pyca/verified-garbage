module
public import VerifiedGarbage.Impl.MlKem.AArch64.FixedHashCallers
public import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Spec.Sha3
abbrev HashFn := Impl.MlKem.AArch64.FixedHashCallers.HashFn

def HashCorrect (hash : HashFn) (sc : Reg) (st wk rate sfx : Nat) (ins outs : List Piece) : Prop :=
 ∀{s₀ : AArch64.State},HSetup sc st wk rate s₀ → sfx<256 → ins≠[] →
 (∀p∈ins,PieceOk sc st wk s₀ false p) → (∀p∈outs,PieceOk sc st wk s₀ true p) →
 outs.Pairwise (fun p q=>(preg s₀ p).Disjoint (preg s₀ q)) →
 WP isa (hash sc st wk rate sfx ins outs) s₀ fun s'=>
  Kept (STr sc st s₀::WKr sc wk s₀::below s₀.sp 16::outs.map (preg s₀)) s₀ s' ∧
  Outs s₀ s'.mem rate (absorb rate (pad rate (BitVec.ofNat 8 sfx) (ins.map (pbytes s₀)).flatten)) 0 outs

theorem hashWith_correct (v : Proof.Sha3.AArch64.Permutation) (sc : Reg)
 (st wk rate sfx : Nat) (ins outs : List Piece) :
 HashCorrect (hashWith v.callee) sc st wk rate sfx ins outs :=
 fun hS hsfx hne hin hout hpw=>hashWith_ok v hS hsfx hne hin hout hpw
end VG.Proof.MlKem.AArch64.FixedHash
