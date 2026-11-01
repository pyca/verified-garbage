module

import VerifiedGarbage.Proof.MillerRabin.X86.TimingStage
public import VerifiedGarbage.Proof.MillerRabin.X86.TableMath
import VerifiedGarbage.Proof.MillerRabin.X86.TimingCopy
import VerifiedGarbage.Proof.MillerRabin.X86.TimingAttach
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingPrivate
import VerifiedGarbage.Proof.MillerRabin.X86.TimingSequences
import VerifiedGarbage.Proof.MillerRabin.X86.TableInit
import VerifiedGarbage.Proof.MillerRabin.X86.TableStep
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.MillerRabin.X86.Stage

/-! # Power-table construction reuses the prepared modulus at every product -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86

structure TableSecret where
  c : Nat
  A : Nat → Nat
  V : Nat → BitVec 32
  slots : List Nat

def TableStart (g : Geometry) (capacity : Nat) (p : BitVec 32) (σ : TableSecret) (s : State) : Prop :=
  Stage g capacity σ.c p σ.A initialArrays σ.V σ.slots s ∧ σ.c % 2 = 1 ∧ σ.A aX < σ.c

def TableStage (g : Geometry) (capacity : Nat) (p : BitVec 32) (k : Nat) (σ : TableSecret) (s : State) : Prop :=
  Stage g capacity σ.c p (tableValues σ.A σ.c g.w k) (tableArrays k) σ.V σ.slots s ∧
    σ.c % 2 = 1 ∧ σ.A aX < σ.c

theorem tableInit_relCT {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} :
    RelCT isa (Two g (TableStart g capacity p))
      (seqs [copy aTable aOne, copy (aTable + 1) aX, copy aY aX]) (Two g (TableStage g capacity p 0)) := by
  refine private_lift (RelCT.seq (copy_relCT v aTable aOne (by decide) (by decide))
    (RelCT.seq (copy_relCT v (aTable + 1) aX (by decide) (by decide))
      (copy_relCT v aY aX (by decide) (by decide)))) ?_
  intro σ s ⟨S, odd, lt⟩
  exact WP.mono (tableInit_ok v S) fun _ R => ⟨R.1, odd, lt⟩

theorem tableStep_relCT {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity k : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (index : k < 14) :
    RelCT isa (Two g (TableStage g capacity p k))
      (.seq (mulY name code aX) (copy (aTable + k + 2) aY)) (Two g (TableStage g capacity p (k + 1))) := by
  refine private_attach ?_ ?_ (fun _ _ H => H.1.data.context)
  · apply RelCT.seq (Q := VG.X86.Taint.Agree (roundTaint [.edi]))
      ((mulY_relCT (p := p) verified noSp stack v length (by change 5 < 8 ∧ 5 ≠ 2 ∧ 5 ≠ 3; decide)).mono ?_ (fun _ _ H => H))
    · exact (copy_relCT v (aTable + k + 2) aY (by unfold aTable; omega) (by decide)).mono
        (fun _ _ H => H) (fun _ _ H => H.2.2)
    · intro s t ⟨P, ⟨σ, S, oddS, ltS⟩, ⟨ρ, T, oddT, ltT⟩⟩
      refine ⟨P, S.mulInput oddS (by simp [tableArrays, initialArrays]) ?_,
        T.mulInput oddT (by simp [tableArrays, initialArrays]) ?_⟩
      · rw [tableValues_x]; exact ltS
      · rw [tableValues_x]; exact ltT
  · intro σ s ⟨S, odd, lt⟩
    exact WP.mono (tableStep_ok verified noSp stack v S length odd lt index) fun _ R => ⟨R.1, odd, lt⟩

theorem table_relCT {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (length : g.L = 8 * capacity) :
    RelCT isa (Two g (TableStart g capacity p)) (table name code) (Two g (TableStage g capacity p 14)) := by
  unfold table
  exact seqs_append_relCT _ _ (tableInit_relCT v)
    (seqs_range_relCT 14 _ (fun k => Two g (TableStage g capacity p k))
      (fun _ index => tableStep_relCT verified noSp stack v length index))

end VG.Proof.MillerRabin.X86
