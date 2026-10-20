module
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.Rsa.Arm.PrivGeometry

import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Arguments retained in six stack slots across the three RSA calls -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont

def slotValue (g : PrivGeometry) (i : Nat) : BitVec 32 :=
  match i with
  | 0 => g.output | 1 => g.sources 0 | 2 => BitVec.ofNat 32 g.length
  | 3 => g.sources 1 | 4 => BitVec.ofNat 32 g.exponentLength | _ => g.sources 2

def PrivSlots (g : PrivGeometry) (mem : Mem) : Prop :=
  ∀ i < 6, mem.readW (off (State.addr g.stack) (64 + 4 * i)) 32 = slotValue g i

theorem PrivSlots.after {g : PrivGeometry} {m m' : Mem} {regions : List Region}
    (h : PrivSlots g m) (frame : Frame regions m m')
    (sep : ∀ r ∈ regions, (⟨off (State.addr g.stack) 64, 24⟩ : Region).Disjoint r) : PrivSlots g m' := by
  have eq := WorkspaceEq.of_frame (base := off (State.addr g.stack) 64) (size := 24) (by decide) frame sep
  intro i hi
  have word := eq.word (d := 4 * i) (bits := 32) (by omega)
  have address : off (off (State.addr g.stack) 64) (4 * i) = off (State.addr g.stack) (64 + 4 * i) :=
    Offset.add_add _ 64 (4 * i)
  rw [address] at word
  exact word.trans (h i hi)
end VG.Proof.Rsa.Arm
