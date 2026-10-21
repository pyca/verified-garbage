module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base

public import VerifiedGarbage.Proof.Mont.X86.ArgFar

import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Args
public import VerifiedGarbage.Proof.Mont.X86.Compact.Entry
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryArgs
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryMemory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.ArgWs

/-! # The prepared multiplication's cdecl arguments before its cache frame -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Mont.X86.Dynamic (ArgFar readSrc_keep)

def rawArg (i : Nat) : MemOp := at_ .esp (4 + 4 * i)

structure RawArgs (s : State) (W : Addr) (L : Nat) (A : Nat → BitVec 32) : Prop where
  read : ∀ i < 5, readSrc s (.mem (rawArg i)) = some (A i)
  far : ∀ i < 5, ArgFar s W L (rawArg i)

theorem RawArgs.of_keeps {s t : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32}
    (h : RawArgs s W L A) {rs : List Reg} (K : Keeps rs s t) (sp : .esp ∉ rs)
    (O : Outs W [(0, L)] s.mem t.mem) : RawArgs t W L A :=
  ⟨fun i hi => (readSrc_keep (h.far i hi) O (by simp) (K.1 _ sp) K.2.1 K.2.2).trans (h.read i hi),
    fun i hi => (h.far i hi).keep (K.1 _ sp)⟩

theorem RawArgs.of_upd {s t : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32}
    (h : RawArgs s W L A) {d : Reg} {v : BitVec 32} (U : Upd s t d v) (sp : d ≠ .esp) :
    RawArgs t W L A :=
  h.of_keeps U.keeps (by simpa using sp.symm) (by rw [U.mem]; exact Outs.refl _ _ _)

theorem rawArg_address (s : State) (i : Nat) : s.ea (rawArg i) = argAddr s i := rfl

theorem raw_args {s : State} (A : Compact.Entry s) :
    RawArgs s (Compact.wsOf s) (Compact.lenOf s) (arg s) := by
  constructor
  · intro i index
    change s.load32 (argAddr s i) = _
    have access : InRegions (s.rd ++ s.wr) (argAddr s i) 4 := by
      rw [A.rd]
      refine ⟨_, List.mem_append_left _ (List.mem_singleton_self _), ?_⟩
      rw [Compact.argument_offset A index]
      exact Offset.contains_base _ (by omega) (by omega)
    rw [State.load32, ite_eq_left access]
    rfl
  · intro i index j byte
    apply VG.Proof.Mont.X86.Dynamic.ofs_far
    intro hc
    apply A.argSeparate _ hc
    rw [rawArg_address, Compact.argument_offset A index, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by omega) (by omega)

theorem raw_ws {s : State} (A : Compact.Entry s) : Ws s (Compact.wsOf s) (Compact.lenOf s) := by
  refine ⟨?_, ?_⟩
  · rw [A.wr]
    exact List.mem_singleton_self _
  · rw [A.ws_toNat]
    exact A.bound

end VG.Proof.Mont.X86.PreparedSquare
