module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignFnInput

import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignRegions
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Spec.Weierstrass
/-! # Entering the wrapper preserves all sources and incoming arguments -/

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/SignEntryInput.lean`, which only this module imported.
section

/-! # Native cdecl inputs before reserving the two wrapper frames -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Proof.Rsa.X86.PrivChecked VG.Impl.RsaPkcs1Sig.X86.Sign VG.Proof.Bignum.X86
open VG.Proof.Dsa.X86 (allocated)

structure EntryInput (g : Geometry) (bs : Fin 8 → List Byte) (s : State) : Prop where
  valid : g.Valid
  stackFit : sigStack ≤ (s.gpr .esp).toNat
  base : g.stack = s.gpr .esp - 16 - BitVec.ofNat 32 VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes
  source : ∀ i, PublicBytes (g.sources i) (g.sourceLength i) (bs i) s
  outputWrite : InRegions s.wr (byteAddr g.output) g.length
  workspaceWrite : InRegions s.wr (byteAddr g.workspace) (8 * g.scratchLength)
  argumentsRead : InRegions (s.rd ++ s.wr) g.argumentsRegion.base 84
  arguments : ∀ j < 21, s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + 4 * j)) 32 = g.argument j
  returnSeparate : ∀ r ∈ bodyWrites g, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r

theorem EntryInput.enteredSp {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : EntryInput g bs s) : (entered s).gpr .esp = g.stack := by
  rw [entered, VG.Proof.Dsa.X86.allocated_esp, pushed_esp]
  exact h.base.symm

theorem EntryInput.savedAddr {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : EntryInput g bs s) : ((pushed savedRegisters s).gpr .esp).setWidth 64 = g.savedRegion.base := by
  have eq : (pushed savedRegisters s).gpr .esp = g.stack + BitVec.ofNat 32 VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes := by
    rw [← h.enteredSp]
    exact (BitVec.sub_add_cancel _ _).symm
  rw [eq]
  exact h.valid.offsetAddr (by decide)

theorem EntryInput.enteredFrame {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : EntryInput g bs s) : Frame [g.savedRegion] s.mem (entered s).mem := by
  have f := pushed_frame (rs := savedRegisters) (s := s) (by decide)
    (by change 16 ≤ _; have := h.stackFit; unfold sigStack at this; omega)
  unfold below at f
  rw [← pushed_esp] at f
  change Frame [⟨((pushed savedRegisters s).gpr .esp).setWidth 64, 16⟩] s.mem (entered s).mem at f
  rw [h.savedAddr] at f
  exact f

theorem entered_read {s : State} {p : Addr} {n : Nat} (read : InRegions (s.rd ++ s.wr) p n) :
    InRegions ((entered s).rd ++ (entered s).wr) p n := by
  obtain ⟨r, hr, hc⟩ := read
  refine ⟨r, ?_, hc⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact List.mem_append_left _ hr
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))

theorem entered_write {s : State} {p : Addr} {n : Nat} (write : InRegions s.wr p n) :
    InRegions (entered s).wr p n := by
  obtain ⟨r, hr, hc⟩ := write
  exact ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), hc⟩
end VG.Proof.RsaPkcs1Sig.X86.Sgn
end

end

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Proof.Rsa.X86.PrivChecked VG.Proof.Bignum.X86

theorem EntryInput.enteredSource {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : EntryInput g bs s) (i : Fin 8) :
    PublicBytes (g.sources i) (g.sourceLength i) (bs i) (entered s) := by
  refine ⟨(h.source i).fits, entered_read (h.source i).read, ?_⟩
  have sep : ∀ r ∈ [g.savedRegion], (g.sourceRegion i).Disjoint r := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ((h.valid.stackSources i).sub_left h.valid.savedSub).symm
  exact (Rsa.rsa_bytes_frame h.enteredFrame (by have := (h.source i).fits; omega) sep).trans (h.source i).bytes

theorem EntryInput.enteredArguments {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : EntryInput g bs s) (j : Nat) (hj : j < 21) :
    (entered s).mem.readW (byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + 4 * j)) 32 = g.argument j := by
  have sep : ∀ r ∈ [g.savedRegion], g.argumentsRegion.Disjoint r := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact (h.valid.stackArguments.sub_left h.valid.savedSub).symm
  have eq := h.enteredFrame.readW (r := g.argumentsRegion)
    (Offset.contains_base _ (by omega : 4 * j + 32 / 8 ≤ 84) (by omega)) sep (by decide : 32 / 8 < 2 ^ 64)
  have address : g.argumentsRegion.base + BitVec.ofNat 64 (4 * j) =
      byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + 4 * j) :=
    Offset.add_add _ _ _
  change (entered s).mem.readW (g.argumentsRegion.base + BitVec.ofNat 64 (4 * j)) 32 =
    s.mem.readW (g.argumentsRegion.base + BitVec.ofNat 64 (4 * j)) 32 at eq
  rw [address] at eq
  exact eq.trans (h.arguments j hj)

theorem EntryInput.ready {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : EntryInput g bs s) : FnInput g bs s := by
  refine ⟨h.stackFit, ⟨h.valid, h.enteredSp, ?_, h.enteredSource,
    entered_write h.outputWrite, entered_write h.workspaceWrite,
    entered_read h.argumentsRead, h.enteredArguments⟩, h.returnSeparate⟩
  refine ⟨by have := h.valid.stackHigh; omega, ?_⟩
  change (⟨byteAddr g.stack, VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes⟩ : Region) ∈
    ⟨byteAddr ((entered s).gpr .esp), VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes⟩ :: (pushed savedRegisters s).wr
  rw [h.enteredSp]
  exact List.mem_cons_self
end VG.Proof.RsaPkcs1Sig.X86.Sgn
