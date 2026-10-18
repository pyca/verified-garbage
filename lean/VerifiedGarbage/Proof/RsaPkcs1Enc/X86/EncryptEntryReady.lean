module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptEntryInput
public import VerifiedGarbage.Proof.Rsa.BytesFrame

/-! # Entering the wrapper preserves all sources and incoming arguments -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86 VG.Proof.Rsa.X86.PrivChecked VG.Proof.Bignum.X86

theorem EntryInput.enteredSource {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : EntryInput g bs s) (i : Fin 5) :
    PublicBytes (g.sources i) (g.sourceLength i) (bs i) (entered s) := by
  refine ⟨(h.source i).fits, entered_read (h.source i).read, ?_⟩
  have sep : ∀ r ∈ [g.savedRegion], (g.sourceRegion i).Disjoint r := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ((h.valid.stackSources i).sub_left h.valid.savedSub).symm
  exact (Rsa.rsa_bytes_frame h.enteredFrame (by have := (h.source i).fits; omega) sep).trans (h.source i).bytes

theorem EntryInput.enteredArguments {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : EntryInput g bs s) (j : Nat) (hj : j < 14) :
    (entered s).mem.readW (byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes + 20 + 4 * j)) 32 = g.argument j := by
  have sep : ∀ r ∈ [g.savedRegion], g.argumentsRegion.Disjoint r := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact (h.valid.stackArguments.sub_left h.valid.savedSub).symm
  have eq := h.enteredFrame.readW (r := g.argumentsRegion)
    (Offset.contains_base _ (by omega : 4 * j + 32 / 8 ≤ 56) (by omega)) sep (by decide : 32 / 8 < 2 ^ 64)
  have address : g.argumentsRegion.base + BitVec.ofNat 64 (4 * j) =
      byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes + 20 + 4 * j) :=
    Offset.add_add _ _ _
  change (entered s).mem.readW (g.argumentsRegion.base + BitVec.ofNat 64 (4 * j)) 32 =
    s.mem.readW (g.argumentsRegion.base + BitVec.ofNat 64 (4 * j)) 32 at eq
  rw [address] at eq
  exact eq.trans (h.arguments j hj)

theorem EntryInput.ready {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : EntryInput g bs s) : FnInput g bs s := by
  refine ⟨h.stackFit, ⟨h.valid, h.enteredSp, ?_, h.enteredSource,
    entered_write h.outputWrite, entered_write h.workspaceWrite,
    entered_read h.argumentsRead, h.enteredArguments⟩, h.returnSeparate⟩
  refine ⟨by have := h.valid.stackHigh; omega, ?_⟩
  change (⟨byteAddr g.stack, VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes⟩ : Region) ∈
    ⟨byteAddr ((entered s).gpr .esp), VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes⟩ :: (pushed savedRegisters s).wr
  rw [h.enteredSp]
  exact List.mem_cons_self
end VG.Proof.RsaPkcs1Enc.X86.Enc
