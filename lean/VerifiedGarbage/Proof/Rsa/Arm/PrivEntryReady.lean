module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivEntryInput
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Entering both frames preserves every input and incoming stack argument -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont

theorem PrivEntryInput.enteredSource {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivEntryInput g bs s) (i : Fin 8) :
    PublicBytes (g.sources i) (g.sourceLength i) (bs i) (entered s) := by
  refine ⟨(h.source i).fits, entered_read (h.source i).read, ?_⟩
  have sep : ∀ r ∈ [g.savedRegion], (g.sourceRegion i).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ((h.valid.stackSources i).sub_left h.valid.savedSub).symm
  exact (rsa_bytes_frame h.enteredFrame (by have := (h.source i).fits; omega) sep).trans (h.source i).bytes

theorem PrivEntryInput.enteredArguments {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivEntryInput g bs s) (j : Nat) (hj : j < 16) :
    (entered s).mem.readW (off (State.addr g.stack) (arg j)) 32 = g.argument j := by
  have sep : ∀ r ∈ [g.savedRegion], g.argumentsRegion.Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact (h.valid.stackArguments.sub_left h.valid.savedSub).symm
  have eq := (WorkspaceEq.of_frame (base := g.argumentsRegion.base) (size := 64) (by decide) h.enteredFrame sep).word
    (d := 4 * j) (bits := 32) (by omega)
  have address : off g.argumentsRegion.base (4 * j) = off (State.addr g.stack) (arg j) :=
    Offset.add_add _ (frameBytes + 56) (4 * j)
  rw [address] at eq
  rw [eq]
  have incoming := h.arguments j hj
  rw [h.argumentsAddr, address] at incoming
  exact incoming

theorem PrivEntryInput.ready {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivEntryInput g bs s) : PrivFnInput g bs s := by
  refine ⟨h.stackFit, ⟨h.valid, h.enteredSp, ?_, h.enteredSource,
    entered_write h.outputWrite, entered_write h.workspaceWrite, ?_, h.enteredArguments⟩,
    h.output, h.modulus, h.count⟩
  · refine ⟨by have := h.valid.stackHigh; omega, ?_⟩
    change (⟨State.addr g.stack, frameBytes⟩ : Region) ∈
      ⟨State.addr (entered s).sp, frameBytes⟩ :: (pcPushed s).wr
    rw [h.enteredSp]
    exact List.mem_cons_self
  · rw [← h.argumentsAddr]
    exact entered_read h.argumentsRead
end VG.Proof.Rsa.Arm
