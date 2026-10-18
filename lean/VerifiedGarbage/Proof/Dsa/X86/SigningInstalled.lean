module

public import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
public import VerifiedGarbage.Proof.Dsa.X86.PackedKeyBuffers
public import VerifiedGarbage.Proof.Dsa.X86.SignSized

/-! # Signing original caller bytes after cdecl argument installation -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem signingInstalled_spec {s t : State} (A : SigningABI s)
    (I : Installed (argumentPointer s 9) ((arg s 10).toNat * 8) Entry.signArguments 2 4 6 s t) :
    let result := Spec.Dsa.signBytes (arg s 4).toNat (arg s 6).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 7) (arg s 8).toNat)
    WP isa (Entry.sized true (arg s 4).toNat (arg s 6).toNat) t fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus result ∧
      Spec.Rsa.bytesAt sf.mem (argumentPointer s 0) (2 * (arg s 6).toNat) =
        result.getD (List.replicate (2 * (arg s 6).toNat) 0) ∧
      Keeps powerClob t sf ∧
      StackOutputFrame (t.gpr .esp) (argumentPointer s 9) (argumentPointer s 0) usedBytes (2 * (arg s 6).toNat) t.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved t.mem (off (argumentPointer s 9)) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off (argumentPointer s 9)) regs Entry.savedRegisters := by
  dsimp only
  have L : 0 < (arg s 4).toNat ∧ 0 < (arg s 6).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega
  obtain ⟨Key, KeyBytes⟩ := I.input (by decide : (2, .p) ∈ Entry.signArguments) A.keyBound
    (by rw [A.rd, A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨Nonce, NonceBytes⟩ := I.input (by decide : (5, .nonce) ∈ Entry.signArguments) A.nonceBound
    (by rw [A.rd, A.wr]; simp) A.nonceScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowNonce.symm)
  obtain ⟨D, DigestBytes⟩ := I.input (by decide : (7, .digest) ∈ Entry.signArguments) A.digestBound
    (by rw [A.rd, A.wr]; simp) A.digestScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowDigest.symm)
  obtain ⟨Qptr, Gptr, Yptr, Xptr⟩ := I.pointers (by decide)
  obtain ⟨P, Q, G, Y, X, KeyValue⟩ := privateKey_buffers Key L.1 L.2
    (by have := A.keyLength; omega) KeyBytes Qptr Gptr Yptr Xptr
  apply signSized_spec (out := arg s 0) I.scr A.used A.lengths P Q G Y X Nonce D rfl rfl rfl rfl rfl rfl
    (congrArg BitVec.toNat (I.arguments (8, .digestLen) (by decide))) DigestBytes
    (I.arguments (0, .out) (by decide))
    (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using I.arguments (6, .qLen) (by decide))
    (by have := A.outBound; have := A.outLength; omega)
    ?_ (by rw [← A.outLength]; exact A.outScratch.symm)
    (by simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using A.keyLength)
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]) KeyValue
    (congrArg Spec.Dsa.decodeBE NonceBytes.symm)
  intro e k he
  rw [I.keeps.2.2, A.wr]
  refine ⟨_, List.mem_cons_self, Offset.contains_base _ (by have := A.outLength; omega) ?_⟩
  have := A.outBound
  have := A.outLength
  omega

end VG.Proof.Dsa.X86
