module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.Copy
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptScratch

/-! # Copy the given private exponent to the end of its fixed-width buffer -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

def dOffset (g : Geometry) : Nat := sD + g.length - g.privateLength
def dPointer (g : Geometry) : BitVec 32 := g.workspace + BitVec.ofNat 32 (dOffset g)

theorem Context.copyDContext {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) : CopyCtx s (g.sources 2) (dPointer g) g.privateLength := by
  have kmax := h.valid.maxLength
  have len : g.privateLength ≤ 1024 := Nat.le_trans h.valid.privateFits h.valid.maxLength
  have srcFit : (g.sources 2).toNat + g.privateLength ≤ 2 ^ 32 := (h.sources 2).fits
  have fit : dOffset g + g.privateLength ≤ 8448 := by
    have := h.valid.privateFits
    unfold dOffset sD
    omega
  have start : dOffset g < 8448 := by unfold dOffset sD; omega
  have dstFit : (dPointer g).toNat + g.privateLength ≤ 2 ^ 32 := h.valid.scratchFit fit start
  have dstAddr : byteAddr (dPointer g) = (g.scratch (dOffset g) g.privateLength).base :=
    h.valid.scratchAddress start
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [byteAddr_add (by omega)]
    exact CallLay.inRegions_sub (off := i) (h.sources 2).read (by change i + 1 ≤ g.privateLength; omega)
      (by change g.privateLength < 2 ^ 64; omega)
  · intro i hi
    rw [byteAddr_add (by omega), dstAddr]
    change InRegions s.wr (byteAddr g.workspace + BitVec.ofNat 64 (dOffset g) + BitVec.ofNat 64 i) 1
    rw [Offset.add_add]
    exact h.scratchWrite (d := dOffset g + i) (by omega)
  · intro i hi j hj eq
    rw [byteAddr_add (by omega), byteAddr_add (by omega)] at eq
    apply (h.valid.sourcesWorkspace 2) (byteAddr (g.sources 2) + BitVec.ofNat 64 i)
    · exact Offset.contains_base _ (by change i + 1 ≤ g.privateLength; omega) (by omega)
    · rw [eq, dstAddr]
      exact h.valid.scratchSub fit _ (Offset.contains_base _ (by omega) (by omega))
  · intro i hi j hj eq
    rw [byteAddr_add (by omega), byteAddr_add (by omega)] at eq
    have same := (BitVec.add_right_inj _).mp eq
    have nums := congrArg BitVec.toNat same
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega)] at nums
    exact nums

theorem copyD_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) (src : s.gpr .esi = g.sources 2) (dst : s.gpr .ebx = dPointer g)
    (count : s.gpr .ecx = BitVec.ofNat 32 g.privateLength) :
    WP isa VG.Impl.Bignum.X86.copyBytes s fun t => Context g bs t ∧
      Frame [g.scratch (dOffset g) g.privateLength] s.mem t.mem ∧ Keeps [.eax, .ebx, .esi, .ecx] s t ∧
      Spec.Rsa.bytesAt t.mem (g.scratch (dOffset g) g.privateLength).base g.privateLength = bs 2 := by
  have fit : dOffset g + g.privateLength ≤ 8448 := by
    have := h.valid.privateFits
    have := h.valid.maxLength
    unfold dOffset sD
    omega
  have start : dOffset g < 8448 := by have := h.valid.maxLength; unfold dOffset sD; omega
  have dstFit : (dPointer g).toNat + g.privateLength ≤ 2 ^ 32 := h.valid.scratchFit fit start
  have addr : byteAddr (dPointer g) = (g.scratch (dOffset g) g.privateLength).base :=
    h.valid.scratchAddress start
  refine WP.mono (VG.Proof.Bignum.X86.copyBytes_ok s h.copyDContext h.valid.privatePositive src dst count) ?_
  intro t out
  have F := copyBytes_frame dstFit out
  rw [addr] at F
  have bytes := copyBytes_bytes (srcFit := (h.sources 2).fits) dstFit out
  rw [addr, (h.sources 2).bytes] at bytes
  refine ⟨h.after (F.sub ?_) out.rest (out.rest.1 .esp (by decide)), F, out.rest, bytes⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨g.workspaceRegion, by simp [bodyWrites], h.valid.scratchSub fit⟩

end VG.Proof.RsaPkcs1Enc.X86.Dec
