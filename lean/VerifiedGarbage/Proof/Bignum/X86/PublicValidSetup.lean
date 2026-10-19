module

public import VerifiedGarbage.Proof.Bignum.X86.PublicControls
public import VerifiedGarbage.Proof.Bignum.X86.PublicInputs
public import VerifiedGarbage.Proof.Bignum.MemoryFrame

/-! # Public width selection retains all input buffers and caller resources -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem publicValidSetup_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (H : PublicInputs base bytes len args s) :
    WP isa (.seq (.block PublicFn.saveExponent) (.block PublicFn.widthArgs)) s fun t =>
      PublicInputs base bytes len args t ∧ t.gpr .esp = s.gpr .esp ∧
      t.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.modulusWords len) ∧
      Spec.Rsa.bytesAt t.mem (byteAddr (args 2)) len = Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len := by
  have size := H.space
  rw [PublicContext.size_eq] at size
  refine WP.seq (WP.mono (saveExponent_frame H.scratch (by omega)) fun u ⟨O, K⟩ => ?_)
  have O' : Outside base 0 bytes s.mem u.mem := O.mono (by omega) (by omega)
  have Hu := H.keep K (by decide) (by decide) O'
  refine WP.mono (widthArgs_ok H.upper (by rw [← H.nLen]; exact (Hu.stack 3 (by decide)).readSrc))
    fun t ⟨W, M, Kt⟩ => ?_
  have Kst := (K.mono (by simp : ([] : List Reg) ⊆ [.eax])).trans Kt
  have Ost : Outside base 0 bytes s.mem t.mem := by rw [M]; exact O'
  exact ⟨H.keep Kst (by decide) (by decide) Ost, Kst.1 _ (by decide), W,
    scratch_bytes Ost (by have := H.upper; omega) H.nApart⟩

end VG.Proof.Bignum.X86
