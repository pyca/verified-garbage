module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrfStep

/-! # The PRF loop terminates after the public number of HMAC blocks -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt
open VG.Proof.RsaPkcs1Enc

theorem prfLoop_ok (v : VG.Proof.Sha256.X86.Variants.Backend)
    {g : Geometry} {bs : Fin 9 → List Byte} {s0 s : State} {R : PrfConfig} {key extra : List Byte}
    (h : PrfInvariant g bs s0 R key extra 0 s)
    (messageOk : ∀ (i : Nat), i < R.blocks → ∀ (a : State), Context g bs a →
      a.gpr .edi = g.workspace + BitVec.ofNat 32 sMsg → a.gpr .ebx = BitVec.ofNat 32 i →
      a.gpr .edx = BitVec.ofNat 32 g.length →
      WP isa (.block (msgBytes R.label R.lenCode)) a fun t => Context g bs t ∧
        Frame [g.scratch sMsg 16] a.mem t.mem ∧ Keeps [.eax, .ecx] a t ∧
        Spec.Rsa.bytesAt t.mem (g.scratch sMsg (R.label.length + 4)).base (R.label.length + 4) =
          prfMessage i (R.label.map (BitVec.ofNat 8)) R.length) :
    WP isa (.loop (prfBody (hashFns v) R.label R.lenCode R.dst) .ne) s
      (PrfInvariant g bs s0 R key extra R.blocks) := by
  refine WP.loop (M := isa) (fun n t => ∃ i, n = R.blocks - i ∧ i < R.blocks ∧
    PrfInvariant g bs s0 R key extra i t) ?_ R.blocks s ⟨0, rfl, R.blockPositive, h⟩
  rintro n t ⟨i, rfl, bound, hi⟩
  refine WP.mono (prfInvariant_step v hi bound (messageOk i bound)) ?_
  rintro u ⟨hu, zf⟩
  have ev : isa.eval .ne u = some (!decide (i + 1 = R.blocks)) := by
    simp only [eval, zf, Word32.sub_beq_zero (a := i + 1) (b := R.blocks) (by have := R.blockBound; omega)
      (by have := R.blockBound; omega), Option.map_some]
  by_cases done : i + 1 = R.blocks
  · exact Or.inl ⟨by rw [ev, decide_eq_true done]; rfl, by rw [← done]; exact hu⟩
  · exact Or.inr ⟨by rw [ev, decide_eq_false done]; rfl,
      R.blocks - (i + 1), by omega, i + 1, rfl, by omega, hu⟩

end VG.Proof.RsaPkcs1Enc.X86.Dec
