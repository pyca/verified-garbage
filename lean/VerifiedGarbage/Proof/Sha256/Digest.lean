import VerifiedGarbage.Proof.Sha256.Md
import VerifiedGarbage.Proof.MdStream.Prefix
import VerifiedGarbage.Spec.Sha256.Contract
import VerifiedGarbage.Proof.Sha256.Scratch

/-!
# SHA-224's digest, from the hash value in memory

The final hash value is stored as eight 32-bit words, and its output
(`md.digest`) is all of them, big-endian (`digest_eq`). SHA-224's digest is
its first 28 bytes, the first 7 words (`digest_take`): every target's
`finalize` of SHA-224 writes them so, with its working space as an
argument first (`finalize224ScratchContract`).
-/

namespace VG.Proof.Sha256

open VG.Proof.MdStream (bytes32 bytes32_length take_flatMap_range)

/-- The first `n` words of the hash value at `p`, big-endian. -/
theorem digest_take (mem : Mem) (p : Addr) {n : Nat} (hn : n ≤ 8) :
    (md.digest (md.stateAt mem p)).take (4 * n) = (List.range n).flatMap fun k =>
      bytes32 true (mem.readW (p + BitVec.ofNat 64 (4 * k)) 32) := by
  rw [digest_eq]
  exact take_flatMap_range _ (fun _ => bytes32_length _ _) hn

/-- SHA-224's digest is the first 28 bytes of the final hash value from its
initial hash value. -/
theorem sha224_eq (m : List Byte) : (md.hash Spec.Sha256.H0_224 m).take 28 = Spec.Sha256.sha224 m := rfl

/-- `vg_sha224_finalize` with its working space in `scratch`
(`Spec.Sha256.finalize224Sig` and the scratch of
`Spec.Sha256.finalizeScratchSig`). -/
def finalize224ScratchSig : Sig where
  params := [("state", .array true .u8 96), ("count", .int .u64 true),
    ("out", .array true .u8 28), ("scratch", .array true .u64 76)]

/-- `Spec.Sha256.finalize224Post`, whatever `scratch` is. -/
def finalize224ScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finalize224ScratchSig.contract A (post := fun state count out _scratch =>
    Spec.Sha256.finalize224Post A.ptrBits state count out) (stack := stack)

/-- `finalize224Post` reads the memory on entry only within the streaming
state (see `finalizePost_local`). -/
theorem finalize224Post_local (pb : Nat) :
    ∀ vs m₁ m₂ m' r, vs.length = (Spec.Sha256.finalize224Sig.words pb).length →
      (∀ b ∈ Sig.bufs Spec.Sha256.finalize224Sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (Spec.Sha256.finalize224Sig.words pb) (Spec.Sha256.finalize224Post pb) vs m₁ m' r →
        Curry.apply (Spec.Sha256.finalize224Sig.words pb) (Spec.Sha256.finalize224Post pb) vs m₂ m' r
  | [st, ct, ot], m₁, m₂, m', r, _, hb, h => by
    simp only [Spec.Sha256.finalize224Sig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    have hs : ∀ i < 96, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    intro msg hr hc
    exact h msg (reprFrom_congr (fun i hi => (hs i hi).symm) hr) hc

end VG.Proof.Sha256
