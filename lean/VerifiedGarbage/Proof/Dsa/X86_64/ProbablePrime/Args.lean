module

public import VerifiedGarbage.Impl.Dsa.X86_64.ProbablePrime
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Arguments
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul

/-! # The probable-prime test's arguments in the arithmetic workspace's header

The block writes the test's header arguments from registers: as
`argumentWrites` of `argList`, whose frame words are the registers `rsi`,
`r9` and `rcx`. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Impl.Dsa.X86_64.ProbablePrime
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Dsa.X86_64.Generation (argumentWrites argumentValue argumentFits)

/-- The arguments, with the working space, `rand` and `rand_len` as the
words 0, 1 and 2. -/
def argList (bits : Nat) : List HeaderArgument :=
  [⟨kOut, .frame 0 Impl.Dsa.Generation.Layout.witness⟩, ⟨kLen, .literal (draw bits)⟩,
   ⟨kUsedP, .literal (len bits)⟩, ⟨kChecks, .literal (checks bits)⟩,
   ⟨20, .frame 0 (candidate bits)⟩, ⟨kRand, .frame 1 0⟩, ⟨kRandLen, .frame 2 0⟩,
   ⟨kUsed, .literal 0⟩]

/-- The registers the arguments come from. -/
def argWords (s : State) (k : Nat) : BitVec 64 :=
  if k = 0 then s.gpr .rsi else if k = 1 then s.gpr .r9 else s.gpr .rcx

theorem argList_fits {bits : Nat} (hb : bits ≤ 3072) : ∀ a ∈ argList bits, argumentFits a := by
  intro a ha
  simp only [argList, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only [argumentFits]
  · decide
  · refine ⟨by decide, by decide, ?_⟩; unfold draw; split <;> omega
  · refine ⟨by decide, by decide, ?_⟩; unfold len; omega
  · refine ⟨by decide, by decide, ?_⟩; unfold checks; split <;> omega
  · refine ⟨by decide, by decide, by decide, ?_⟩; unfold candidate; split <;> decide
  · decide
  · decide
  · decide

theorem ofNat32_setWidth {n : Nat} (h : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem args_ok {bits : Nat} (hb : bits ≤ 3072) {s : State} {B : Addr} (hB : Scr s B 256)
    (hdi : s.gpr .rdi = B) :
    WP isa (.block (args bits)) s fun t =>
      t.mem = argumentWrites B (argWords s) s.mem (argList bits) ∧ Keep [.rax] s t := by
  have hd := ofNat32_setWidth (n := draw bits) (by unfold draw; split <;> omega)
  have hl := ofNat32_setWidth (n := len bits) (by unfold len; omega)
  have hk := ofNat32_setWidth (n := checks bits) (by unfold checks; split <;> omega)
  have hc : BitVec.signExtend 64 (BitVec.ofNat 32 (candidate bits)) = BitVec.ofNat 64 (candidate bits) := by
    unfold candidate; split <;> decide
  have hw : BitVec.signExtend 64 (BitVec.ofNat 32 Impl.Dsa.Generation.Layout.witness) =
      BitVec.ofNat 64 Impl.Dsa.Generation.Layout.witness := by decide
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = argumentWrites B (argWords s) s.mem (argList bits)) (by
    xrun [Impl.Dsa.X86_64.ProbablePrime.args, State.ea, Impl.Bignum.X86_64.hdr, hdi, kOut, kLen, kUsedP, kChecks, kE,
      kRand, kRandLen, kUsed, VG.Impl.Bignum.sFn, hdrOff, Nat.reduceMul, Nat.reduceAdd, hd, hl, hk, hc, hw,
      hB.st (d := 128) (by decide), hB.st (d := 136) (by decide), hB.st (d := 144) (by decide),
      hB.st (d := 152) (by decide), hB.st (d := 160) (by decide), hB.st (d := 184) (by decide),
      hB.st (d := 192) (by decide), hB.st (d := 200) (by decide)]
    simp only [argumentWrites, argList, argumentValue, argWords, kOut, kLen, kUsedP, kChecks, kE,
      kRand, kRandLen, kUsed, VG.Impl.Bignum.sFn, Nat.reduceMul, Nat.reduceAdd,
      BitVec.add_zero, ite_true, ite_false, Nat.one_ne_zero, Nat.reduceEqDiff]
    rfl) rfl) fun t ⟨hm, hk⟩ => ⟨hm, hk⟩

end VG.Proof.Dsa.X86_64.ProbablePrime
