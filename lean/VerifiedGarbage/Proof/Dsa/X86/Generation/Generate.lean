module
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
public import Aesop.BuiltinRules
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Entry
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchStorage
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash
import VerifiedGarbage.Proof.Dsa.X86.Generation.FinishOutput
import VerifiedGarbage.Proof.Dsa.X86.Generation.InitializeSearch
import VerifiedGarbage.Proof.Dsa.X86.Generation.NativeParameterSearch
import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterResult

/-! # The complete initialized parameter generator, before cdecl save and restore -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

def generationWrites (P : SearchContextPlan) : List Region :=
  [⟨P.geometry.base, usedBytes P.geometry.pLen⟩] ++ parameterWrites P.geometry ++
    [⟨(P.saved 6).setWidth 64, 2 * P.geometry.pLen + P.geometry.qLen⟩]

def GenerationResult (P : SearchContextPlan) (s t : State) : Prop :=
  let result := Spec.Dsa.generateParametersBytes P.geometry.pLen P.geometry.qLen P.seeds.bytes P.hs.bytes P.witnesses.bytes
  t.gpr .eax = (if result.isSome then 1 else 0) ∧
  Spec.Rsa.bytesAt t.mem ((P.saved 6).setWidth 64) (2 * P.geometry.pLen + P.geometry.qLen) =
    result.getD (List.replicate (2 * P.geometry.pLen + P.geometry.qLen) 0) ∧
  Frame (generationWrites P) s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .esp = s.gpr .esp

theorem generate_ok {H : Hash} (Khash : HashOK H) (F : KeyRandom.CheckCall.CheckFn)
    {P : SearchContextPlan} {W : Nat → BitVec 32} {s : State}
    (R : SearchStorage P W s) (cursor : W 16 = 0)
    (digest : H.D = P.geometry.qLen) (final : H.F = P.geometry.qLen)
    (hash : ∀ bs, Khash.SH.H.hash bs = Spec.Dsa.seedHash (8 * P.geometry.qLen) bs)
    (hashSize : ∀ bs, (Spec.Dsa.seedHash (8 * P.geometry.qLen) bs).length = P.geometry.qLen)
    (seeds : P.seeds.bytes.length % P.geometry.qLen = 0)
    (hs : P.hs.bytes.length % P.geometry.pLen = 0)
    (length : P.saved 7 = BitVec.ofNat 32 (2 * P.geometry.pLen + P.geometry.qLen))
    (room : (P.saved 6).toNat + (2 * P.geometry.pLen + P.geometry.qLen) ≤ 2 ^ 32)
    (apart : (P.geometry.part packed (2 * P.geometry.pLen + P.geometry.qLen)).Disjoint
      ⟨(P.saved 6).setWidth 64, 2 * P.geometry.pLen + P.geometry.qLen⟩)
    (write : ∀ i, i < 2 * P.geometry.pLen + P.geometry.qLen → InRegions s.wr (off ((P.saved 6).setWidth 64) i) 1) :
    WP isa (generate H F.name F.code P.geometry.pLen P.geometry.qLen) s fun t =>
      GenerationResult P s t := by
  unfold generate
  refine WP.seq (WP.mono (initializeSearch_ok R) fun a ⟨Ra, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (nativeParameterSearch_ok Khash F Ra cursor (Nat.zero_le _) digest final hash hashSize)
    fun b result => ?_)
  have resultCopy := result
  obtain ⟨V, Rb, _, Ob, rd, wr⟩ := resultCopy
  refine WP.mono (finishOutput_ok result length room apart (by intro i hi; rw [wr, Ka.2.2]; exact write i hi))
    fun t ⟨ax, bytes, Ot, Kt⟩ => ?_
  unfold GenerationResult
  rw [parameterRemaining_result P seeds hs]
  have someEq : ((parameterRemaining P 0 0).map (Spec.Dsa.encodeParams P.geometry.pLen P.geometry.qLen)).isSome =
      (parameterRemaining P 0 0).isSome := by cases parameterRemaining P 0 0 <;> rfl
  refine ⟨by rw [someEq]; exact ax, bytes, ?_, Kt.2.1.trans (rd.trans Ka.2.1),
    Kt.2.2.trans (wr.trans Ka.2.2), ?_⟩
  · apply Frame.trans (Oa.mono (fun r hr => List.mem_append_left _ (List.mem_append_left _ hr)))
    apply Frame.trans (Ob.mono (fun r hr => List.mem_append_left _ (List.mem_append_right _ hr)))
    exact Ot.mono (fun r hr => List.mem_append_right _ hr)
  · exact (Kt.1 _ (by decide)).trans (Rb.arena.frameReg.trans R.arena.frameReg.symm)
end VG.Proof.Dsa.X86.Generation
