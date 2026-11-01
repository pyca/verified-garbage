module

public import VerifiedGarbage.Impl.Dsa.X86.Arith
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Dsa.X86.PowABI
import VerifiedGarbage.Proof.Dsa.X86.PowCorrect
import VerifiedGarbage.Proof.Dsa.X86.PowVerified
import VerifiedGarbage.Proof.Dsa.X86.MulBody
import VerifiedGarbage.Proof.Dsa.X86.MulTiming
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Dsa.ModPowContract
public import VerifiedGarbage.Proof.Dsa.ModArithContract

/-! # IA-32 DSA products against the shared DSA specification -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Mul
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Arith
open VG.Proof.Dsa.X86.Pow (ABI ws bytes numAt_eq8 scratch_fits)

theorem abi_of {n : Nat} {s : State}
    (h : (Proof.Dsa.ModArith.mulContract (mulLayout n) abi 20).pre s) : ABI n 0 s 20 := by
  sig_pre [Proof.Dsa.ModArith.mulContract, Proof.Dsa.ModPow.sig, mulLayout, abi, argSlots, argVal, argBytes,
    stackBelow] at h
  sig_split h
  constructor <;> try with_reducible assumption
  dsimp only [bytes]
  omega

theorem correct {n : Nat} (hn : 0 < n) (hn48 : n ≤ 48)
    (s : State) (h : (Proof.Dsa.ModArith.mulContract (mulLayout n) abi 20).pre s) :
    ∃ tr t, Exec isa (mulBody n) s tr t ∧ abiPreserved s t ∧
      (Proof.Dsa.ModArith.mulContract (mulLayout n) abi 20).post s t := by
  have A := abi_of h
  have M : wordsVal s.mem (ws s) (slot n 0) n =
      Proof.Dsa.ModPow.numAt s.mem (ws s) (slot n 0) (8 * n) := (numAt_eq8 ..).symm
  obtain ⟨tr, t, E, V, O, R, _, _⟩ := body_ok (A.entry (by decide)) A.size hn hn48 M A.gt_one A.odd
  have F : Frame [⟨ws s, bytes s⟩] s.mem t.mem := by
    intro x hx
    have H := hx _ (List.mem_cons_self ..)
    refine O x (fun r hr => ?_)
    have B := scratch_fits A.size r hr
    simp only [Region.Contains, ofs] at H ⊢
    omega
  refine ⟨tr, t, E, ⟨R, ?_⟩, ?_⟩
  · exact F.readW (by
      simpa only [BitVec.add_zero] using
        Offset.contains_base ((s.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide) (by decide))
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl
        exact A.retScratch) (by decide)
  · sig_post [Proof.Dsa.ModArith.mulContract, Proof.Dsa.ModPow.sig, mulLayout, abi, argSlots, argVal, argBytes]
    refine ⟨?_, ?_⟩
    · simpa only [numAt_eq8] using V
    · intro i hi hj
      have bound := A.bound
      have e : ofs (ws s) (ws s + BitVec.ofNat 64 i) = i := by
        simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by dsimp only [bytes] at bound; omega)]
      exact O _ (fun r hr => by rw [e]; exact hj r hr)

theorem publicArgs {n : Nat} {s t : State}
    (H : (Proof.Dsa.ModArith.mulContract (mulLayout n) abi 20).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 := by
  sig_pub [Proof.Dsa.ModArith.mulContract, Proof.Dsa.ModPow.sig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  constructor <;> with_reducible assumption

theorem constantTime (n : Nat) :
    ConstantTime isa (Proof.Dsa.ModArith.mulContract (mulLayout n) abi 20).pre
      (Proof.Dsa.ModArith.mulContract (mulLayout n) abi 20).pub (mulBody n) := by
  intro s t tr ur sf tf hs ht hp E F
  have A := publicArgs hp
  exact ((body_relCT n) s t tr ur sf tf
    ⟨A.1, A.2, (abi_of hs).readArg, (abi_of ht).readArg⟩ E F).1

theorem satisfiable {n : Nat} (hn : 0 < n) (hn48 : n ≤ 48) :
    ∃ s, (Proof.Dsa.ModArith.mulContract (mulLayout n) abi 20).pre s := by
  refine ⟨Pow.satState, ?_⟩
  have a0 : arg Pow.satState 0 = 0x01010101 := by decide
  have a1 : arg Pow.satState 1 = 0x01010101 := by decide
  sig_pre [Proof.Dsa.ModArith.mulContract, Proof.Dsa.ModPow.sig, mulLayout, abi, argSlots, argVal, argBytes,
    stackBelow]
  simp only [a0, a1]
  sig_and_intros
  all_goals try decide
  all_goals try exact Region.disjoint_of_sep (by decide)
  · rw [show BitVec.toNat (16843009 : BitVec 32) = 16843009 from rfl]
    simp only [contextBytes, slot, stride]; omega
  all_goals
    obtain ⟨k, hk⟩ : ∃ k, 8 * n = k + 2 := ⟨8 * n - 2, by omega⟩
    unfold Proof.Dsa.ModPow.numAt
    rw [hk]
  · exact (Pow.read_ones _ k).1
  · exact Nat.lt_trans (by decide) (Pow.read_ones _ k).2

theorem verified (n : Nat) (hn : 0 < n := by decide) (hn48 : n ≤ 48 := by decide) :
    Verified target (mulBody n) (Proof.Dsa.ModArith.mulContract (mulLayout n) abi 20) :=
  ⟨correct hn hn48, constantTime n, satisfiable hn hn48⟩

end VG.Proof.Dsa.X86.Mul
