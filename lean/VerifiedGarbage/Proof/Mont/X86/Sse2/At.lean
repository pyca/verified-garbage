module

public import VerifiedGarbage.Proof.Mont.X86.Sse2.AtABI
public import VerifiedGarbage.Proof.Mont.X86.Sse2.Time
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Mont.X86.Square.FinalMath
import VerifiedGarbage.Proof.Mont.X86.ArgWs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # `vg_rsa_mont_mul_at` on x86 with SSE2: correctness

`at_correct`: from `mulContract abi 56`'s precondition, `atBody` terminates
with the callee-saved registers and the return address as they were and the
contract's postcondition.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Rsa.MontMul (Apart numAt scratchBytes)
open VG.Proof.Mont.X86.Dynamic (ofs_far)

theorem read_val32 (m : Mem) (base : Addr) : ∀ (k d : Nat),
    (m.read (off base d) (4 * k)).toNat = val32 m base d k
  | 0, d => by simp [Mem.read, val32]
  | k + 1, d => by
    rw [show 4 * (k + 1) = 4 * k + 4 from rfl, read_toNat_add, val32, ← read_val32 m base k (d + 4),
      Offset.add_add]
    congr 1

theorem numAt_val32' (m : Mem) (ws : Addr) (d n : Nat) : numAt m ws d (8 * n) = val32 m ws d (2 * n) := by
  unfold numAt
  rw [show 8 * n = 4 * (2 * n) by omega]
  exact read_val32 m ws (2 * n) d

theorem numAt_w32' (m : Mem) (ws : Addr) (d : Nat) : numAt m ws d 4 = w32 m ws d := by
  unfold numAt
  rw [show 4 = 4 * 1 from rfl, read_val32 m ws 1 d]
  simp [val32]

theorem atBody_noSp : NoSp (seqs [.block atParams, withParams, .block restoreRegs]) :=
  NoSp.of_all (by decide +kernel)

/-- What `body atParams` takes of a state meeting the contract's precondition. -/
theorem atReady {s : State} (A : AtABI s) :
    Ready atParams (wsOf s) (lenOf s) (nAt s) (arg s 5).toNat (arg s 3).toNat (arg s 4).toNat (arg s 6).toNat
      (arg s 7).toNat (arg s 8).toNat s := by
  have Ly := A.lay
  have hinv := A.inv
  have hb := A.bLt
  rw [numAt_val32', numAt_w32'] at hinv
  rw [numAt_val32', numAt_val32'] at hb
  exact ⟨A.entry, Ly, atParams_ok A, VG.Proof.Mont.X86.Square.low_inverse s.mem (wsOf s) _ _ Ly.hN hinv, hb⟩

theorem at_correct (s : State) (h : (Proof.Rsa.MontMul.mulContract abi 56).pre s) :
    ∃ tr t, Exec isa atBody s tr t ∧ abiPreserved s t ∧ (Proof.Rsa.MontMul.mulContract abi 56).post s t := by
  have A := atAbi_of h
  have R := atReady A
  obtain ⟨tr, t, E, lt, cong, mem, cs, -, -⟩ := body_ok R.entry R.ly atBody_noSp R.par R.inv R.bLt
  have hso := A.so
  have hol := A.o_le
  have hscr := A.s_le
  have hst := A.stackBound
  simp only [Apart, scratchBytes] at hso hscr
  refine ⟨tr, t, E, ⟨cs, ?_⟩, ?_⟩
  · refine Mem.readW_congr fun i hi => mem _ (fun r hr => ?_) (fun hc => ?_)
    · have := ofs_far (base := wsOf s) (size := lenOf s) (x := (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 i)
        fun hc => A.retScratch _ (Offset.contains_base _ (by omega) (by omega)) hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [nAt, lenOf] at this ⊢ <;> omega
    · have := (s.gpr .esp).isLt
      simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
        at hc
      omega
  · sig_post [Proof.Rsa.MontMul.mulContract, Proof.Rsa.MontMul.sig, abi, argSlots, argVal, argBytes]
    refine ⟨?_, ?_, ?_⟩
    · rw [numAt_val32', numAt_val32']; exact lt
    · rw [numAt_val32', numAt_val32', numAt_val32', numAt_val32',
        show 64 * (arg s 2).toNat = 32 * nAt s by simp only [nAt]; omega]
      exact cong
    · intro i hi hj
      have hb := A.bound
      apply mem _ (fun r hr => ?_) (fun hc => ?_)
      · rw [show ofs (wsOf s) (wsOf s + BitVec.ofNat 64 i) = i by
          simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by omega)]]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have := hj
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, scratchBytes] at this
        rcases hr with rfl | rfl <;> simp only [nAt] <;> omega
      · have := (s.gpr .esp).isLt
        have := (arg s 0).isLt
        have := A.stackLo
        refine A.stkScratch (wsOf s + BitVec.ofNat 64 i) ?_ ?_
        · simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
            at hc ⊢
          omega
        · simp only [Region.Contains, lenOf, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_setWidth,
            BitVec.toNat_ofNat]
          omega

end VG.Proof.Mont.X86.Sse2
