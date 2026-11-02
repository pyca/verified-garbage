module

public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtFn
public import VerifiedGarbage.Impl.Bignum.RISCV64.Crt
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtMid2
import VerifiedGarbage.Proof.Bignum.CrtResult
import VerifiedGarbage.Proof.Bignum.CrtNatural
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The RSA private-key operation on RISC-V: correctness

`crt` saves the callee-saved registers, stores its arguments and sets up `X`
(`front_ok`), computes the result (`mid1_ok`, `mid2_ok`) and restores the
registers (`fn_correct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Crt

open VG VG.RISCV64 VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64

theorem pres_saved : ∀ r ∈ preserved, ∃ i < 13, r = Crt.saved i := by decide

theorem a0_not_saved : ∀ i < 13, Reg.a0 ≠ Crt.saved i := by decide

theorem toNat_flag (b : Bool) : BitVec.ofNat 64 (if b then 1 else 0) = BitVec.ofNat 64 b.toNat := by
  cases b <;> rfl

theorem fn_correct (s : State) (h : fnContract.pre s) :
    ∃ tr t, Exec isa crt s tr t ∧ abiPreserved s t ∧ fnContract.post s t := by
  show WP isa crt s fun t => abiPreserved s t ∧ fnContract.post s t
  suffices main : WP isa crt s fun t =>
      ((∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.gpr .ra = s.gpr .ra) ∧ fnContract.post s t from
    WP.mono (WP.rdwr main) fun t ⟨⟨⟨hp, hra⟩, hpost⟩, _, _, hsp⟩ => ⟨⟨hp, hsp, hra⟩, hpost⟩
  have hP := pre_facts h
  have hn := hP.nw
  have hpre := h
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hk, hk'⟩, -, -,
    -, -, -, -, -, -, -, hsl, alS, -⟩ := hpre
  simp only [Spec.Rsa.scratchWords] at hsl
  have hZ : 256 ≤ cZ s := by show 256 ≤ (stackArg s 9).toNat * 8; omega_arith
  have alS' : (cS s).toNat % 8 = 0 := alS
  unfold crt
  refine WP.seq (WP.mono (front_ok s h) fun s₁ hF => ?_)
  refine mid1_ok hP hF fun t M => ?_
  refine mid2_ok hP hF M fun u ub u0 usav u6 uwr => ?_
  have hin : ∀ i < 13, InRegions u.wr (Mont.off (savW (cS s)) (8 * i)) 8 := fun i hi => by
    rw [uwr, hwr]
    show InRegions _ (cS s + BitVec.ofNat 64 112 + BitVec.ofNat 64 (8 * i)) 8
    rw [Offset.add_add]
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _),
      Offset.contains_base _ (by show _ ≤ (stackArg s 9).toNat * 8; omega_arith) (by omega_arith)⟩
  have hal : ∀ i < 13, (Mont.off (savW (cS s)) (8 * i)).toNat % 8 = 0 := fun i hi => by
    show (cS s + BitVec.ofNat 64 112 + BitVec.ofNat 64 (8 * i)).toNat % 8 = 0
    rw [Offset.add_add, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith
  refine WP.mono (restore_ok u (S := cS s) (v := fun i => s.gpr (Crt.saved i)) u6 hin hal usav)
    fun w ⟨wrs, wot, wm, _, _, _⟩ => ⟨⟨fun r hr => ?_, wrs 11 (by decide)⟩, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := pres_saved r hr
    exact wrs i hi
  · show Spec.Rsa.written w.mem (s.gpr .a0) (ck s) ((w.gpr .a0).setWidth 32) _
    rw [wm, wot .a0 a0_not_saved, u0]
    refine VG.Proof.Bignum.crtWritten_of (VG.Proof.Bignum.bytesAt_length _ _ _) ub (toNat_flag _)
      (fun hv => ?_) (fun hv => ?_)
    · have hcb : cb s = (decide (vC s < vN s) && decide (vQI s < vP s) && decide (vP s * vQ s = vN s)) := by
        simp only [cb, crtMask, hv, Bool.true_and]
      refine ⟨?_, ?_⟩
      · rw [hcb]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, c, b⟩, fun ⟨a, c, b⟩ => ⟨⟨a, b⟩, c⟩⟩
      · unfold vr
        cases hb : cb s
        · rfl
        · obtain ⟨_, _, _, _, hp1', _, _, _⟩ := mask_true hP.k64
            (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.pk) (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.qk)
            hb
          simp only [↓reduceIte, VG.Proof.Bignum.crtResult]
          rw [VG.Proof.Bignum.crt_coefficient_natural (Nat.lt_trans Nat.zero_lt_one hp1')]
          unfold vh vm1 vm2 mQ mP mQI
          simp only [hb, ↓reduceIte]
          exact Nat.add_comm _ _
    · have hcb : cb s = false := by simp only [cb, crtMask, hv, Bool.false_and]
      exact ⟨hcb, by unfold vr; rw [hcb]; rfl⟩

end VG.Proof.Bignum.RISCV64.Crt
