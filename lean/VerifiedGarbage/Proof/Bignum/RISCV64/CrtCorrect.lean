module

public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtFn
public import VerifiedGarbage.Impl.Bignum.RISCV64.Crt
public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtMid1
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtMid2
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
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
registers (`fn_correct`); `crtP` does the same from the cached `R²` of
each prime (`fn_correctP`).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Crt

open VG VG.RISCV64 VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64

theorem pres_saved : ∀ r ∈ preserved, ∃ i < 13, r = Crt.saved i := by decide

theorem a0_not_saved : ∀ i < 13, Reg.a0 ≠ Crt.saved i := by decide

theorem toNat_flag (b : Bool) : BitVec.ofNat 64 (if b then 1 else 0) = BitVec.ofNat 64 b.toNat := by
  cases b <;> rfl

/-- `crtG pc`: with `pc`, given the cached values (`R2F`). -/
theorem crt_wp (pc : Bool) (s : State) {X : List Region} (h : preCore (baseRd s ++ X) s)
    (hR2 : pc = true → R2F s) : WP isa (crtG pc) s fun t => abiPreserved s t ∧ postCore s t := by
  suffices main : WP isa (crtG pc) s fun t =>
      ((∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.gpr .ra = s.gpr .ra) ∧ postCore s t from
    WP.mono (WP.rdwr main) fun t ⟨⟨⟨hp, hra⟩, hpost⟩, _, _, hsp⟩ => ⟨⟨hp, hsp, hra⟩, hpost⟩
  have hP := pre_factsG h
  have hn := hP.nw
  have hpre := h
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hk, hk'⟩, -, -,
    -, -, -, -, -, -, -, hsl, alS, -⟩ := hpre
  simp only [Spec.Rsa.scratchWords] at hsl
  have hZ : 256 ≤ cZ s := by show 256 ≤ (stackArg s 9).toNat * 8; omega_arith
  have alS' : (cS s).toNat % 8 = 0 := alS
  unfold crtG
  refine WP.seq (WP.mono (front_okG (pc := pc) s h) fun s₁ ⟨hF, hR⟩ => ?_)
  refine mid1G_ok hP hF (fun hp => ⟨hR2 hp, hR hp⟩) fun t M => ?_
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

/-- A cache of two numbers of `a` and `b` words, as their words. -/
theorem cache_words {m : Mem} {P : Addr} {a b X Y : Nat}
    (h : Spec.Rsa.wordsAt m P (a + b) = Spec.Rsa.toWords X a ++ Spec.Rsa.toWords Y b)
    (hX : X < 2 ^ (64 * a)) (hY : Y < 2 ^ (64 * b)) :
    wordsVal m P 0 a = X ∧ wordsVal m P (8 * a) b = Y := by
  rw [Pre.wordsVal_eq_wv, Pre.wordsVal_eq_wv]
  rw [Spec.Rsa.wordsAt, Spec.Rsa.toWords, Spec.Rsa.toWords, List.range_add, List.map_append, List.map_map] at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  rw [List.map_inj_left] at h1 h2
  refine ⟨?_, ?_⟩
  · rw [← Nat.mod_eq_of_lt hX]
    refine VG.Proof.Bignum.wv_of_words fun i hi => ?_
    show (m.readW (P + BitVec.ofNat 64 (0 + 8 * i)) 64).toNat = _
    rw [Nat.zero_add, h1 i (List.mem_range.mpr hi), BitVec.toNat_ofNat]
  · rw [← Nat.mod_eq_of_lt hY]
    refine VG.Proof.Bignum.wv_of_words fun i hi => ?_
    have := h2 i (List.mem_range.mpr hi)
    simp only [Function.comp_apply] at this
    show (m.readW (P + BitVec.ofNat 64 (8 * a + 8 * i)) 64).toNat = _
    rw [show 8 * a + 8 * i = 8 * (a + i) by omega_arith, this, BitVec.toNat_ofNat]

theorem primeWords_eq (n : Nat) : Spec.Rsa.primeWords n = wordsOf n := by
  unfold wordsOf Spec.Rsa.primeWords Spec.Rsa.modulusWords; split <;> omega_arith

/-- `R2F` from `fnContractP`'s precondition. -/
theorem r2F_of {s : State} (h : fnContractP.pre s) : R2F s where
  hS := h.2.2.2.1
  al := h.2.2.2.2.1
  rd i hi := by
    have hi' : i < wordsOf (s.gpr .a7).toNat + wordsOf (stackArg s 1).toNat := hi
    have := h.2.2.2.1; simp only at this
    exact ⟨r2R s, List.mem_append_left _ (by rw [h.1.1]; exact List.mem_append_right _ (List.mem_singleton_self _)),
      Offset.contains_base _ (show 8 * i + 8 ≤ 8 * (wordsOf (s.gpr .a7).toNat + wordsOf (stackArg s 1).toNat) by
        omega_arith) (by omega_arith)⟩
  sep x hx := Pub.sep_of_disjoint h.2.2.1 x hx
  val hb := by
    have hw := h.2.2.2.2.2.1
    simp only [Spec.Rsa.primeR2, VG.Proof.Bignum.bytesAt_length, primeWords_eq] at hw
    have hP := pre_factsG h.1
    obtain ⟨mP1, _, mQ1, _, mPb, mQb, _, _⟩ := masked_facts hP
    have eP : mP s = vP s := by simp only [mP, hb, ↓reduceIte]
    have eQ : mQ s = vQ s := by simp only [mQ, hb, ↓reduceIte]
    rw [eP] at mP1 mPb; rw [eQ] at mQ1 mQb
    have dP : cwP s = wordsOf (cpL s) := rfl
    have dQ : cwQ s = wordsOf (cqL s) := rfl
    have hpw : cpL s ≤ 8 * cwP s := by have := wordsOf_ge (l := cpL s); omega_arith
    have hqw : cqL s ≤ 8 * cwQ s := by have := wordsOf_ge (l := cqL s); omega_arith
    exact cache_words hw
      (Nat.lt_trans (Nat.mod_lt _ (Nat.lt_trans Nat.zero_lt_one mP1)) (Nat.lt_of_lt_of_le mPb (pow256_le hpw)))
      (Nat.lt_trans (Nat.mod_lt _ (Nat.lt_trans Nat.zero_lt_one mQ1)) (Nat.lt_of_lt_of_le mQb (pow256_le hqw)))
  pq := h.2.2.2.2.2.2

theorem fn_correct (s : State) (h : fnContract.pre s) :
    ∃ tr t, Exec isa crt s tr t ∧ abiPreserved s t ∧ fnContract.post s t :=
  crt_wp false s (X := []) (by rw [List.append_nil]; exact h) nofun

theorem fn_correctP (s : State) (h : fnContractP.pre s) :
    ∃ tr t, Exec isa crtP s tr t ∧ abiPreserved s t ∧ fnContractP.post s t :=
  crt_wp true s h.1 fun _ => r2F_of h

end VG.Proof.Bignum.RISCV64.Crt
