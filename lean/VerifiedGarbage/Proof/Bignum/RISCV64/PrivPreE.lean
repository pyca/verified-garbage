module
-- separate module: the precomputation's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Bignum.RISCV64.PrivPreD
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtSave
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# An RSA private key's precomputed values on RISC-V: correctness

`vg_rsa_private_precompute` checks the key (`partA_ok`), writes the factors'
values (`partB_ok`) and the modulus's (`partC_ok`), and restores the
registers (`fn_correct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.PrivPre

open VG VG.RISCV64 VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum.RISCV64.Crt (savW restore_ok wordsOf)

/-- `pre`'s words, as `n`'s and the two factors'. -/
theorem wordsAt_three (m : Mem) (P : Addr) (a b c : Nat) :
    Spec.Rsa.wordsAt m P (a + b + c) = Spec.Rsa.wordsAt m P a ++
      (List.range b).map (fun i => Mont.word m P (8 * a + 8 * i)) ++
      (List.range c).map (fun i => Mont.word m P (8 * a + 8 * b + 8 * i)) := by
  have e1 : ∀ i, m.readW (P + BitVec.ofNat 64 (8 * (a + i))) 64 = Mont.word m P (8 * a + 8 * i) := fun i => by
    rw [Nat.mul_add]
  have e2 : ∀ i, m.readW (P + BitVec.ofNat 64 (8 * (a + b + i))) 64 = Mont.word m P (8 * a + 8 * b + 8 * i) :=
    fun i => by rw [Nat.mul_add, Nat.mul_add]
  simp only [Spec.Rsa.wordsAt, List.range_add, List.map_append, List.map_map, Function.comp_def, e1, e2]

theorem pres_saved : ∀ r ∈ preserved, ∃ i < 13, r = Crt.saved i := by decide

theorem a0_not_saved : ∀ i < 13, Reg.a0 ≠ Crt.saved i := by decide

theorem toWords_r2 (w P : Nat) :
    Spec.Rsa.toWords (2 ^ (128 * w) % P) w = (List.range w).map (r2Word true w P) := rfl

theorem r2Word_false (w P n : Nat) : (List.range n).map (r2Word false w P) = List.replicate n 0 := by
  rw [show r2Word false w P = fun _ => 0 from rfl, List.map_const', List.length_range]

theorem fn_correct (s₀ : State) (h : fnContract.pre s₀) :
    ∃ tr t, Exec isa PrivPre.code s₀ tr t ∧ abiPreserved s₀ t ∧ fnContract.post s₀ t := by
  show WP isa PrivPre.code s₀ fun t => abiPreserved s₀ t ∧ fnContract.post s₀ t
  suffices main : WP isa PrivPre.code s₀ fun t =>
      ((∀ r ∈ preserved, t.gpr r = s₀.gpr r) ∧ t.gpr .ra = s₀.gpr .ra) ∧ fnContract.post s₀ t from
    WP.mono (WP.rdwr main) fun t ⟨⟨⟨hp, hra⟩, hpost⟩, _, _, hsp⟩ => ⟨⟨hp, hsp, hra⟩, hpost⟩
  have hP := pre_facts h
  have hwr : s₀.wr = [preR s₀, scrR s₀] := h.2.2.1
  have hn := hP.nw
  have hpl := hP.preLen
  have room := hP.room
  have dcZ : cZ s₀ = (stackArg s₀ 1).toNat * 8 := rfl
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eX8 := e (cwX s₀) 8
  unfold PrivPre.code
  refine partA_ok h fun t hA => partN_ok hP hA fun t' hN => partB_ok hP hN fun u hB => partC_ok hP hB fun v hC => ?_
  have hin : ∀ i < 13, InRegions v.wr (Mont.off (savW (cS s₀)) (8 * i)) 8 := fun i hi => by
    rw [hC.keep.2.2, hwr]
    show InRegions _ (cS s₀ + BitVec.ofNat 64 112 + BitVec.ofNat 64 (8 * i)) 8
    rw [Offset.add_add]
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hal : ∀ i < 13, (Mont.off (savW (cS s₀)) (8 * i)).toNat % 8 = 0 := fun i hi => by
    have al := hP.al
    show (cS s₀ + BitVec.ofNat 64 112 + BitVec.ofNat 64 (8 * i)).toNat % 8 = 0
    rw [Offset.add_add, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith
  refine WP.mono (restore_ok v (S := cS s₀) (v := fun i => s₀.gpr (Crt.saved i)) hC.s6 hin hal hC.sav)
    fun w ⟨wrs, wot, wm, _, _, _⟩ => ⟨⟨fun r hr => ?_, wrs 11 (by decide)⟩, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := pres_saved r hr
    exact wrs i hi
  · show match Spec.Rsa.privatePrecompute (nB s₀) (pB s₀) (qB s₀) with
      | some ws => (w.gpr .a0).setWidth 32 = 1 ∧ Spec.Rsa.wordsAt w.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat = ws
      | none => (w.gpr .a0).setWidth 32 = 0 ∧
        Spec.Rsa.wordsAt w.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat = List.replicate (s₀.gpr .a1).toNat 0
    rw [wm, wot .a0 a0_not_saved, hC.a0, hpl,
      show wordsOf (cpL s₀) = cwP s₀ from rfl, show wordsOf (cqL s₀) = cwQ s₀ from rfl,
      wordsAt_three v.mem (s₀.gpr .a0) (2 * cw s₀) (cwP s₀) (cwQ s₀),
      show 8 * (2 * cw s₀) = 16 * cw s₀ by omega_arith]
    have ewP := List.map_congr_left (l := List.range (cwP s₀)) fun i hi => hC.wP i (List.mem_range.mp hi)
    have ewQ := List.map_congr_left (l := List.range (cwQ s₀)) fun i hi => hC.wQ i (List.mem_range.mp hi)
    rw [ewP, ewQ]
    have lp : (pB s₀).length = cpL s₀ := VG.Proof.Bignum.bytesAt_length _ _ _
    have lq : (qB s₀).length = cqL s₀ := VG.Proof.Bignum.bytesAt_length _ _ _
    have ln : (nB s₀).length = ck s₀ := VG.Proof.Bignum.bytesAt_length _ _ _
    cases hb : cb s₀
    · have hnone : Spec.Rsa.privatePrecompute (nB s₀) (pB s₀) (qB s₀) = none := by
        unfold Spec.Rsa.privatePrecompute
        split
        · next hpq =>
          have hv : Spec.Rsa.modulusValid (cN s₀) (ck s₀) = false := by
            have := hb; simp only [cb, privMask, Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
            exact this.resolve_right (fun h' => h' hpq)
          simp only [Spec.Rsa.publicPrecompute, ln, hv, Bool.false_eq_true, ↓reduceIte, Option.map_none]
        · rfl
      rw [hnone]
      refine ⟨rfl, ?_⟩
      have z0 : Spec.Rsa.wordsAt v.mem (s₀.gpr .a0) (2 * cw s₀) = List.replicate (2 * cw s₀) 0 := by
        rw [Spec.Rsa.wordsAt, List.map_congr_left (g := fun _ => (0 : BitVec 64))
          fun i hi => hC.nZ hb i (List.mem_range.mp hi), List.map_const', List.length_range]
      rw [z0]
      rw [r2Word_false, r2Word_false, List.replicate_append_replicate, List.replicate_append_replicate]
    · have hv : Spec.Rsa.modulusValid (cN s₀) (ck s₀) = true ∧ cP s₀ * cQ s₀ = cN s₀ := by
        have := hb; simp only [cb, privMask, Bool.and_eq_true, decide_eq_true_eq] at this; exact this
      obtain ⟨ws, hws⟩ : ∃ ws, Spec.Rsa.publicPrecompute (nB s₀) = some ws :=
        ⟨_, by simp only [Spec.Rsa.publicPrecompute, ln, hv.1, ↓reduceIte]; rfl⟩
      have hsome : Spec.Rsa.privatePrecompute (nB s₀) (pB s₀) (qB s₀) =
          some (ws ++ Spec.Rsa.primeR2 (pB s₀) ++ Spec.Rsa.primeR2 (qB s₀)) := by
        unfold Spec.Rsa.privatePrecompute
        rw [ite_eq_left_of_eq_true _ _ (eq_true hv.2), hws]; rfl
      rw [hsome]
      refine ⟨rfl, ?_⟩
      have := hC.nW hb
      rw [hws, Option.some.injEq] at this
      rw [← this]
      simp only [Spec.Rsa.primeR2, lp, lq, ← wordsOf_eq]
      rfl

end VG.Proof.Bignum.RISCV64.PrivPre
