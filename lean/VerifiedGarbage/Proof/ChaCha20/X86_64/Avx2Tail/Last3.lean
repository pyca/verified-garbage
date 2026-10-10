import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Out
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Rounds3

/-!
# ChaCha20 on x86-64 with AVX2, the last bytes: three sets

`last3`'s straight-line code, as `Out.lean`'s: the input states of the three
sets (the third set's lane increments `4, 5` summed from the second set's,
`inT3`), and the output, the first two sets XORed into 256 bytes of data and
the third stored to `buf[0, 128)`.
-/

namespace VG.Proof.ChaCha20.X86_64.Avx2Tail

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2Tail
open VG.Spec.ChaCha20 (Word stateAt serialize)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx512 (T Sym Sym.init xidx xidx_lt xidx_zreg stateAt_get byte_dword add_ofNat')
open VG.Proof.ChaCha20.X86_64.Avx512Tail (bsize regn baseR wregs Ctx S0 byte_out)
open VG.Impl.ChaCha20.X86_64.Avx512 (zreg)
open VG.Proof.ChaCha20.X86_64.Avx2 (plus ctr_get Consts)

/-- Word `i` of block `l` of set `k` of three before the rounds: the third
set's word 12 has the second set's low lane increment and its own added. -/
def inT3 (k i l : Nat) : T :=
  if k < 2 then inT k i l
  else if i / 4 = 3 then .add (.add (.mem 1 (64 + i % 4)) (.mem 1 (64 + 4 * l + i % 4))) (.mem 0 i)
  else .mem 0 i

def outT3 (k i l : Nat) : T := .add (.reg (4 * k + i / 4) (4 * l + i % 4)) (inT3 k i l)

/-! ## The kernel's checks -/

def masks3Ok (σ : Sym) : Bool :=
  (List.range 8).all fun p => σ.reg 14 p == .mem 1 (32 + p) && σ.reg 15 p == .mem 1 (40 + p)

def setup3Check : Bool :=
  match run 64 Sym.init setup3 with
  | some σ => !σ.dirty && masks3Ok σ && (List.range 3).all fun k => (List.range 4).all fun r =>
      (List.range 8).all fun p => σ.reg (4 * k + r) p == inT3 k (4 * r + p % 4) (p / 4)
  | none => false

def last3Check : Bool :=
  match run 64 Sym.init (addIn3 ++ xorSetT .xmm0 .xmm1 .xmm2 .xmm3 0 ++ xorSetT .xmm4 .xmm5 .xmm6 .xmm7 128 ++
      storeSetT .xmm8 .xmm9 .xmm10 .xmm11 0) with
  | some σ =>
    ((List.range 4).all fun j => (List.range 16).all fun i =>
      σ.mem 2 (16 * j + i) == .xor (.mem 2 (16 * j + i)) (outT3 (j / 2) i (j % 2))) &&
    (List.range 2).all fun l => (List.range 16).all fun i => σ.mem 1 (16 * l + i) == outT3 2 i l
  | none => false

theorem setup3Check_eq : setup3Check = true := by decide +kernel
theorem last3Check_eq : last3Check = true := by decide +kernel

/-! ## Evaluation -/

section
variable {D : Nat} {s : State}

theorem inT3_eval (hi : Incs s.mem (s.gpr .r9)) {k i l : Nat} (hk : k < 3) (hi16 : i < 16) (hl : l < 2) :
    T.eval D s (inT3 k i l) = (ctr (S0 s) (2 * k + l))[i] := by
  by_cases hk2 : k < 2
  · simp only [inT3, hk2, ite_true]; exact inT_eval hi hk2 hi16 hl
  obtain rfl : k = 2 := by omega
  rw [ctr_get _ _ _ hi16]
  simp only [inT3, show ¬ (2 < 2) from by decide, ite_false]
  have e₁ := hi 1 (by decide) (i % 4) (by omega)
  have e₂ := hi 1 (by decide) (4 * l + i % 4) (by omega)
  rw [show 56 + 8 * 1 + i % 4 = 64 + i % 4 by omega, Nat.mod_mod, show i % 4 / 4 = 0 by omega] at e₁
  rw [show 56 + 8 * 1 + (4 * l + i % 4) = 64 + 4 * l + i % 4 by omega,
    show (4 * l + i % 4) / 4 = l by omega, show (4 * l + i % 4) % 4 = i % 4 by omega] at e₂
  split
  · simp only [T.eval, regn, baseR, e₁, e₂, stateAt_get _ _ hi16]
    by_cases h12 : i = 12
    · subst h12
      simp only [ite_true]
      rw [BitVec.add_comm]; congr 1
      apply BitVec.eq_of_toNat_eq; simp; omega
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h12]
      simp
  · simp only [T.eval, regn, baseR, stateAt_get _ _ hi16]
    rw [ite_eq_right (by omega)]

theorem outT3_eval {vs : Nat → CState} (hz : HB 3 vs s) (hi : Incs s.mem (s.gpr .r9)) {k i l : Nat}
    (hk : k < 3) (hi16 : i < 16) (hl : l < 2) :
    T.eval D s (outT3 k i l) = (plus vs (S0 s) (2 * k + l))[i] := by
  simp only [outT3, plus, Vector.getElem_zipWith]
  rw [← inT3_eval (D := D) hi hk hi16 hl]
  simp only [T.eval, yw, show (4 * l + i % 4) / 4 = l by omega, show (4 * l + i % 4) % 4 = i % 4 by omega]
  rw [hz k hk l hl i hi16]

end

theorem ym3_of {D : Nat} {σ : Sym} {s s' : State} (h : SRel D σ s s') (hm : masks3Ok σ = true)
    (hc : Consts s.mem (s.gpr .r9)) : YM3 s' := by
  simp only [masks3Ok, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at hm
  intro l
  exact ⟨lane_of h .xmm14 32 _ (fun p hp => (hm p hp).1) hc.lo16 hc.hi16 l,
    lane_of h .xmm15 40 _ (fun p hp => (hm p hp).2) hc.m8.1 hc.m8.2 l⟩

/-! ## The instructions -/

theorem setup3_ok {s : State} (hc : Ctx 64 s) (hm : Consts s.mem (s.gpr .r9)) (hi : Incs s.mem (s.gpr .r9)) :
    WP isa (.block setup3) s fun s' =>
      HB 3 (fun j => ctr (S0 s) j) s' ∧ YM3 s' ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  have e := setup3Check_eq
  unfold setup3Check at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc setup3 (SRel.init 64 s) hr) fun s' h => ⟨fun k hk l hl i hi16 => ?_,
      ym3_of h e.1.2 hm, h.clean e.1.1, h.gpr, h.rd, h.wr⟩
    have r := h.reg (zreg (4 * k + i / 4)) (4 * l + i % 4) (by omega)
    rw [xidx_zreg _ (by omega), e.2 k hk _ (by omega) _ (by omega)] at r
    simp only [yw, show (4 * l + i % 4) / 4 = l by omega, show (4 * l + i % 4) % 4 = i % 4 by omega,
      show 4 * (i / 4) + i % 4 = i by omega] at r
    rw [r, inT3_eval hi hk hi16 hl]
  · cases e

theorem last3_ok {s : State} (hc : Ctx 64 s) (hi : Incs s.mem (s.gpr .r9)) {vs : Nat → CState}
    (hz : HB 3 vs s) :
    WP isa (.block (addIn3 ++ xorSetT .xmm0 .xmm1 .xmm2 .xmm3 0 ++ xorSetT .xmm4 .xmm5 .xmm6 .xmm7 128 ++
      storeSetT .xmm8 .xmm9 .xmm10 .xmm11 0)) s fun s' =>
      (∀ k < 256, s'.mem (s.gpr .rsi + BitVec.ofNat 64 k) = s.mem (s.gpr .rsi + BitVec.ofNat 64 k) ^^^
        (serialize (plus vs (S0 s) (k / 64))).getD (k % 64) 0) ∧
      (∀ k < 128, s'.mem (s.gpr .r9 + BitVec.ofNat 64 k) =
        (serialize (plus vs (S0 s) (4 + k / 64))).getD (k % 64) 0) ∧
      Frame (wregs 64 s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := last3Check_eq
  unfold last3Check at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc _ (SRel.init 64 s) hr) fun s' h => ⟨fun k hk => ?_, fun k hk => ?_,
      h.frame, h.gpr, h.rd, h.wr⟩
    · have d := h.mem 2 (k / 4) (by decide) (by simp only [bsize]; omega)
      rw [show k / 4 = 16 * (k / 64) + k % 64 / 4 by omega, e.1 _ (by omega) _ (by omega)] at d
      simp only [T.eval, regn, baseR] at d
      rw [outT3_eval hz hi (by omega) (by omega) (by omega),
        show 2 * (k / 64 / 2) + k / 64 % 2 = k / 64 by omega,
        show 4 * (16 * (k / 64) + k % 64 / 4) = 4 * (k / 4) by omega] at d
      rw [byte_dword s'.mem, byte_dword s.mem, d, BitVec.extractLsb'_xor,
        serialize_getD _ (Nat.mod_lt _ (by decide)), show k % 64 % 4 = k % 4 by omega]
    · refine byte_out (f := fun j => plus vs (S0 s) (4 + j)) ?_
      have d := h.mem 1 (k / 4) (by decide) (by simp only [bsize]; omega)
      rw [show k / 4 = 16 * (k / 64) + k % 64 / 4 by omega, e.2 _ (by omega) _ (by omega),
        outT3_eval hz hi (by decide) (by omega) (by omega), show 2 * 2 + k / 64 = 4 + k / 64 by omega] at d
      simp only [regn, baseR] at d
      rw [show 4 * (16 * (k / 64) + k % 64 / 4) = 4 * (k / 4) by omega] at d
      exact d
  · cases e

end VG.Proof.ChaCha20.X86_64.Avx2Tail
