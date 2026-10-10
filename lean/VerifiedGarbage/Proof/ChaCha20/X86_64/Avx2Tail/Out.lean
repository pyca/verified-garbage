import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Sym
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512Tail.Out

/-!
# ChaCha20 on x86-64 with AVX2, the last bytes: the input states and the output

The terms the code around the rounds leaves (`Sym`), compared by the kernel
with the input states and the keystream blocks, and evaluated.
-/

namespace VG.Proof.ChaCha20.X86_64.Avx2Tail

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2Tail
open VG.Spec.ChaCha20 (Word stateAt serialize)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx512 (T Sym Sym.init xidx xidx_lt xidx_zreg stateAt_get byte_dword add_ofNat')
open VG.Proof.ChaCha20.X86_64.Avx512Tail (bsize regn baseR wregs Ctx S0 byte_out)
open VG.Impl.ChaCha20.X86_64.Avx512 (zreg)
open VG.Proof.ChaCha20.X86_64.Avx2 (plus ctr_get Consts hiR hiR_contains)

/-- The lane increments in `buf`: `0, 1` for the first set and `2, 3` for the
second, each in doubleword 0 of a lane, from `buf + 224`. -/
def Incs (m : Mem) (buf : Addr) : Prop :=
  ∀ k < 2, ∀ p < 8, m.readW (buf + BitVec.ofNat 64 (4 * (56 + 8 * k + p))) 32 =
    if p % 4 = 0 then BitVec.ofNat 32 (2 * k + p / 4) else 0

/-- Word `i` of block `l` of set `k` before the rounds. -/
def inT (k i l : Nat) : T :=
  if i / 4 = 3 then .add (.mem 0 i) (.mem 1 (56 + 8 * k + 4 * l + i % 4)) else .mem 0 i

/-- Word `i` of block `l` of set `k` of the output. -/
def outT (k i l : Nat) : T := .add (.reg (4 * k + i / 4) (4 * l + i % 4)) (inT k i l)

/-- The lane increments survive a frame that does not touch them. -/
theorem incs_frame {buf : Addr} {m m' : Mem} {rs : List Region} (h : Incs m buf) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (hiR buf).Disjoint r) : Incs m' buf := by
  intro k hk p hp
  rw [← h k hk p hp]
  exact hf.readW (hiR_contains buf (by omega) (by omega)) hd (by decide)

/-! ## The kernel's checks -/

/-- The masks, loaded from `buf + 128` and `buf + 160`. -/
def masksOk (σ : Sym) : Bool :=
  (List.range 8).all fun p => σ.reg 8 p == .mem 1 (32 + p) && σ.reg 9 p == .mem 1 (40 + p)

def setupCheck (D : Nat) : Bool :=
  match run D Sym.init setup with
  | some σ => !σ.dirty && masksOk σ && (List.range 2).all fun k => (List.range 4).all fun r =>
      (List.range 8).all fun p => σ.reg (4 * k + r) p == inT k (4 * r + p % 4) (p / 4)
  | none => false

def setup1Check : Bool :=
  match run 0 Sym.init setup1 with
  | some σ => !σ.dirty && masksOk σ && (List.range 4).all fun r =>
      (List.range 8).all fun p => σ.reg r p == inT 0 (4 * r + p % 4) (p / 4)
  | none => false

def lastCheck : Bool :=
  match run 0 Sym.init (addIn ++ storeSet .xmm0 .xmm1 .xmm2 .xmm3 0 ++ storeSet .xmm4 .xmm5 .xmm6 .xmm7 128) with
  | some σ => (List.range 4).all fun j => (List.range 16).all fun i =>
      σ.mem 1 (16 * j + i) == outT (j / 2) i (j % 2)
  | none => false

def last1Check : Bool :=
  match run 0 Sym.init (addIn1 ++ storeSet .xmm0 .xmm1 .xmm2 .xmm3 0) with
  | some σ => (List.range 2).all fun l => (List.range 16).all fun i => σ.mem 1 (16 * l + i) == outT 0 i l
  | none => false

theorem setupCheck_0 : setupCheck 0 = true := by decide +kernel
theorem setup1Check_eq : setup1Check = true := by decide +kernel
theorem lastCheck_eq : lastCheck = true := by decide +kernel
theorem last1Check_eq : last1Check = true := by decide +kernel


/-! ## Evaluation -/

section
variable {D : Nat} {s : State}

theorem inT_eval (hi : Incs s.mem (s.gpr .r9)) {k i l : Nat} (hk : k < 2) (hi16 : i < 16) (hl : l < 2) :
    T.eval D s (inT k i l) = (ctr (S0 s) (2 * k + l))[i] := by
  rw [ctr_get _ _ _ hi16]
  simp only [inT]
  have e := hi k hk (4 * l + i % 4) (by omega)
  rw [show 56 + 8 * k + (4 * l + i % 4) = 56 + 8 * k + 4 * l + i % 4 by omega,
    show (4 * l + i % 4) / 4 = l by omega, show (4 * l + i % 4) % 4 = i % 4 by omega] at e
  split
  · simp only [T.eval, regn, baseR, e, stateAt_get _ _ hi16]
    by_cases h12 : i = 12
    · subst h12; simp
    · rw [ite_eq_right (by omega), ite_eq_right h12]; exact BitVec.add_zero _
  · simp only [T.eval, regn, baseR, stateAt_get _ _ hi16]
    rw [ite_eq_right (by omega)]

theorem outT_eval {S : Nat} {vs : Nat → CState} (hz : HB S vs s) (hi : Incs s.mem (s.gpr .r9)) {k i l : Nat}
    (hk : k < S) (hk2 : k < 2) (hi16 : i < 16) (hl : l < 2) :
    T.eval D s (outT k i l) = (plus vs (S0 s) (2 * k + l))[i] := by
  simp only [outT, plus, Vector.getElem_zipWith]
  rw [← inT_eval (D := D) hi hk2 hi16 hl]
  simp only [T.eval, yw, show (4 * l + i % 4) / 4 = l by omega, show (4 * l + i % 4) % 4 = i % 4 by omega]
  rw [hz k hk l hl i hi16]

end

/-- A register loaded with the 32 bytes at `buf + 4 o`, each lane `x`. -/
theorem lane_of {D : Nat} {σ : Sym} {s s' : State} (h : SRel D σ s s') (r : XReg) (o : Nat) (x : BitVec 128)
    (hr : ∀ p < 8, σ.reg (xidx r) p = .mem 1 (o + p))
    (h0 : (s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 (4 * o)) 256).extractLsb' 0 128 = x)
    (h1 : (s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 (4 * o)) 256).extractLsb' 128 128 = x) :
    ∀ l, s'.lane r l = x := by
  have hl : ∀ l < 2, s'.lane r l = x := by
    intro l hl
    have dq : ∀ q < 4, dword (s'.lane r l) q = dword x q := by
      intro q hq
      rw [← yw_lk s' r hq, h.reg r _ (by omega), hr _ (by omega)]
      simp only [T.eval, regn, baseR]
      have d := dword_read256 s.mem (s.gpr .r9 + BitVec.ofNat 64 (4 * o)) (p := 4 * l + q) (by omega)
      rw [show (4 * l + q) / 4 = l by omega, show (4 * l + q) % 4 = q by omega, add_ofNat',
        show 4 * o + 4 * (4 * l + q) = 4 * (o + (4 * l + q)) by omega] at d
      rw [← d]
      rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
      · rw [Nat.mul_zero, h0]
      · rw [Nat.mul_one, h1]
    exact ext_dword (dq 0 (by decide)) (dq 1 (by decide)) (dq 2 (by decide)) (dq 3 (by decide))
  intro l
  by_cases h0 : l = 0
  · exact hl l (by omega)
  · rw [show s'.lane r l = s'.lane r 1 by simp [State.lane, h0]]; exact hl 1 (by decide)

/-- The masks in `ymm8`, `ymm9`, from the terms the setup leaves there. -/
theorem ym_of {D : Nat} {σ : Sym} {s s' : State} (h : SRel D σ s s') (hm : masksOk σ = true)
    (hc : Consts s.mem (s.gpr .r9)) : YM s' := by
  simp only [masksOk, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at hm
  intro l
  exact ⟨lane_of h .xmm8 32 _ (fun p hp => (hm p hp).1) hc.lo16 hc.hi16 l,
    lane_of h .xmm9 40 _ (fun p hp => (hm p hp).2) hc.m8.1 hc.m8.2 l⟩

/-! ## The instructions -/

theorem setup_ok {s : State} (hc : Ctx 0 s) (hm : Consts s.mem (s.gpr .r9))
    (hi : Incs s.mem (s.gpr .r9)) :
    WP isa (.block setup) s fun s' =>
      HB 2 (fun j => ctr (S0 s) j) s' ∧ YM s' ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  have e := setupCheck_0
  unfold setupCheck at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc setup (SRel.init 0 s) hr) fun s' h => ⟨fun k hk l hl i hi16 => ?_,
      ym_of h e.1.2 hm, h.clean e.1.1, h.gpr, h.rd, h.wr⟩
    have r := h.reg (zreg (4 * k + i / 4)) (4 * l + i % 4) (by omega)
    rw [xidx_zreg _ (by omega), e.2 k hk _ (by omega) _ (by omega)] at r
    simp only [yw, show (4 * l + i % 4) / 4 = l by omega, show (4 * l + i % 4) % 4 = i % 4 by omega,
      show 4 * (i / 4) + i % 4 = i by omega] at r
    rw [r, inT_eval hi hk hi16 hl]
  · cases e

theorem setup1_ok {s : State} (hc : Ctx 0 s) (hm : Consts s.mem (s.gpr .r9)) (hi : Incs s.mem (s.gpr .r9)) :
    WP isa (.block setup1) s fun s' =>
      HB 1 (fun j => ctr (S0 s) j) s' ∧ YM s' ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  have e := setup1Check_eq
  unfold setup1Check at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc setup1 (SRel.init 0 s) hr) fun s' h => ⟨fun k hk l hl i hi16 => ?_,
      ym_of h e.1.2 hm, h.clean e.1.1, h.gpr, h.rd, h.wr⟩
    obtain rfl : k = 0 := by omega
    have r := h.reg (zreg (4 * 0 + i / 4)) (4 * l + i % 4) (by omega)
    rw [xidx_zreg _ (by omega), e.2 _ (by omega) _ (by omega)] at r
    simp only [yw, show (4 * l + i % 4) / 4 = l by omega, show (4 * l + i % 4) % 4 = i % 4 by omega,
      show 4 * (4 * 0 + i / 4) + i % 4 = i by omega] at r
    rw [r, inT_eval hi (by decide) hi16 hl]
  · cases e

theorem last_ok {s : State} (hc : Ctx 0 s) (hi : Incs s.mem (s.gpr .r9)) {vs : Nat → CState}
    (hz : HB 2 vs s) :
    WP isa (.block (addIn ++ storeSet .xmm0 .xmm1 .xmm2 .xmm3 0 ++ storeSet .xmm4 .xmm5 .xmm6 .xmm7 128)) s
      fun s' =>
      (∀ k < 256, s'.mem (s.gpr .r9 + BitVec.ofNat 64 k) = (serialize (plus vs (S0 s) (k / 64))).getD (k % 64) 0) ∧
      Frame (wregs 0 s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := lastCheck_eq
  unfold lastCheck at e
  split at e
  · rename_i σ hr
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc _ (SRel.init 0 s) hr) fun s' h => ⟨fun k hk => ?_, h.frame, h.gpr,
      h.rd, h.wr⟩
    refine byte_out ?_
    have d := h.mem 1 (k / 4) (by decide) (by simp only [bsize]; omega)
    rw [show k / 4 = 16 * (k / 64) + k % 64 / 4 by omega, e _ (by omega) _ (by omega),
      outT_eval hz hi (by omega) (by omega) (by omega) (by omega),
      show 2 * (k / 64 / 2) + k / 64 % 2 = k / 64 by omega] at d
    simp only [regn, baseR] at d
    rw [show 4 * (16 * (k / 64) + k % 64 / 4) = 4 * (k / 4) by omega] at d
    exact d
  · cases e

theorem last1_ok {s : State} (hc : Ctx 0 s) (hi : Incs s.mem (s.gpr .r9)) {vs : Nat → CState}
    (hz : HB 1 vs s) :
    WP isa (.block (addIn1 ++ storeSet .xmm0 .xmm1 .xmm2 .xmm3 0)) s fun s' =>
      (∀ k < 128, s'.mem (s.gpr .r9 + BitVec.ofNat 64 k) = (serialize (plus vs (S0 s) (k / 64))).getD (k % 64) 0) ∧
      Frame (wregs 0 s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := last1Check_eq
  unfold last1Check at e
  split at e
  · rename_i σ hr
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc _ (SRel.init 0 s) hr) fun s' h => ⟨fun k hk => ?_, h.frame, h.gpr,
      h.rd, h.wr⟩
    refine byte_out ?_
    have d := h.mem 1 (k / 4) (by decide) (by simp only [bsize]; omega)
    rw [show k / 4 = 16 * (k / 64) + k % 64 / 4 by omega, e _ (by omega) _ (by omega),
      outT_eval hz hi (by decide) (by decide) (by omega) (by omega)] at d
    simp only [regn, baseR] at d
    rw [show 4 * (16 * (k / 64) + k % 64 / 4) = 4 * (k / 4) by omega, Nat.mul_zero, Nat.zero_add] at d
    exact d
  · cases e

end VG.Proof.ChaCha20.X86_64.Avx2Tail
