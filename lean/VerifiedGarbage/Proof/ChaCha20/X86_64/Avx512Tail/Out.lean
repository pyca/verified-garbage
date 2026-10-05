import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512Tail.Sym
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Finish

/-!
# ChaCha20 on x86-64 with AVX-512, the last bytes: the input states and the output

The terms the code around the rounds leaves (`Sym`), compared by the kernel
with the input states and the keystream blocks, and evaluated.
-/

namespace VG.Proof.ChaCha20.X86_64.Avx512Tail

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512Tail
open VG.Spec.ChaCha20 (Word stateAt serialize)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx512 (T Sym Sym.init xidx xidx_lt zw xidx_zreg stateAt_get byte_dword
  add_ofNat')
open VG.Impl.ChaCha20.X86_64.Avx512 (zreg)
open VG.Proof.ChaCha20.X86_64.Avx2 (plus ctr_get)

/-- The first doubleword of the lane increments of set `k` in `buf`. -/
def incB : Nat → Nat
  | 0 => 64 | _ => 48

/-- The lane increments in `buf`: `0, 1, 2, 3` for the first set and `4, 5,
6, 7` for the second, each in doubleword 0 of a lane. -/
def Incs (m : Mem) (buf : Addr) : Prop :=
  ∀ k < 2, ∀ p < 16, m.readW (buf + BitVec.ofNat 64 (4 * (incB k + p))) 32 =
    if p % 4 = 0 then BitVec.ofNat 32 (4 * k + p / 4) else 0

/-- Word `i` of block `l` of set `k` before the rounds: word `i` of the
state, with the lane increment added to row 3. -/
def inT (k i l : Nat) : T :=
  if i / 4 = 3 then .add (.mem 0 i) (.mem 1 (incB k + 4 * l + i % 4)) else .mem 0 i

/-- Word `i` of block `l` of set `k` of the output: the rounds' result plus
the input. -/
def outT (k i l : Nat) : T :=
  .add (.reg (4 * k + i / 4) (4 * l + i % 4)) (inT k i l)

/-- The same, as `finish2` adds row 3 of the input. -/
def outT2 (k i l : Nat) : T :=
  .add (.reg (4 * k + i / 4) (4 * l + i % 4))
    (if i / 4 = 3 then .add (.mem 1 (incB k + 4 * l + i % 4)) (.mem 0 i) else .mem 0 i)

/-! ## The kernel's checks -/

def setupCheck : Bool :=
  match run 0 Sym.init setup with
  | some σ => !σ.dirty && (List.range 4).all fun r => (List.range 16).all fun p =>
      σ.reg r p == inT 0 (4 * r + p % 4) (p / 4)
  | none => false

def setup2Check (D : Nat) : Bool :=
  match run D Sym.init setup2 with
  | some σ => !σ.dirty && (List.range 2).all fun k => (List.range 4).all fun r => (List.range 16).all fun p =>
      σ.reg (4 * k + r) p == inT k (4 * r + p % 4) (p / 4)
  | none => false

def finishCheck : Bool :=
  match run 0 Sym.init finish with
  | some σ => (List.range 4).all fun l => (List.range 16).all fun i => σ.mem 1 (16 * l + i) == outT 0 i l
  | none => false

def fullCheck : Bool :=
  match run 128 Sym.init (finish2 ++ xor256 .xmm0 .xmm1 .xmm2 .xmm3 0 ++ xor256 .xmm4 .xmm5 .xmm6 .xmm7 256) with
  | some σ =>
    ((List.range 8).all fun j => (List.range 16).all fun i =>
      σ.mem 2 (16 * j + i) == .xor (.mem 2 (16 * j + i)) (outT2 (j / 4) i (j % 4))) &&
    (List.range 80).all fun i => σ.mem 1 i == .mem 1 i
  | none => false

def partCheck : Bool :=
  match run 64 Sym.init (finish2 ++ xor256 .xmm0 .xmm1 .xmm2 .xmm3 0 ++ store .xmm4 .xmm5 .xmm6 .xmm7) with
  | some σ =>
    (List.range 4).all fun l => (List.range 16).all fun i =>
      σ.mem 2 (16 * l + i) == .xor (.mem 2 (16 * l + i)) (outT2 0 i l) &&
      σ.mem 1 (16 * l + i) == outT2 1 i l
  | none => false

theorem setupCheck_eq : setupCheck = true := by decide +kernel
theorem setup2Check_128 : setup2Check 128 = true := by decide +kernel
theorem setup2Check_64 : setup2Check 64 = true := by decide +kernel
theorem finishCheck_eq : finishCheck = true := by decide +kernel
theorem fullCheck_eq : fullCheck = true := by decide +kernel
theorem partCheck_eq : partCheck = true := by decide +kernel


/-! ## Evaluation -/

section
variable {D : Nat} {s : State}

/-- The state at `rdi`. -/
abbrev S0 (s : State) : CState := stateAt s.mem (s.gpr .rdi)

theorem inT_eval (hi : Incs s.mem (s.gpr .r9)) {k i l : Nat} (hk : k < 2) (hi16 : i < 16) (hl : l < 4) :
    T.eval D s (inT k i l) = (ctr (S0 s) (4 * k + l))[i] := by
  rw [ctr_get _ _ _ hi16]
  simp only [inT]
  have e := hi k hk (4 * l + i % 4) (by omega)
  rw [show incB k + (4 * l + i % 4) = incB k + 4 * l + i % 4 by omega,
    show (4 * l + i % 4) / 4 = l by omega, show (4 * l + i % 4) % 4 = i % 4 by omega] at e
  split
  · rename_i h3
    simp only [T.eval, regn, baseR, e, stateAt_get _ _ hi16]
    by_cases h12 : i = 12
    · subst h12; simp
    · rw [ite_eq_right (by omega), ite_eq_right h12]; exact BitVec.add_zero _
  · simp only [T.eval, regn, baseR, stateAt_get _ _ hi16]
    rw [ite_eq_right (by omega)]

theorem reg_eval {S : Nat} {vs : Nat → CState} (hz : HB S vs s) {k i l : Nat} (hk : k < S) (hi : i < 16)
    (hl : l < 4) : T.eval D s (.reg (4 * k + i / 4) (4 * l + i % 4)) = (vs (4 * k + l))[i] := by
  simp only [T.eval, zw, show (4 * l + i % 4) / 4 = l by omega, show (4 * l + i % 4) % 4 = i % 4 by omega]
  exact hz k hk l hl i hi

theorem outT_eval {S : Nat} {vs : Nat → CState} (hz : HB S vs s) (hi : Incs s.mem (s.gpr .r9)) {k i l : Nat}
    (hk : k < S) (hk2 : k < 2) (hi16 : i < 16) (hl : l < 4) :
    T.eval D s (outT k i l) = (plus vs (S0 s) (4 * k + l))[i] := by
  simp only [outT, plus, Vector.getElem_zipWith]
  rw [← inT_eval (D := D) hi hk2 hi16 hl, ← reg_eval hz hk hi16 hl]
  rfl

theorem outT2_eval {S : Nat} {vs : Nat → CState} (hz : HB S vs s) (hi : Incs s.mem (s.gpr .r9)) {k i l : Nat}
    (hk : k < S) (hk2 : k < 2) (hi16 : i < 16) (hl : l < 4) :
    T.eval D s (outT2 k i l) = (plus vs (S0 s) (4 * k + l))[i] := by
  rw [← outT_eval (D := D) hz hi hk hk2 hi16 hl]
  simp only [outT2, outT, inT]
  split
  · simp only [T.eval]; exact congrArg _ (BitVec.add_comm _ _)
  · rfl

end

/-! ## The instructions -/

theorem setup_ok {s : State} (hc : Ctx 0 s) (hi : Incs s.mem (s.gpr .r9)) :
    WP isa (.block setup) s fun s' =>
      HB 1 (fun j => ctr (S0 s) j) s' ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := setupCheck_eq
  unfold setupCheck at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc setup (SRel.init 0 s) hr) fun s' h => ⟨fun k hk l hl i hi16 => ?_,
      h.clean e.1, h.gpr, h.rd, h.wr⟩
    obtain rfl : k = 0 := by omega
    have r := h.reg (zreg (4 * 0 + i / 4)) (4 * l + i % 4) (by omega)
    rw [xidx_zreg _ (by omega), e.2 _ (by omega) _ (by omega)] at r
    simp only [zw, show (4 * l + i % 4) / 4 = l by omega, show (4 * l + i % 4) % 4 = i % 4 by omega,
      show 4 * (4 * 0 + i / 4) + i % 4 = i by omega] at r
    rw [r, inT_eval hi (by decide) hi16 hl]
  · cases e

theorem setup2_ok {D : Nat} (hD : D = 128 ∨ D = 64) {s : State} (hc : Ctx D s) (hi : Incs s.mem (s.gpr .r9)) :
    WP isa (.block setup2) s fun s' =>
      HB 2 (fun j => ctr (S0 s) j) s' ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e : setup2Check D = true := by rcases hD with rfl | rfl; exacts [setup2Check_128, setup2Check_64]
  unfold setup2Check at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc setup2 (SRel.init D s) hr) fun s' h => ⟨fun k hk l hl i hi16 => ?_,
      h.clean e.1, h.gpr, h.rd, h.wr⟩
    have r := h.reg (zreg (4 * k + i / 4)) (4 * l + i % 4) (by omega)
    rw [xidx_zreg _ (by omega), e.2 k hk _ (by omega) _ (by omega)] at r
    simp only [zw, show (4 * l + i % 4) / 4 = l by omega, show (4 * l + i % 4) % 4 = i % 4 by omega,
      show 4 * (i / 4) + i % 4 = i by omega] at r
    rw [r, inT_eval hi hk hi16 hl]
  · cases e

/-- A byte of the output, from its doubleword. -/
theorem byte_out {m : Mem} {a : Addr} {f : Nat → CState} {k : Nat}
    (h : m.readW (a + BitVec.ofNat 64 (4 * (k / 4))) 32 = (f (k / 64))[k % 64 / 4]'(by omega)) :
    m (a + BitVec.ofNat 64 k) = (serialize (f (k / 64))).getD (k % 64) 0 := by
  rw [byte_dword m a k, h, serialize_getD _ (Nat.mod_lt _ (by decide)), show k % 64 % 4 = k % 4 by omega]

theorem finish_ok {s : State} (hc : Ctx 0 s) (hi : Incs s.mem (s.gpr .r9)) {vs : Nat → CState}
    (hz : HB 1 vs s) :
    WP isa (.block finish) s fun s' =>
      (∀ k < 256, s'.mem (s.gpr .r9 + BitVec.ofNat 64 k) = (serialize (plus vs (S0 s) (k / 64))).getD (k % 64) 0) ∧
      Frame (wregs 0 s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := finishCheck_eq
  unfold finishCheck at e
  split at e
  · rename_i σ hr
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc finish (SRel.init 0 s) hr) fun s' h => ⟨fun k hk => ?_, h.frame, h.gpr,
      h.rd, h.wr⟩
    refine byte_out ?_
    have d := h.mem 1 (k / 4) (by decide) (by simp only [bsize]; omega)
    rw [show k / 4 = 16 * (k / 64) + k % 64 / 4 by omega, e _ (by omega) _ (by omega),
      outT_eval hz hi (by decide) (by decide) (by omega) (by omega)] at d
    simp only [regn, baseR] at d
    rw [show 4 * (16 * (k / 64) + k % 64 / 4) = 4 * (k / 4) by omega, Nat.mul_zero, Nat.zero_add] at d
    exact d
  · cases e

theorem full_ok {s : State} (hc : Ctx 128 s) (hi : Incs s.mem (s.gpr .r9)) {vs : Nat → CState}
    (hz : HB 2 vs s) :
    WP isa (.block (finish2 ++ xor256 .xmm0 .xmm1 .xmm2 .xmm3 0 ++ xor256 .xmm4 .xmm5 .xmm6 .xmm7 256)) s
      fun s' =>
      (∀ k < 512, s'.mem (s.gpr .rsi + BitVec.ofNat 64 k) = s.mem (s.gpr .rsi + BitVec.ofNat 64 k) ^^^
        (serialize (plus vs (S0 s) (k / 64))).getD (k % 64) 0) ∧
      (∀ i < 80, s'.mem.readW (s.gpr .r9 + BitVec.ofNat 64 (4 * i)) 32 =
        s.mem.readW (s.gpr .r9 + BitVec.ofNat 64 (4 * i)) 32) ∧
      Frame (wregs 128 s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := fullCheck_eq
  unfold fullCheck at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc _ (SRel.init 128 s) hr) fun s' h => ⟨fun k hk => ?_, fun i hi' => ?_,
      h.frame, h.gpr, h.rd, h.wr⟩
    · have d := h.mem 2 (k / 4) (by decide) (by simp only [bsize]; omega)
      rw [show k / 4 = 16 * (k / 64) + k % 64 / 4 by omega, e.1 _ (by omega) _ (by omega)] at d
      simp only [T.eval, regn, baseR] at d
      rw [outT2_eval hz hi (by omega) (by omega) (by omega) (by omega),
        show 4 * (k / 64 / 4) + k / 64 % 4 = k / 64 by omega,
        show 4 * (16 * (k / 64) + k % 64 / 4) = 4 * (k / 4) by omega] at d
      rw [byte_dword s'.mem, byte_dword s.mem, d, BitVec.extractLsb'_xor,
        serialize_getD _ (Nat.mod_lt _ (by decide)), show k % 64 % 4 = k % 4 by omega]
    · have d := h.mem 1 i (by decide) (by simp only [bsize]; omega)
      rw [e.2 i hi'] at d
      simpa only [T.eval, regn, baseR] using d
  · cases e

theorem part_ok {s : State} (hc : Ctx 64 s) (hi : Incs s.mem (s.gpr .r9)) {vs : Nat → CState}
    (hz : HB 2 vs s) :
    WP isa (.block (finish2 ++ xor256 .xmm0 .xmm1 .xmm2 .xmm3 0 ++ store .xmm4 .xmm5 .xmm6 .xmm7)) s
      fun s' =>
      (∀ k < 256, s'.mem (s.gpr .rsi + BitVec.ofNat 64 k) = s.mem (s.gpr .rsi + BitVec.ofNat 64 k) ^^^
        (serialize (plus vs (S0 s) (k / 64))).getD (k % 64) 0) ∧
      (∀ k < 256, s'.mem (s.gpr .r9 + BitVec.ofNat 64 k) =
        (serialize (plus vs (S0 s) (4 + k / 64))).getD (k % 64) 0) ∧
      Frame (wregs 64 s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := partCheck_eq
  unfold partCheck at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc _ (SRel.init 64 s) hr) fun s' h => ⟨fun k hk => ?_, fun k hk => ?_,
      h.frame, h.gpr, h.rd, h.wr⟩
    · have d := h.mem 2 (k / 4) (by decide) (by simp only [bsize]; omega)
      rw [show k / 4 = 16 * (k / 64) + k % 64 / 4 by omega, (e _ (by omega) _ (by omega)).1] at d
      simp only [T.eval, regn, baseR] at d
      rw [outT2_eval hz hi (by decide) (by decide) (by omega) (by omega), Nat.mul_zero, Nat.zero_add,
        show 4 * (16 * (k / 64) + k % 64 / 4) = 4 * (k / 4) by omega] at d
      rw [byte_dword s'.mem, byte_dword s.mem, d, BitVec.extractLsb'_xor,
        serialize_getD _ (Nat.mod_lt _ (by decide)), show k % 64 % 4 = k % 4 by omega]
    · have d := h.mem 1 (k / 4) (by decide) (by simp only [bsize]; omega)
      rw [show k / 4 = 16 * (k / 64) + k % 64 / 4 by omega, (e _ (by omega) _ (by omega)).2,
        outT2_eval hz hi (by decide) (by decide) (by omega) (by omega)] at d
      simp only [regn, baseR] at d
      rw [show 4 * (16 * (k / 64) + k % 64 / 4) = 4 * (k / 4) by omega, Nat.mul_one] at d
      rw [byte_dword s'.mem, d, serialize_getD _ (Nat.mod_lt _ (by decide)),
        show k % 64 % 4 = k % 4 by omega]
  · cases e

end VG.Proof.ChaCha20.X86_64.Avx512Tail
