import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Finish
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512Tail.Tail

/-!
# ChaCha20 on x86-64 with AVX-512: the last 513 to 1023 bytes

`last16`, from the state after the sixteen-block loop of
`vg_chacha20_xor_avx512` (`Avx512Tail.TInv`, with 513 to 1023 bytes left)
to the end of the function. The code around the rounds runs with `buf` at
`r9`, so that the checks of the last bytes (`Avx512Tail.run`), which allow
at most 512 bytes of data, cover it: `finishP` writes only the first 512
bytes, and the code after it the next ones, from `rsi + 512`.
-/

namespace VG.Proof.ChaCha20.X86_64.Avx512Last

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word stateAt keystream serialize)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx512 (T Sym Sym.init xidx xidx_lt zw xidx_zreg stateAt_get ZH Incs
  setupT outT)
open VG.Proof.ChaCha20.X86_64.Avx512Tail (run Ctx SRel srun_ok regn baseR bsize wregs)
open VG.Proof.ChaCha20.X86_64.Avx2 (APre est edp eL ebp edR D0 KS frR eL_lt add_ofNat in_dR plus
  plus_block ctr_get ctr_ctr calleeSaved_ne xorAvx2X86_64)

/-! ## The kernel's checks -/

def setupCheck : Bool :=
  match run 0 Sym.init (setupB .r9) with
  | some σ => !σ.dirty && (List.range 16).all fun k => (List.range 16).all fun p => σ.reg k p == setupT k p
  | none => false

def finishCheck : Bool :=
  match run 128 Sym.init finishP with
  | some σ =>
    ((List.range 128).all fun i => σ.mem 2 i == .xor (.mem 2 i) (outT (i % 16) (i / 16))) &&
    (List.range 8).all fun j => (List.range 16).all fun p =>
      σ.reg (xidx (blkReg (8 + j))) p == outT p (8 + j)
  | none => false

/-- Both branches of `cond j`, for each `j`: the block register into the
data, or into `buf`, and the other block registers kept. -/
def condCheck : Bool :=
  (List.range 8).all fun j =>
    (match run (16 * j + 16) Sym.init (xor64 (blkReg (8 + j)) .xmm2 (64 * j)) with
     | some σ =>
       ((List.range 16).all fun i =>
         σ.mem 2 (16 * j + i) == .xor (.mem 2 (16 * j + i)) (.reg (xidx (blkReg (8 + j))) i)) &&
       ((List.range (16 * j)).all fun i => σ.mem 2 i == .mem 2 i) &&
       ((List.range 16).all fun i => σ.mem 1 i == .mem 1 i) &&
       (List.range 8).all fun l => (List.range 16).all fun p =>
         σ.reg (xidx (blkReg (8 + l))) p == .reg (xidx (blkReg (8 + l))) p
     | none => false) &&
    (match run 0 Sym.init [.vmovdqu32Store (at_ .r9 0) (blkReg (8 + j))] with
     | some σ =>
       ((List.range 16).all fun i => σ.mem 1 i == .reg (xidx (blkReg (8 + j))) i) &&
       (List.range 8).all fun l => (List.range 16).all fun p =>
         σ.reg (xidx (blkReg (8 + l))) p == .reg (xidx (blkReg (8 + l))) p
     | none => false)

theorem setupCheck_eq : setupCheck = true := by decide +kernel
theorem finishCheck_eq : finishCheck = true := by decide +kernel
theorem condCheck_eq : condCheck = true := by decide +kernel

/-! ## Evaluation -/

/-- The state at `rdi`. -/
abbrev S0 (s : State) : CState := stateAt s.mem (s.gpr .rdi)

theorem outT_eval {D : Nat} {s : State} {vs : Nat → CState} (hz : ZH vs s) (hi : Incs s.mem (s.gpr .r9))
    {w j : Nat} (hw : w < 16) (hj : j < 16) :
    Avx512Tail.T.eval D s (outT w j) = (plus vs (S0 s) j)[w] := by
  have r := hz (Impl.ChaCha20.X86_64.Avx512.zreg w) j hj
  simp only [xidx_zreg w hw] at r
  simp only [plus, Vector.getElem_zipWith, ctr_get _ _ _ hw, outT]
  split
  · rename_i e; subst e
    simp only [Avx512Tail.T.eval, regn, baseR, r, stateAt_get _ _ (show 12 < 16 by decide), hi j hj,
      BitVec.add_assoc]
  · simp only [Avx512Tail.T.eval, regn, baseR, r, stateAt_get _ _ hw]

/-! ## The sixteen input states -/

theorem setup_ok {s : State} (hc : Ctx 0 s) (hi : Incs s.mem (s.gpr .r9)) :
    WP isa (.block (setupB .r9)) s fun s' =>
      ZH (fun j => ctr (S0 s) j) s' ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := setupCheck_eq
  unfold setupCheck at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc _ (SRel.init 0 s) hr) fun s' h => ⟨fun r j hj => ?_,
      h.clean e.1, h.gpr, h.rd, h.wr⟩
    rw [h.reg r j hj, e.2 _ (xidx_lt r) j hj, ctr_get _ _ _ (xidx_lt r)]
    simp only [setupT]
    split
    · simp only [Avx512Tail.T.eval, regn, baseR]
      rw [stateAt_get _ _ (by decide), hi j hj]
    · simp only [Avx512Tail.T.eval, regn, baseR]
      exact stateAt_get _ _ (xidx_lt r)
  · cases e

/-! ## The output -/

/-- The first eight blocks into the data, the next eight left in registers. -/
theorem finish_ok {s : State} (hc : Ctx 128 s) (hi : Incs s.mem (s.gpr .r9)) {vs : Nat → CState}
    (hz : ZH vs s) :
    WP isa (.block finishP) s fun s' =>
      (∀ k < 512, s'.mem (s.gpr .rsi + BitVec.ofNat 64 k) = s.mem (s.gpr .rsi + BitVec.ofNat 64 k) ^^^
        (serialize (plus vs (S0 s) (k / 64))).getD (k % 64) 0) ∧
      (∀ j < 8, ∀ p (hp : p < 16), zw s' (blkReg (8 + j)) p = (plus vs (S0 s) (8 + j))[p]'hp) ∧
      Frame (wregs 128 s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := finishCheck_eq
  unfold finishCheck at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc _ (SRel.init 128 s) hr) fun s' h => ⟨fun k hk => ?_, fun j hj p hp => ?_,
      h.frame, h.gpr, h.rd, h.wr⟩
    · have d := h.mem 2 (k / 4) (by decide) (by simp only [bsize]; omega)
      rw [e.1 _ (by omega)] at d
      simp only [Avx512Tail.T.eval, regn, baseR] at d
      rw [show k / 4 / 16 = k / 64 by omega, show k / 4 % 16 = k % 64 / 4 by omega,
        outT_eval hz hi (by omega) (by omega)] at d
      rw [Avx512.byte_dword s'.mem, Avx512.byte_dword s.mem, d, BitVec.extractLsb'_xor,
        serialize_getD _ (Nat.mod_lt _ (by decide)), show k % 64 % 4 = k % 4 by omega]
    · rw [h.reg _ p hp, e.2 j hj p hp, outT_eval hz hi hp (by omega)]
  · cases e

/-! ## The next eight blocks, as far as they fit -/

theorem condX_run {j : Nat} (hj : j < 8) : ∃ σ, run (16 * j + 16) Sym.init (xor64 (blkReg (8 + j)) .xmm2 (64 * j)) = some σ ∧
    (∀ i < 16, σ.mem 2 (16 * j + i) = .xor (.mem 2 (16 * j + i)) (.reg (xidx (blkReg (8 + j))) i)) ∧
    (∀ i < 16 * j, σ.mem 2 i = .mem 2 i) ∧ (∀ i < 16, σ.mem 1 i = .mem 1 i) ∧
    (∀ l < 8, ∀ p < 16, σ.reg (xidx (blkReg (8 + l))) p = .reg (xidx (blkReg (8 + l))) p) := by
  have e := condCheck_eq
  simp only [condCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true] at e
  have e := (e j hj).1
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at e
    exact ⟨σ, hr, e.1.1.1, e.1.1.2, e.1.2, e.2⟩
  · cases e

theorem condS_run {j : Nat} (hj : j < 8) : ∃ σ, run 0 Sym.init [.vmovdqu32Store (at_ .r9 0) (blkReg (8 + j))] = some σ ∧
    (∀ i < 16, σ.mem 1 i = .reg (xidx (blkReg (8 + j))) i) ∧
    (∀ l < 8, ∀ p < 16, σ.reg (xidx (blkReg (8 + l))) p = .reg (xidx (blkReg (8 + l))) p) := by
  have e := condCheck_eq
  simp only [condCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true] at e
  have e := (e j hj).2
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at e
    exact ⟨σ, hr, e.1, e.2⟩
  · cases e

/-- Where `cond` runs: the data from byte `q` on (fewer than 512 bytes of
it left), `buf` at `r9`. -/
structure At (s₀ : State) (q : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = est s₀
  r9 : s.gpr .r9 = ebp s₀
  rsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 q
  rdx : s.gpr .rdx = BitVec.ofNat 64 (eL s₀ - q)
  le : q ≤ eL s₀
  small : eL s₀ - q < 512
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem At.of_gpr {s₀ : State} {q : Nat} {s s' : State} (h : At s₀ q s) (hg : s'.gpr = s.gpr)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : At s₀ q s' :=
  ⟨by rw [hg]; exact h.rdi, by rw [hg]; exact h.r9, by rw [hg]; exact h.rsi, by rw [hg]; exact h.rdx,
    h.le, h.small, hrd.trans h.rd, hwr.trans h.wr⟩

set_option simprocs false in
theorem cmpJ_ok {s₀ : State} {q j : Nat} (hj : j < 8) {s : State} (h : At s₀ q s) :
    WP isa (.block [.alu .cmp .rdx (.imm (BitVec.ofNat 32 (64 * j + 64)))]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r p, zw s' r p = zw s r p) ∧ s'.cf = some (decide (eL s₀ - q < 64 * j + 64)) := by
  have hL := eL_lt s₀
  have se : BitVec.signExtend 64 (BitVec.ofNat 32 (64 * j + 64)) = BitVec.ofNat 64 (64 * j + 64) := by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', se]
  refine ⟨trivial, trivial, trivial, trivial, fun _ _ => rfl, ?_⟩
  rw [h.rdx, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]

theorem bufR_sub (b : Addr) {n : Nat} (hn : n ≤ 320) : Region.Sub ⟨b, n⟩ (Avx2.bufR b) :=
  Region.sub_prefix hn

/-- Block `8 + j` into the data, if it fits, or else into `buf`. -/
theorem cond_ok {s₀ : State} (hp : APre s₀) {q j : Nat} (hj : j < 8) {s : State} (h : At s₀ q s)
    {B : CState} (hB : ∀ p (hp : p < 16), zw s (blkReg (8 + j)) p = B[p]'hp) :
    WP isa (cond j) s fun s' => At s₀ q s' ∧ s'.gpr = s.gpr ∧
      (∀ l < 8, ∀ p < 16, zw s' (blkReg (8 + l)) p = zw s (blkReg (8 + l)) p) ∧
      (∀ k < eL s₀ - q, s'.mem (edp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k) =
        if 64 * j + 64 ≤ eL s₀ - q ∧ k / 64 = j then
          s.mem (edp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k) ^^^ (serialize B).getD (k % 64) 0
        else s.mem (edp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k)) ∧
      (∀ k < 64, s'.mem (ebp s₀ + BitVec.ofNat 64 k) =
        if 64 * j + 64 ≤ eL s₀ - q then s.mem (ebp s₀ + BitVec.ofNat 64 k) else (serialize B).getD k 0) ∧
      Frame [Avx2.bufR (ebp s₀), Avx512Tail.win s₀ q (eL s₀ - q)] s.mem s'.mem := by
  have hL := eL_lt s₀
  have hle := h.le
  have hsm := h.small
  refine WP.seq (WP.mono (cmpJ_ok hj h) fun s₁ ⟨g₁, m₁, rd₁, wr₁, z₁, c₁⟩ => ?_)
  have h₁ : At s₀ q s₁ := h.of_gpr g₁ rd₁ wr₁
  have nb : ∀ k < eL s₀ - q, ¬ (⟨ebp s₀, 256⟩ : Region).Contains (edp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k) 1 :=
    fun k hk hc => hp.d_b _ (by rw [add_ofNat]; exact in_dR (by omega)) (bufR_sub _ (by omega) _ hc)
  refine WP.ite (decide (eL s₀ - q < 64 * j + 64)) (by simp [eval, c₁]) (fun hs => ?_) (fun hs => ?_)
  · -- The block does not fit: into `buf`.
    simp only [decide_eq_true_eq] at hs
    obtain ⟨σ, hr, hm, hk⟩ := condS_run hj
    have hc : Ctx 0 s₁ := Avx512Tail.ctx_of hp (D := 0) (p := q) (by omega) (by decide) h₁.rdi h₁.r9 h₁.rsi h₁.wr
    refine WP.mono (srun_ok hc _ (SRel.init 0 s₁) hr) fun s₂ e => ⟨h₁.of_gpr e.gpr e.rd e.wr,
      e.gpr.trans g₁, fun l hl p hp' => ?_, fun k hk => ?_, fun k hk => ?_, ?_⟩
    · rw [e.reg _ p hp', hk l hl p hp']
      simp only [Avx512Tail.T.eval, Avx512.zreg_xidx, z₁]
    · rw [ite_eq_right (by omega), e.frame _ (by
        intro r hr; simp only [wregs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.r9]; exact nb k hk
        · simp [Region.Contains]), m₁]
    · rw [ite_eq_right (by omega)]
      have d := e.mem 1 (k / 4) (by decide) (by simp only [bsize]; omega)
      rw [hm _ (by omega)] at d
      simp only [Avx512Tail.T.eval, regn, baseR, Avx512.zreg_xidx, h₁.r9, z₁, hB _ (by omega : k / 4 < 16)] at d
      rw [Avx512.byte_dword s₂.mem, d, serialize_getD _ hk]
    · rw [← m₁]
      refine e.frame.sub fun r hr => ?_
      simp only [wregs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨Avx2.bufR (ebp s₀), by simp, by rw [h₁.r9]; exact bufR_sub _ (by omega)⟩
      · refine ⟨Avx512Tail.win s₀ q (eL s₀ - q), by simp, ?_⟩
        intro x hx; simp [Region.Contains] at hx
  · -- The block fits: into the data.
    simp only [decide_eq_false_iff_not] at hs
    obtain ⟨σ, hr, hx, hlo, hbuf, hk⟩ := condX_run hj
    have hc : Ctx (16 * j + 16) s₁ := Avx512Tail.ctx_of hp (p := q) (by omega) (by omega) h₁.rdi h₁.r9
      h₁.rsi h₁.wr
    refine WP.mono (srun_ok hc _ (SRel.init _ s₁) hr) fun s₂ e => ⟨h₁.of_gpr e.gpr e.rd e.wr,
      e.gpr.trans g₁, fun l hl p hp' => ?_, fun k hk => ?_, fun k hk => ?_, ?_⟩
    · rw [e.reg _ p hp', hk l hl p hp']
      simp only [Avx512Tail.T.eval, Avx512.zreg_xidx, z₁]
    · rw [Avx512.byte_dword s₂.mem, Avx512.byte_dword s.mem, ← m₁]
      by_cases hkj : k / 64 = j
      · rw [ite_eq_left ⟨by omega, hkj⟩]
        have d := e.mem 2 (k / 4) (by decide) (by simp only [bsize]; omega)
        rw [show k / 4 = 16 * j + k % 64 / 4 by omega, hx _ (by omega)] at d
        simp only [Avx512Tail.T.eval, regn, baseR, Avx512.zreg_xidx, h₁.rsi, z₁,
          hB _ (by omega : k % 64 / 4 < 16)] at d
        rw [show 4 * (16 * j + k % 64 / 4) = 4 * (k / 4) by omega] at d
        rw [d, BitVec.extractLsb'_xor, serialize_getD _ (Nat.mod_lt _ (by decide)),
          show k % 64 % 4 = k % 4 by omega]
      · rw [ite_eq_right (by omega)]
        by_cases hlt : k < 64 * j
        · have d := e.mem 2 (k / 4) (by decide) (by simp only [bsize]; omega)
          rw [hlo _ (by omega)] at d
          simp only [Avx512Tail.T.eval, regn, baseR, h₁.rsi] at d
          rw [d]
        · rw [← Avx512.byte_dword s₂.mem, ← Avx512.byte_dword s₁.mem]
          refine e.frame _ ?_
          intro r hr; simp only [wregs, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [h₁.r9]; exact nb k hk
          · rw [h₁.rsi]
            simp only [Region.Contains]
            rw [show edp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k - (edp s₀ + BitVec.ofNat 64 q) =
              BitVec.ofNat 64 k by bv_omega, toNat_ofNat_lt (by omega)]
            omega
    · rw [ite_eq_left (by omega), Avx512.byte_dword s₂.mem, Avx512.byte_dword s.mem, ← m₁]
      have d := e.mem 1 (k / 4) (by decide) (by simp only [bsize]; omega)
      rw [hbuf _ (by omega)] at d
      simp only [Avx512Tail.T.eval, regn, baseR, h₁.r9] at d
      rw [d]
    · rw [← m₁]
      refine e.frame.sub fun r hr => ?_
      simp only [wregs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨Avx2.bufR (ebp s₀), by simp, by rw [h₁.r9]; exact bufR_sub _ (by omega)⟩
      · refine ⟨Avx512Tail.win s₀ q (eL s₀ - q), by simp, ?_⟩
        rw [h₁.rsi]
        exact Region.sub_prefix (by omega)

/-- Before `conds n`, from `sC`: blocks `8 + n` to 15 done (into the data
if they fit; the one the data ends in, if any, into `buf`), blocks `8 + l`,
`l < n`, still in their registers. -/
structure CI (s₀ : State) (q : Nat) (B : Nat → CState) (sC : State) (n : Nat) (s : State) : Prop where
  at_ : At s₀ q s
  gpr : s.gpr = sC.gpr
  regs : ∀ l < n, ∀ p (hp : p < 16), zw s (blkReg (8 + l)) p = (B l)[p]'hp
  data : ∀ k < eL s₀ - q, s.mem (edp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k) =
    if n ≤ k / 64 ∧ 64 * (k / 64) + 64 ≤ eL s₀ - q then
      sC.mem (edp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k) ^^^ (serialize (B (k / 64))).getD (k % 64) 0
    else sC.mem (edp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k)
  buf : n ≤ (eL s₀ - q) / 64 → ∀ k < 64,
    s.mem (ebp s₀ + BitVec.ofNat 64 k) = (serialize (B ((eL s₀ - q) / 64))).getD k 0
  frame : Frame [Avx2.bufR (ebp s₀), Avx512Tail.win s₀ q (eL s₀ - q)] sC.mem s.mem

theorem conds_ok {s₀ : State} (hp : APre s₀) {q : Nat} {B : Nat → CState} {sC : State} :
    ∀ n ≤ 8, ∀ {s : State}, CI s₀ q B sC n s → WP isa (conds n) s (CI s₀ q B sC 0)
  | 0, _, _, h => WP.block_nil h
  | n + 1, hn, s, h => by
    refine WP.seq (WP.mono (cond_ok hp (j := n) (by omega) h.at_ (h.regs n (by omega)))
      fun s' ⟨a', g', z', d', b', f'⟩ => conds_ok hp n (by omega) ⟨a', g'.trans h.gpr, fun l hl p hp' => ?_,
        fun k hk => ?_, fun hq k hk => ?_, h.frame.trans f'⟩)
    · rw [z' l (by omega) p hp']; exact h.regs l (by omega) p hp'
    · rw [d' k hk, h.data k hk]
      by_cases hkn : k / 64 = n
      · rw [ite_eq_right (by omega : ¬ (n + 1 ≤ k / 64 ∧ _))]
        by_cases hf : 64 * n + 64 ≤ eL s₀ - q
        · rw [ite_eq_left ⟨hf, hkn⟩, ite_eq_left ⟨by omega, by omega⟩, hkn]
        · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      · rw [ite_eq_right (by omega : ¬ (64 * n + 64 ≤ eL s₀ - q ∧ k / 64 = n))]
        by_cases hc : n + 1 ≤ k / 64 ∧ 64 * (k / 64) + 64 ≤ eL s₀ - q
        · rw [ite_eq_left hc, ite_eq_left ⟨by omega, hc.2⟩]
        · rw [ite_eq_right hc, ite_eq_right (by omega)]
    · rw [b' k hk]
      by_cases hf : 64 * n + 64 ≤ eL s₀ - q
      · rw [ite_eq_left hf]; exact h.buf (by omega) k hk
      · rw [ite_eq_right hf, show (eL s₀ - q) / 64 = n by omega]

/-! ## The code between the parts -/

theorem mov_ok (s : State) :
    WP isa (.block [.mov .r9 (.reg .rcx)]) s fun s' =>
      s'.gpr .r9 = s.gpr .rcx ∧ (∀ r, r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ ∀ r p, zw s' r p = zw s r p := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some, Option.some.injEq,
    exists_eq_left']
  exact ⟨by simp [State.setReg], fun r hr => by simp [State.setReg, hr], rfl, rfl, rfl, fun _ _ => rfl⟩

theorem adv512_ok {s₀ : State} {p : Nat} (hge : 512 ≤ eL s₀ - p) {s : State}
    (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 p)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 (eL s₀ - p)) :
    WP isa (.block adv512) s fun s' =>
      s'.gpr .rsi = edp s₀ + BitVec.ofNat 64 (p + 512) ∧
      s'.gpr .rdx = BitVec.ofNat 64 (eL s₀ - (p + 512)) ∧
      (∀ r, r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ (∀ r p, zw s' r p = zw s r p) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hL := eL_lt s₀
  have se : BitVec.signExtend 64 (512 : BitVec 32) = 512 := by decide
  apply WP.of_runBlock
  simp only [adv512, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.bind_some, Option.some.injEq,
    exists_eq_left', se]
  refine ⟨by rw [hrsi]; bv_omega, by rw [hrdx]; bv_omega, fun r h₁ h₂ => by simp [h₁, h₂],
    fun _ _ => rfl, by simp⟩

theorem shr_shl (r : Nat) (hr : r < 2 ^ 64) :
    BitVec.ofNat 64 r >>> 6 <<< 6 = BitVec.ofNat 64 (64 * (r / 64)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hr]
  omega

theorem adv_ok {s₀ : State} {q : Nat} {s : State} (h : At s₀ q s) :
    WP isa (.block adv) s fun s' =>
      s'.gpr .rsi = edp s₀ + BitVec.ofNat 64 (q + 64 * ((eL s₀ - q) / 64)) ∧
      s'.gpr .rdx = BitVec.ofNat 64 (eL s₀ - (q + 64 * ((eL s₀ - q) / 64))) ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hL := eL_lt s₀
  have hle := h.le
  have hsm := h.small
  apply WP.of_runBlock
  simp only [adv, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, execShift, arithFlags, State.setReg, State.setFlags, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left', Nat.reduceLeDiff, and_self]
  rw [h.rdx, shr_shl _ (by omega)]
  refine ⟨by rw [h.rsi]; bv_omega, by bv_omega, fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃], by simp⟩

/-! ## The whole pass -/

theorem last16_eq : last16 = .seq (.block (([.mov .r9 (.reg .rcx)] : List Instr) ++ setupB .r9))
    (.seq (rounds 10) (.seq (.block (finishP ++ adv512)) (.seq (conds 8) (.seq (.block adv)
      (.seq Impl.ChaCha20.X86_64.Avx512Tail.fromBuf (.block [.vop .vzeroupper, .mov .rsi (.reg .r9)])))))) := rfl

theorem r9_ne {r : Reg} (hr : r ∈ calleeSaved) : r ≠ .r9 := (Avx512Tail.r9_not_calleeSaved hr).1

theorem last16_ok {s₀ : State} (hp : APre s₀) {p : Nat} (hgt : 512 < eL s₀ - p) (hlt : eL s₀ - p < 1024)
    {s : State} (h : Avx512Tail.TInv s₀ p s) (hi : Incs s.mem (ebp s₀)) :
    WP isa last16 s fun s' =>
      (gprPreserved s₀ s' ∧ xorAvx2X86_64.post s₀ s') ∧ s'.gpr .rsi = s₀.gpr .rcx := by
  have hL := eL_lt s₀
  have hle := h.le
  rw [last16_eq]
  -- The sixteen input states.
  refine WP.seq (WP.block_append (WP.mono (mov_ok s) fun s₁ ⟨r9₁, g₁, m₁, rd₁, wr₁, _⟩ => ?_))
  have gk₁ : ∀ r, r ≠ .r9 → s₁.gpr r = s.gpr r := g₁
  have r9₁' : s₁.gpr .r9 = ebp s₀ := by rw [r9₁, h.rcx]
  have hc₁ : Ctx 0 s₁ := Avx512Tail.ctx_of hp (p := p) (by omega) (by decide)
    (by rw [gk₁ _ (by decide)]; exact h.rdi) r9₁' (by rw [gk₁ _ (by decide)]; exact h.rsi) (wr₁.trans h.wr)
  have hi₁ : Incs s₁.mem (s₁.gpr .r9) := by rw [m₁, r9₁']; exact hi
  refine WP.mono (setup_ok hc₁ hi₁) fun s₂ ⟨hz₂, m₂, g₂, rd₂, wr₂⟩ => ?_
  -- The rounds.
  refine WP.seq (WP.mono (Avx512.rounds_ok hz₂ 10) fun s₃ ⟨hz₃, sm₃⟩ => ?_)
  have g₃ : s₃.gpr = s₁.gpr := sm₃.gpr.trans g₂
  have m₃ : s₃.mem = s.mem := sm₃.mem.trans (m₂.trans m₁)
  have rd₃ : s₃.rd = s₀.rd := sm₃.rd.trans (rd₂.trans (rd₁.trans h.rd))
  have wr₃ : s₃.wr = s₀.wr := sm₃.wr.trans (wr₂.trans (wr₁.trans h.wr))
  have rdi₃ : s₃.gpr .rdi = est s₀ := by rw [g₃, gk₁ _ (by decide)]; exact h.rdi
  have rsi₃ : s₃.gpr .rsi = edp s₀ + BitVec.ofNat 64 p := by rw [g₃, gk₁ _ (by decide)]; exact h.rsi
  have rdx₃ : s₃.gpr .rdx = BitVec.ofNat 64 (eL s₀ - p) := by rw [g₃, gk₁ _ (by decide)]; exact h.rdx
  have r9₃ : s₃.gpr .r9 = ebp s₀ := by rw [g₃]; exact r9₁'
  have hS₁ : S0 s₁ = ctr (Avx2.S0 s₀) (p / 64) := by
    simp only [S0, m₁, gk₁ _ (by decide : Reg.rdi ≠ .r9), h.rdi]; exact h.cnt
  have hS₃ : S0 s₃ = ctr (Avx2.S0 s₀) (p / 64) := by simp only [S0, m₃, rdi₃]; exact h.cnt
  -- The output: eight blocks into the data, eight into registers.
  have hc₃ : Ctx 128 s₃ := Avx512Tail.ctx_of hp (p := p) (by omega) (by decide) rdi₃ r9₃ rsi₃ wr₃
  have hi₃ : Incs s₃.mem (s₃.gpr .r9) := by rw [m₃, r9₃]; exact hi
  refine WP.seq (WP.block_append (WP.mono (finish_ok hc₃ hi₃ hz₃) fun s₄ ⟨d₄, z₄, f₄, g₄, rd₄, wr₄⟩ => ?_))
  refine WP.mono (adv512_ok (s₀ := s₀) (p := p) (by omega) (by rw [g₄]; exact rsi₃) (by rw [g₄]; exact rdx₃))
    fun s₅ ⟨rsi₅, rdx₅, g₅, z₅, m₅, rd₅, wr₅⟩ => ?_
  have gk₅ : ∀ r, r ≠ .rsi → r ≠ .rdx → s₅.gpr r = s₃.gpr r := fun r a b => by rw [g₅ r a b, g₄]
  rw [show wregs 128 s₃ = [⟨ebp s₀, 256⟩, Avx512Tail.win s₀ p 512] by
    simp only [wregs, r9₃, rsi₃, Avx512Tail.win, Nat.reduceMul]] at f₄
  obtain ⟨B, hBd⟩ : ∃ B : Nat → CState,
      B = fun l => plus (fun j => Nat.repeat Spec.ChaCha20.innerBlock 10 (ctr (S0 s₁) j)) (S0 s₃) (8 + l) :=
    ⟨_, rfl⟩
  have A₅ : At s₀ (p + 512) s₅ := ⟨by rw [gk₅ _ (by decide) (by decide)]; exact rdi₃,
    by rw [gk₅ _ (by decide) (by decide)]; exact r9₃, rsi₅, rdx₅, by omega, by omega,
    rd₅.trans (rd₄.trans rd₃), wr₅.trans (wr₄.trans wr₃)⟩
  have C₅ : CI s₀ (p + 512) B s₅ 8 s₅ := ⟨A₅, rfl, fun l hl q hq => by rw [z₅, hBd]; exact z₄ l hl q hq,
    fun k hk => by rw [ite_eq_right (by omega)], fun hq => absurd hq (by omega), Frame.refl _ _⟩
  -- The next eight blocks, as far as they fit.
  refine WP.seq (WP.mono (conds_ok hp 8 (by decide) C₅) fun s₆ C₆ => ?_)
  refine WP.seq (WP.mono (adv_ok C₆.at_) fun s₇ ⟨rsi₇, rdx₇, g₇, m₇, rd₇, wr₇⟩ => ?_)
  -- The rest, from `buf`.
  have r9₇ : s₇.gpr .r9 = ebp s₀ := by rw [g₇ _ (by decide) (by decide) (by decide)]; exact C₆.at_.r9
  have nb : ∀ k < eL s₀, ¬ (⟨ebp s₀, 256⟩ : Region).Contains (edp s₀ + BitVec.ofNat 64 k) 1 :=
    fun k hk hc => hp.d_b _ (in_dR hk) (bufR_sub _ (by omega) _ hc)
  have nB : ∀ k < eL s₀, ¬ (Avx2.bufR (ebp s₀)).Contains (edp s₀ + BitVec.ofNat 64 k) 1 :=
    fun k hk hc => hp.d_b _ (in_dR hk) hc
  -- The data before this pass's ninth block, as `finishP` left it.
  have early : ∀ k < p + 512, s₆.mem (edp s₀ + BitVec.ofNat 64 k) = D0 s₀ k ^^^ (KS s₀).getD k 0 := by
    intro k hk
    rw [C₆.frame _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact nB k (by omega)
        · exact Avx512Tail.not_win (by omega) (by omega) (.inl hk)), m₅]
    by_cases hkp : k < p
    · rw [f₄ _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact nb k (by omega)
        · exact Avx512Tail.not_win (by omega) (by omega) (.inl hkp)), m₃, h.data k (by omega), ite_eq_left hkp]
    · have x := d₄ (k - p) (by omega)
      rw [rsi₃, Avx512Tail.ea_win (s₀ := s₀) (p := p) (by omega) |>.symm, m₃] at x
      rw [x, h.data k (by omega), ite_eq_right hkp, hS₃, hS₁, Avx512Tail.ks_at h.dvd (by omega) (by omega)]
  -- The data from the ninth block on, before this pass.
  have late : ∀ k, p + 512 ≤ k → k < eL s₀ → s₅.mem (edp s₀ + BitVec.ofNat 64 k) = D0 s₀ k := by
    intro k hk₁ hk₂
    rw [m₅, f₄ _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact nb k hk₂
        · exact Avx512Tail.not_win (by omega) hk₂ (.inr hk₁)), m₃, h.data k hk₂, ite_eq_right (by omega)]
  have hB : ∀ k, p + 512 ≤ k → k < eL s₀ →
      (serialize (B ((k - (p + 512)) / 64))).getD ((k - (p + 512)) % 64) 0 = (KS s₀).getD k 0 := by
    intro k hk₁ hk₂
    rw [Avx512Tail.ks_at h.dvd (by omega) hk₂, hBd]
    simp only [hS₃, hS₁]
    rw [show 8 + (k - (p + 512)) / 64 = (k - p) / 64 by omega,
      show (k - (p + 512)) % 64 = (k - p) % 64 by omega]
  have keep₇ : ∀ r ∈ calleeSaved, s₇.gpr r = s₀.gpr r := fun r hr => by
    obtain ⟨_, a, b, c⟩ := Avx512Tail.r9_not_calleeSaved hr
    obtain ⟨a', b', c'⟩ := calleeSaved_ne hr
    rw [g₇ r a' b' c', C₆.gpr, gk₅ r b' c', g₃, gk₁ r (r9_ne hr)]
    exact h.keep r hr
  have hmb := C₆.buf
  generalize hm : (eL s₀ - (p + 512)) / 64 = m at rsi₇ rdx₇ hmb
  refine WP.seq (WP.mono (Avx512Tail.fromBuf_ok hp (p := p + 512 + 64 * m) (n := eL s₀ - (p + 512 + 64 * m))
    (by omega) (by omega) rsi₇ r9₇ rdx₇ (rd₇.trans C₆.at_.rd) (wr₇.trans C₆.at_.wr) keep₇
    (fun k hk => ?_) (fun k hk => ?_) (fun k hk => ?_) ?_) fun s₈ d₈ => Avx512Tail.fin_ok (d₈.fin hp))
  · rw [m₇]
    by_cases hk5 : k < p + 512
    · exact early k hk5
    · have x := C₆.data (k - (p + 512)) (by omega_arith)
      rw [Avx512Tail.ea_win (s₀ := s₀) (p := p + 512) (by omega_arith) |>.symm] at x
      rw [x, ite_eq_left ⟨Nat.zero_le _, by omega⟩, late k (by omega_arith) (by omega_arith), hB k (by omega_arith) (by omega_arith)]
  · have x := C₆.data (64 * m + k) (by omega_arith)
    rw [add_ofNat] at x
    rw [m₇, add_ofNat, show p + 512 + 64 * m + k = p + 512 + (64 * m + k) by omega_arith, x,
      ite_eq_right (by omega_arith), late _ (by omega_arith) (by omega_arith)]
  · have y := hB (p + 512 + 64 * m + k) (by omega_arith) (by omega_arith)
    rw [show (p + 512 + 64 * m + k - (p + 512)) / 64 = m by omega_arith,
      show (p + 512 + 64 * m + k - (p + 512)) % 64 = k by omega_arith] at y
    rw [m₇, hmb (Nat.zero_le _) k (by omega_arith), y]
  · rw [m₇]
    refine h.frame.trans ?_
    rw [← m₃]
    refine (f₄.sub fun r hr => ?_).trans ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨Avx2.bufR (ebp s₀), by simp, bufR_sub _ (by omega)⟩
      · exact ⟨edR s₀, by simp, Avx512Tail.win_sub (by omega)⟩
    · rw [← m₅]
      refine C₆.frame.sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨Avx2.bufR (ebp s₀), by simp, fun _ h => h⟩
      · exact ⟨edR s₀, by simp, Avx512Tail.win_sub (by omega)⟩

end VG.Proof.ChaCha20.X86_64.Avx512Last
