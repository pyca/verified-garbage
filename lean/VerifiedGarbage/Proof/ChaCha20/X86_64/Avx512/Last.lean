module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Finish
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512Tail.Tail
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# ChaCha20 on x86-64 with AVX-512: the last 513 to 1023 bytes

`last16`, from the state after the sixteen-block loop of
`vg_chacha20_xor_avx512` (`Avx512Tail.TInv`, with 513 to 1023 bytes left)
to the end of the function, from the source at `rsi` to the destination at
`rsi + r11`. The code around the rounds runs with `buf` at
`r9`, so that the checks of the last bytes (`Avx512Tail.run`), which allow
at most 512 bytes of data, cover it: `finishP` writes only the first 512
bytes, and the code after it the next ones, from `rsi + 512`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx512Last

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word stateAt keystream serialize)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx512 (T Sym Sym.init xidx xidx_lt zw xidx_zreg stateAt_get ZH Incs
  setupT outT)
open VG.Proof.ChaCha20.X86_64.Avx512Tail (run runT Ctx CtxT SRel SRelT srun_ok srunT_ok regn baseR bsize wregs
  wregsT memBase_0 memBase_1 memBase_2 memBase_3 TInv XI S0)
open VG.Proof.ChaCha20.X86_64.Avx2 (TPre est edp edq eL ebp edR eqR D0 Q0 KS frT eL_lt add_ofNat in_dR in_eqR
  plus plus_block ctr_get ctr_ctr calleeSaved_ne)
open VG.Proof.ChaCha20.X86_64.Avx2Tail (DoneT winQ winQ_sub not_winQ)
open VG.Proof.ChaCha20.X86_64.Avx512 (dstR)

/-! ## The kernel's checks -/

def setupCheck : Bool :=
  match run 0 Sym.init (setupB .r9) with
  | some σ => !σ.dirty && (List.range 16).all fun k => (List.range 16).all fun p => σ.reg k p == setupT k p
  | none => false

def finishCheck : Bool :=
  match runT true 128 Sym.init finishP with
  | some σ =>
    ((List.range 128).all fun i => σ.mem 3 i == .xor (.mem 2 i) (outT (i % 16) (i / 16))) &&
    (List.range 8).all fun j => (List.range 16).all fun p =>
      σ.reg (xidx (blkReg (8 + j))) p == outT p (8 + j)
  | none => false

/-- Both branches of `cond j`, for each `j`: the block register into the
data, or into `buf`, and the other block registers kept. -/
def condCheck : Bool :=
  (List.range 8).all fun j =>
    (match runT true (16 * j + 16) Sym.init (xor64 (blkReg (8 + j)) .xmm2 (64 * j)) with
     | some σ =>
       ((List.range 16).all fun i =>
         σ.mem 3 (16 * j + i) == .xor (.mem 2 (16 * j + i)) (.reg (xidx (blkReg (8 + j))) i)) &&
       ((List.range (16 * j)).all fun i => σ.mem 3 i == .mem 3 i) &&
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

theorem outT_eval {D : Nat} {s : State} {vs : Nat → CState} (hz : ZH vs s) (hi : Incs s.mem (s.gpr .r9))
    {w j : Nat} (hw : w < 16) (hj : j < 16) :
    Avx512Tail.T.eval D s (outT w j) = (plus vs (S0 s) j)[w] := by
  have r := hz (Impl.ChaCha20.X86_64.Avx512.zreg w) j hj
  simp only [xidx_zreg w hw] at r
  simp only [plus, Vector.getElem_zipWith, ctr_get _ _ _ hw, outT]
  split
  · rename_i e; subst e
    simp only [Avx512Tail.T.eval, memBase_0, memBase_1, r, stateAt_get _ _ (show 12 < 16 by decide), hi j hj,
      BitVec.add_assoc]
  · simp only [Avx512Tail.T.eval, memBase_0, r, stateAt_get _ _ hw]

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
    · simp only [Avx512Tail.T.eval, memBase_0, memBase_1]
      rw [stateAt_get _ _ (by decide), hi j hj]
    · simp only [Avx512Tail.T.eval, memBase_0]
      exact stateAt_get _ _ (xidx_lt r)
  · cases e

/-! ## The output -/

/-- The first eight blocks XORed with the source at `rsi` into the destination
at `rsi + r11` (`dstR`), the next eight left in registers. -/
theorem finish_ok {s : State} (hc : CtxT true 128 s) (hi : Incs s.mem (s.gpr .r9)) {vs : Nat → CState}
    (hz : ZH vs s) :
    WP isa (.block finishP) s fun s' =>
      (∀ k < 512, s'.mem ((dstR 128 s).base + BitVec.ofNat 64 k) = s.mem (s.gpr .rsi + BitVec.ofNat 64 k) ^^^
        (serialize (plus vs (S0 s) (k / 64))).getD (k % 64) 0) ∧
      (∀ j < 8, ∀ p (hp : p < 16), zw s' (blkReg (8 + j)) p = (plus vs (S0 s) (8 + j))[p]'hp) ∧
      Frame (wregsT true 128 s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := finishCheck_eq
  unfold finishCheck at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srunT_ok hc _ (SRelT.init true 128 s) hr) fun s' h => ⟨fun k hk => ?_, fun j hj p hp => ?_,
      h.frame, h.gpr, h.rd, h.wr⟩
    · have d := h.mem3 rfl (k / 4) (by omega_arith)
      rw [e.1 _ (by omega_arith)] at d
      simp only [Avx512Tail.T.eval, memBase_2] at d
      rw [show k / 4 / 16 = k / 64 by omega_arith, show k / 4 % 16 = k % 64 / 4 by omega_arith,
        outT_eval hz hi (by omega_arith) (by omega_arith)] at d
      rw [Avx512.byte_dword s'.mem, Avx512.byte_dword s.mem, d, BitVec.extractLsb'_xor,
        serialize_getD _ (Nat.mod_lt _ (by decide)), show k % 64 % 4 = k % 4 by omega_arith]
    · rw [h.reg _ p hp, e.2 j hj p hp, outT_eval hz hi hp (by omega_arith)]
  · cases e

/-! ## The next eight blocks, as far as they fit -/

theorem condX_run {j : Nat} (hj : j < 8) :
    ∃ σ, runT true (16 * j + 16) Sym.init (xor64 (blkReg (8 + j)) .xmm2 (64 * j)) = some σ ∧
    (∀ i < 16, σ.mem 3 (16 * j + i) = .xor (.mem 2 (16 * j + i)) (.reg (xidx (blkReg (8 + j))) i)) ∧
    (∀ i < 16 * j, σ.mem 3 i = .mem 3 i) ∧ (∀ i < 16, σ.mem 1 i = .mem 1 i) ∧
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
    rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', se]
  refine ⟨trivial, trivial, trivial, trivial, fun _ _ => rfl, ?_⟩
  rw [h.rdx, toNat_ofNat_lt (by omega_arith), toNat_ofNat_lt (by omega_arith)]

theorem bufR_sub (b : Addr) {n : Nat} (hn : n ≤ 320) : Region.Sub ⟨b, n⟩ (Avx2.bufR b) :=
  Region.sub_prefix hn

theorem At.dst {s₀ : State} {q : Nat} {s : State} (h : At s₀ q s) (h11 : s.gpr .r11 = edq s₀ - edp s₀)
    {D : Nat} : (dstR D s).base = edq s₀ + BitVec.ofNat 64 q := by
  simp only [dstR, h.rsi, h11]; rw [BitVec.add_comm, XorBuf.sub_add_add]

/-- Block `8 + j` XORed with the source into the destination, if it fits,
or else into `buf`. -/
theorem cond_ok {s₀ : State} (hp : TPre s₀) {q j : Nat} (hj : j < 8) {s : State} (h : At s₀ q s)
    (h11 : s.gpr .r11 = edq s₀ - edp s₀)
    {B : CState} (hB : ∀ p (hp : p < 16), zw s (blkReg (8 + j)) p = B[p]'hp) :
    WP isa (cond j) s fun s' => At s₀ q s' ∧ s'.gpr = s.gpr ∧
      (∀ l < 8, ∀ p < 16, zw s' (blkReg (8 + l)) p = zw s (blkReg (8 + l)) p) ∧
      (∀ k < eL s₀ - q, s'.mem (edq s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k) =
        if 64 * j + 64 ≤ eL s₀ - q ∧ k / 64 = j then
          s.mem (edp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k) ^^^ (serialize B).getD (k % 64) 0
        else s.mem (edq s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k)) ∧
      (∀ k < 64, s'.mem (ebp s₀ + BitVec.ofNat 64 k) =
        if 64 * j + 64 ≤ eL s₀ - q then s.mem (ebp s₀ + BitVec.ofNat 64 k) else (serialize B).getD k 0) ∧
      Frame [Avx2.bufR (ebp s₀), winQ s₀ q (eL s₀ - q)] s.mem s'.mem := by
  have hL := eL_lt s₀
  have hle := h.le
  have hsm := h.small
  refine WP.seq (WP.mono (cmpJ_ok hj h) fun s₁ ⟨g₁, m₁, rd₁, wr₁, z₁, c₁⟩ => ?_)
  have h₁ : At s₀ q s₁ := h.of_gpr g₁ rd₁ wr₁
  have h11₁ : s₁.gpr .r11 = edq s₀ - edp s₀ := by rw [g₁]; exact h11
  have nb : ∀ k < eL s₀ - q, ¬ (⟨ebp s₀, 256⟩ : Region).Contains (edq s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k) 1 :=
    fun k hk hc => hp.q_b _ (by rw [add_ofNat]; exact in_eqR (by omega_arith)) (bufR_sub _ (by omega_arith) _ hc)
  refine WP.ite (decide (eL s₀ - q < 64 * j + 64)) (by simp [eval, c₁]) (fun hs => ?_) (fun hs => ?_)
  · -- The block does not fit: into `buf`.
    simp only [decide_eq_true_eq] at hs
    obtain ⟨σ, hr, hm, hk⟩ := condS_run hj
    have hc : Ctx 0 s₁ := Avx512Tail.ctx0_of hp h₁.rdi h₁.r9 h₁.wr
    refine WP.mono (srun_ok hc _ (SRel.init 0 s₁) hr) fun s₂ e => ⟨h₁.of_gpr e.gpr e.rd e.wr,
      e.gpr.trans g₁, fun l hl p hp' => ?_, fun k hk => ?_, fun k hk => ?_, ?_⟩
    · rw [e.reg _ p hp', hk l hl p hp']
      simp only [Avx512Tail.T.eval, Avx512.zreg_xidx, z₁]
    · rw [ite_eq_right (by omega_arith), e.frame _ (by
        intro r hr; simp only [wregsT, wregs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.r9]; exact nb k hk
        · simp [Region.Contains]), m₁]
    · rw [ite_eq_right (by omega_arith)]
      have d := e.mem 1 (k / 4) (by decide) (by simp only [bsize]; omega_arith)
      rw [hm _ (by omega_arith)] at d
      simp only [Avx512Tail.T.eval, regn, baseR, Avx512.zreg_xidx, h₁.r9, z₁, hB _ (by omega_arith : k / 4 < 16)] at d
      rw [Avx512.byte_dword s₂.mem, d, serialize_getD _ hk]
    · rw [← m₁]
      refine e.frame.sub fun r hr => ?_
      simp only [wregsT, wregs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨Avx2.bufR (ebp s₀), by simp, by rw [h₁.r9]; exact bufR_sub _ (by omega_arith)⟩
      · refine ⟨winQ s₀ q (eL s₀ - q), by simp, ?_⟩
        intro x hx; simp [Region.Contains] at hx
  · -- The block fits: into the destination.
    simp only [decide_eq_false_iff_not] at hs
    obtain ⟨σ, hr, hx, hlo, hbuf, hk⟩ := condX_run hj
    have hc : CtxT true (16 * j + 16) s₁ := ⟨Avx512Tail.ctx0_of hp h₁.rdi h₁.r9 h₁.wr,
      Avx512Tail.ctx3_of hp (p := q) (by omega_arith) h₁.rdi h₁.r9 h₁.rsi h11₁ h₁.rd h₁.wr, by omega_arith⟩
    have hd := h₁.dst h11₁ (D := 16 * j + 16)
    refine WP.mono (srunT_ok hc _ (SRelT.init true _ s₁) hr) fun s₂ e => ⟨h₁.of_gpr e.gpr e.rd e.wr,
      e.gpr.trans g₁, fun l hl p hp' => ?_, fun k hk => ?_, fun k hk => ?_, ?_⟩
    · rw [e.reg _ p hp', hk l hl p hp']
      simp only [Avx512Tail.T.eval, Avx512.zreg_xidx, z₁]
    · rw [← hd, Avx512.byte_dword s₂.mem, ← m₁]
      by_cases hkj : k / 64 = j
      · rw [ite_eq_left ⟨by omega_arith, hkj⟩, Avx512.byte_dword s₁.mem]
        have d := e.mem3 rfl (k / 4) (by omega_arith)
        rw [show k / 4 = 16 * j + k % 64 / 4 by omega_arith, hx _ (by omega_arith)] at d
        simp only [Avx512Tail.T.eval, memBase_2, Avx512.zreg_xidx, h₁.rsi, z₁,
          hB _ (by omega_arith : k % 64 / 4 < 16)] at d
        rw [show 4 * (16 * j + k % 64 / 4) = 4 * (k / 4) by omega_arith] at d
        rw [d, BitVec.extractLsb'_xor, serialize_getD _ (Nat.mod_lt _ (by decide)),
          show k % 64 % 4 = k % 4 by omega_arith]
      · rw [ite_eq_right (by omega_arith), hd]
        by_cases hlt : k < 64 * j
        · have d := e.mem3 rfl (k / 4) (by omega_arith)
          rw [hlo _ (by omega_arith)] at d
          simp only [Avx512Tail.T.eval, memBase_3, hd] at d
          rw [d, ← Avx512.byte_dword s₁.mem]
        · rw [← Avx512.byte_dword s₂.mem]
          refine e.frame _ ?_
          intro r hr; simp only [wregsT, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [h₁.r9]; exact nb k hk
          · rw [show dstR (16 * j + 16) s₁ = winQ s₀ q (4 * (16 * j + 16)) by simp only [dstR] at hd ⊢; rw [hd]]
            rw [add_ofNat]
            exact not_winQ (k := q + k) (by omega_arith) (by omega_arith) (.inr (by omega_arith))
    · rw [ite_eq_left (by omega_arith), Avx512.byte_dword s₂.mem, Avx512.byte_dword s.mem, ← m₁]
      have d := e.mem 1 (k / 4) (by decide) (by simp only [bsize]; omega_arith) (fun _ e => nomatch e)
      rw [hbuf _ (by omega_arith)] at d
      simp only [Avx512Tail.T.eval, memBase_1, regn, baseR, h₁.r9] at d
      rw [d]
    · rw [← m₁]
      refine e.frame.sub fun r hr => ?_
      simp only [wregsT, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨Avx2.bufR (ebp s₀), by simp, by rw [h₁.r9]; exact bufR_sub _ (by omega_arith)⟩
      · refine ⟨winQ s₀ q (eL s₀ - q), by simp, ?_⟩
        rw [show dstR (16 * j + 16) s₁ = winQ s₀ q (4 * (16 * j + 16)) by simp only [dstR] at hd ⊢; rw [hd]]
        exact Region.sub_prefix (by omega_arith)

/-- Before `conds n`, from `sC`: blocks `8 + n` to 15 done (into the
destination if they fit; the one the data ends in, if any, into `buf`),
blocks `8 + l`, `l < n`, still in their registers. -/
structure CI (s₀ : State) (q : Nat) (B : Nat → CState) (sC : State) (n : Nat) (s : State) : Prop where
  at_ : At s₀ q s
  gpr : s.gpr = sC.gpr
  regs : ∀ l < n, ∀ p (hp : p < 16), zw s (blkReg (8 + l)) p = (B l)[p]'hp
  data : ∀ k < eL s₀ - q, s.mem (edq s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k) =
    if n ≤ k / 64 ∧ 64 * (k / 64) + 64 ≤ eL s₀ - q then
      sC.mem (edp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k) ^^^ (serialize (B (k / 64))).getD (k % 64) 0
    else sC.mem (edq s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k)
  buf : n ≤ (eL s₀ - q) / 64 → ∀ k < 64,
    s.mem (ebp s₀ + BitVec.ofNat 64 k) = (serialize (B ((eL s₀ - q) / 64))).getD k 0
  frame : Frame [Avx2.bufR (ebp s₀), winQ s₀ q (eL s₀ - q)] sC.mem s.mem

/-- The source of the blocks not done yet is as before them. -/
theorem CI.src {s₀ : State} (hp : TPre s₀) {q : Nat} {B : Nat → CState} {sC : State} {n : Nat} {s : State}
    (h : CI s₀ q B sC n s) {k : Nat} (hk : k < eL s₀ - q) (hkn : k / 64 < n) :
    s.mem (edp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k) = sC.mem (edp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k) := by
  have hL := eL_lt s₀
  have hle := h.at_.le
  rcases hp.alias with he | hdis
  · have := h.data k hk
    rw [ite_eq_right (by omega_arith)] at this
    simp only [edq, edp] at he this ⊢; rwa [he] at this
  · rw [add_ofNat]
    refine h.frame _ fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact fun hc => hp.d_b _ (in_dR (by omega_arith)) hc
    · exact fun hc => hdis _ (in_dR (by omega_arith)) (winQ_sub (by omega_arith) _ hc)

theorem conds_ok {s₀ : State} (hp : TPre s₀) {q : Nat} {B : Nat → CState} {sC : State}
    (h11 : sC.gpr .r11 = edq s₀ - edp s₀) :
    ∀ n ≤ 8, ∀ {s : State}, CI s₀ q B sC n s → WP isa (conds n) s (CI s₀ q B sC 0)
  | 0, _, _, h => WP.block_nil h
  | n + 1, hn, s, h => by
    refine WP.seq (WP.mono (cond_ok hp (j := n) (by omega_arith) h.at_ (by rw [h.gpr]; exact h11)
      (h.regs n (by omega_arith)))
      fun s' ⟨a', g', z', d', b', f'⟩ => conds_ok hp h11 n (by omega_arith) ⟨a', g'.trans h.gpr,
        fun l hl p hp' => ?_, fun k hk => ?_, fun hq k hk => ?_, h.frame.trans f'⟩)
    · rw [z' l (by omega_arith) p hp']; exact h.regs l (by omega_arith) p hp'
    · rw [d' k hk]
      by_cases hkn : k / 64 = n
      · by_cases hf : 64 * n + 64 ≤ eL s₀ - q
        · rw [ite_eq_left ⟨hf, hkn⟩, ite_eq_left ⟨by omega_arith, by omega_arith⟩, hkn,
            h.src hp hk (by omega_arith)]
        · rw [ite_eq_right (by omega_arith), h.data k hk, ite_eq_right (by omega_arith),
            ite_eq_right (by omega_arith)]
      · rw [ite_eq_right (by omega_arith : ¬ (64 * n + 64 ≤ eL s₀ - q ∧ k / 64 = n)), h.data k hk]
        by_cases hc : n + 1 ≤ k / 64 ∧ 64 * (k / 64) + 64 ≤ eL s₀ - q
        · rw [ite_eq_left hc, ite_eq_left ⟨by omega_arith, hc.2⟩]
        · rw [ite_eq_right hc, ite_eq_right (by omega_arith)]
    · rw [b' k hk]
      by_cases hf : 64 * n + 64 ≤ eL s₀ - q
      · rw [ite_eq_left hf]; exact h.buf (by omega_arith) k hk
      · rw [ite_eq_right hf, show (eL s₀ - q) / 64 = n by omega_arith]

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
  omega_arith

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
  rw [h.rdx, shr_shl _ (by omega_arith)]
  refine ⟨by rw [h.rsi]; bv_omega, by bv_omega, fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃], by simp⟩

/-! ## The whole pass -/

theorem last16_eq : last16 = .seq (.block (([.mov .r9 (.reg .rcx)] : List Instr) ++ setupB .r9))
    (.seq (rounds 10) (.seq (.block (finishP ++ adv512)) (.seq (conds 8) (.seq (.block adv)
      (.seq Impl.ChaCha20.X86_64.Avx512Tail.fromBuf (.block [.vop .vzeroupper, .mov .rsi (.reg .r9)])))))) := rfl

theorem r9_ne {r : Reg} (hr : r ∈ calleeSaved) : r ≠ .r9 := (Avx2Tail.r9_not_calleeSaved hr).1

theorem last16_ok {s₀ : State} (hp : TPre s₀) {p : Nat} (hgt : 512 < eL s₀ - p) (hlt : eL s₀ - p < 1024)
    {s : State} (h : TInv (XI s₀) s₀ p s) (hi : Incs s.mem (ebp s₀)) :
    WP isa last16 s fun s' => gprPreserved s₀ s' ∧ (xorTo 16).post s₀ s' := by
  have hL := eL_lt s₀
  have hle := h.le
  rw [last16_eq]
  -- The sixteen input states.
  refine WP.seq (WP.block_append (WP.mono (mov_ok s) fun s₁ ⟨r9₁, g₁, m₁, rd₁, wr₁, _⟩ => ?_))
  have gk₁ : ∀ r, r ≠ .r9 → s₁.gpr r = s.gpr r := g₁
  have r9₁' : s₁.gpr .r9 = ebp s₀ := by rw [r9₁, h.rcx]
  have h₁ : TInv (XI s₀) s₀ p s₁ := h.of gk₁ m₁ rd₁ wr₁
  have hi₁ : Incs s₁.mem (s₁.gpr .r9) := by rw [m₁, r9₁']; exact hi
  refine WP.mono (setup_ok (h₁.ctx0 hp r9₁' rfl rfl) hi₁) fun s₂ ⟨hz₂, m₂, g₂, rd₂, wr₂⟩ => ?_
  -- The rounds.
  refine WP.seq (WP.mono (Avx512.rounds_ok hz₂ 10) fun s₃ ⟨hz₃, sm₃⟩ => ?_)
  have g₃ : s₃.gpr = s₁.gpr := sm₃.gpr.trans g₂
  have m₃ : s₃.mem = s₁.mem := sm₃.mem.trans m₂
  have rd₃ : s₃.rd = s₁.rd := sm₃.rd.trans rd₂
  have wr₃ : s₃.wr = s₁.wr := sm₃.wr.trans wr₂
  have r9₃ : s₃.gpr .r9 = ebp s₀ := by rw [g₃]; exact r9₁'
  -- The output: eight blocks into the destination, eight into registers.
  have hi₃ : Incs s₃.mem (s₃.gpr .r9) := by rw [m₃, r9₃, m₁]; exact hi
  refine WP.seq (WP.block_append (WP.mono (finish_ok (h₁.ctxT hp r9₁' (D := 128) (by omega_arith) (by decide)
    g₃ rd₃ wr₃) hi₃ hz₃) fun s₄ ⟨d₄, z₄, f₄, g₄, rd₄, wr₄⟩ => ?_))
  refine WP.mono (adv512_ok (s₀ := s₀) (p := p) (by omega_arith) (by rw [g₄, g₃]; exact h₁.rsi)
    (by rw [g₄, g₃]; exact h₁.rdx)) fun s₅ ⟨rsi₅, rdx₅, g₅, z₅, m₅, rd₅, wr₅⟩ => ?_
  have gk₅ : ∀ r, r ≠ .rsi → r ≠ .rdx → s₅.gpr r = s₁.gpr r := fun r a b => by rw [g₅ r a b, g₄, g₃]
  rw [h₁.wregs r9₁' g₃, m₃] at f₄
  obtain ⟨B, hBd⟩ : ∃ B : Nat → CState,
      B = fun l => plus (fun j => Nat.repeat Spec.ChaCha20.innerBlock 10 (ctr (S0 s₁) j)) (S0 s₃) (8 + l) :=
    ⟨_, rfl⟩
  have A₅ : At s₀ (p + 512) s₅ := ⟨by rw [gk₅ _ (by decide) (by decide)]; exact h₁.rdi,
    by rw [gk₅ _ (by decide) (by decide)]; exact r9₁', rsi₅, rdx₅, by omega_arith, by omega_arith,
    rd₅.trans (rd₄.trans (rd₃.trans h₁.rd)), wr₅.trans (wr₄.trans (wr₃.trans h₁.wr))⟩
  have C₅ : CI s₀ (p + 512) B s₅ 8 s₅ := ⟨A₅, rfl, fun l hl q hq => by rw [z₅, hBd]; exact z₄ l hl q hq,
    fun k hk => by rw [ite_eq_right (by omega_arith)], fun hq => absurd hq (by omega_arith), Frame.refl _ _⟩
  -- The destination after `finishP`.
  have nb : ∀ k < eL s₀, ¬ (⟨ebp s₀, 256⟩ : Region).Contains (edq s₀ + BitVec.ofNat 64 k) 1 :=
    fun k hk hc => hp.q_b _ (in_eqR hk) (bufR_sub _ (by omega_arith) _ hc)
  have nB : ∀ k < eL s₀, ¬ (Avx2.bufR (ebp s₀)).Contains (edq s₀ + BitVec.ofNat 64 k) 1 :=
    fun k hk hc => hp.q_b _ (in_eqR hk) hc
  have D₅ : ∀ k < eL s₀, s₅.mem (edq s₀ + BitVec.ofNat 64 k) =
      if k < p + 512 then D0 s₀ k ^^^ (KS s₀).getD k 0 else Q0 s₀ k := by
    intro k hk
    rw [m₅]
    by_cases hin : p ≤ k ∧ k < p + 512
    · have x := d₄ (k - p) (by omega_arith)
      rw [h₁.cntAt g₃ m₃, h₁.cntAt rfl rfl, h₁.dst g₃, g₃, h₁.rsi, m₃, add_ofNat, add_ofNat,
        Nat.add_sub_cancel' hin.1, h₁.src hp hin.1 hk] at x
      rw [x, ite_eq_left hin.2, Avx512Tail.ks_at h.dvd hin.1 hk]
    · rw [f₄ _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact nb k hk
        · exact not_winQ (by omega_arith) hk (by omega_arith)), m₁, h.data k hk]
      by_cases hkp : k < p
      · rw [ite_eq_left hkp, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right hkp, ite_eq_right (by omega_arith)]
  have F₅ : Frame (frT s₀) s₀.mem s₅.mem := by
    rw [m₅]
    refine h.frame.trans ?_
    rw [← m₁]
    refine f₄.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨Avx2.bufR (ebp s₀), by simp, bufR_sub _ (by omega_arith)⟩
    · exact ⟨eqR s₀, by simp, winQ_sub (by omega_arith)⟩
  -- The next eight blocks, as far as they fit.
  refine WP.seq (WP.mono (conds_ok hp (by rw [gk₅ _ (by decide) (by decide)]; exact h₁.r11) 8 (by decide) C₅)
    fun s₆ C₆ => ?_)
  refine WP.seq (WP.mono (adv_ok C₆.at_) fun s₇ ⟨rsi₇, rdx₇, g₇, m₇, rd₇, wr₇⟩ => ?_)
  -- The rest, from `buf`.
  have r9₇ : s₇.gpr .r9 = ebp s₀ := by rw [g₇ _ (by decide) (by decide) (by decide)]; exact C₆.at_.r9
  have r11₇ : s₇.gpr .r11 = edq s₀ - edp s₀ := by
    rw [g₇ _ (by decide) (by decide) (by decide), C₆.gpr, gk₅ _ (by decide) (by decide)]; exact h₁.r11
  have keep₇ : ∀ r ∈ calleeSaved, s₇.gpr r = s₀.gpr r := fun r hr => by
    obtain ⟨a', b', c'⟩ := calleeSaved_ne hr
    rw [g₇ r a' b' c', C₆.gpr, gk₅ r b' c']
    exact h₁.keep r hr
  have hmb := C₆.buf
  generalize hm : (eL s₀ - (p + 512)) / 64 = m at rsi₇ rdx₇ hmb
  have hB : ∀ k, p + 512 ≤ k → k < eL s₀ →
      (serialize (B ((k - (p + 512)) / 64))).getD ((k - (p + 512)) % 64) 0 = (KS s₀).getD k 0 := by
    intro k hk₁ hk₂
    rw [Avx512Tail.ks_at h.dvd (by omega_arith) hk₂, hBd]
    simp only [h₁.cntAt g₃ m₃, h₁.cntAt rfl rfl]
    rw [show 8 + (k - (p + 512)) / 64 = (k - p) / 64 by omega_arith,
      show (k - (p + 512)) % 64 = (k - p) % 64 by omega_arith]
  -- The destination after the blocks that fit.
  have D₇ : ∀ k < eL s₀, s₇.mem (edq s₀ + BitVec.ofNat 64 k) =
      if k < p + 512 + 64 * m then D0 s₀ k ^^^ (KS s₀).getD k 0 else Q0 s₀ k := by
    intro k hk
    rw [m₇]
    by_cases hk5 : k < p + 512
    · rw [C₆.frame _ (by
          intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact nB k hk
          · exact not_winQ (by omega_arith) hk (.inl hk5)), D₅ k hk, ite_eq_left hk5, ite_eq_left (by omega_arith)]
    · have x := C₆.data (k - (p + 512)) (by omega_arith)
      rw [add_ofNat, add_ofNat, Nat.add_sub_cancel' (by omega_arith)] at x
      rw [x]
      by_cases hf : k < p + 512 + 64 * m
      · rw [ite_eq_left ⟨Nat.zero_le _, by omega_arith⟩, ite_eq_left hf,
          hp.src_of D₅ F₅ (by omega_arith) hk, hB k (by omega_arith) hk]
      · rw [ite_eq_right (by omega_arith), ite_eq_right hf, D₅ k hk, ite_eq_right hk5]
  have F₇ : Frame (frT s₀) s₀.mem s₇.mem := by
    rw [m₇]
    refine F₅.trans (C₆.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨Avx2.bufR (ebp s₀), by simp, fun _ h => h⟩
    · exact ⟨eqR s₀, by simp, winQ_sub (by omega_arith)⟩
  refine WP.seq (WP.mono (Avx2Tail.fromBufY_ok true hp (p := p + 512 + 64 * m) (n := eL s₀ - (p + 512 + 64 * m))
    (by omega_arith) (by omega_arith) rsi₇ r11₇ r9₇ rdx₇ (rd₇.trans (C₆.at_.rd)) (wr₇.trans C₆.at_.wr) keep₇
    (fun k hk => by rw [D₇ k (by omega_arith), ite_eq_left hk]) (fun k hk => ?_) (fun k hk => ?_) F₇)
    fun s₈ d₈ => Avx2Tail.fin_ok (d₈.fin hp))
  · rw [add_ofNat]
    exact hp.src_of D₇ F₇ (by omega_arith) (by omega_arith)
  · have y := hB (p + 512 + 64 * m + k) (by omega_arith) (by omega_arith)
    rw [show (p + 512 + 64 * m + k - (p + 512)) / 64 = m by omega_arith,
      show (p + 512 + 64 * m + k - (p + 512)) % 64 = k by omega_arith] at y
    rw [m₇, hmb (Nat.zero_le _) k (by omega_arith), y]

end VG.Proof.ChaCha20.X86_64.Avx512Last
