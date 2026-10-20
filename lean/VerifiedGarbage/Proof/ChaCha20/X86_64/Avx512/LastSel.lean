module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.XorSplit
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512Tail.SymSel
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Last
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.FinishSel
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Xor

/-!
# ChaCha20 keystream XOR with the data's first bytes from another buffer on x86-64 with AVX-512: the last 513 to 1023 bytes

`last16Sel`, from the state after the loop (`SInv`, with 513 to 1023 bytes
left) to the end of the function, as `last16` (`Last.lean`), each block of
the input loaded by `selXor`: the first eight by `finishPSel`, the next as
far as they fit by `condSel`, and the block the data ends in, if it ends
within one, from `dst`, where the input's bytes from `C` on are.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx512Split

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx512
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word stateAt keystream serialize)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx512 (T Sym Sym.init xidx xidx_lt zw ZH Incs outT srcR inpW inpW_byte byte_dword)
open VG.Proof.ChaCha20.X86_64.Avx512Tail (Ctx SRel srun_ok regn baseR bsize wregs selD)
open VG.Proof.ChaCha20.X86_64.Avx512Last (S0 outT_eval condS_run cmpJ_ok adv512_ok adv_ok mov_ok At bufR_sub)
open VG.Proof.ChaCha20.X86_64.Avx2 (add_ofNat plus)

/-! ## The kernel's checks -/

def finishPSelCheck : Bool :=
  match Avx512Tail.runPieces 128 Sym.init finishPSel with
  | some σ =>
    ((List.range 128).all fun i => σ.mem 2 i == .xor (.inp i) (outT (i % 16) (i / 16))) &&
    (List.range 8).all fun j => (List.range 16).all fun p =>
      σ.reg (xidx (blkReg (8 + j))) p == outT p (8 + j)
  | none => false

/-- The block register into the data, by `selXor`, for each `j`, and the
other block registers kept. -/
def condSelCheck : Bool :=
  (List.range 8).all fun j =>
    match selD (16 * j + 16) Sym.init (blkReg (8 + j)) .xmm2 (64 * j) with
    | some σ =>
      ((List.range 16).all fun i =>
        σ.mem 2 (16 * j + i) == .xor (.inp (16 * j + i)) (.reg (xidx (blkReg (8 + j))) i)) &&
      ((List.range (16 * j)).all fun i => σ.mem 2 i == .mem 2 i) &&
      ((List.range 16).all fun i => σ.mem 1 i == .mem 1 i) &&
      (List.range 8).all fun l => (List.range 16).all fun p =>
        σ.reg (xidx (blkReg (8 + l))) p == .reg (xidx (blkReg (8 + l))) p
    | none => false

theorem finishPSelCheck_eq : finishPSelCheck = true := by decide +kernel
theorem condSelCheck_eq : condSelCheck = true := by decide +kernel

/-! ## The output -/

/-- The first eight blocks into the data, from either buffer; the next eight
left in registers. -/
theorem finishPSel_ok {s : State} (hc : Ctx 128 s) (hs : Avx512Tail.SelOk 128 s) (hi : Incs s.mem (s.gpr .r9))
    {vs : Nat → CState} (hz : ZH vs s) :
    WP isa (pieces finishPSel) s fun s' =>
      (∀ k < 512, s'.mem (s.gpr .rsi + BitVec.ofNat 64 k) =
        (if 64 * (k / 64) + 64 ≤ (s.gpr .r10).toNat then s.mem (s.gpr .r8 + BitVec.ofNat 64 k)
          else s.mem (s.gpr .rsi + BitVec.ofNat 64 k)) ^^^
        (serialize (plus vs (S0 s) (k / 64))).getD (k % 64) 0) ∧
      (∀ j < 8, ∀ p (hp : p < 16), zw s' (blkReg (8 + j)) p = (plus vs (S0 s) (8 + j))[p]'hp) ∧
      Frame (wregs 128 s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := finishPSelCheck_eq
  unfold finishPSelCheck at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (Avx512Tail.runPieces_ok hc hs _ (SRel.init 128 s) hr) fun s' h => ⟨fun k hk => ?_,
      fun j hj p hp => ?_, h.frame, h.gpr, h.rd, h.wr⟩
    · have d := h.mem 2 (k / 4) (by decide) (by simp only [bsize]; omega_arith)
      rw [e.1 _ (by omega_arith)] at d
      simp only [Avx512Tail.T.eval, regn, baseR] at d
      rw [show k / 4 / 16 = k / 64 by omega_arith, show k / 4 % 16 = k % 64 / 4 by omega_arith,
        outT_eval hz hi (by omega_arith) (by omega_arith)] at d
      rw [byte_dword s'.mem, d, BitVec.extractLsb'_xor, inpW_byte,
        serialize_getD _ (Nat.mod_lt _ (by decide)), show k % 64 % 4 = k % 4 by omega_arith]
    · rw [h.reg _ p hp, e.2 j hj p hp, outT_eval hz hi hp (by omega_arith)]
  · cases e

/-! ## The next eight blocks, as far as they fit -/

theorem condSel_run {j : Nat} (hj : j < 8) : ∃ σ, selD (16 * j + 16) Sym.init (blkReg (8 + j)) .xmm2 (64 * j) = some σ ∧
    (∀ i < 16, σ.mem 2 (16 * j + i) = .xor (.inp (16 * j + i)) (.reg (xidx (blkReg (8 + j))) i)) ∧
    (∀ i < 16 * j, σ.mem 2 i = .mem 2 i) ∧ (∀ i < 16, σ.mem 1 i = .mem 1 i) ∧
    (∀ l < 8, ∀ p < 16, σ.reg (xidx (blkReg (8 + l))) p = .reg (xidx (blkReg (8 + l))) p) := by
  have e := condSelCheck_eq
  simp only [condSelCheck, List.all_eq_true, List.mem_range] at e
  have e := e j hj
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at e
    exact ⟨σ, hr, e.1.1.1, e.1.1.2, e.1.2, e.2⟩
  · cases e

/-- Where `condSel` runs: the data from byte `q` on (fewer than 512 bytes of
it left), `buf` at `r9`, `src` from byte `q` on at `r8`, and `r10` the bytes
of `C` from `q` on. -/
structure AtS (s₀ : State) (C q : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = sst s₀
  r9 : s.gpr .r9 = sbp s₀
  rsi : s.gpr .rsi = sdp s₀ + BitVec.ofNat 64 q
  rdx : s.gpr .rdx = BitVec.ofNat 64 (sL s₀ - q)
  le : q ≤ sL s₀
  small : sL s₀ - q < 512
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r8 : s.gpr .r8 = ssp s₀ + BitVec.ofNat 64 q
  r10 : s.gpr .r10 = BitVec.ofNat 64 (C - q)
  frame : Frame [stR s₀, sdR s₀, bufR s₀] s₀.mem s.mem

theorem AtS.at_ {s₀ : State} {C q : Nat} {s : State} (h : AtS s₀ C q s) : At (V s₀) q s :=
  ⟨h.rdi, h.r9, h.rsi, h.rdx, h.le, h.small, h.rd, h.wr⟩

theorem AtS.of_gpr {s₀ : State} {C q : Nat} {s s' : State} (h : AtS s₀ C q s) (hg : s'.gpr = s.gpr)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame [stR s₀, sdR s₀, bufR s₀] s₀.mem s'.mem) :
    AtS s₀ C q s' :=
  ⟨by rw [hg]; exact h.rdi, by rw [hg]; exact h.r9, by rw [hg]; exact h.rsi, by rw [hg]; exact h.rdx, h.le,
    h.small, hrd.trans h.rd, hwr.trans h.wr, by rw [hg]; exact h.r8, by rw [hg]; exact h.r10, hf⟩

/-- The bytes of `src` a selected load in the last pass may read. -/
theorem selOkD_of {s₀ : State} (hp : APre s₀) {C : Nat} (hC : COk s₀ C) {q D : Nat} (hD : q + 4 * D ≤ sL s₀)
    {s : State} (hr9 : s.gpr .r9 = sbp s₀) (hrsi : s.gpr .rsi = sdp s₀ + BitVec.ofNat 64 q)
    (hr8 : s.gpr .r8 = ssp s₀ + BitVec.ofNat 64 q) (hr10 : s.gpr .r10 = BitVec.ofNat 64 (C - q))
    (hrd : s.rd = s₀.rd) : Avx512Tail.SelOk D s := by
  have hS := sS_lt s₀
  have hL := sL_lt s₀
  have e10 : (s.gpr .r10).toNat = C - q := by
    rw [hr10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hC.le; omega)]
  have con : ∀ a n, 0 < n → (srcR s).Contains a n → (srR s₀).Contains a n := fun a n hn ha => by
    have hw := hp.wrap_s
    have hc := hC.le
    simp only [srcR, hr8, e10, Region.Contains] at ha ⊢
    have e : (a - ssp s₀).toNat = (a - (ssp s₀ + BitVec.ofNat 64 q)).toNat + q := by
      have : q < 2 ^ 64 := by omega
      bv_omega
    omega
  have sub : Region.Sub (srcR s) (srR s₀) := fun a ha => con a 1 (by decide) ha
  refine ⟨fun a n hn ha => ?_, fun r hr => ?_⟩
  · rw [hrd, hp.rd]
    exact ⟨srR s₀, by simp, con a n hn ha⟩
  · simp only [wregs, hr9, hrsi, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.s_b.sub_left sub).sub_right (Region.sub_prefix (by omega))
    · exact (hp.s_d.sub_left sub).sub_right (Avx512Tail.win_sub (s₀ := V s₀) hD)

/-- Block `8 + j` into the data from either buffer, if it fits, or else into
`buf`. -/
theorem condSel_ok {s₀ : State} (hp : APre s₀) {C : Nat} (hC : COk s₀ C) {q j : Nat} (hj : j < 8) {s : State}
    (h : AtS s₀ C q s) {B : CState} (hB : ∀ p (hp : p < 16), zw s (blkReg (8 + j)) p = B[p]'hp) :
    WP isa (condSel j) s fun s' => AtS s₀ C q s' ∧ s'.gpr = s.gpr ∧
      (∀ l < 8, ∀ p < 16, zw s' (blkReg (8 + l)) p = zw s (blkReg (8 + l)) p) ∧
      (∀ k < sL s₀ - q, s'.mem (sdp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k) =
        if 64 * j + 64 ≤ sL s₀ - q ∧ k / 64 = j then
          (if 64 * j + 64 ≤ C - q then s.mem (ssp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k)
            else s.mem (sdp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k)) ^^^ (serialize B).getD (k % 64) 0
        else s.mem (sdp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k)) ∧
      (∀ k < 64, s'.mem (sbp s₀ + BitVec.ofNat 64 k) =
        if 64 * j + 64 ≤ sL s₀ - q then s.mem (sbp s₀ + BitVec.ofNat 64 k) else (serialize B).getD k 0) ∧
      Frame [Avx2.bufR (sbp s₀), Avx512Tail.win (V s₀) q (sL s₀ - q)] s.mem s'.mem := by
  have hV := V_APre hp
  have hL := sL_lt s₀
  have hS := sS_lt s₀
  have hle := h.le
  have hsm := h.small
  have hCS := hC.le
  have hLV : Avx2.eL (V s₀) = sL s₀ := rfl
  have fr : ∀ {m : Mem}, Frame [Avx2.bufR (sbp s₀), Avx512Tail.win (V s₀) q (sL s₀ - q)] s.mem m →
      Frame [stR s₀, sdR s₀, bufR s₀] s₀.mem m := fun hf => h.frame.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨bufR s₀, by simp, fun _ h => h⟩
    · exact ⟨sdR s₀, by simp, Avx512Tail.win_sub (s₀ := V s₀) (by omega_arith)⟩)
  refine WP.seq (WP.mono (cmpJ_ok hj h.at_) fun s₁ ⟨g₁, m₁, rd₁, wr₁, z₁, c₁'⟩ => ?_)
  have c₁ : s₁.cf = some (decide (sL s₀ - q < 64 * j + 64)) := c₁'
  have h₁ : AtS s₀ C q s₁ := h.of_gpr g₁ rd₁ wr₁ (by rw [m₁]; exact h.frame)
  have nb : ∀ k < sL s₀ - q, ¬ (⟨sbp s₀, 256⟩ : Region).Contains (sdp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k) 1 :=
    fun k hk hc => hp.d_b _ (by rw [add_ofNat]; exact Avx2.in_dR (s₀ := V s₀) (by omega_arith))
      (bufR_sub _ (by omega_arith) _ hc)
  refine WP.ite (decide (sL s₀ - q < 64 * j + 64)) (by simp [eval, c₁]) (fun hs => ?_) (fun hs => ?_)
  · -- The block does not fit: into `buf`.
    simp only [decide_eq_true_eq] at hs
    obtain ⟨σ, hr, hm, hk⟩ := condS_run hj
    have hc : Ctx 0 s₁ := Avx512Tail.ctx_of hV (D := 0) (p := q) (by omega_arith) (by decide) h₁.rdi
      h₁.r9 h₁.rsi h₁.wr
    refine WP.mono (srun_ok hc _ (SRel.init 0 s₁) hr) fun s₂ e => ?_
    have F : Frame [Avx2.bufR (sbp s₀), Avx512Tail.win (V s₀) q (sL s₀ - q)] s.mem s₂.mem := by
      rw [← m₁]
      refine e.frame.sub fun r hr => ?_
      simp only [wregs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨Avx2.bufR (sbp s₀), by simp, by rw [h₁.r9]; exact bufR_sub _ (by omega_arith)⟩
      · refine ⟨Avx512Tail.win (V s₀) q (sL s₀ - q), by simp, ?_⟩
        intro x hx; simp [Region.Contains] at hx
    refine ⟨h₁.of_gpr e.gpr e.rd e.wr (fr F), e.gpr.trans g₁, fun l hl p hp' => ?_, fun k hk => ?_,
      fun k hk => ?_, F⟩
    · rw [e.reg _ p hp', hk l hl p hp']
      simp only [Avx512Tail.T.eval, Avx512.zreg_xidx, z₁]
    · rw [ite_eq_right (by omega_arith), e.frame _ (by
        intro r hr; simp only [wregs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.r9]; exact nb k hk
        · simp [Region.Contains]), m₁]
    · rw [ite_eq_right (by omega_arith)]
      have d := e.mem 1 (k / 4) (by decide) (by simp only [bsize]; omega_arith)
      rw [hm _ (by omega_arith)] at d
      simp only [Avx512Tail.T.eval, regn, baseR, Avx512.zreg_xidx, h₁.r9, z₁, hB _ (by omega_arith : k / 4 < 16)] at d
      rw [byte_dword s₂.mem, d, serialize_getD _ hk]
  · -- The block fits: into the data.
    simp only [decide_eq_false_iff_not] at hs
    obtain ⟨σ, hr, hx, hlo, hbuf, hk⟩ := condSel_run hj
    have hc : Ctx (16 * j + 16) s₁ := Avx512Tail.ctx_of hV (p := q) (by omega_arith) (by omega_arith) h₁.rdi
      h₁.r9 h₁.rsi h₁.wr
    have hsel : Avx512Tail.SelOk (16 * j + 16) s₁ := selOkD_of hp hC (by omega_arith) h₁.r9 h₁.rsi h₁.r8
      h₁.r10 h₁.rd
    have e10 : (s₁.gpr .r10).toNat = C - q := by
      rw [h₁.r10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    refine WP.mono (Avx512Tail.sel_ok hc hsel (SRel.init _ s₁) hr) fun s₂ e => ?_
    have F : Frame [Avx2.bufR (sbp s₀), Avx512Tail.win (V s₀) q (sL s₀ - q)] s.mem s₂.mem := by
      rw [← m₁]
      refine e.frame.sub fun r hr => ?_
      simp only [wregs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨Avx2.bufR (sbp s₀), by simp, by rw [h₁.r9]; exact bufR_sub _ (by omega_arith)⟩
      · refine ⟨Avx512Tail.win (V s₀) q (sL s₀ - q), by simp, ?_⟩
        rw [h₁.rsi]
        exact Region.sub_prefix (by omega_arith)
    refine ⟨h₁.of_gpr e.gpr e.rd e.wr (fr F), e.gpr.trans g₁, fun l hl p hp' => ?_, fun k hk => ?_,
      fun k hk => ?_, F⟩
    · rw [e.reg _ p hp', hk l hl p hp']
      simp only [Avx512Tail.T.eval, Avx512.zreg_xidx, z₁]
    · rw [byte_dword s₂.mem, ← m₁]
      by_cases hkj : k / 64 = j
      · rw [ite_eq_left ⟨by omega_arith, hkj⟩]
        have d := e.mem 2 (k / 4) (by decide) (by simp only [bsize]; omega_arith)
        rw [show k / 4 = 16 * j + k % 64 / 4 by omega_arith, hx _ (by omega_arith)] at d
        simp only [Avx512Tail.T.eval, regn, baseR, Avx512.zreg_xidx, z₁, h₁.rsi,
          hB _ (by omega_arith : k % 64 / 4 < 16)] at d
        rw [show 4 * (16 * j + k % 64 / 4) = 4 * (k / 4) by omega_arith,
          show 16 * j + k % 64 / 4 = k / 4 by omega_arith] at d
        rw [d, BitVec.extractLsb'_xor, inpW_byte, serialize_getD _ (Nat.mod_lt _ (by decide)),
          show k % 64 % 4 = k % 4 by omega_arith, e10, h₁.r8, h₁.rsi, hkj]
      · rw [ite_eq_right (by omega_arith)]
        by_cases hlt : k < 64 * j
        · have d := e.mem 2 (k / 4) (by decide) (by simp only [bsize]; omega_arith)
          rw [hlo _ (by omega_arith)] at d
          simp only [Avx512Tail.T.eval, regn, baseR, h₁.rsi] at d
          rw [d, ← byte_dword]
        · rw [← byte_dword s₂.mem]
          refine e.frame _ ?_
          intro r hr; simp only [wregs, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [h₁.r9]; exact nb k hk
          · rw [h₁.rsi]
            simp only [Region.Contains]
            rw [show sdp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k - (sdp s₀ + BitVec.ofNat 64 q) =
              BitVec.ofNat 64 k by bv_omega, toNat_ofNat_lt (by omega_arith)]
            omega_arith
    · rw [ite_eq_left (by omega_arith), byte_dword s₂.mem, byte_dword s.mem, ← m₁]
      have d := e.mem 1 (k / 4) (by decide) (by simp only [bsize]; omega_arith)
      rw [hbuf _ (by omega_arith)] at d
      simp only [Avx512Tail.T.eval, regn, baseR, h₁.r9] at d
      rw [d]

/-- Before `condsSel n`, from `sC`: blocks `8 + n` to 15 done (the input
XORed into the data if they fit; the one the data ends in, if any, into
`buf`), blocks `8 + l`, `l < n`, still in their registers. -/
structure CIS (s₀ : State) (C q : Nat) (B : Nat → CState) (sC : State) (n : Nat) (s : State) : Prop where
  at_ : AtS s₀ C q s
  gpr : s.gpr = sC.gpr
  regs : ∀ l < n, ∀ p (hp : p < 16), zw s (blkReg (8 + l)) p = (B l)[p]'hp
  data : ∀ k < sL s₀ - q, s.mem (sdp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k) =
    if n ≤ k / 64 ∧ 64 * (k / 64) + 64 ≤ sL s₀ - q then
      I s₀ (q + k) ^^^ (serialize (B (k / 64))).getD (k % 64) 0
    else sC.mem (sdp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k)
  buf : n ≤ (sL s₀ - q) / 64 → ∀ k < 64,
    s.mem (sbp s₀ + BitVec.ofNat 64 k) = (serialize (B ((sL s₀ - q) / 64))).getD k 0
  frame : Frame [Avx2.bufR (sbp s₀), Avx512Tail.win (V s₀) q (sL s₀ - q)] sC.mem s.mem

theorem condsSel_ok {s₀ : State} (hp : APre s₀) {C : Nat} (hC : COk s₀ C) {q : Nat} (hq : q % 64 = 0)
    {B : Nat → CState} {sC : State}
    (hsC : ∀ k < sL s₀ - q, C ≤ q + k → sC.mem (sdp s₀ + BitVec.ofNat 64 q + BitVec.ofNat 64 k) = I s₀ (q + k)) :
    ∀ n ≤ 8, ∀ {s : State}, CIS s₀ C q B sC n s → WP isa (condsSel n) s (CIS s₀ C q B sC 0)
  | 0, _, _, h => WP.block_nil h
  | n + 1, hn, s, h => by
    have hS := sS_lt s₀
    have hCS := hC.le
    have hC64 := hC.dvd
    have hle := h.at_.le
    refine WP.seq (WP.mono (condSel_ok hp hC (j := n) (by omega_arith) h.at_ (h.regs n (by omega_arith)))
      fun s' ⟨a', g', z', d', b', f'⟩ => condsSel_ok hp hC hq hsC n (by omega_arith)
        ⟨a', g'.trans h.gpr, fun l hl p hp' => ?_, fun k hk => ?_, fun hq' k hk => ?_, h.frame.trans f'⟩)
    · rw [z' l (by omega_arith) p hp']; exact h.regs l (by omega_arith) p hp'
    · rw [d' k hk]
      by_cases hkn : k / 64 = n
      · by_cases hf : 64 * n + 64 ≤ sL s₀ - q
        · rw [ite_eq_left ⟨hf, hkn⟩,
            ite_eq_left (c := n ≤ k / 64 ∧ 64 * (k / 64) + 64 ≤ sL s₀ - q) ⟨by omega_arith, by omega_arith⟩, hkn]
          congr 1
          by_cases hsrc : 64 * n + 64 ≤ C - q
          · rw [ite_eq_left hsrc, add_ofNat, src_frame hp h.at_.frame (by omega_arith)]
            simp only [I, show q + k < sS s₀ by omega_arith, ite_true]
          · rw [ite_eq_right hsrc, h.data k hk, ite_eq_right (by omega_arith), hsC k hk (by omega_arith)]
        · rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith), h.data k hk,
            ite_eq_right (by omega_arith)]
      · rw [ite_eq_right (by omega_arith : ¬ (64 * n + 64 ≤ sL s₀ - q ∧ k / 64 = n)), h.data k hk]
        by_cases hc : n + 1 ≤ k / 64 ∧ 64 * (k / 64) + 64 ≤ sL s₀ - q
        · rw [ite_eq_left hc, ite_eq_left ⟨by omega_arith, hc.2⟩]
        · rw [ite_eq_right hc, ite_eq_right (by omega_arith)]
    · rw [b' k hk]
      by_cases hf : 64 * n + 64 ≤ sL s₀ - q
      · rw [ite_eq_left hf]; exact h.buf (by omega_arith) k hk
      · rw [ite_eq_right hf, show (sL s₀ - q) / 64 = n by omega_arith]

/-! ## The whole pass -/

theorem last16Sel_eq : last16Sel = .seq (.block (([.mov .r9 (.reg .rcx)] : List Instr) ++ setupB .r9))
    (.seq (rounds 10) (.seq (pieces finishPSel) (.seq (.block (adv512 ++
      (([.alu .add .r8 (.imm (BitVec.ofNat 32 512))] : List Instr) ++ subSat 512)))
    (.seq (condsSel 8) (.seq (.block adv)
      (.seq Impl.ChaCha20.X86_64.Avx512Tail.fromBuf (.block [.vop .vzeroupper, .mov .rsi (.reg .r9)]))))))) := rfl

theorem V_KS {s₀ : State} (hp : APre s₀) : Avx2.KS (V s₀) = keystream (stateAt s₀.mem (sst s₀)) (sL s₀) := by
  show keystream (Avx2.S0 (V s₀)) (sL s₀) = _
  rw [V_S0 hp]

theorem last16Sel_ok {s₀ : State} (hp : APre s₀) {C : Nat} (hC : COk s₀ C) {t : Nat}
    (hgt : 512 < sL s₀ - 1024 * t) (hlt : sL s₀ - 1024 * t < 1024) {s : State} (h : SInv s₀ C t s) :
    WP isa last16Sel s fun s' =>
      (gprPreserved (V s₀) s' ∧ Avx2.xorAvx2X86_64.post (V s₀) s') ∧ s'.gpr .rsi = (V s₀).gpr .rcx := by
  have hV := V_APre hp
  have hL := sL_lt s₀
  have hS := sS_lt s₀
  have hCS := hC.le
  have hC64 := hC.dvd
  have hLV : Avx2.eL (V s₀) = sL s₀ := rfl
  have hle := h.le
  have hSL := hp.le
  rw [last16Sel_eq]
  -- The sixteen input states.
  refine WP.seq (WP.block_append (WP.mono (mov_ok s) fun s₁ ⟨r9₁, g₁, m₁, rd₁, wr₁, _⟩ => ?_))
  have gk₁ : ∀ r, r ≠ .r9 → s₁.gpr r = s.gpr r := g₁
  have r9₁' : s₁.gpr .r9 = sbp s₀ := by rw [r9₁, h.rcx]
  have hc₁ : Ctx 0 s₁ := Avx512Tail.ctx_of hV (p := 1024 * t) (by omega_arith) (by decide)
    (by rw [gk₁ _ (by decide)]; exact h.rdi) r9₁' (by rw [gk₁ _ (by decide)]; exact h.rsi) (wr₁.trans h.wr)
  have hi₁ : Incs s₁.mem (s₁.gpr .r9) := by rw [m₁, r9₁']; exact h.incs
  refine WP.mono (Avx512Last.setup_ok hc₁ hi₁) fun s₂ ⟨hz₂, m₂, g₂, rd₂, wr₂⟩ => ?_
  -- The rounds.
  refine WP.seq (WP.mono (Avx512.rounds_ok hz₂ 10) fun s₃ ⟨hz₃, sm₃⟩ => ?_)
  have g₃ : s₃.gpr = s₁.gpr := sm₃.gpr.trans g₂
  have m₃ : s₃.mem = s.mem := sm₃.mem.trans (m₂.trans m₁)
  have rd₃ : s₃.rd = s₀.rd := sm₃.rd.trans (rd₂.trans (rd₁.trans h.rd))
  have wr₃ : s₃.wr = s₀.wr := sm₃.wr.trans (wr₂.trans (wr₁.trans h.wr))
  have rdi₃ : s₃.gpr .rdi = sst s₀ := by rw [g₃, gk₁ _ (by decide)]; exact h.rdi
  have rsi₃ : s₃.gpr .rsi = sdp s₀ + BitVec.ofNat 64 (1024 * t) := by rw [g₃, gk₁ _ (by decide)]; exact h.rsi
  have rdx₃ : s₃.gpr .rdx = BitVec.ofNat 64 (sL s₀ - 1024 * t) := by rw [g₃, gk₁ _ (by decide)]; exact h.rdx
  have r8₃ : s₃.gpr .r8 = ssp s₀ + BitVec.ofNat 64 (1024 * t) := by rw [g₃, gk₁ _ (by decide)]; exact h.r8
  have r10₃ : s₃.gpr .r10 = BitVec.ofNat 64 (C - 1024 * t) := by rw [g₃, gk₁ _ (by decide)]; exact h.r10
  have r9₃ : s₃.gpr .r9 = sbp s₀ := by rw [g₃]; exact r9₁'
  have hS₁ : S0 s₁ = ctr (stateAt s₀.mem (sst s₀)) (16 * t) := by
    simp only [S0, m₁, gk₁ _ (by decide : Reg.rdi ≠ .r9), h.rdi]; exact h.cnt
  have hS₃ : S0 s₃ = ctr (stateAt s₀.mem (sst s₀)) (16 * t) := by simp only [S0, m₃, rdi₃]; exact h.cnt
  -- The output: eight blocks into the data, eight into registers.
  have hc₃ : Ctx 128 s₃ := Avx512Tail.ctx_of hV (p := 1024 * t) (by omega_arith) (by decide) rdi₃ r9₃ rsi₃ wr₃
  have hs₃ : Avx512Tail.SelOk 128 s₃ := selOkD_of hp hC (q := 1024 * t) (by omega_arith) r9₃ rsi₃ r8₃ r10₃
    (by rw [rd₃])
  have hi₃ : Incs s₃.mem (s₃.gpr .r9) := by rw [m₃, r9₃]; exact h.incs
  refine WP.seq (WP.mono (finishPSel_ok hc₃ hs₃ hi₃ hz₃) fun s₄ ⟨d₄, z₄, f₄, g₄, rd₄, wr₄⟩ => ?_)
  refine WP.seq (WP.block_append (WP.mono (adv512_ok (s₀ := V s₀) (p := 1024 * t) (s := s₄) (by omega_arith)
    (by rw [g₄]; exact rsi₃) (by rw [g₄]; exact rdx₃))
    fun s₅' ⟨rsi₅', rdx₅', g₅', z₅', m₅', rd₅', wr₅'⟩ => ?_))
  refine WP.mono (advSel_ok s₅' (n := 512) (c := C - 1024 * t) (by decide) (by omega_arith)
    (by rw [g₅' _ (by decide) (by decide), g₄]; exact r10₃))
    fun s₅ ⟨r8₅, r10₅, g₅, m₅, rd₅, wr₅, z₅⟩ => ?_
  have gk₅ : ∀ r, r ≠ .rsi → r ≠ .rdx → r ≠ .rax → r ≠ .r8 → r ≠ .r10 → s₅.gpr r = s₃.gpr r :=
    fun r a b c d e => by rw [g₅ r c d e, g₅' r a b, g₄]
  rw [show wregs 128 s₃ = [⟨sbp s₀, 256⟩, Avx512Tail.win (V s₀) (1024 * t) 512] by
    simp only [wregs, r9₃, rsi₃, Avx512Tail.win, Nat.reduceMul]; rfl] at f₄
  obtain ⟨B, hBd⟩ : ∃ B : Nat → CState,
      B = fun l => plus (fun j => Nat.repeat Spec.ChaCha20.innerBlock 10 (ctr (S0 s₁) j)) (S0 s₃) (8 + l) :=
    ⟨_, rfl⟩
  have F₅ : Frame [stR s₀, sdR s₀, bufR s₀] s₀.mem s₅.mem := by
    rw [m₅, m₅']
    refine h.frame.trans ?_
    rw [← m₃]
    refine f₄.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨bufR s₀, by simp, bufR_sub _ (by omega_arith)⟩
    · exact ⟨sdR s₀, by simp, Avx512Tail.win_sub (s₀ := V s₀) (by omega_arith)⟩
  have A₅ : AtS s₀ C (1024 * t + 512) s₅ :=
    ⟨by rw [gk₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact rdi₃,
      by rw [gk₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact r9₃,
      by rw [g₅ _ (by decide) (by decide) (by decide)]; exact rsi₅',
      by rw [g₅ _ (by decide) (by decide) (by decide)]; exact rdx₅', by omega_arith, by omega_arith,
      rd₅.trans (rd₅'.trans (rd₄.trans rd₃)), wr₅.trans (wr₅'.trans (wr₄.trans wr₃)),
      by rw [r8₅, g₅' _ (by decide) (by decide), g₄, r8₃, add_ofNat],
      by rw [r10₅, Nat.sub_sub], F₅⟩
  have C₅ : CIS s₀ C (1024 * t + 512) B s₅ 8 s₅ := ⟨A₅, rfl,
    fun l hl q hq => by rw [z₅, z₅', hBd]; exact z₄ l hl q hq,
    fun k hk => by rw [ite_eq_right (by omega_arith)], fun hq => absurd hq (by omega_arith), Frame.refl _ _⟩
  -- The data before this pass's ninth block, as `finishPSel` left it.
  have early : ∀ k < 1024 * t + 512, s₅.mem (sdp s₀ + BitVec.ofNat 64 k) =
      I s₀ k ^^^ (keystream (stateAt s₀.mem (sst s₀)) (sL s₀)).getD k 0 := by
    intro k hk
    rw [m₅, m₅']
    by_cases hkp : k < 1024 * t
    · rw [f₄ _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact fun hc => hp.d_b _ (Avx2.in_dR (s₀ := V s₀) (by omega_arith)) (bufR_sub _ (by omega_arith) _ hc)
        · exact Avx512Tail.not_win (s₀ := V s₀) (by omega_arith) (by omega_arith) (.inl hkp)), m₃, h.done k hkp]
    · have x := d₄ (k - 1024 * t) (by omega_arith)
      rw [rsi₃, r8₃, r10₃, m₃, sel_byte hp hC h (by omega_arith) (by omega_arith), add_ofNat,
        Nat.add_sub_cancel' (by omega_arith : 1024 * t ≤ k)] at x
      rw [x, hS₃, hS₁, ← V_KS hp, Avx512Tail.ks_at (s₀ := V s₀) (p := 1024 * t) (k := k) ⟨16 * t, by omega_arith⟩
        (by omega_arith) (by omega_arith), show 1024 * t / 64 = 16 * t by omega_arith, V_S0 hp]
  -- The next eight blocks, as far as they fit.
  have hsC : ∀ k < sL s₀ - (1024 * t + 512), C ≤ 1024 * t + 512 + k →
      s₅.mem (sdp s₀ + BitVec.ofNat 64 (1024 * t + 512) + BitVec.ofNat 64 k) = I s₀ (1024 * t + 512 + k) := by
    intro k hk hck
    have hk' : 1024 * t + 512 + k < sL s₀ := by omega_arith
    rw [add_ofNat, m₅, m₅', f₄ (sdp s₀ + BitVec.ofNat 64 (1024 * t + 512 + k)) (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact fun hc => hp.d_b _ (Avx2.in_dR (s₀ := V s₀) hk') (bufR_sub _ (by omega_arith) _ hc)
        · exact Avx512Tail.not_win (s₀ := V s₀) (by omega_arith) hk' (.inr (by omega_arith))), m₃]
    exact h.todo _ hk' (by omega_arith) hck
  refine WP.seq (WP.mono (condsSel_ok hp hC (by omega_arith) hsC 8 (by decide) C₅) fun s₆ C₆ => ?_)
  refine WP.seq (WP.mono (adv_ok C₆.at_.at_) fun s₇ ⟨rsi₇, rdx₇, g₇, m₇, rd₇, wr₇⟩ => ?_)
  -- The rest, from `buf`.
  have r9₇ : s₇.gpr .r9 = sbp s₀ := by rw [g₇ _ (by decide) (by decide) (by decide)]; exact C₆.at_.r9
  have keep₇ : ∀ r ∈ calleeSaved, s₇.gpr r = (V s₀).gpr r := fun r hr => by
    obtain ⟨_, a, b, c⟩ := Avx512Tail.r9_not_calleeSaved hr
    obtain ⟨a', b', c', d', e'⟩ := calleeSaved_ne hr
    rw [g₇ r a' b' c', C₆.gpr, gk₅ r b' c' a' d' e', g₃, gk₁ r (Avx512Last.r9_ne hr), V_keep s₀ hr]
    exact h.keep r hr
  have hB : ∀ k, 1024 * t + 512 ≤ k → k < sL s₀ →
      (serialize (B ((k - (1024 * t + 512)) / 64))).getD ((k - (1024 * t + 512)) % 64) 0 =
        (keystream (stateAt s₀.mem (sst s₀)) (sL s₀)).getD k 0 := by
    intro k hk₁ hk₂
    rw [← V_KS hp, Avx512Tail.ks_at (s₀ := V s₀) (p := 1024 * t) (k := k) ⟨16 * t, by omega_arith⟩ (by omega_arith) hk₂,
      hBd]
    simp only [hS₃, hS₁]
    rw [V_S0 hp, show 8 + (k - (1024 * t + 512)) / 64 = (k - 1024 * t) / 64 by omega_arith,
      show (k - (1024 * t + 512)) % 64 = (k - 1024 * t) % 64 by omega_arith,
      show 1024 * t / 64 = 16 * t by omega_arith]
  have hmb := C₆.buf
  replace rsi₇ : s₇.gpr .rsi = sdp s₀ + BitVec.ofNat 64 (1024 * t + 512 + 64 * ((sL s₀ - (1024 * t + 512)) / 64)) :=
    rsi₇
  replace rdx₇ : s₇.gpr .rdx =
      BitVec.ofNat 64 (sL s₀ - (1024 * t + 512 + 64 * ((sL s₀ - (1024 * t + 512)) / 64))) := rdx₇
  generalize hm : (sL s₀ - (1024 * t + 512)) / 64 = m at rsi₇ rdx₇ hmb
  refine WP.seq (WP.mono (Avx512Tail.fromBuf_ok hV (p := 1024 * t + 512 + 64 * m)
    (n := sL s₀ - (1024 * t + 512 + 64 * m))
    (by omega_arith) (by omega_arith) rsi₇ r9₇ rdx₇ (rd₇.trans C₆.at_.rd) (wr₇.trans C₆.at_.wr) keep₇
    (fun k hk => ?_) (fun k hk => ?_) (fun k hk => ?_) ?_) fun s₈ d₈ => Avx512Tail.fin_ok (d₈.fin hV))
  · show s₇.mem (sdp s₀ + BitVec.ofNat 64 k) = Avx2.D0 (V s₀) k ^^^ (Avx2.KS (V s₀)).getD k 0
    rw [m₇, V_D0 s₀ (k := k) (by omega_arith), V_KS hp]
    by_cases hk5 : k < 1024 * t + 512
    · rw [C₆.frame (sdp s₀ + BitVec.ofNat 64 k) (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact fun hc => hp.d_b _ (Avx2.in_dR (s₀ := V s₀) (by omega_arith)) hc
        · exact Avx512Tail.not_win (s₀ := V s₀) (by omega_arith) (by omega_arith) (.inl hk5))]
      exact early k hk5
    · have x := C₆.data (k - (1024 * t + 512)) (by omega_arith)
      rw [add_ofNat, Nat.add_sub_cancel' (by omega_arith : 1024 * t + 512 ≤ k),
        ite_eq_left ⟨Nat.zero_le _, by omega_arith⟩] at x
      rw [x, hB k (by omega_arith) (by omega_arith)]
  · show s₇.mem (sdp s₀ + BitVec.ofNat 64 (1024 * t + 512 + 64 * m) + BitVec.ofNat 64 k) =
      Avx2.D0 (V s₀) (1024 * t + 512 + 64 * m + k)
    have ea : sdp s₀ + BitVec.ofNat 64 (1024 * t + 512 + 64 * m) + BitVec.ofNat 64 k =
        sdp s₀ + BitVec.ofNat 64 (1024 * t + 512) + BitVec.ofNat 64 (64 * m + k) := by
      rw [add_ofNat, add_ofNat, Nat.add_assoc]
    have x := C₆.data (64 * m + k) (by omega_arith)
    rw [m₇, ea, x, ite_eq_right (by omega_arith), hsC _ (by omega_arith) (by omega_arith),
      V_D0 s₀ (by omega_arith), show 1024 * t + 512 + (64 * m + k) = 1024 * t + 512 + 64 * m + k by omega_arith]
  · show s₇.mem (sbp s₀ + BitVec.ofNat 64 k) = (Avx2.KS (V s₀)).getD (1024 * t + 512 + 64 * m + k) 0
    have y := hB (1024 * t + 512 + 64 * m + k) (by omega_arith) (by omega_arith)
    rw [show (1024 * t + 512 + 64 * m + k - (1024 * t + 512)) / 64 = m by omega_arith,
      show (1024 * t + 512 + 64 * m + k - (1024 * t + 512)) % 64 = k by omega_arith] at y
    rw [m₇, V_KS hp, hmb (Nat.zero_le _) k (by omega_arith), y]
  · rw [m₇]
    exact V_frame C₆.at_.frame

end VG.Proof.ChaCha20.X86_64.Avx512Split
