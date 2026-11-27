module

import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.AesCcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesCcm.X86_64.Run
import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Impl.AesCcm.X86_64
public import VerifiedGarbage.Proof.AesCcm.Ctr
public import VerifiedGarbage.Proof.AesCcm.X86_64.Callee

/-! ### `AesCcm.X86_64.Chunk`, which this module and modules that import it used -/

section

/-!
# AES-CCM on x86-64: a chunk of counter mode (`ctrChunk`)

Untrusted: everything here is checked by Lean. After `b` whole blocks
(`CtrInv`), `ctrChunk` encrypts `k = min (n/16 − b, 2³² − (1 + b) mod 2³²)`
more by `vg_aes_ctr32` from `Ctr₁₊ᵦ`, whose counters do not wrap around in
their low 32 bits, so that they are CCM's (`chunk_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

variable [fp : Footprint]

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- What `ctr` writes: `Ctrⱼ` and the keystream block at `W + 64`, `k` at
`W + 216`, the working space of the functions called, the stack below `SP`
and the data. -/
abbrev ctrR (W SP D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 64, 32⟩, ⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 384, scratchBytes⟩, below SP 16, ⟨D, n⟩]

/-- What `ctr` writes, within what the pieces may write. -/
theorem ctrR_mut (W SP D : Addr) (n : Nat) : ∀ r ∈ ctrR W SP D n, ∃ r' ∈ mutR W SP D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
  · exact ⟨wK W, by simp, Offset.sub W (by decide) (by decide)⟩
  · exact ⟨wC W, by simp, scratch_sub_tail W⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- What `ctr` needs, of the state `s` it starts from. -/
structure CtrCtx (K W SP : Addr) (s : State) (R : Nat) (nonce : List Byte) (D : Addr) (n : Nat) : Prop where
  lay : Lay K W SP
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  ro : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R
  h7 : 7 ≤ nonce.length
  h13 : nonce.length ≤ 13
  hn : n < 256 ^ (15 - nonce.length)
  c0 : bytesAt s.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0
  buf : Buf K W SP s D n
  dw : Covers [⟨D, n⟩] s.wr
  dk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩

namespace CtrCtx

variable {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {D : Addr} {n : Nat}

/-- The parts of `W` that `ctr` does not write. -/
theorem disj (C : CtrCtx K W SP s R nonce D n) {d k : Nat}
    (h : d + k ≤ 64 ∨ (96 ≤ d ∧ d + k ≤ 216) ∨ (224 ≤ d ∧ d + k ≤ 384)) :
    ∀ r ∈ ctrR W SP D n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact C.lay.w_w (by omega_arith) (by omega_arith) (by decide)
  · exact C.lay.w_w (by omega_arith) (by omega_arith) (by decide)
  · exact C.lay.w_w (.inl (by omega_arith)) (by omega_arith) (by have := tailBytes_le; have := scratchBytes_le; omega)
  · exact (C.lay.stk_w' (by omega_arith)).symm
  · exact (C.buf.w.sub_right (Lay.wSub (by omega_arith))).symm

theorem kdisj (C : CtrCtx K W SP s R nonce D n) : ∀ r ∈ ctrR W SP D n, (⟨K, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact C.lay.k_w.sub_right (Lay.wSub (by decide))
  · exact C.lay.k_w.sub_right (Lay.wSub (by decide))
  · exact C.lay.k_w.sub_right (Lay.wSub (by have := tailBytes_le; have := scratchBytes_le; omega))
  · exact C.lay.stk_k.symm
  · exact C.dk

theorem bytes_kept (C : CtrCtx K W SP s R nonce D n) {m : Mem} (hf : Frame (ctrR W SP D n) s.mem m) {d k : Nat}
    (h : d + k ≤ 64 ∨ (96 ≤ d ∧ d + k ≤ 216) ∨ (224 ≤ d ∧ d + k ≤ 384)) :
    bytesAt m (W + BitVec.ofNat 64 d) k = bytesAt s.mem (W + BitVec.ofNat 64 d) k :=
  bytesAt_frame hf (C.disj h) (by omega_arith)

theorem readW_kept (C : CtrCtx K W SP s R nonce D n) {m : Mem} (hf : Frame (ctrR W SP D n) s.mem m) {d : Nat}
    (h : d + 8 ≤ 64 ∨ (96 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 384)) :
    m.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (w := 64) (Region.contains_self _ _) (C.disj h) (by decide)

theorem ciph_kept (C : CtrCtx K W SP s R nonce D n) {m : Mem} (hf : Frame (ctrR W SP D n) s.mem m) :
    Spec.Ccm.ctxCiph m K R = Spec.Ccm.ctxCiph s.mem K R :=
  ctxCiph_frame hf C.kdisj (by rcases C.rounds with h | h | h <;> subst h <;> decide)

end CtrCtx

/-- The state of `ctr` after `b` whole blocks: those encrypted, the rest of
the data as it was. -/
structure CtrInv (K W SP : Addr) (s : State) (R : Nat) (nonce : List Byte) (D : Addr) (n b : Nat) (t : State) :
    Prop where
  env : Env K W SP t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  r12 : t.gpr .r12 = D + BitVec.ofNat 64 (16 * b)
  rbx : t.gpr .rbx = BitVec.ofNat 64 (n / 16 - b)
  r14 : t.gpr .r14 = BitVec.ofNat 64 (1 + b)
  le : b ≤ n / 16
  frame : Frame (ctrR W SP D n) s.mem t.mem
  done : bytesAt t.mem D (16 * b) = xorFrom (Spec.Ccm.ctxCiph s.mem K R) nonce 1 (bytesAt s.mem D (16 * b))
  rest : bytesAt t.mem (D + BitVec.ofNat 64 (16 * b)) (n - 16 * b) =
    bytesAt s.mem (D + BitVec.ofNat 64 (16 * b)) (n - 16 * b)

omit fp in
theorem low32 (x : Nat) : ((BitVec.ofNat 64 x).setWidth 32).setWidth 64 = BitVec.ofNat 64 (x % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

omit fp in
theorem two32_sub {y : Nat} (hy : y < 2 ^ 32) :
    (4294967296 : BitVec 64) - BitVec.ofNat 64 y = BitVec.ofNat 64 (2 ^ 32 - y) :=
  ofNat_sub (a := 2 ^ 32) (b := y) (Nat.le_of_lt hy) (by decide)

omit fp in
/-- `k = min (m, 2³² − (1 + b) mod 2³²)` in `r8`, for `m` blocks left. -/
theorem kSel_ok {b m : Nat} {t : State} (hbx : t.gpr .rbx = BitVec.ofNat 64 m)
    (h14 : t.gpr .r14 = BitVec.ofNat 64 (1 + b)) (hm : m < 2 ^ 64) :
    WP isa (.seq (.block [.mov32 .r8 (.reg .r14), .movImm64 .rcx 0x100000000, .alu .sub .rcx (.reg .r8),
        .mov .r8 (.reg .rbx), .alu .cmp .rbx (.reg .rcx)]) (.ite .b (.block []) (.block [.mov .r8 (.reg .rcx)]))) t
      fun t₂ => t₂.mem = t.mem ∧ t₂.gpr .r8 = BitVec.ofNat 64 (min m (2 ^ 32 - (1 + b) % 2 ^ 32)) ∧
        (∀ r, r ≠ .r8 → r ≠ .rcx → t₂.gpr r = t.gpr r) ∧ t₂.rd = t.rd ∧ t₂.wr = t.wr := by
  obtain ⟨t₁, run₁, hm₁, hr8₁, hcx₁, hcf₁, hg₁, hrd₁, hwr₁⟩ : ∃ t₁, runBlock isa
      [.mov32 .r8 (.reg .r14), .movImm64 .rcx 0x100000000, .alu .sub .rcx (.reg .r8),
        .mov .r8 (.reg .rbx), .alu .cmp .rbx (.reg .rcx)] t = some t₁ ∧ t₁.mem = t.mem ∧
      t₁.gpr .r8 = BitVec.ofNat 64 m ∧ t₁.gpr .rcx = BitVec.ofNat 64 (2 ^ 32 - (1 + b) % 2 ^ 32) ∧
      t₁.cf = some (decide (m < 2 ^ 32 - (1 + b) % 2 ^ 32)) ∧
      (∀ r, r ≠ .r8 → r ≠ .rcx → t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h14]
      rw [low32, two32_sub (Nat.mod_lt _ (by decide))]
    · simp only [cf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h14, hbx]
      rw [low32, two32_sub (Nat.mod_lt _ (by decide)), toNat_ofNat_of_lt hm,
        toNat_ofNat_of_lt (by omega_arith)]
    · intro r h₁ h₂; simp only [gpr_setReg, gpr_arithFlags, h₁, h₂, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite _ (eval_b hcf₁) (fun ht => ?_) (fun hf => ?_)
  · have h := of_decide_eq_true ht
    exact WP.of_runBlock ⟨t₁, rfl, hm₁, by rw [hr8₁, Nat.min_eq_left (by omega_arith)], hg₁, hrd₁, hwr₁⟩
  · have h := of_decide_eq_false hf
    refine WP.of_runBlock ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_⟩
    · exact hm₁
    · simp only [gpr_setReg, ite_true, hcx₁, Nat.min_eq_right (Nat.le_of_not_lt h)]
    · intro r h₁ h₂; simp only [gpr_setReg, h₁, ite_false]; exact hg₁ r h₁ h₂
    · exact hrd₁
    · exact hwr₁

/-- The arguments of the call, and `Ctr₁₊ᵦ`. -/
theorem setup_ok {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {D : Addr} {n : Nat}
    (C : CtrCtx K W SP s R nonce D n) {b k : Nat} {t t₂ : State} (I : CtrInv K W SP s R nonce D n b t)
    (hb : b < n / 16) (hm₂ : t₂.mem = t.mem) (hr8₂ : t₂.gpr .r8 = BitVec.ofNat 64 k)
    (hg₂ : ∀ r, r ≠ .r8 → r ≠ .rcx → t₂.gpr r = t.gpr r) (hrd₂ : t₂.rd = t.rd) (hwr₂ : t₂.wr = t.wr) :
    ∃ t₅, runBlock isa (([.mov .rsi (.mem (at_ .r15 roundsO)), .mov .rax (.reg .r14)] : List Instr) ++ ctrAt ++
        ([.store (at_ .r15 kO) .r8, .mov .rdi (.reg .r13)] : List Instr) ++ ptr .rdx .r15 c1O ++ ([.mov .rcx (.reg .r12)] : List Instr) ++
        ptr .r9 .r15 scrO) t₂ = some t₅ ∧
      Frame [⟨W + BitVec.ofNat 64 64, 16⟩, ⟨W + BitVec.ofNat 64 216, 8⟩] t.mem t₅.mem ∧
      bytesAt t₅.mem (W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce (1 + b) ∧
      t₅.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k ∧
      t₅.gpr .rdi = K ∧ t₅.gpr .rsi = BitVec.ofNat 64 R ∧ t₅.gpr .rdx = W + BitVec.ofNat 64 64 ∧
      t₅.gpr .rcx = D + BitVec.ofNat 64 (16 * b) ∧ t₅.gpr .r8 = BitVec.ofNat 64 k ∧
      t₅.gpr .r9 = W + BitVec.ofNat 64 384 ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp, .rbx, .r12, .r14], t₅.gpr r = t.gpr r) ∧ t₅.rd = t.rd ∧ t₅.wr = t.wr := by
  have E := I.env
  have E₂ : Env K W SP t₂ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hrd₂ hwr₂
  have h15 := E₂.r15
  have rR := E₂.perm.wR (show 232 + 8 ≤ 2560 by decide)
  have hRo : t₂.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
    rw [hm₂, C.readW_kept I.frame (by omega_arith), C.ro]
  obtain ⟨t₃, run₃, hm₃, hsi₃, hax₃, hg₃, hrd₃, hwr₃⟩ : ∃ t₃, runBlock isa
      [.mov .rsi (.mem (at_ .r15 roundsO)), .mov .rax (.reg .r14)] t₂ = some t₃ ∧ t₃.mem = t₂.mem ∧
      t₃.gpr .rsi = BitVec.ofNat 64 R ∧ t₃.gpr .rax = BitVec.ofNat 64 (1 + b) ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → t₃.gpr r = t₂.gpr r) ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by crun [h15, rR], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, hRo]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, hg₂ .r14 (by decide) (by decide), I.r14]
    · intro r h₁ h₂; simp only [gpr_setReg, h₁, h₂, ite_false]
    all_goals rfl
  have E₃ : Env K W SP t₃ := E₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide)) hrd₃ hwr₃
  have hc0₃ : bytesAt t₃.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 := by
    rw [hm₃, hm₂, C.bytes_kept I.frame (by omega_arith), C.c0]
  have hq16 : n / 16 < 256 ^ (15 - nonce.length) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) C.hn
  obtain ⟨t₄, run₄, f₄, hc₄, hg₄, hrd₄, hwr₄⟩ :=
    ctrAt_ok E₃ C.h7 C.h13 hc0₃ (i := 1 + b) (by omega_arith) hax₃
  have E₄ : Env K W SP t₄ := E₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₄ _ (by decide) (by decide) (by decide)) hrd₄ hwr₄
  have h15₄ := E₄.r15
  have wk := E₄.perm.wW (show 216 + 8 ≤ 2560 by decide)
  have g₄ : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → t₄.gpr r = t.gpr r := fun r a c d e f => by
    rw [hg₄ r a c d, hg₃ r a e, hg₂ r f c]
  have r8₄ : t₄.gpr .r8 = BitVec.ofNat 64 k := by
    rw [hg₄ .r8 (by decide) (by decide) (by decide), hg₃ .r8 (by decide) (by decide), hr8₂]
  obtain ⟨t₅, run₅, hm₅, hdi, hsi, hdx, hcx, hr8, hr9, hg₅, hrd₅, hwr₅⟩ : ∃ t₅, runBlock isa
      ([.store (at_ .r15 kO) .r8, .mov .rdi (.reg .r13)] ++ ptr .rdx .r15 c1O ++ [.mov .rcx (.reg .r12)] ++
        ptr .r9 .r15 scrO) t₄ = some t₅ ∧ t₅.mem = t₄.mem.writeW (W + BitVec.ofNat 64 216) (BitVec.ofNat 64 k) ∧
      t₅.gpr .rdi = K ∧ t₅.gpr .rsi = BitVec.ofNat 64 R ∧ t₅.gpr .rdx = W + BitVec.ofNat 64 64 ∧
      t₅.gpr .rcx = D + BitVec.ofNat 64 (16 * b) ∧ t₅.gpr .r8 = BitVec.ofNat 64 k ∧
      t₅.gpr .r9 = W + BitVec.ofNat 64 384 ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp, .rbx, .r12, .r14], t₅.gpr r = t.gpr r) ∧ t₅.rd = t.rd ∧ t₅.wr = t.wr := by
    refine ⟨_, by crun [h15₄, wk], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, r8₄]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, E₄.r13]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
        hg₄ .rsi (by decide) (by decide) (by decide), hsi₃]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15₄]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
        g₄ .r12 (by decide) (by decide) (by decide) (by decide) (by decide), I.r12]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, r8₄]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15₄]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq] <;>
        exact g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · simp only [rd_setReg, rd_arithFlags]; rw [hrd₄, hrd₃, hrd₂]
    · simp only [wr_setReg, wr_arithFlags]; rw [hwr₄, hwr₃, hwr₂]
  have hdis : (⟨W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 216, 8⟩ :=
    C.lay.w_w (.inl (by decide)) (by decide) (by decide)
  refine ⟨t₅, ?_, ?_, ?_, by rw [hm₅, Mem.readW_writeW_self64], hdi, hsi, hdx, hcx, hr8, hr9, hg₅, hrd₅, hwr₅⟩
  · simp only [List.append_assoc]
    rw [runBlock_append, run₃, Option.bind_some, runBlock_append, run₄, Option.bind_some]
    simpa only [List.append_assoc] using run₅
  · rw [hm₅, ← hm₂, ← hm₃]
    exact (f₄.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩).writeW
      (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (by simp) _ (Region.contains_self _ _)
  · rw [hm₅, bytesAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self ⟨W + BitVec.ofNat 64 216, 8⟩) _
      (Region.contains_self _ _)) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hdis)
      (by decide), hc₄]

omit fp in
/-- What follows the call: `k` blocks past them, and ZF set when none is left. -/
theorem step_ok {W D : Addr} {t : State} {n b k : Nat} (h15 : t.gpr .r15 = W)
    (rk : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 216) 8)
    (hkO : t.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k)
    (hbx : t.gpr .rbx = BitVec.ofNat 64 (n / 16 - b)) (h14 : t.gpr .r14 = BitVec.ofNat 64 (1 + b))
    (h12 : t.gpr .r12 = D + BitVec.ofNat 64 (16 * b)) (hkb : b + k ≤ n / 16) (hn : n < 2 ^ 64) :
    ∃ t', runBlock isa
      [.mov .rax (.mem (at_ .r15 kO)), .alu .sub .rbx (.reg .rax), .alu .add .r14 (.reg .rax),
        .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .alu .add .r12 (.reg .rax), .alu .test .rbx (.reg .rbx)] t = some t' ∧ t'.mem = t.mem ∧
      t'.gpr .rbx = BitVec.ofNat 64 (n / 16 - (b + k)) ∧ t'.gpr .r14 = BitVec.ofNat 64 (1 + (b + k)) ∧
      t'.gpr .r12 = D + BitVec.ofNat 64 (16 * (b + k)) ∧ t'.zf = some (decide (b + k = n / 16)) ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp], t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by crun [h15, rk], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hkO, hbx]
    rw [show n / 16 - (b + k) = n / 16 - b - k by omega_arith]
    exact ofNat_sub (by omega_arith) (by omega_arith)
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hkO, h14]
    rw [ofNat_add_ofNat, Nat.add_assoc]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hkO, h12, ofNat_add_ofNat,
      BitVec.add_assoc]
    rw [show 16 * b + (k + k + (k + k) + (k + k + (k + k)) + (k + k + (k + k) + (k + k + (k + k)))) =
      16 * (b + k) by omega_arith]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hkO, hbx]
    rw [ofNat_sub (by omega_arith) (by omega_arith), and_self_beq (by omega_arith)]
    simp only [Option.some.injEq, decide_eq_decide]
    omega_arith
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

/-- The state after a chunk of `k` blocks. -/
theorem chunk_inv {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {D : Addr} {n : Nat}
    (C : CtrCtx K W SP s R nonce D n) {b k : Nat} {t : State} (I : CtrInv K W SP s R nonce D n b t)
    (hk32 : (1 + b) % 2 ^ 32 + k ≤ 2 ^ 32) (hkb : b + k ≤ n / 16) {t₅ t₆ t₇ : State}
    (f₅ : Frame [⟨W + BitVec.ofNat 64 64, 16⟩, ⟨W + BitVec.ofNat 64 216, 8⟩] t.mem t₅.mem)
    (hc₅ : bytesAt t₅.mem (W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce (1 + b))
    (hsp : t₅.gpr .rsp = SP)
    (h : CtrPost t₅ K (W + BitVec.ofNat 64 64) (D + BitVec.ofNat 64 (16 * b)) (W + BitVec.ofNat 64 384) R k t₆)
    (hm₇ : t₇.mem = t₆.mem) :
    Frame (ctrR W SP D n) s.mem t₇.mem ∧
      bytesAt t₇.mem D (16 * (b + k)) =
        xorFrom (Spec.Ccm.ctxCiph s.mem K R) nonce 1 (bytesAt s.mem D (16 * (b + k))) ∧
      bytesAt t₇.mem (D + BitVec.ofNat 64 (16 * (b + k))) (n - 16 * (b + k)) =
        bytesAt s.mem (D + BitVec.ofNat 64 (16 * (b + k))) (n - 16 * (b + k)) := by
  have L := C.lay
  have hn64 : n < 2 ^ 64 := C.buf.lt
  have cR : Frame [⟨W + BitVec.ofNat 64 64, 16⟩, ⟨W + BitVec.ofNat 64 216, 8⟩, ⟨D + BitVec.ofNat 64 (16 * b), 16 * k⟩,
      ⟨W + BitVec.ofNat 64 384, scratchBytes⟩, below SP 8] t.mem t₇.mem := by
    have fc := h.frame
    rw [hsp] at fc
    rw [hm₇]
    refine (f₅.sub fun r hr => ?_).trans (fc.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  have toR : ∀ r ∈ [(⟨W + BitVec.ofNat 64 64, 16⟩ : Region), ⟨W + BitVec.ofNat 64 216, 8⟩,
      ⟨D + BitVec.ofNat 64 (16 * b), 16 * k⟩, ⟨W + BitVec.ofNat 64 384, scratchBytes⟩, below SP 8],
      ∃ r' ∈ ctrR W SP D n, Region.Sub r r' := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨D, n⟩, by simp, Offset.sub_base D (by omega_arith)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 384, scratchBytes⟩, by simp, Region.sub_prefix (by simp)⟩
    · exact ⟨below SP 16, by simp, below8_sub SP⟩
  -- Separation of the data from what the chunk wrote.
  have sep : ∀ {a l : Nat}, (a + l ≤ 16 * b ∨ 16 * (b + k) ≤ a) → a + l ≤ n →
      ∀ r ∈ [(⟨W + BitVec.ofNat 64 64, 16⟩ : Region), ⟨W + BitVec.ofNat 64 216, 8⟩,
        ⟨D + BitVec.ofNat 64 (16 * b), 16 * k⟩, ⟨W + BitVec.ofNat 64 384, scratchBytes⟩, below SP 8],
        (⟨D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
    intro a l ha hl r hr
    have hB := C.buf.slice (a := a) (k := l) hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hB.w.sub_right (Lay.wSub (by decide))
    · exact hB.w.sub_right (Lay.wSub (by decide))
    · exact Offset.disjoint D (by omega_arith) (by omega_arith) (by omega_arith)
    · exact hB.w.sub_right (Lay.wSub (by have := tailBytes_le; have := scratchBytes_le; omega))
    · exact (hB.stk.sub_left (below8_sub SP)).symm
  have hbk : 16 * (b + k) = 16 * b + 16 * k := Nat.mul_add _ _ _
  refine ⟨I.frame.trans (cR.sub toR), ?_, ?_⟩
  · -- The blocks done.
    have h₁ : bytesAt t₇.mem D (16 * b) = bytesAt t.mem D (16 * b) := by
      have := bytesAt_frame cR (sep (a := 0) (l := 16 * b) (.inl (by omega_arith)) (by omega_arith)) (by omega_arith)
      rwa [BitVec.add_zero] at this
    have hinc : ∀ i < k, Nat.repeat Spec.Gcm.inc32 i (Spec.Gcm.blockAt t₅.mem (W + BitVec.ofNat 64 64)) =
        Spec.Gcm.ofBytes (Spec.Ccm.ctrBlock nonce (1 + b + i)) := fun i hi => by
      show Nat.repeat Spec.Gcm.inc32 i (Spec.Gcm.ofBytes (bytesAt t₅.mem (W + BitVec.ofNat 64 64) 16)) = _
      rw [hc₅]
      exact repeat_inc32_ctrBlock C.h7 C.h13 hk32
        (by have := Nat.lt_of_le_of_lt (Nat.div_le_self n 16) C.hn; omega_arith) i hi
    have hx := ctr32_ccm (by have := C.h13; omega_arith) hinc h.out
    have f₅' : Frame (ctrR W SP D n) s.mem t₅.mem := I.frame.trans (f₅.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub W (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩)
    have hx₅ : bytesAt t₅.mem (D + BitVec.ofNat 64 (16 * b)) (16 * k) =
        bytesAt s.mem (D + BitVec.ofNat 64 (16 * b)) (16 * k) := by
      have hB := C.buf.slice (a := 16 * b) (k := n - 16 * b) (by omega_arith)
      rw [bytesAt_prefix t₅.mem _ (show 16 * k ≤ n - 16 * b by omega_arith),
        bytesAt_prefix s.mem _ (show 16 * k ≤ n - 16 * b by omega_arith), ← I.rest,
        bytesAt_frame f₅ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hB.w.sub_right (Lay.wSub (by decide))
          · exact hB.w.sub_right (Lay.wSub (by decide))) (by omega_arith)]
    rw [hbk, Proof.Cmac.Stream.bytesAt_append, Proof.Cmac.Stream.bytesAt_append, h₁, I.done, hm₇, hx, hx₅,
      C.ciph_kept f₅', xorFrom_append _ _ _ (length_bytesAt _ _ _), Nat.add_comm 1 b]
  · -- The rest of the data.
    have hR' := bytesAt_frame cR (sep (a := 16 * (b + k)) (l := n - 16 * (b + k)) (.inr (Nat.le_refl _))
      (by omega_arith)) (by omega_arith)
    rw [hR', show D + BitVec.ofNat 64 (16 * (b + k)) = D + BitVec.ofNat 64 (16 * b) + BitVec.ofNat 64 (16 * k) by
        rw [add_ofNat_assoc, hbk],
      show n - 16 * (b + k) = n - 16 * b - 16 * k by omega_arith, bytesAt_suffix _ _ (show 16 * k ≤ n - 16 * b by omega_arith),
      bytesAt_suffix _ _ (show 16 * k ≤ n - 16 * b by omega_arith), I.rest]

/-- One chunk. -/
theorem chunk_ok (v : Ctr32Impl) [CtrFits v] {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {D : Addr} {n : Nat}
    (C : CtrCtx K W SP s R nonce D n) {b : Nat} {t : State} (I : CtrInv K W SP s R nonce D n b t)
    (hb : b < n / 16) :
    WP isa (ctrChunk v.callee) t fun t' => ∃ k, k = min (n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32) ∧ 1 ≤ k ∧
      b + k ≤ n / 16 ∧ CtrInv K W SP s R nonce D n (b + k) t' ∧ t'.zf = some (decide (b + k = n / 16)) := by
  have L := C.lay
  have hn64 : n < 2 ^ 64 := C.buf.lt
  refine seq_assoc (WP.seq (WP.mono (kSel_ok I.rbx I.r14 (by omega_arith)) fun t₂ ⟨hm₂, hr8₂, hg₂, hrd₂, hwr₂⟩ => ?_))
  obtain ⟨k, hk⟩ : ∃ k, k = min (n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32) := ⟨_, rfl⟩
  rw [← hk] at hr8₂
  have hk1 : 1 ≤ k := by rw [hk]; have := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide); omega_arith
  have hkb : b + k ≤ n / 16 := by rw [hk]; omega_arith
  have hk32 : (1 + b) % 2 ^ 32 + k ≤ 2 ^ 32 := by
    rw [hk]; have := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide); omega_arith
  obtain ⟨t₅, run₅, f₅, hc₅, hkO₅, hdi, hsi, hdx, hcx, hr8, hr9, hg₅, hrd₅, hwr₅⟩ :=
    setup_ok C I hb hm₂ hr8₂ hg₂ hrd₂ hwr₂
  have E₅ : Env K W SP t₅ := I.env.keep (fun r hr => hg₅ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)) hrd₅ hwr₅
  refine WP.seq (WP.of_runBlock ⟨t₅, run₅, ?_⟩)
  -- The call.
  have hS := (C.buf.of_eq (hrd₅.trans I.rd) (hwr₅.trans I.wr)).slice (a := 16 * b) (k := 16 * k) (by omega_arith)
  have hqc : (⟨D + BitVec.ofNat 64 (16 * b), 16 * k⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 64, 16⟩ :=
    hS.w.sub_right (Lay.wSub (by decide))
  have hqk : (⟨K, 240⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * b), 16 * k⟩ :=
    C.dk.sub_right (Offset.sub_base D (by omega_arith))
  have hqw : Covers [⟨D + BitVec.ofNat 64 (16 * b), 16 * k⟩] t₅.wr := by
    rw [hwr₅, I.wr]; exact covers_off C.dw (by omega_arith) hn64
  refine WP.seq (WP.mono (ctr_call v (cargs L E₅ C.rounds (c := 64) (by decide) (srcBuf hS) hqc hqk hqw
    hdi hsi hdx hcx hr8 hr9)) fun t₆ h => ?_)
  have E₆ : Env K W SP t₆ := E₅.of_saved h.saved h.rd h.wr
  have sv : ∀ r ∈ [Reg.rbx, .r12, .r14], t₆.gpr r = t.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [h.saved r (by rcases hr with rfl | rfl | rfl <;> decide), hg₅ r (by rcases hr with rfl | rfl | rfl <;> simp)]
  have dK : ∀ r ∈ [(⟨W + BitVec.ofNat 64 64, 16⟩ : Region), ⟨D + BitVec.ofNat 64 (16 * b), 16 * k⟩,
      ⟨W + BitVec.ofNat 64 384, scratchBytes⟩, below (t₅.gpr .rsp) 8], (⟨W + BitVec.ofNat 64 216, 8⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact (hS.w.sub_right (Lay.wSub (by decide))).symm
    · exact L.w_w (.inl (by decide)) (by decide) (by have := tailBytes_le; have := scratchBytes_le; omega)
    · rw [E₅.rsp]; exact ((L.stk_w' (by decide)).sub_left (below8_sub _)).symm
  have hkO : t₆.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k := by
    rw [h.frame.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) dK (by decide), hkO₅]
  obtain ⟨t₇, run₇, hm₇, hbx₇, h14₇, h12₇, hzf₇, hg₇, hrd₇, hwr₇⟩ :=
    step_ok E₆.r15 (E₆.perm.wR (show 216 + 8 ≤ 2560 by decide)) hkO (by rw [sv .rbx (by simp), I.rbx])
      (by rw [sv .r14 (by simp), I.r14]) (by rw [sv .r12 (by simp), I.r12]) hkb hn64
  obtain ⟨fr, dn, rs⟩ := chunk_inv C I hk32 hkb f₅ hc₅ E₅.rsp h hm₇
  exact WP.of_runBlock ⟨t₇, run₇, k, hk, hk1, hkb, ⟨E₆.keep hg₇ hrd₇ hwr₇, by rw [hrd₇, h.rd, hrd₅, I.rd],
    by rw [hwr₇, h.wr, hwr₅, I.wr], h12₇, hbx₇, h14₇, hkb, fr, dn, rs⟩, hzf₇⟩

end VG.Proof.AesCcm.X86_64

end

end

/-!
# AES-CCM on x86-64: counter mode (`ctr`)

Untrusted: everything here is checked by Lean. `ctr` encrypts the whole
blocks of the data in chunks (`ctrHead_ok`, by `chunk_ok`), then its last
`n mod 16` bytes with `CIPH_K(Ctr₁₊ₙ/₁₆)`, which `vg_aes_ctr32` writes over a
zero block (`tail_ok`): the data XORed with CCM's keystream from `Ctr₁`
(`ctr_ok`), which is its encryption (`Proof.AesCcm.crypt_eq`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

variable [fp : Footprint]

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr xorLoop)
open VG.Proof.AesGcm.X86_64 (LoopPre xorLoop_ok xorBytes)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- `r12`, `rbx` and `r14` for the first chunk. -/
theorem ctrHeadBlk_ok {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {N A D : Addr}
    {nl al n tl : Nat} (C : CtrCtx K W SP s R nonce D n) (E : Env K W SP s) (S : Slots W R N A D nl al n tl s.mem) :
    WP isa (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbx (.mem (at_ .r15 lenO)), .shift .shr .rbx 4,
      .mov32 .r14 (imm 1), .alu .test .rbx (.reg .rbx)]) s fun s₁ =>
      CtrInv K W SP s R nonce D n 0 s₁ ∧ s₁.zf = some (decide (n / 16 = 0)) := by
  have h15 := E.r15
  obtain r₁ := E.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain r₂ := E.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have hn64 := C.buf.lt
  have hd := S.data
  have hl := S.len
  obtain ⟨s₁, run₁, hm₁, h12, hbx, h14, hzf, hg, hrd, hwr⟩ : ∃ s₁, runBlock isa
      [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbx (.mem (at_ .r15 lenO)), .shift .shr .rbx 4,
        .mov32 .r14 (imm 1), .alu .test .rbx (.reg .rbx)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .r12 = D ∧ s₁.gpr .rbx = BitVec.ofNat 64 (n / 16) ∧ s₁.gpr .r14 = BitVec.ofNat 64 1 ∧
      s₁.zf = some (decide (n / 16 = 0)) ∧ (∀ r ∈ [Reg.r13, .r15, .rsp], s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [h15, r₁, r₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hd]
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hl, shr4 n hn64]
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hl,
        shr4 n hn64, and_self_beq (show n / 16 < 2 ^ 64 by omega_arith)]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  exact WP.of_runBlock ⟨s₁, run₁, ⟨E.keep hg hrd hwr, hrd, hwr, by rw [h12, Nat.mul_zero, BitVec.add_zero],
    by rw [hbx, Nat.sub_zero], h14, Nat.zero_le _, by rw [hm₁]; exact Frame.refl _ _, rfl, by rw [hm₁]⟩, hzf⟩

/-- The whole blocks, in chunks. -/
theorem ctrHead_ok (v : Ctr32Impl) [CtrFits v] {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {N A D : Addr}
    {nl al n tl : Nat} (C : CtrCtx K W SP s R nonce D n) (E : Env K W SP s) (S : Slots W R N A D nl al n tl s.mem) :
    WP isa (.seq (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbx (.mem (at_ .r15 lenO)), .shift .shr .rbx 4,
      .mov32 .r14 (imm 1), .alu .test .rbx (.reg .rbx)]) (.ite .e (.block []) (.loop (ctrChunk v.callee) .ne))) s
      (CtrInv K W SP s R nonce D n (n / 16)) := by
  refine WP.seq (WP.mono (ctrHeadBlk_ok C E S) fun s₁ ⟨I₀, hzf⟩ => ?_)
  refine WP.ite _ (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 := of_decide_eq_true ht
    exact WP.of_runBlock ⟨s₁, rfl, by rw [h0]; exact I₀⟩
  · have h0 := of_decide_eq_false hf
    refine WP.loop (M := isa) (fun m t => ∃ b, m = n / 16 - b ∧ b < n / 16 ∧ CtrInv K W SP s R nonce D n b t) ?_
      (n / 16 - 0) s₁ ⟨0, rfl, by omega_arith, I₀⟩
    rintro m t ⟨b, rfl, hb, I⟩
    refine WP.mono (chunk_ok v C I hb) fun t' ⟨k, _, hk1, hkb, I', hz⟩ => ?_
    by_cases he : b + k = n / 16
    · left; exact ⟨(eval_ne hz).trans (by simp [he]), by rw [← he]; exact I'⟩
    · right; exact ⟨(eval_ne hz).trans (by simp [he]), n / 16 - (b + k), by omega_arith, b + k, rfl, by omega_arith, I'⟩

omit fp in
/-- The arguments of the call for the last bytes: `Ctr₁₊ₙ/₁₆` and a zero
block at `W + 80`. -/
theorem tailSetup_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {R : Nat} {nonce : List Byte} {j : Nat}
    (hRo : t.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt t.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    (hj : j < 256 ^ (15 - nonce.length)) (h14 : t.gpr .r14 = BitVec.ofNat 64 j) :
    ∃ t', runBlock isa (([.mov .rsi (.mem (at_ .r15 roundsO)), .mov .rax (.reg .r14)] : List Instr) ++ ctrAt ++ zero16 ksO ++
        ([.mov .rdi (.reg .r13)] : List Instr) ++ ptr .rdx .r15 c1O ++ ptr .rcx .r15 ksO ++ ([.mov32 .r8 (imm 1)] : List Instr) ++
        ptr .r9 .r15 scrO) t = some t' ∧
      Frame [⟨W + BitVec.ofNat 64 64, 32⟩] t.mem t'.mem ∧
      bytesAt t'.mem (W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce j ∧
      bytesAt t'.mem (W + BitVec.ofNat 64 80) 16 = Spec.Ccm.zeros 16 ∧
      t'.gpr .rdi = K ∧ t'.gpr .rsi = BitVec.ofNat 64 R ∧ t'.gpr .rdx = W + BitVec.ofNat 64 64 ∧
      t'.gpr .rcx = W + BitVec.ofNat 64 80 ∧ t'.gpr .r8 = BitVec.ofNat 64 1 ∧ t'.gpr .r9 = W + BitVec.ofNat 64 384 ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp, .rbp, .r12], t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have h15 := E.r15
  obtain rR := E.perm.wR (show 232 + 8 ≤ 2560 by decide)
  obtain ⟨t₁, run₁, hm₁, hsi₁, hax₁, hg₁, hrd₁, hwr₁⟩ : ∃ t₁, runBlock isa
      [.mov .rsi (.mem (at_ .r15 roundsO)), .mov .rax (.reg .r14)] t = some t₁ ∧ t₁.mem = t.mem ∧
      t₁.gpr .rsi = BitVec.ofNat 64 R ∧ t₁.gpr .rax = BitVec.ofNat 64 j ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by crun [h15, rR], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, hRo]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, h14]
    · intro r h₁ h₂; simp only [gpr_setReg, h₁, h₂, ite_false]
    all_goals rfl
  obtain E₁ : Env K W SP t₁ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)) hrd₁ hwr₁
  obtain ⟨t₂, run₂, f₂, hc₂, hg₂, hrd₂, hwr₂⟩ := ctrAt_ok E₁ h7 h13 (by rw [hm₁]; exact hc0) hj hax₁
  obtain E₂ : Env K W SP t₂ := E₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hrd₂ hwr₂
  have h15₂ := E₂.r15
  obtain w₁ := E₂.perm.wW (show 80 + 8 ≤ 2560 by decide)
  obtain w₂ := E₂.perm.wW (show 88 + 8 ≤ 2560 by decide)
  obtain ⟨t₃, run₃, hm₃, hdi, hsi, hdx, hcx, hr8, hr9, hg₃, hrd₃, hwr₃⟩ : ∃ t₃, runBlock isa
      (zero16 ksO ++ [.mov .rdi (.reg .r13)] ++ ptr .rdx .r15 c1O ++ ptr .rcx .r15 ksO ++ [.mov32 .r8 (imm 1)] ++
        ptr .r9 .r15 scrO) t₂ = some t₃ ∧
      t₃.mem = (t₂.mem.writeW (W + BitVec.ofNat 64 80) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 88) (0 : BitVec 64) ∧
      t₃.gpr .rdi = K ∧ t₃.gpr .rsi = BitVec.ofNat 64 R ∧ t₃.gpr .rdx = W + BitVec.ofNat 64 64 ∧
      t₃.gpr .rcx = W + BitVec.ofNat 64 80 ∧ t₃.gpr .r8 = BitVec.ofNat 64 1 ∧ t₃.gpr .r9 = W + BitVec.ofNat 64 384 ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp, .rbp, .r12], t₃.gpr r = t.gpr r) ∧ t₃.rd = t.rd ∧ t₃.wr = t.wr := by
    refine ⟨_, by crun [zero16, h15₂, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, E₂.r13]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
        hg₂ .rsi (by decide) (by decide) (by decide), hsi₁]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15₂]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15₂]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15₂]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq] <;>
        rw [hg₂ _ (by decide) (by decide) (by decide), hg₁ _ (by decide) (by decide)]
    · simp only [rd_setReg, rd_arithFlags]; rw [hrd₂, hrd₁]
    · simp only [wr_setReg, wr_arithFlags]; rw [hwr₂, hwr₁]
  obtain e88 : W + BitVec.ofNat 64 88 = W + BitVec.ofNat 64 80 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  obtain c80 : ∀ d, 80 ≤ d → d + 8 ≤ 96 → (⟨W + BitVec.ofNat 64 64, 32⟩ : Region).Contains (W + BitVec.ofNat 64 d) 8 :=
    fun d h₁ h₂ => Offset.contains W (by omega_arith) (by omega_arith) (by decide)
  refine ⟨t₃, ?_, ?_, ?_, ?_, hdi, hsi, hdx, hcx, hr8, hr9, hg₃, hrd₃, hwr₃⟩
  · simp only [List.append_assoc]
    rw [runBlock_append, run₁, Option.bind_some, runBlock_append, run₂, Option.bind_some]
    simpa only [List.append_assoc] using run₃
  · rw [hm₃, ← hm₁]
    exact ((f₂.sub fun r hr => ⟨⟨W + BitVec.ofNat 64 64, 32⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by simp)⟩).writeW
      (List.mem_singleton_self _) (0 : BitVec 64) (c80 80 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) (0 : BitVec 64) (c80 88 (by decide) (by decide))
  · have fz : Frame [⟨W + BitVec.ofNat 64 80, 16⟩] t₂.mem t₃.mem := by
      rw [hm₃]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (0 : BitVec 64)
        (Offset.contains W (d := 80) (n := 8) (e := 80) (k := 16) (by decide) (by decide) (by decide))).writeW
        (List.mem_singleton_self _) (0 : BitVec 64)
        (Offset.contains W (d := 88) (n := 8) (e := 80) (k := 16) (by decide) (by decide) (by decide))
    obtain dz : ∀ r ∈ [(⟨W + BitVec.ofNat 64 80, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)
    rw [bytesAt_frame fz dz (by decide), hc₂]
  · rw [hm₃, e88, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl

/-- The last `r = n mod 16` bytes, from `t` after the whole blocks, with `r`
in `rbp`. -/
theorem tail_ok (v : Ctr32Impl) [CtrFits v] {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {D : Addr} {n : Nat}
    (C : CtrCtx K W SP s R nonce D n) {t t₀ : State} (I : CtrInv K W SP s R nonce D n (n / 16) t)
    (hm₀ : t₀.mem = t.mem) (hg₀ : ∀ r, r ≠ .rbp → t₀.gpr r = t.gpr r)
    (hbp : t₀.gpr .rbp = BitVec.ofNat 64 (n % 16)) (hrd₀ : t₀.rd = t.rd) (hwr₀ : t₀.wr = t.wr) (h0 : n % 16 ≠ 0) :
    WP isa (.seq (.block (([.mov .rsi (.mem (at_ .r15 roundsO)), .mov .rax (.reg .r14)] : List Instr) ++ ctrAt ++ zero16 ksO ++
          ([.mov .rdi (.reg .r13)] : List Instr) ++ ptr .rdx .r15 c1O ++ ptr .rcx .r15 ksO ++
          ([.mov32 .r8 (imm 1)] : List Instr) ++ ptr .r9 .r15 scrO))
      (.seq (callCtr v.callee)
        (.seq (.block (([.mov .rdi (.reg .r12)] : List Instr) ++ ptr .rsi .r15 ksO ++ ([.mov .rcx (.reg .rbp)] : List Instr))) xorLoop))) t₀
      fun t' => Env K W SP t' ∧ t'.rd = s.rd ∧ t'.wr = s.wr ∧ Frame (ctrR W SP D n) s.mem t'.mem ∧
        bytesAt t'.mem D n = xorFrom (Spec.Ccm.ctxCiph s.mem K R) nonce 1 (bytesAt s.mem D n) := by
  have L := C.lay
  have hn64 : n < 2 ^ 64 := C.buf.lt
  obtain E₀ : Env K W SP t₀ := I.env.keep (fun r hr => hg₀ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) hrd₀ hwr₀
  obtain hq16 : n / 16 < 256 ^ (15 - nonce.length) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) C.hn
  obtain ⟨t₁, run₁, f₁, hc₁, hz₁, hdi, hsi, hdx, hcx, hr8, hr9, hg₁, hrd₁, hwr₁⟩ :=
    tailSetup_ok E₀ (by rw [hm₀, C.readW_kept I.frame (by omega_arith), C.ro]) C.h7 C.h13
      (by rw [hm₀, C.bytes_kept I.frame (by omega_arith), C.c0]) (j := 1 + n / 16) (by have := C.hn; omega_arith)
      (by rw [hg₀ _ (by decide), I.r14])
  obtain E₁ : Env K W SP t₁ := E₀.keep (fun r hr => hg₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)) hrd₁ hwr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  -- The keystream block.
  obtain hq := srcW (s := t₁) L E₁.perm (t := 80) (k := 16 * 1) (by decide)
  obtain hqc : (⟨W + BitVec.ofNat 64 80, 16 * 1⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 64, 16⟩ :=
    L.w_w (.inr (by decide)) (by decide) (by decide)
  obtain hqk : (⟨K, 240⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 80, 16 * 1⟩ := L.k_w.sub_right (Lay.wSub (by decide))
  refine WP.seq (WP.mono (ctr_call v (cargs L E₁ C.rounds (c := 64) (by decide) hq hqc hqk
    (E₁.perm.wC (d := 80) (n := 16 * 1) (by decide)) hdi hsi hdx hcx hr8 hr9)) fun t₂ h => ?_)
  obtain E₂ : Env K W SP t₂ := E₁.of_saved h.saved h.rd h.wr
  have h15₂ := E₂.r15
  obtain hbp₂ : t₂.gpr .rbp = BitVec.ofNat 64 (n % 16) := by rw [h.saved _ (by decide), hg₁ _ (by simp), hbp]
  obtain h12₂ : t₂.gpr .r12 = D + BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [h.saved _ (by decide), hg₁ _ (by simp), hg₀ _ (by decide), I.r12]
  obtain ⟨t₃, run₃, hm₃, hdi₃, hsi₃, hcx₃, hg₃, hrd₃, hwr₃⟩ : ∃ t₃, runBlock isa
      ([.mov .rdi (.reg .r12)] ++ ptr .rsi .r15 ksO ++ [.mov .rcx (.reg .rbp)]) t₂ = some t₃ ∧ t₃.mem = t₂.mem ∧
      t₃.gpr .rdi = D + BitVec.ofNat 64 (16 * (n / 16)) ∧ t₃.gpr .rsi = W + BitVec.ofNat 64 80 ∧
      t₃.gpr .rcx = BitVec.ofNat 64 (n % 16) ∧ (∀ r ∈ [Reg.r13, .r15, .rsp], t₃.gpr r = t₂.gpr r) ∧
      t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by crun [h15₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h12₂]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15₂]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbp₂]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  obtain E₃ : Env K W SP t₃ := E₂.keep hg₃ hrd₃ hwr₃
  obtain rd₃ : t₃.rd = s.rd := by rw [hrd₃, h.rd, hrd₁, hrd₀, I.rd]
  obtain wr₃ : t₃.wr = s.wr := by rw [hwr₃, h.wr, hwr₁, hwr₀, I.wr]
  obtain hS := C.buf.slice (a := 16 * (n / 16)) (k := n % 16) (by omega_arith)
  obtain lp : LoopPre t₃ (W + BitVec.ofNat 64 80) (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    ⟨hsi₃, hdi₃, hcx₃, by omega_arith, by omega_arith, covers_left (E₃.perm.wC (d := 80) (n := n % 16) (by omega_arith)),
      by rw [wr₃]; exact covers_off C.dw (by omega_arith) hn64, (hS.w.sub_right (Lay.wSub (by omega_arith))).symm⟩
  refine WP.mono (xorLoop_ok t₃ lp) fun t₄ ⟨hm₄, hg₄, hrd₄, hwr₄⟩ => ?_
  -- What the tail wrote.
  have hsp : t₁.gpr .rsp = SP := E₁.rsp
  obtain cT : Frame [⟨W + BitVec.ofNat 64 64, 32⟩, ⟨W + BitVec.ofNat 64 384, scratchBytes⟩, below SP 8] t.mem t₃.mem := by
    have fc := h.frame
    rw [hsp] at fc
    rw [hm₃, ← hm₀]
    refine (f₁.sub fun r hr => ?_).trans (fc.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by simp)⟩
      · exact ⟨⟨W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub W (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  obtain sep : ∀ {a l : Nat}, a + l ≤ n → ∀ r ∈ [(⟨W + BitVec.ofNat 64 64, 32⟩ : Region),
      ⟨W + BitVec.ofNat 64 384, scratchBytes⟩, below SP 8], (⟨D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
    intro a l hl r hr
    obtain hB := C.buf.slice (a := a) (k := l) hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hB.w.sub_right (Lay.wSub (by decide))
    · exact hB.w.sub_right (Lay.wSub (by have := tailBytes_le; have := scratchBytes_le; omega))
    · exact (hB.stk.sub_left (below8_sub SP)).symm
  obtain ⟨xs, hxs⟩ : ∃ xs, xs = xorBytes t₃.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (W + BitVec.ofNat 64 80) (n % 16) :=
    ⟨_, rfl⟩
  rw [← hxs] at hm₄
  obtain hxl : xs.length = n % 16 := by simp [hxs, xorBytes, length_bytesAt]
  obtain fw : Frame [⟨D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩] t₃.mem t₄.mem := by
    rw [hm₄]; exact writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
  refine ⟨E₃.keep (fun r hr => hg₄ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
      hrd₄ hwr₄, by rw [hrd₄, rd₃], by rw [hwr₄, wr₃], ?_, ?_⟩
  · refine I.frame.trans ((cT.sub fun r hr => ?_).trans (fw.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨W + BitVec.ofNat 64 384, scratchBytes⟩, by simp, Region.sub_prefix (by simp)⟩
      · exact ⟨below SP 16, by simp, below8_sub SP⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨D, n⟩, by simp, Offset.sub_base D (by omega_arith)⟩
  · -- The bytes.
    obtain h₁ : bytesAt t₃.mem D (16 * (n / 16)) = bytesAt t.mem D (16 * (n / 16)) := by
      have := bytesAt_frame cT (sep (a := 0) (l := 16 * (n / 16)) (by omega_arith)) (by omega_arith)
      rwa [BitVec.add_zero] at this
    obtain h₂ : bytesAt t₃.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
        bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
      rw [bytesAt_frame cT (sep (by omega_arith)) (by omega_arith), show n % 16 = n - 16 * (n / 16) by omega_arith, I.rest]
    obtain f₁' : Frame (ctrR W SP D n) s.mem t₁.mem := I.frame.trans (by
      rw [← hm₀]; exact f₁.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩)
    obtain hBC : BlockCipher (Spec.Ccm.ctxCiph s.mem K R) := fun x => Proof.Cmac.aesWith_length _ _ x
    obtain hks : bytesAt t₃.mem (W + BitVec.ofNat 64 80) 16 =
        Spec.Ccm.ctxCiph s.mem K R (Spec.Ccm.ctrBlock nonce (1 + n / 16)) := by
      obtain hx := ctr32_ccm (nonce := nonce) (k := 1) (j := 1 + n / 16) (by have := C.h13; omega_arith) (fun i hi => by
        rw [show i = 0 by omega_arith, Nat.add_zero]
        show Spec.Gcm.ofBytes _ = _
        rw [hc₁]) h.out
      rw [Nat.mul_one] at hx
      rw [hm₃, hx, hz₁, C.ciph_kept f₁', xorFrom_zeros hBC]
    obtain ht := xorFrom_tail (ciph := Spec.Ccm.ctxCiph s.mem K R) nonce (1 + n / 16)
      (d := bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16)) (by rw [length_bytesAt]; omega_arith)
    rw [length_bytesAt, hBC] at ht
    obtain ht' := ht.resolve_right (by omega_arith)
    rw [hm₄, bytesAt_writeBytes_at t₃.mem D xs (by rw [hxl]; omega_arith) hn64,
      List.drop_eq_nil_of_le (by rw [length_bytesAt, hxl]; omega_arith), List.append_nil,
      ← bytesAt_prefix t₃.mem D (show 16 * (n / 16) ≤ n by omega_arith), h₁, I.done, hxs, xorBytes, h₂,
      bytesAt_prefix t₃.mem (W + BitVec.ofNat 64 80) (show n % 16 ≤ 16 by omega_arith), hks, ht']
    conv => rhs; rw [show n = 16 * (n / 16) + n % 16 from (Nat.div_add_mod n 16).symm]
    rw [Proof.Cmac.Stream.bytesAt_append, xorFrom_append _ _ _ (length_bytesAt _ _ _), Nat.add_comm 1 (n / 16)]

omit fp in
/-- `rbp = n mod 16`, and ZF set when there are no last bytes. -/
theorem ctrB3_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {n : Nat}
    (hl : t.mem.readW (W + BitVec.ofNat 64 200) 64 = BitVec.ofNat 64 n) (hn64 : n < 2 ^ 64) :
    WP isa (.block [.mov .rbp (.mem (at_ .r15 lenO)), .alu .and .rbp (imm 15), .alu .test .rbp (.reg .rbp)]) t
      fun t₀ => t₀.mem = t.mem ∧ t₀.gpr .rbp = BitVec.ofNat 64 (n % 16) ∧ t₀.zf = some (decide (n % 16 = 0)) ∧
        (∀ r, r ≠ .rbp → t₀.gpr r = t.gpr r) ∧ t₀.rd = t.rd ∧ t₀.wr = t.wr := by
  have h15 := E.r15
  obtain rl := E.perm.wR (show 200 + 8 ≤ 2560 by decide)
  refine WP.of_runBlock ⟨_, by crun [h15, rl], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hl, and15',
      toNat_ofNat_of_lt hn64]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hl, and15',
      toNat_ofNat_of_lt hn64, and_self_beq (show n % 16 < 2 ^ 64 by omega_arith)]
  · intro r h₁; simp only [gpr_setReg, gpr_arithFlags, h₁, ite_false]
  all_goals rfl

/-- Counter mode: the data XORed with CCM's keystream from `Ctr₁`. -/
theorem ctr_ok (v : Ctr32Impl) [CtrFits v] {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {N A D : Addr}
    {nl al n tl : Nat} (C : CtrCtx K W SP s R nonce D n) (E : Env K W SP s) (S : Slots W R N A D nl al n tl s.mem) :
    WP isa (ctr v.callee) s fun s' => Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame (ctrR W SP D n) s.mem s'.mem ∧
      bytesAt s'.mem D n = xorFrom (Spec.Ccm.ctxCiph s.mem K R) nonce 1 (bytesAt s.mem D n) := by
  have hn64 : n < 2 ^ 64 := C.buf.lt
  refine seq_assoc (WP.seq (WP.mono (ctrHead_ok v C E S) fun t I => ?_))
  obtain hl : t.mem.readW (W + BitVec.ofNat 64 200) 64 = BitVec.ofNat 64 n := by
    rw [C.readW_kept I.frame (by omega_arith)]; exact S.len
  refine WP.seq (WP.mono (ctrB3_ok I.env hl hn64) fun t₀ ⟨hm₀, hbp, hzf, hg₀, hrd₀, hwr₀⟩ => ?_)
  refine WP.ite _ (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 := of_decide_eq_true ht
    refine WP.of_runBlock ⟨t₀, rfl, I.env.keep (fun r hr => hg₀ r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
      hrd₀ hwr₀, by rw [hrd₀, I.rd], by rw [hwr₀, I.wr], by rw [hm₀]; exact I.frame, ?_⟩
    have hd := I.done
    rw [show 16 * (n / 16) = n by omega_arith] at hd
    rw [hm₀, hd]
  · exact tail_ok v C I hm₀ hg₀ hbp hrd₀ hwr₀ (of_decide_eq_false hf)

end VG.Proof.AesCcm.X86_64
