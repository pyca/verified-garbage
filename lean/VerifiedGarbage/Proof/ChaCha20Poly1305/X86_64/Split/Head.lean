module

import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Copy
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealSplit
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.CT
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Copy
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Lit
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512Tail.Tail
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# ChaCha20-Poly1305 with the data's first bytes from `src`, x86-64: the copy

`vg_chacha20_poly1305_seal_split(key = rdi, nonce = rsi, aad = rdx,
aad_len = rcx, src = r8, src_len = r9, dst = [rsp + 8], len = [rsp + 16],
tag = [rsp + 24], work = [rsp + 32])`, from a state satisfying `FPre` (what
its contract with `work` gives), first copies the first `cnt` bytes of `src`
to `dst` (`head_ok`): all of them (`whole`), or as many as the prologue's
keystream covers (`cntOf`). It keeps `key`, `nonce`, `aad_len` and `src` in
`work[0, 32)` meanwhile, and leaves `work`, `tag` and `dst` in `r10`, `r11`
and `rax` for the frame.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Split

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.SealSplit
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (Width copyBytes)
open VG.Spec.Poly1305 (bytesAt)
open VG.WriteBytes

/-! ## The entry state -/

section
variable (s : State)
/-- The arguments on entry. -/
abbrev eSrc : Addr := s.gpr .r8
abbrev eSN : Nat := (s.gpr .r9).toNat
abbrev eDst : Addr := stackArg s 0
abbrev eLn : Nat := (stackArg s 1).toNat
abbrev eTg : Addr := stackArg s 2
abbrev eW : Addr := stackArg s 3
/-- Their regions, the stack arguments, the return address and the stack
below it. -/
abbrev ekR : Region := ⟨s.gpr .rdi, 32⟩
abbrev enR : Region := ⟨s.gpr .rsi, 12⟩
abbrev eaR : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
abbrev esR : Region := ⟨eSrc s, eSN s⟩
abbrev edR : Region := ⟨eDst s, eLn s⟩
abbrev etR : Region := ⟨eTg s, 16⟩
abbrev ewR : Region := ⟨eW s, 1696⟩
abbrev eargR : Region := ⟨stackArgAddr s 0, 32⟩
abbrev eretR : Region := ⟨s.gpr .rsp, 8⟩
abbrev estkR : Region := below (s.gpr .rsp) 64

/-- The number of bytes of `src` the copy copies. -/
def cntOf (whole : Bool) : Nat := if whole then eSN s else min (eSN s) (mOf 960 1024 (eLn s))
end

/-- What the contract of `vg_chacha20_poly1305_seal_split` with `work`
gives. -/
structure FPre (s : State) : Prop where
  rd : s.rd = [ekR s, enR s, eaR s, esR s, eargR s]
  wr : s.wr = [edR s, etR s, ewR s]
  k_d : (ekR s).Disjoint (edR s)
  k_t : (ekR s).Disjoint (etR s)
  k_w : (ekR s).Disjoint (ewR s)
  n_d : (enR s).Disjoint (edR s)
  n_t : (enR s).Disjoint (etR s)
  n_w : (enR s).Disjoint (ewR s)
  a_d : (eaR s).Disjoint (edR s)
  a_t : (eaR s).Disjoint (etR s)
  a_w : (eaR s).Disjoint (ewR s)
  s_d : (esR s).Disjoint (edR s)
  s_t : (esR s).Disjoint (etR s)
  s_w : (esR s).Disjoint (ewR s)
  d_t : (edR s).Disjoint (etR s)
  d_w : (edR s).Disjoint (ewR s)
  t_w : (etR s).Disjoint (ewR s)
  d_g : (edR s).Disjoint (eargR s)
  t_g : (etR s).Disjoint (eargR s)
  w_g : (ewR s).Disjoint (eargR s)
  r_a : (eretR s).Disjoint (eaR s)
  r_s : (eretR s).Disjoint (esR s)
  r_d : (eretR s).Disjoint (edR s)
  r_t : (eretR s).Disjoint (etR s)
  r_w : (eretR s).Disjoint (ewR s)
  b_k : (estkR s).Disjoint (ekR s)
  b_n : (estkR s).Disjoint (enR s)
  b_a : (estkR s).Disjoint (eaR s)
  b_s : (estkR s).Disjoint (esR s)
  b_d : (estkR s).Disjoint (edR s)
  b_t : (estkR s).Disjoint (etR s)
  b_w : (estkR s).Disjoint (ewR s)
  o_k : (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64
  o_n : (s.gpr .rsi).toNat + 12 ≤ 2 ^ 64
  o_a : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  o_s : (eSrc s).toNat + eSN s ≤ 2 ^ 64
  o_d : (eDst s).toNat + eLn s ≤ 2 ^ 64
  o_t : (eTg s).toNat + 16 ≤ 2 ^ 64
  o_w : (eW s).toNat + 1696 ≤ 2 ^ 64
  sp_lo : 64 ≤ (s.gpr .rsp).toNat
  sp_hi : (s.gpr .rsp).toNat + 40 ≤ 2 ^ 64
  le : eSN s ≤ eLn s

/-! ## Steps -/

/-- `loadW`: `work` into `rax`. -/
theorem loadW_ok {a : State} {W : Addr} (hW : a.mem.readW (off (a.gpr .rsp) 32) 64 = W)
    (r₃₂ : InRegions (a.rd ++ a.wr) (off (a.gpr .rsp) 32) 8) :
    WP isa (.block loadW) a fun e => e.gpr .rax = W ∧ (∀ r, r ≠ .rax → e.gpr r = a.gpr r) ∧
      e.mem = a.mem ∧ e.rd = a.rd ∧ e.wr = a.wr := by
  apply WP.of_runBlock
  simp only [loadW, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_at,
    gpr_setReg, mem_setReg, rd_setReg, wr_setReg, ↓reduceIte, r₃₂, hW, Option.map_some, Option.some.injEq,
    exists_eq_left']
  exact ⟨by simp, fun r h => by simp [h], by simp, by simp, by simp⟩

/-- `stash`: `key`, `nonce`, `aad_len` and `src` into `work[0, 32)`. -/
theorem stash_ok {a : State} {W : Addr} (hrax : a.gpr .rax = W)
    (w₀ : InRegions a.wr (off W 0) 8) (w₈ : InRegions a.wr (off W 8) 8)
    (w₁₆ : InRegions a.wr (off W 16) 8) (w₂₄ : InRegions a.wr (off W 24) 8) :
    WP isa (.block stash) a fun e => e.gpr = a.gpr ∧
      e.mem = (((a.mem.writeW (off W 0) (a.gpr .rdi)).writeW (off W 8) (a.gpr .rsi)).writeW
        (off W 16) (a.gpr .rcx)).writeW (off W 24) (a.gpr .r8) ∧
      e.rd = a.rd ∧ e.wr = a.wr := by
  subst hrax
  apply WP.of_runBlock
  simp only [stash, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_at,
    ↓reduceIte, w₀, w₈, w₁₆, w₂₄, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial⟩

/-- `cmp x, src; cmovb rcx, r`. -/
theorem cmpB_ok {t : State} {x r : Reg} {src : VG.X86_64.Src} {b : BitVec 64} (hs : readSrc t src = some b) :
    WP isa (.block [.alu .cmp x src, .cmov .b .rcx (.reg r)]) t fun t' =>
      t'.gpr .rcx = (if (t.gpr x).toNat < b.toNat then t.gpr r else t.gpr .rcx) ∧
      (∀ q, q ≠ .rcx → t'.gpr q = t.gpr q) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, exec, execAlu, hs, Option.bind_some]
  by_cases h : (t.gpr x).toNat < b.toNat
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execCmov, eval, readSrc, h,
      gpr_arithFlags, cf_arithFlags, mem_arithFlags, rd_arithFlags, wr_arithFlags, gpr_setReg, mem_setReg,
      rd_setReg, wr_setReg, Option.bind_some, Option.map_some, decide_true, ↓reduceIte,
      Option.some.injEq, exists_eq_left']
    exact ⟨by simp, fun q hq => by simp [hq], trivial, trivial, trivial⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execCmov, eval, readSrc, h,
      gpr_arithFlags, cf_arithFlags, mem_arithFlags, rd_arithFlags, wr_arithFlags, gpr_setReg, mem_setReg,
      rd_setReg, wr_setReg, Option.bind_some, Option.map_some, decide_false, ↓reduceIte,
      Bool.false_eq_true, Option.some.injEq, exists_eq_left']
    exact ⟨by simp, fun q _ => by simp, by simp, by simp, by simp⟩

/-- `cmp x, src; cmovae rcx, r`. -/
theorem cmpAE_ok {t : State} {x r : Reg} {src : VG.X86_64.Src} {b : BitVec 64} (hs : readSrc t src = some b) :
    WP isa (.block [.alu .cmp x src, .cmov .ae .rcx (.reg r)]) t fun t' =>
      t'.gpr .rcx = (if (t.gpr x).toNat < b.toNat then t.gpr .rcx else t.gpr r) ∧
      (∀ q, q ≠ .rcx → t'.gpr q = t.gpr q) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, exec, execAlu, hs, Option.bind_some]
  by_cases h : (t.gpr x).toNat < b.toNat
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execCmov, eval, readSrc, h,
      gpr_arithFlags, cf_arithFlags, mem_arithFlags, rd_arithFlags, wr_arithFlags, gpr_setReg, mem_setReg,
      rd_setReg, wr_setReg, Option.bind_some, Option.map_some, decide_true, ↓reduceIte,
      Bool.not_true, Bool.false_eq_true, Option.some.injEq, exists_eq_left']
    exact ⟨by simp, fun q _ => by simp, by simp, by simp, by simp⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execCmov, eval, readSrc, h,
      gpr_arithFlags, cf_arithFlags, mem_arithFlags, rd_arithFlags, wr_arithFlags, gpr_setReg, mem_setReg,
      rd_setReg, wr_setReg, Option.bind_some, Option.map_some, decide_false, ↓reduceIte,
      Bool.not_false, Option.some.injEq, exists_eq_left']
    exact ⟨by simp, fun q hq => by simp [hq], by simp, by simp, by simp⟩

theorem and1023' (len : Nat) (hl : len < 2 ^ 64) :
    BitVec.ofNat 64 len &&& BitVec.signExtend 64 (1023 : BitVec 32) = BitVec.ofNat 64 (len % 1024) :=
  and1023 len hl

/-- The first instructions of `prefixLen false`: `len` in `r10` and `rcx`
its bytes past the last multiple of 1024, rounded up to a block. -/
theorem prefixA_ok {a : State} {Ln : Nat} (hLn : Ln < 2 ^ 64)
    (hL : a.mem.readW (off (a.gpr .rsp) 16) 64 = BitVec.ofNat 64 Ln)
    (r₁₆ : InRegions (a.rd ++ a.wr) (off (a.gpr .rsp) 16) 8) :
    WP isa (.block [.mov .r10 (.mem (at_ .rsp 16)), .mov .rcx (.reg .r10), .alu .and .rcx (.imm 1023),
      .alu .add .rcx (.imm 63), .alu .and .rcx (.imm (BitVec.ofInt 32 (-64))), .mov32 .rdi (.imm 0)]) a
      fun e => e.gpr .r10 = BitVec.ofNat 64 Ln ∧ e.gpr .rcx = BitVec.ofNat 64 ((Ln % 1024 + 63) / 64 * 64) ∧
        e.gpr .rdi = 0 ∧ (∀ q, q ≠ .rcx → q ≠ .rdi → q ≠ .r10 → e.gpr q = a.gpr q) ∧ e.mem = a.mem ∧
        e.rd = a.rd ∧ e.wr = a.wr := by
  have hr : Ln % 1024 + 63 < 1087 := by omega
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu, State.load64, ea_at,
    State.setReg32, r₁₆, hL, ↓reduceIte, gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg,
    rd_arithFlags, wr_setReg, wr_arithFlags, reduceCtorEq, and1023' Ln hLn, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left', show BitVec.signExtend 64 (63 : BitVec 32) = 63 by decide]
  rw [show BitVec.ofNat 64 (Ln % 1024) + 63 = BitVec.ofNat 64 (Ln % 1024 + 63) by
    rw [BitVec.ofNat_add]; rfl, round64 _ hr]
  exact ⟨by simp, by simp, by simp, fun q h₁ h₂ h₃ => by simp [h₁, h₂, h₃], by simp, by simp, by simp⟩

theorem sx961 (t : State) : readSrc t (.imm 961) = some (BitVec.ofNat 64 961) :=
  congrArg some (by decide : BitVec.signExtend 64 (961 : BitVec 32) = BitVec.ofNat 64 961)

/-- `prefixLen false`: `rcx` = the smaller of `src_len` and `m`. -/
theorem prefixF_ok {a : State} {Ln : Nat} (hLn : Ln < 2 ^ 64)
    (hL : a.mem.readW (off (a.gpr .rsp) 16) 64 = BitVec.ofNat 64 Ln)
    (r₁₆ : InRegions (a.rd ++ a.wr) (off (a.gpr .rsp) 16) 8) :
    WP isa (.block (prefixLen false)) a fun e =>
      e.gpr .rcx = BitVec.ofNat 64 (min (a.gpr .r9).toNat (mOf 960 1024 Ln)) ∧
      (∀ q, q ≠ .rcx → q ≠ .rdi → q ≠ .r10 → e.gpr q = a.gpr q) ∧ e.mem = a.mem ∧ e.rd = a.rd ∧
      e.wr = a.wr := by
  have hy : (Ln % 1024 + 63) / 64 * 64 < 2 ^ 64 := by omega
  have hS := (a.gpr .r9).isLt
  rw [show prefixLen false = [.mov .r10 (.mem (at_ .rsp 16)), .mov .rcx (.reg .r10), .alu .and .rcx (.imm 1023),
      .alu .add .rcx (.imm 63), .alu .and .rcx (.imm (BitVec.ofInt 32 (-64))), .mov32 .rdi (.imm 0)] ++
      ([.alu .cmp .rcx (.imm 961), .cmov .ae .rcx (.reg .rdi)] : List Instr) ++
      ([.alu .cmp .r10 (.imm 961), .cmov .b .rcx (.reg .r10)] : List Instr) ++
      ([.alu .cmp .r9 (.reg .rcx), .cmov .b .rcx (.reg .r9)] : List Instr) from rfl]
  refine WP.block_append (WP.block_append (WP.block_append (WP.mono (prefixA_ok hLn hL r₁₆)
    fun e₁ ⟨r10₁, rcx₁, rdi₁, g₁, m₁, rd₁, wr₁⟩ => ?_)))
  refine WP.mono (cmpAE_ok (x := .rcx) (r := .rdi) (src := .imm 961) (b := BitVec.ofNat 64 961) (sx961 _))
    fun e₂ ⟨rcx₂, g₂, m₂, rd₂, wr₂⟩ => ?_
  refine WP.mono (cmpB_ok (x := .r10) (r := .r10) (src := .imm 961) (b := BitVec.ofNat 64 961) (sx961 _))
    fun e₃ ⟨rcx₃, g₃, m₃, rd₃, wr₃⟩ => ?_
  refine WP.mono (cmpB_ok (x := .r9) (r := .r9) (src := .reg .rcx) (b := e₃.gpr .rcx) rfl)
    fun e₄ ⟨rcx₄, g₄, m₄, rd₄, wr₄⟩ => ?_
  have r9₃ : e₃.gpr .r9 = a.gpr .r9 := by
    rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide) (by decide) (by decide)]
  have c₃ : e₃.gpr .rcx = BitVec.ofNat 64 (mOf 960 1024 Ln) := by
    rw [rcx₃, g₂ _ (by decide), r10₁, rcx₂, rcx₁, rdi₁, toNat_ofNat_lt hLn, toNat_ofNat_lt hy,
      toNat_ofNat_lt (by decide)]
    simp only [mOf, splitOf, show (1024 : Nat) ≠ 0 by decide, show (1024 : Nat) ≠ 512 by decide, ite_false]
    by_cases h₁ : Ln < 961
    · have h₁' : Ln ≤ 960 := by omega
      simp only [h₁, h₁', ↓reduceIte]
    · have h₁' : ¬ Ln ≤ 960 := by omega
      simp only [h₁, h₁', ↓reduceIte]
      by_cases h₂ : (Ln % 1024 + 63) / 64 * 64 < 961
      · have h₂' : (Ln % 1024 + 63) / 64 * 64 ≤ 960 := by omega
        simp only [h₂, h₂', ↓reduceIte]
      · have h₂' : ¬ (Ln % 1024 + 63) / 64 * 64 ≤ 960 := by omega
        simp only [h₂, h₂', ↓reduceIte]; rfl
  refine ⟨?_, fun q h₁ h₂ h₃ => ?_, by rw [m₄, m₃, m₂, m₁], by rw [rd₄, rd₃, rd₂, rd₁],
    by rw [wr₄, wr₃, wr₂, wr₁]⟩
  · have hm := mOf_le 960 1024 Ln
    rw [rcx₄, r9₃, c₃, toNat_ofNat_lt (by omega)]
    by_cases h : (a.gpr .r9).toNat < mOf 960 1024 Ln
    · simp only [h, ↓reduceIte, Nat.min_eq_left (Nat.le_of_lt h), BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · simp only [h, ↓reduceIte, Nat.min_eq_right (Nat.le_of_not_lt h)]
  · rw [g₄ _ h₁, g₃ _ h₁, g₂ _ h₁, g₁ _ h₁ h₂ h₃]

/-! ## The stash -/

/-- The memory after `stash`. -/
def stashM (s : State) : Mem :=
  (((s.mem.writeW (off (eW s) 0) (s.gpr .rdi)).writeW (off (eW s) 8) (s.gpr .rsi)).writeW
    (off (eW s) 16) (s.gpr .rcx)).writeW (off (eW s) 24) (s.gpr .r8)

theorem w_in (s : State) {k : Nat} (hk : k + 8 ≤ 1696) : (ewR s).Contains (off (eW s) k) 8 := by
  rw [off_eq]; exact Offset.contains_base _ (by omega) (by omega)

theorem stashM_frame (s : State) : Frame [ewR s] s.mem (stashM s) :=
  ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (w_in s (by decide))).writeW
    (List.mem_singleton_self _) _ (w_in s (by decide))).writeW (List.mem_singleton_self _) _
    (w_in s (by decide))).writeW (List.mem_singleton_self _) _ (w_in s (by decide))

theorem wsep {W : Addr} {d e : Nat} (h : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 1696) (he : e + 8 ≤ 1696) :
    Mem.Sep (off W d) (64 / 8) (off W e) (64 / 8) := by
  rw [off_eq, off_eq]; exact Offset.sep W h (by omega) (by omega)

theorem stashM_rdi (s : State) : (stashM s).readW (off (eW s) 0) 64 = s.gpr .rdi := by
  simp only [stashM]
  rw [Mem.readW_writeW_sep (wsep (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (wsep (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (wsep (by omega) (by omega) (by omega)) (by decide), Mem.readW_writeW_self64]

theorem stashM_rsi (s : State) : (stashM s).readW (off (eW s) 8) 64 = s.gpr .rsi := by
  simp only [stashM]
  rw [Mem.readW_writeW_sep (wsep (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (wsep (by omega) (by omega) (by omega)) (by decide), Mem.readW_writeW_self64]

theorem stashM_rcx (s : State) : (stashM s).readW (off (eW s) 16) 64 = s.gpr .rcx := by
  simp only [stashM]
  rw [Mem.readW_writeW_sep (wsep (by omega) (by omega) (by omega)) (by decide), Mem.readW_writeW_self64]

theorem stashM_r8 (s : State) : (stashM s).readW (off (eW s) 24) 64 = s.gpr .r8 := by
  simp only [stashM]; rw [Mem.readW_writeW_self64]

/-! ## The copy -/

/-- The memory after the copy of `n` bytes. -/
def headM (s : State) (n : Nat) : Mem :=
  writeBytes (stashM s) (eDst s) (Spec.Aes.bytesAt (stashM s) (eSrc s) n)

/-- A byte of a region that does not wrap around, by its address. -/
theorem contains_nat {b : Addr} {l x : Nat} (hx : b.toNat ≤ x ∧ x < b.toNat + l) (hl : b.toNat + l ≤ 2 ^ 64) :
    (⟨b, l⟩ : Region).Contains (BitVec.ofNat 64 x) 1 := by
  rw [show BitVec.ofNat 64 x = b + BitVec.ofNat 64 (x - b.toNat) by
    rw [BitVec.add_comm, ← Offset.ofNat_sub_ofNat hx.1, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.sub_add_cancel]]
  exact Offset.contains_base _ (by omega) (by omega)

/-- No byte is in both of two disjoint regions that do not wrap around. -/
theorem disj_nat {b₁ b₂ : Addr} {l₁ l₂ : Nat} (h : (⟨b₁, l₁⟩ : Region).Disjoint ⟨b₂, l₂⟩)
    (h₁ : b₁.toNat + l₁ ≤ 2 ^ 64) (h₂ : b₂.toNat + l₂ ≤ 2 ^ 64) (x : Nat) :
    ¬ ((b₁.toNat ≤ x ∧ x < b₁.toNat + l₁) ∧ (b₂.toNat ≤ x ∧ x < b₂.toNat + l₂)) :=
  fun ⟨hx₁, hx₂⟩ => h _ (contains_nat hx₁ h₁) (contains_nat hx₂ h₂)

namespace FPre

variable {s : State} (hs : FPre s)
include hs

/-- `src` is shorter than half the address space: it, the data (as long at
least) and the return address do not overlap. -/
theorem sn_lt : eSN s < 2 ^ 63 := by
  have o_s := hs.o_s
  have o_d := hs.o_d
  have hr := hs.sp_hi
  have hle := hs.le
  have a₁ := disj_nat hs.s_d o_s o_d (eSrc s).toNat
  have a₂ := disj_nat hs.s_d o_s o_d (eDst s).toNat
  have a₃ := disj_nat hs.r_s (by omega) o_s (s.gpr .rsp).toNat
  have a₄ := disj_nat hs.r_d (by omega) o_d (s.gpr .rsp).toNat
  omega

omit hs in
theorem cnt_le (whole : Bool) : cntOf s whole ≤ eSN s := by
  unfold cntOf; split <;> omega

theorem cnt_lt (whole : Bool) : cntOf s whole < 2 ^ 63 := Nat.lt_of_le_of_lt (cnt_le whole) hs.sn_lt

omit hs in
theorem arg_contains {j : Nat} (hj : j < 4) : (eargR s).Contains (off (s.gpr .rsp) (8 * (j + 1))) 8 := by
  rw [off_eq]; exact Offset.contains _ (e := 8 * (0 + 1)) (by omega) (by omega) (by omega)

/-- A stack argument is readable. -/
theorem arg_in {j : Nat} (hj : j < 4) : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) (8 * (j + 1))) 8 :=
  ⟨eargR s, by rw [hs.rd]; simp, arg_contains hj⟩

/-- A stack argument, in memory that changed only in the working space and
the data. -/
theorem arg_eq {m : Mem} (hf : Frame [ewR s, edR s] s.mem m) {j : Nat} (hj : j < 4) :
    m.readW (off (s.gpr .rsp) (8 * (j + 1))) 64 = stackArg s j := by
  rw [hf.readW (r := eargR s) (arg_contains hj) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hs.w_g.symm
        · exact hs.d_g.symm) (by decide)]
  rfl

theorem headM_frame (n : Nat) (hn : n ≤ eSN s) : Frame [ewR s, edR s] s.mem (headM s n) := by
  have hle := hs.le
  intro x hx
  rw [headM, writeBytes_frame _ _ _ (R := edR s) (by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Proof.AesGcm.X86_64.length_bytesAt]; omega)
      x (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hx _ (by simp)),
    stashM_frame s x (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hx _ (by simp))]

/-- The working space after the copy, as `stash` left it. -/
theorem headM_w (n : Nat) (hn : n ≤ eSN s) {k : Nat} (hk : k + 8 ≤ 1696) :
    (headM s n).readW (off (eW s) k) 64 = (stashM s).readW (off (eW s) k) 64 := by
  have hle := hs.le
  refine Frame.readW (writeBytes_frame _ _ _ (R := edR s) (by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Proof.AesGcm.X86_64.length_bytesAt]; omega))
    (w_in s hk) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.d_w.symm) (by decide)

end FPre

/-- `copyArgs`. -/
theorem copyArgs_ok {a : State} {D : Addr} (hD : a.mem.readW (off (a.gpr .rsp) 8) 64 = D)
    (r₈ : InRegions (a.rd ++ a.wr) (off (a.gpr .rsp) 8) 8) :
    WP isa (.block copyArgs) a fun e => e.gpr .rsi = a.gpr .r8 ∧ e.gpr .rdi = D ∧
      (∀ r, r ≠ .rsi → r ≠ .rdi → e.gpr r = a.gpr r) ∧ e.mem = a.mem ∧ e.rd = a.rd ∧ e.wr = a.wr := by
  apply WP.of_runBlock
  simp only [copyArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_at,
    gpr_setReg, mem_setReg, rd_setReg, wr_setReg, reduceCtorEq, ↓reduceIte, r₈, hD,
    Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp, by simp, fun r h₁ h₂ => by simp [h₁, h₂], by simp, by simp, by simp⟩

/-- `unstash`. -/
theorem unstash_ok {a : State} {W T D : Addr} (hrax : a.gpr .rax = W)
    (hW : a.mem.readW (off (a.gpr .rsp) 32) 64 = W)
    (hT : a.mem.readW (off (a.gpr .rsp) 24) 64 = T) (hD : a.mem.readW (off (a.gpr .rsp) 8) 64 = D)
    (r₃₂ : InRegions (a.rd ++ a.wr) (off (a.gpr .rsp) 32) 8)
    (r₂₄ : InRegions (a.rd ++ a.wr) (off (a.gpr .rsp) 24) 8)
    (r₈ : InRegions (a.rd ++ a.wr) (off (a.gpr .rsp) 8) 8)
    (w₀ : InRegions (a.rd ++ a.wr) (off W 0) 8) (w₈ : InRegions (a.rd ++ a.wr) (off W 8) 8)
    (w₁₆ : InRegions (a.rd ++ a.wr) (off W 16) 8) (w₂₄ : InRegions (a.rd ++ a.wr) (off W 24) 8) :
    WP isa (.block unstash) a fun e => e.gpr .rdi = a.mem.readW (off W 0) 64 ∧
      e.gpr .rsi = a.mem.readW (off W 8) 64 ∧ e.gpr .rcx = a.mem.readW (off W 16) 64 ∧
      e.gpr .r8 = a.mem.readW (off W 24) 64 ∧ e.gpr .r10 = W ∧ e.gpr .r11 = T ∧ e.gpr .rax = D ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdi → r ≠ .rsi → r ≠ .r8 → r ≠ .r10 → r ≠ .r11 → e.gpr r = a.gpr r) ∧
      e.mem = a.mem ∧ e.rd = a.rd ∧ e.wr = a.wr := by
  subst hrax
  apply WP.of_runBlock
  simp only [unstash, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_at,
    gpr_setReg, mem_setReg, rd_setReg, wr_setReg, reduceCtorEq, ↓reduceIte, r₃₂, r₂₄, r₈, hW, hT, hD, w₀, w₈,
    w₁₆, w₂₄, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp,
    fun r h₁ h₂ h₃ h₄ h₅ h₆ h₇ => by simp [h₁, h₂, h₃, h₄, h₅, h₆, h₇], by simp, by simp, by simp⟩

/-- `prefixLen true`. -/
theorem prefixT_ok (a : State) :
    WP isa (.block (prefixLen true)) a fun e => e.gpr .rcx = a.gpr .r9 ∧
      (∀ q, q ≠ .rcx → q ≠ .rdi → q ≠ .r10 → e.gpr q = a.gpr q) ∧ e.mem = a.mem ∧ e.rd = a.rd ∧
      e.wr = a.wr := by
  apply WP.of_runBlock
  simp only [prefixLen, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, gpr_setReg, mem_setReg,
    rd_setReg, wr_setReg, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp, fun q h₁ _ _ => by simp [h₁], by simp, by simp, by simp⟩

/-- After the first `loadW`. -/
def Loaded (s a : State) : Prop :=
  a.gpr .rax = eW s ∧ (∀ r, r ≠ .rax → a.gpr r = s.gpr r) ∧ a.mem = s.mem ∧ a.rd = s.rd ∧ a.wr = s.wr

theorem loaded_ok {s : State} (hs : FPre s) : WP isa (.block loadW) s (Loaded s) :=
  loadW_ok (hs.arg_eq (Frame.refl _ _) (j := 3) (by decide)) (hs.arg_in (j := 3) (by decide))

/-- After `stash`, `prefixLen` and `copyArgs`: ready for the copy. -/
def Ready (whole : Bool) (s b : State) : Prop :=
  b.mem = stashM s ∧ b.gpr .rsi = eSrc s ∧ b.gpr .rdi = eDst s ∧
    b.gpr .rcx = BitVec.ofNat 64 (cntOf s whole) ∧
    (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdi → r ≠ .rsi → r ≠ .r10 → b.gpr r = s.gpr r) ∧ b.rd = s.rd ∧ b.wr = s.wr

theorem ready_ok (whole : Bool) {s a : State} (hs : FPre s) (ha : Loaded s a) :
    WP isa (.block (stash ++ prefixLen whole ++ copyArgs)) a (Ready whole s) := by
  obtain ⟨rax₀, g₀, m₀, rd₀, wr₀⟩ := ha
  have fS : Frame [ewR s, edR s] s.mem (stashM s) := (stashM_frame s).mono (by simp)
  have win : ∀ {k : Nat}, k + 8 ≤ 1696 → InRegions a.wr (off (eW s) k) 8 :=
    fun hk => ⟨ewR s, by rw [wr₀, hs.wr]; simp, w_in s hk⟩
  refine WP.block_append (WP.block_append (WP.mono (stash_ok rax₀ (win (by decide)) (win (by decide))
    (win (by decide)) (win (by decide))) fun e₁ ⟨g₁', m₁, rd₁, wr₁⟩ => ?_))
  have g₁ : ∀ r, r ≠ .rax → e₁.gpr r = s.gpr r := fun r h => by rw [g₁', g₀ r h]
  rw [m₀, g₀ _ (by decide), g₀ _ (by decide), g₀ _ (by decide), g₀ _ (by decide)] at m₁
  rw [rd₀] at rd₁
  rw [wr₀] at wr₁
  have sp₁ : e₁.gpr .rsp = s.gpr .rsp := g₁ _ (by decide)
  have in₁ : ∀ {j}, j < 4 → InRegions (e₁.rd ++ e₁.wr) (off (e₁.gpr .rsp) (8 * (j + 1))) 8 := fun hj => by
    rw [rd₁, wr₁, sp₁]; exact hs.arg_in hj
  have at₁ : ∀ {j}, j < 4 → e₁.mem.readW (off (e₁.gpr .rsp) (8 * (j + 1))) 64 = stackArg s j := fun hj => by
    rw [m₁, sp₁]; exact hs.arg_eq fS hj
  have post : ∀ e₂ : State, e₂.gpr .rcx = BitVec.ofNat 64 (cntOf s whole) →
      (∀ q, q ≠ .rcx → q ≠ .rdi → q ≠ .r10 → e₂.gpr q = e₁.gpr q) → e₂.mem = e₁.mem → e₂.rd = e₁.rd →
      e₂.wr = e₁.wr → WP isa (.block copyArgs) e₂ (Ready whole s) := by
    intro e₂ rcx₂ g₂ m₂ rd₂ wr₂
    have sp₂ : e₂.gpr .rsp = s.gpr .rsp := by rw [g₂ _ (by decide) (by decide) (by decide), sp₁]
    refine WP.mono (copyArgs_ok (D := eDst s) (by rw [m₂, m₁, sp₂]; exact hs.arg_eq fS (j := 0) (by decide))
      (by rw [rd₂, wr₂, rd₁, wr₁, sp₂]; exact hs.arg_in (j := 0) (by decide)))
      fun b ⟨rsi, rdi, g, m, rd, wr⟩ => ⟨by rw [m, m₂, m₁]; rfl, by
        rw [rsi, g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide)], rdi,
        by rw [g _ (by decide) (by decide), rcx₂], fun r a c d i t => by
        rw [g r i d, g₂ r c d t, g₁ r a], by rw [rd, rd₂, rd₁], by rw [wr, wr₂, wr₁]⟩
  cases whole with
  | true =>
    exact WP.mono (prefixT_ok e₁) fun e₂ ⟨rcx₂, g₂, m₂, rd₂, wr₂⟩ =>
      post e₂ (by rw [rcx₂, g₁ _ (by decide)]; simp [cntOf]) g₂ m₂ rd₂ wr₂
  | false =>
    have hL := at₁ (j := 1) (by decide)
    rw [show stackArg s 1 = BitVec.ofNat 64 (eLn s) by simp] at hL
    exact WP.mono (prefixF_ok (stackArg s 1).isLt hL (in₁ (j := 1) (by decide)))
      fun e₂ ⟨rcx₂, g₂, m₂, rd₂, wr₂⟩ =>
        post e₂ (by rw [rcx₂, g₁ _ (by decide)]; rfl) g₂ m₂ rd₂ wr₂

/-- After the copy. -/
def Copied (whole : Bool) (s c : State) : Prop :=
  c.mem = headM s (cntOf s whole) ∧
    (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdi → r ≠ .rsi → r ≠ .r8 → r ≠ .r10 → c.gpr r = s.gpr r) ∧
    c.rd = s.rd ∧ c.wr = s.wr

theorem ready_copy (whole : Bool) {s b : State} (hs : FPre s) (hb : Ready whole s b) :
    Proof.AesGcm.X86_64.Short.CopyPre b (eSrc s) (eDst s) (cntOf s whole) := by
  obtain ⟨_, rsi, rdi, rcx, _, rd, wr⟩ := hb
  have hc := FPre.cnt_le (s := s) whole
  have hle := hs.le
  refine ⟨rsi, rdi, rcx, hs.cnt_lt whole, ?_, ?_, ?_⟩
  · exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨esR s, by rw [rd, hs.rd]; simp, 0, by simp, by simp only; omega⟩
  · exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨edR s, by rw [wr, hs.wr]; simp, 0, by simp, by simp only; omega⟩
  · exact (hs.s_d.sub_left (Region.sub_prefix hc)).sub_right (Region.sub_prefix (by omega))

theorem copied_ok (whole : Bool) (w : Width) {s b : State} (hs : FPre s) (hb : Ready whole s b) :
    WP isa (copyBytes w) b (Copied whole s) :=
  WP.mono (Gather.copyBytes_ok (ready_copy whole hs hb) w) fun c ⟨mc, gc, rdc, wrc⟩ => by
    obtain ⟨m, _, _, _, g, rd, wr⟩ := hb
    exact ⟨by rw [mc, m]; rfl, fun r a c' d e f t => by rw [gc r a f t, g r a c' d e t], by rw [rdc, rd],
      by rw [wrc, wr]⟩

/-- After the second `loadW`. -/
def Loaded2 (whole : Bool) (s d : State) : Prop :=
  d.gpr .rax = eW s ∧ Copied whole s d

theorem loaded2_ok (whole : Bool) {s c : State} (hs : FPre s) (hc : Copied whole s c) :
    WP isa (.block loadW) c (Loaded2 whole s) := by
  obtain ⟨mc, gc, rdc, wrc⟩ := hc
  have spc : c.gpr .rsp = s.gpr .rsp :=
    gc _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have fH := hs.headM_frame (cntOf s whole) (FPre.cnt_le whole)
  exact WP.mono (loadW_ok (by rw [mc, spc]; exact hs.arg_eq fH (j := 3) (by decide))
      (by rw [rdc, wrc, spc]; exact hs.arg_in (j := 3) (by decide)))
    fun d ⟨rax, g, m, rd, wr⟩ => ⟨rax, by rw [m, mc], fun r a b' c' e f t => by rw [g r a, gc r a b' c' e f t],
      by rw [rd, rdc], by rw [wr, wrc]⟩

/-- After `head`. -/
structure Headed (whole : Bool) (s h : State) : Prop where
  mem : h.mem = headM s (cntOf s whole)
  rdi : h.gpr .rdi = s.gpr .rdi
  rsi : h.gpr .rsi = s.gpr .rsi
  rcx : h.gpr .rcx = s.gpr .rcx
  r8 : h.gpr .r8 = s.gpr .r8
  r10 : h.gpr .r10 = eW s
  r11 : h.gpr .r11 = eTg s
  rax : h.gpr .rax = eDst s
  keep : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdi → r ≠ .rsi → r ≠ .r8 → r ≠ .r10 → r ≠ .r11 → h.gpr r = s.gpr r
  rd : h.rd = s.rd
  wr : h.wr = s.wr
  mx : h.mxcsr = s.mxcsr

theorem headed_ok (whole : Bool) {s d : State} (hs : FPre s) (hd : Loaded2 whole s d) :
    WP isa (.block unstash) d fun h => h.mxcsr = s.mxcsr → Headed whole s h := by
  obtain ⟨rax, mc, gc, rdc, wrc⟩ := hd
  have hc := FPre.cnt_le (s := s) whole
  have win : ∀ {k : Nat}, k + 8 ≤ 1696 → InRegions (s.rd ++ s.wr) (off (eW s) k) 8 :=
    fun hk => ⟨ewR s, by rw [hs.wr]; simp, w_in s hk⟩
  have spc : d.gpr .rsp = s.gpr .rsp :=
    gc _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have fH := hs.headM_frame (cntOf s whole) hc
  have at₁ : ∀ {j}, j < 4 → d.mem.readW (off (d.gpr .rsp) (8 * (j + 1))) 64 = stackArg s j := fun hj => by
    rw [mc, spc]; exact hs.arg_eq fH hj
  have in₁ : ∀ {j}, j < 4 → InRegions (d.rd ++ d.wr) (off (d.gpr .rsp) (8 * (j + 1))) 8 := fun hj => by
    rw [rdc, wrc, spc]; exact hs.arg_in hj
  have rw' : d.rd ++ d.wr = s.rd ++ s.wr := by rw [rdc, wrc]
  refine WP.mono (unstash_ok rax (at₁ (j := 3) (by decide)) (at₁ (j := 2) (by decide))
    (at₁ (j := 0) (by decide)) (in₁ (j := 3) (by decide)) (in₁ (j := 2) (by decide)) (in₁ (j := 0) (by decide))
    (by rw [rw']; exact win (by decide)) (by rw [rw']; exact win (by decide))
    (by rw [rw']; exact win (by decide)) (by rw [rw']; exact win (by decide)))
    fun h ⟨rdi', rsi', rcx', r8', r10', r11', rax', g', m', rd', wr'⟩ mxh => ?_
  refine ⟨by rw [m', mc], ?_, ?_, ?_, ?_, r10', r11', rax', fun r a b' c' e f t u => ?_,
    by rw [rd', rdc], by rw [wr', wrc], mxh⟩
  · rw [rdi', mc, hs.headM_w _ hc (by decide), stashM_rdi]
  · rw [rsi', mc, hs.headM_w _ hc (by decide), stashM_rsi]
  · rw [rcx', mc, hs.headM_w _ hc (by decide), stashM_rcx]
  · rw [r8', mc, hs.headM_w _ hc (by decide), stashM_r8]
  · rw [g' r a b' c' e f t u, gc r a b' c' e f t]

theorem head_mx (whole : Bool) (w : Width) : (head whole w).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases whole <;> cases w <;> decide +kernel

theorem head_ok (whole : Bool) (w : Width) {s : State} (hs : FPre s) : WP isa (head whole w) s (Headed whole s) :=
  WP.mono_mx (Q := fun h => h.mxcsr = s.mxcsr → Headed whole s h) (head_mx whole w)
    (WP.seq (WP.mono (loaded_ok hs) fun _ ha =>
      WP.seq (WP.mono (ready_ok whole hs ha) fun _ hb =>
      WP.seq (WP.mono (copied_ok whole w hs hb) fun _ hc =>
      WP.seq (WP.mono (loaded2_ok whole hs hc) fun _ hd => headed_ok whole hs hd)))))
    fun _ hh mx => hh mx

end VG.Proof.ChaCha20Poly1305.X86_64.Split
