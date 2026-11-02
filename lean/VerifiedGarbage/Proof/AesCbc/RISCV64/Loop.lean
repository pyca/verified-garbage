module

public import VerifiedGarbage.Proof.AesCbc.RISCV64.Call
public import VerifiedGarbage.Impl.AesCbc.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.XorBytes
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# AES-CBC on RISC-V: the code between the calls, and the loop

The straight-line pieces that AES-CTR, CMAC and XTS's data units share
(`xorInto`, `copy`), each run in continuation-passing style, the blocks a
byte at a time (`Bytes.xorBytes_ok`, `Bytes.copyBytes_ok`).

The invariant after `k` blocks (`LInv`), for any mode on whole blocks, as on
PPC64LE (`Proof/AesCbc/PPC64LE/Loop.lean`): `s1`–`s6` hold the arguments
(`s4` the next block, `s5` the blocks left), the other callee-saved
registers are our caller's, only the chaining value, the data, the block
function's working space and the saved block have changed since the
registers were saved, the first `k` blocks are the mode's (`Mode.out`) of
the first `k` blocks on entry and the rest are unchanged, and the chaining
value is the mode's after them (`Mode.chain`).

`whole_wp`: if one run of `body` takes the invariant from `k` to `k + 1`
blocks (`BodyOk`), `whole body` meets the contract.
-/

@[expose] public section

namespace VG.Proof.AesCbc.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Align VG.Impl.AesCbc.RISCV64
open VG.Spec.Aes (bytesAt)

/-! ## Blocks of bytes -/

theorem bytes_xor {m m' : Mem} {P Q : Addr}
    (h : ∀ j < 16, m' (P + BitVec.ofNat 64 j) = m (P + BitVec.ofNat 64 j) ^^^ m (Q + BitVec.ofNat 64 j)) :
    bytesAt m' P 16 = Spec.Cbc.xor (bytesAt m P 16) (bytesAt m Q 16) := by
  apply List.ext_getElem (by simp [bytesAt, Spec.Cbc.xor])
  intro j h₁ h₂
  simp only [bytesAt, List.length_map, List.length_range] at h₁
  simp [bytesAt, Spec.Cbc.xor, h j h₁]

theorem bytes_copy {m m' : Mem} {P Q : Addr}
    (h : ∀ j < 16, m' (P + BitVec.ofNat 64 j) = m (Q + BitVec.ofNat 64 j)) :
    bytesAt m' P 16 = bytesAt m Q 16 := by
  apply List.ext_getElem (by simp [bytesAt])
  intro j h₁ h₂
  simp only [bytesAt, List.length_map, List.length_range] at h₁
  simp [bytesAt, h j h₁]

theorem ofNat_zero_add (P : Addr) : P + BitVec.ofNat 64 0 = P := by simp

/-- Each byte of a block in a region. -/
theorem in_bytes {rs : List Region} {P : Addr} (h : ∃ r ∈ rs, Region.Sub ⟨P, 16⟩ r) :
    ∀ i < 16, InRegions rs (P + BitVec.ofNat 64 i) 1 := by
  obtain ⟨r, hr, hs⟩ := h
  exact fun i hi => ⟨r, hr, hs _ (Offset.contains_base _ (by omega) (by omega))⟩

/-! ## Straight-line pieces -/

/-- The block at `dst` XORed with the block at `src`, in place. -/
theorem xorInto_wp {dst src : Reg} {s : State} {P Q : Addr} {rest : List Instr} {Φ : State → Prop}
    (hd3 : dst ≠ .t3) (hd4 : dst ≠ .t4) (hs3 : src ≠ .t3) (hs4 : src ≠ .t4)
    (hp : s.gpr dst = P) (hq : s.gpr src = Q)
    (rq : ∃ r ∈ s.rd ++ s.wr, Region.Sub ⟨Q, 16⟩ r) (wp : ∃ r ∈ s.wr, Region.Sub ⟨P, 16⟩ r)
    (hpq : (⟨P, 16⟩ : Region).Disjoint ⟨Q, 16⟩)
    (k : ∀ s', (∀ r, r ≠ .t3 → r ≠ .t4 → s'.gpr r = s.gpr r) →
      bytesAt s'.mem P 16 = Spec.Cbc.xor (bytesAt s.mem P 16) (bytesAt s.mem Q 16) →
      Frame [⟨P, 16⟩] s.mem s'.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      WP isa (.block rest) s' Φ) :
    WP isa (.block (xorInto dst src ++ rest)) s Φ := by
  rw [xorInto, WP.block_append_iff]
  refine WP.mono (Bytes.xorBytes_ok (Ne.symm hd3) (Ne.symm hs3) (Ne.symm hd4) (Ne.symm hs4)
    (by decide) (by decide) (by rw [hq]; exact in_bytes rq) (by rw [hp]; exact in_bytes wp)
    (fun i hi hc => ?_)) fun s' h => ?_
  · rw [hp, hq] at hc
    exact hpq _ hc (Offset.contains_base _ (by omega) (by omega))
  · have hx := h.xored
    have hf := h.frame
    rw [hp, hq] at hx
    rw [hp] at hf
    exact k s' h.gpr (bytes_xor hx) hf h.rd h.wr h.sp

/-- The block at `src` copied to `dst`. -/
theorem copy_wp {dst src : Reg} {s : State} {P Q : Addr} {rest : List Instr} {Φ : State → Prop}
    (hd : dst ≠ .t3) (hs : src ≠ .t3) (hp : s.gpr dst = P) (hq : s.gpr src = Q)
    (rq : ∃ r ∈ s.rd ++ s.wr, Region.Sub ⟨Q, 16⟩ r) (wp : ∃ r ∈ s.wr, Region.Sub ⟨P, 16⟩ r)
    (hpq : (⟨P, 16⟩ : Region).Disjoint ⟨Q, 16⟩)
    (k : ∀ s', (∀ r, r ≠ .t3 → s'.gpr r = s.gpr r) → bytesAt s'.mem P 16 = bytesAt s.mem Q 16 →
      Frame [⟨P, 16⟩] s.mem s'.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      WP isa (.block rest) s' Φ) :
    WP isa (.block (copy dst src ++ rest)) s Φ := by
  rw [copy, WP.block_append_iff]
  refine WP.mono (Bytes.copyBytes_ok (Ne.symm hs) (Ne.symm hd) (by decide) (by decide)
    (fun i hi => by rw [hq, Nat.zero_add]; exact in_bytes rq i hi)
    (fun i hi => by rw [hp, Nat.zero_add]; exact in_bytes wp i hi)
    (fun i hi hc => ?_)) fun s' h => ?_
  · rw [hp, hq, Nat.zero_add, ofNat_zero_add] at hc
    exact hpq _ hc (Offset.contains_base _ (by omega) (by omega))
  · refine k s' h.gpr (bytes_copy fun j hj => ?_) (by have := h.frame; rwa [hp, ofNat_zero_add] at this)
      h.rd h.wr h.sp
    have := h.copied j hj
    rwa [hp, hq, Nat.zero_add] at this

/-- `addi 2047`, `addi 8` then `andi -8`: `x + 2048` rounded up. -/
theorem sv_arith (x : Addr) :
    (x + BitVec.ofInt 64 2047 + BitVec.ofInt 64 8) &&& BitVec.ofInt 64 (-8) =
      x + BitVec.ofNat 64 2048 + BitVec.ofNat 64 (pad (x + BitVec.ofNat 64 2048)) := by
  rw [← align_eq, BitVec.add_assoc, BitVec.add_assoc,
    show BitVec.ofInt 64 2047 + BitVec.ofInt 64 8 = BitVec.ofNat 64 2048 + BitVec.ofInt 64 7 by decide]

/-- `t0 :=` the register `n`'s value plus 2048, rounded up. -/
theorem savePtr_ok {s : State} (n : Reg) :
    WP isa (.block (savePtr n)) s (· = s.write .t0
      (s.gpr n + BitVec.ofNat 64 2048 + BitVec.ofNat 64 (pad (s.gpr n + BitVec.ofNat 64 2048)))) := by
  apply WP.of_runBlock
  simp only [savePtr, runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 2047 by decide),
    exec_addi (show imm12 8 by decide), exec_logicImm (show imm12 (-8) by decide),
    RegUpd.gpr_write_self, RegUpd.write_write, Option.some.injEq, exists_eq_left']
  rw [sv_arith]

/-! ## The arguments and the invariant -/

section
variable (s₀ : State)

abbrev W : Addr := s₀.gpr .a0
abbrev R : Nat := (s₀.gpr .a1).toNat
abbrev Iv : Addr := s₀.gpr .a2
abbrev Dp : Addr := s₀.gpr .a3
abbrev N : Nat := (s₀.gpr .a4).toNat
abbrev S : Addr := s₀.gpr .a5

/-- How far `scratch + 2048` is below a multiple of 8. -/
abbrev q : Nat := pad (S s₀ + BitVec.ofNat 64 2048)
/-- The saved block and registers: `scratch + 2048`, rounded up. -/
abbrev sv : Addr := S s₀ + BitVec.ofNat 64 2048 + BitVec.ofNat 64 (q s₀)

abbrev schR : Region := ⟨W s₀, 240⟩
abbrev ivR : Region := ⟨Iv s₀, 16⟩
abbrev dataR : Region := ⟨Dp s₀, 16 * N s₀⟩
abbrev scrR : Region := ⟨S s₀, 2176⟩
/-- The block function's working space. -/
abbrev wsR : Region := ⟨S s₀, 2048⟩
/-- The saved block. -/
abbrev cR : Region := ⟨sv s₀, 16⟩

/-- The blocks on entry. -/
abbrev blks : List (List Byte) := Spec.Cbc.blocksAt s₀.mem (Dp s₀) (N s₀)

/-- The chaining value on entry. -/
abbrev iv0 : List Byte := bytesAt s₀.mem (Iv s₀) 16

/-- The address of block `k`. -/
abbrev blk (k : Nat) : Addr := Dp s₀ + BitVec.ofNat 64 (16 * k)

end

theorem q_lt (s₀ : State) : q s₀ < 8 := pad_lt _

theorem sv_add (s₀ : State) (d : Nat) :
    sv s₀ + BitVec.ofNat 64 d = S s₀ + BitVec.ofNat 64 (2048 + q s₀ + d) := align_add _ _ _

theorem sv_eq (s₀ : State) : sv s₀ = S s₀ + BitVec.ofNat 64 (2048 + q s₀) := by
  rw [← ofNat_zero_add (sv s₀), sv_add, Nat.add_zero]

theorem sv_al (s₀ : State) {d : Nat} (hd : d % 8 = 0) : (sv s₀ + BitVec.ofNat 64 d).toNat % 8 = 0 :=
  align_al_add _ hd

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀]
  wr : s₀.wr = [ivR s₀, dataR s₀, scrR s₀]
  sch_iv : (schR s₀).Disjoint (ivR s₀)
  sch_data : (schR s₀).Disjoint (dataR s₀)
  sch_scr : (schR s₀).Disjoint (scrR s₀)
  iv_data : (ivR s₀).Disjoint (dataR s₀)
  iv_scr : (ivR s₀).Disjoint (scrR s₀)
  data_scr : (dataR s₀).Disjoint (scrR s₀)
  iv_wrap : (Iv s₀).toNat + 16 ≤ 2 ^ 64
  data_wrap : (Dp s₀).toNat + 16 * N s₀ ≤ 2 ^ 64
  scr_wrap : (S s₀).toNat + 2176 ≤ 2 ^ 64
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem UPre.of {M : Mode} {s₀ : State} (h : (modeRISCV64 M).pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩

/-- What the prologue saves, and where, from `sv`. -/
abbrev saveL : List (Reg × Nat) := saved

/-- The values saved: `t0` holds `sv`. -/
abbrev saveG (s₀ : State) : Reg → BitVec 64 := (s₀.write .t0 (sv s₀)).gpr

/-- The memory after saving the registers. -/
abbrev savedMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (sv s₀) (saveG s₀) saveL

/-- The registers holding our variables. -/
abbrev vars : List Reg := [.s1, .s2, .s3, .s4, .s5, .s6]

/-- The key schedule as the mode uses it. -/
abbrev wK (s₀ : State) : List Byte := bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1))

/-- The first `k` blocks after the mode. -/
abbrev outK (M : Mode) (s₀ : State) (k : Nat) : List (List Byte) :=
  M.out (R s₀) (wK s₀) (iv0 s₀) ((blks s₀).take k)

/-- The chaining value after the first `k` blocks. -/
abbrev chainK (M : Mode) (s₀ : State) (k : Nat) : List Byte :=
  M.chain (R s₀) (wK s₀) (iv0 s₀) ((blks s₀).take k)

/-- What the code may write once the registers are saved. -/
abbrev Mut (s₀ : State) : List Region := [ivR s₀, dataR s₀, wsR s₀, cR s₀]

/-- The loop invariant, after `k` blocks. -/
structure LInv (M : Mode) (s₀ : State) (k : Nat) (s : State) : Prop where
  s1 : s.gpr .s1 = W s₀
  s2 : s.gpr .s2 = s₀.gpr .a1
  s3 : s.gpr .s3 = Iv s₀
  s4 : s.gpr .s4 = blk s₀ k
  s5 : s.gpr .s5 = BitVec.ofNat 64 (N s₀ - k)
  s6 : s.gpr .s6 = S s₀
  keep : ∀ r ∈ preserved, r ∉ vars → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame (Mut s₀) (savedMem s₀) s.mem
  data : Spec.Cbc.blocksAt s.mem (Dp s₀) (N s₀) = outK M s₀ k ++ (blks s₀).drop k
  iv : bytesAt s.mem (Iv s₀) 16 = chainK M s₀ k

/-! ## Regions -/

section
variable {s₀ : State}

theorem UPre.scr_sub {d n : Nat} (h : d + n ≤ 2176) : Region.Sub ⟨S s₀ + BitVec.ofNat 64 d, n⟩ (scrR s₀) :=
  Offset.sub_base _ h

theorem UPre.data_sub {k : Nat} (hk : k < N s₀) : Region.Sub ⟨blk s₀ k, 16⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega_arith)

theorem cR_sub : Region.Sub (cR s₀) (scrR s₀) := by
  have := q_lt s₀
  rw [cR, sv_eq]; exact UPre.scr_sub (by omega)

theorem wsR_sub : Region.Sub (wsR s₀) (scrR s₀) := Region.sub_prefix (by decide)

theorem UPre.blk_disjoint (hp : UPre s₀) {j k : Nat} (hj : j < N s₀) (hk : k < N s₀) (hjk : j ≠ k) :
    (⟨blk s₀ j, 16⟩ : Region).Disjoint ⟨blk s₀ k, 16⟩ := by
  have := hp.data_wrap
  exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

theorem UPre.cR_wsR (hp : UPre s₀) : (cR s₀).Disjoint (wsR s₀) := by
  have := q_lt s₀
  have := hp.scr_wrap
  rw [cR, sv_eq]; exact Offset.disjoint_base _ (by omega) (by omega)

end

/-- The saved registers' slots, from `sv`. -/
theorem saved_bound : ∀ p ∈ saveL, 16 ≤ p.2 ∧ p.2 + 8 ≤ 72 := by decide

theorem slot_sub (s₀ : State) {d : Nat} (h₁ : 16 ≤ d) (h₂ : d + 8 ≤ 72) :
    Region.Sub ⟨sv s₀ + BitVec.ofNat 64 d, 8⟩ (scrR s₀) := by
  have := q_lt s₀
  rw [sv_add]; exact UPre.scr_sub (by omega)

theorem slots_sub (s₀ : State) : Region.Sub ⟨sv s₀ + BitVec.ofNat 64 16, 56⟩ (scrR s₀) := by
  have := q_lt s₀
  rw [sv_add]; exact UPre.scr_sub (by omega)

/-- Saving the registers changes only their slots. -/
theorem savedMem_frame (s : State) :
    Frame [⟨sv s + BitVec.ofNat 64 16, 56⟩] s.mem (savedMem s) :=
  Spill.saveMem_frame (lo := 16) (n := 56) saved_bound (by decide) _ _ _

theorem in_rw {rs : List Region} {r : Region} (hr : r ∈ rs) {a : Addr} {n : Nat} (hc : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, hc⟩

/-- The regions the function writes. -/
abbrev Big (s₀ : State) : List Region := [ivR s₀, dataR s₀, scrR s₀]

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.sched_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    bytesAt m (W s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)) := by
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_arith
  refine bytesAt_frame hf (fun r hr => ?_) (by omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.sch_iv.sub_left (Region.sub_prefix hR)
  · exact hp.sch_data.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)

omit hp in
theorem UPre.big_of {m : Mem} (hf : Frame (Mut s₀) (savedMem s₀) m) : Frame (Big s₀) s₀.mem m := by
  have f₀ : Frame (Big s₀) s₀.mem (savedMem s₀) :=
    (savedMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, slots_sub s₀⟩
  exact f₀.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, wsR_sub⟩
    · exact ⟨scrR s₀, by simp, cR_sub⟩)

/-- The blocks after a step that changed only block `k`, the chaining
value, the working space and the saved block. -/
theorem UPre.blocksAt_step {m m' : Mem} {k : Nat} (hk : k < N s₀)
    (hf : Frame [⟨blk s₀ k, 16⟩, ivR s₀, wsR s₀, cR s₀] m m') :
    Spec.Cbc.blocksAt m' (Dp s₀) (N s₀) =
      (Spec.Cbc.blocksAt m (Dp s₀) (N s₀)).set k (bytesAt m' (blk s₀ k) 16) := by
  refine blocksAt_set fun j hj hjk => bytesAt_frame hf (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.blk_disjoint hj hk hjk
  · exact hp.iv_data.symm.sub_left (UPre.data_sub hj)
  · exact (hp.data_scr.sub_left (UPre.data_sub hj)).sub_right wsR_sub
  · exact (hp.data_scr.sub_left (UPre.data_sub hj)).sub_right cR_sub

omit hp in
/-- Block `k` before the step, from the invariant. -/
theorem LInv.block {M : Mode} {k : Nat} {s : State} (h : LInv M s₀ k s) (hk : k < N s₀) :
    bytesAt s.mem (blk s₀ k) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
  have hl : (outK M s₀ k).length = k := by
    rw [outK, M.length_out]; simp [Spec.Cbc.blocksAt]; omega_arith
  have := congrArg (·[k]?) h.data
  simp only [List.getElem?_eq_getElem (show k < (Spec.Cbc.blocksAt s.mem (Dp s₀) (N s₀)).length by
      rw [length_blocksAt]; exact hk),
    List.getElem?_append_right (show (outK M s₀ k).length ≤ k by omega_arith), hl, Nat.sub_self,
    List.getElem?_drop, Nat.add_zero,
    List.getElem?_eq_getElem (show k < (blks s₀).length by simp [Spec.Cbc.blocksAt]; exact hk)] at this
  show bytesAt s.mem (Dp s₀ + BitVec.ofNat 64 (16 * k)) 16 = _
  rw [← getElem_blocksAt _ _ hk]
  exact Option.some.inj this

end

theorem take_succ_blks (s₀ : State) {k : Nat} (hk : k < N s₀) :
    (blks s₀).take (k + 1) = (blks s₀).take k ++ [(blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cbc.blocksAt]; exact hk)]
  rfl

theorem a1_ofNat (s₀ : State) : s₀.gpr .a1 = BitVec.ofNat 64 (R s₀) := by
  apply BitVec.eq_of_toNat_eq; simp [R]

theorem a4_ofNat (s₀ : State) : s₀.gpr .a4 = BitVec.ofNat 64 (N s₀) := by
  apply BitVec.eq_of_toNat_eq; simp [N]

/-! ## The loop -/

/-- One run of `body` takes the invariant from `k` blocks to `k + 1`. -/
def BodyOk (M : Mode) (body : Prog isa) : Prop :=
  ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, LInv M s₀ k s →
    WP isa body s (LInv M s₀ (k + 1))

theorem loop_ok {M : Mode} {body : Prog isa} (hb : BodyOk M body) {s₀ : State} (hp : UPre s₀) {k : Nat}
    (hk : k < N s₀) {s : State} (h : LInv M s₀ k s) :
    WP isa (.loop body (.nonzero .s5)) s (LInv M s₀ (N s₀)) := by
  have hN := (s₀.gpr .a4).isLt
  refine WP.loop (M := isa) (body := body) (c := .nonzero .s5) (Q := LInv M s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv M s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (hb hp hk h) fun s' h' => ?_
  have ev := eval_nonzero_ofNat s' .s5 (k := N s₀ - (k + 1)) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hN) h'.s5
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega_arith]
  · right
    refine ⟨by rw [ev]; simp [hz], N s₀ - (k + 1), by omega_arith, k + 1, rfl, by omega_arith, h'⟩

/-! ## Saving and restoring the registers -/

theorem save_eq : save = savePtr .a5 ++ Spill.saveCode .t0 saveL := rfl

theorem restore_eq : restore = savePtr .s6 ++ Spill.restoreCode .t0 saveL := rfl

/-- A saved register's slot, within the scratch buffer. -/
theorem slot_contains (s₀ : State) {d : Nat} (h₁ : 16 ≤ d) (h₂ : d + 8 ≤ 72) :
    (scrR s₀).Contains (sv s₀ + BitVec.ofNat 64 d) 8 := by
  have := q_lt s₀
  rw [sv_add]; exact Offset.contains_base _ (by omega) (by omega)

theorem prologue_wp {M : Mode} {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (save ++ setup)) s₀ (LInv M s₀ 0) := by
  have hN := (s₀.gpr .a4).isLt
  rw [save_eq, List.append_assoc, WP.block_append_iff]
  refine WP.mono (savePtr_ok .a5) fun s₁ e => ?_
  subst e
  have t₀ : (s₀.write .t0 (sv s₀)).gpr .t0 = sv s₀ := RegUpd.gpr_write_self _ _ _
  refine Spill.save_ok (b := .t0) (l := saveL) (by rw [t₀]; exact align_al _) (by decide)
    (fun p hp' => ?_) ?_
  · have := saved_bound p hp'
    rw [t₀]
    show InRegions s₀.wr _ 8
    rw [hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (slot_contains s₀ this.1 this.2)
  unfold setup mov
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ =>
    wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ => WP.block_nil ?_
  have f₀ := savedMem_frame s₀
  have disj : ∀ (r : Region), r ∈ [ivR s₀, dataR s₀] →
      ∀ r' ∈ [(⟨sv s₀ + BitVec.ofNat 64 16, 56⟩ : Region)], r.Disjoint r' := by
    intro r hr r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hr'
    subst hr'
    rcases hr with rfl | rfl
    · exact hp.iv_scr.sub_right (slots_sub s₀)
    · exact hp.data_scr.sub_right (slots_sub s₀)
  have ivS : bytesAt (savedMem s₀) (Iv s₀) 16 = iv0 s₀ :=
    bytesAt_frame f₀ (disj _ (by simp)) (by decide)
  have dataS : Spec.Cbc.blocksAt (savedMem s₀) (Dp s₀) (N s₀) = blks s₀ := by
    simp only [Spec.Cbc.blocksAt]
    refine List.map_congr_left fun j hj => bytesAt_frame f₀ (fun r hr => ?_) (by decide)
    have := List.mem_range.mp hj
    exact (disj _ (by simp) r hr).sub_left (UPre.data_sub this)
  have m₆ : s₆.mem = savedMem s₀ := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    show Spill.saveMem s₀.mem ((s₀.write .t0 (sv s₀)).gpr .t0) _ _ = _
    rw [t₀]
  have g₀ (r : Reg) (hr : r ≠ .t0) : (s₀.write .t0 (sv s₀)).gpr r = s₀.gpr r :=
    RegUpd.gpr_write_of_ne _ _ hr
  exact {
    s1 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr]; exact g₀ .a0 (by decide)
    s2 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.other _ (by decide)]; exact g₀ .a1 (by decide)
    s3 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
        u₂.other _ (by decide), u₁.other _ (by decide)]; exact g₀ .a2 (by decide)
    s4 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), g₀ .a3 (by decide)]; simp
    s5 := by
      rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), g₀ .a4 (by decide), a4_ofNat]; rfl
    s6 := by
      rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide)]; exact g₀ .a5 (by decide)
    keep := fun r hr hv => by
      simp only [vars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
      rw [u₆.other _ h6, u₅.other _ h5, u₄.other _ h4, u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]
      exact g₀ _ (fun e => by subst e; revert hr; decide)
    rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]; rfl
    wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; rfl
    sp := by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]; rfl
    frame := by rw [m₆]; exact Frame.refl _ _
    data := by rw [m₆, dataS, outK, List.take_zero, M.out_nil, List.drop_zero, List.nil_append]
    iv := by rw [m₆, ivS, chainK, List.take_zero, M.chain_nil] }

/-- No blocks, or `mid` on all of them. -/
theorem ends_mid_wp {M : Mode} {mid : Prog isa} {s₀ : State} {s₁ : State}
    (hm : 0 < N s₀ → WP isa mid s₁ (LInv M s₀ (N s₀))) (h : LInv M s₀ 0 s₁) :
    WP isa (.ite (.zero .s5) (.block []) mid) s₁ (LInv M s₀ (N s₀)) := by
  have hN := (s₀.gpr .a4).isLt
  have ev := eval_zero_ofNat s₁ .s5 (k := N s₀ - 0) (by omega_arith) h.s5
  rw [Nat.sub_zero] at ev
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact hm (by omega_arith)

theorem slots_disj {s₀ : State} (hp : UPre s₀) :
    ∀ p ∈ saveL, ∀ r ∈ Mut s₀, Region.Disjoint ⟨sv s₀ + BitVec.ofNat 64 p.2, 8⟩ r := by
  intro p hp' r hr
  have hb := saved_bound p hp'
  have := q_lt s₀
  have := hp.scr_wrap
  have hsub : Region.Sub ⟨sv s₀ + BitVec.ofNat 64 p.2, 8⟩ (scrR s₀) := slot_sub s₀ hb.1 hb.2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.iv_scr.symm.sub_left hsub
  · exact hp.data_scr.symm.sub_left hsub
  · rw [sv_add]; exact Offset.disjoint_base _ (by omega) (by omega)
  · rw [sv_add, cR, sv_eq]; exact Offset.disjoint _ (by omega) (by omega) (by omega)

/-- The postcondition of the whole function, but for the stack pointer. -/
def Done (M : Mode) (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧ (modeRISCV64 M).post s₀ s'

theorem epilogue_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {s₂ : State} (h₂ : LInv M s₀ (N s₀) s₂) :
    WP isa (.block restore) s₂ (Done M s₀) := by
  have hsv : Spill.Saved (sv s₀) (saveG s₀) saveL s₂.mem :=
    (Spill.saveMem_saved (by decide) _ _ _).frame h₂.frame (slots_disj hp)
  have hall : (blks s₀).take (N s₀) = blks s₀ := List.take_of_length_le (by simp [Spec.Cbc.blocksAt])
  have hnil : (blks s₀).drop (N s₀) = [] := List.drop_of_length_le (by simp [Spec.Cbc.blocksAt])
  rw [restore_eq, WP.block_append_iff]
  refine WP.mono (savePtr_ok .s6) fun s₃ e => ?_
  subst e
  rw [h₂.s6]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := saveL) (B := sv s₀) (align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp' => ?_) hsv) fun s₄ r₄ => ?_
  · have := saved_bound p hp'
    show InRegions (s₂.rd ++ s₂.wr) _ 8
    rw [h₂.rd, h₂.wr, hp.rd, hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (slot_contains s₀ this.1 this.2)
  have g₀ (r : Reg) (hr : r ≠ .t0) : saveG s₀ r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · have h0 : r ≠ .t0 := fun e => by subst e; revert hr; decide
    rw [r₄.gpr_of (r := r) ?_, g₀ r h0]
    by_cases hv : r ∈ vars
    · left
      simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · right
      rw [RegUpd.gpr_write_of_ne _ _ h0, h₂.keep r hr hv, g₀ r h0]
  · rw [r₄.gpr (.ra, 16) (by decide), g₀ .ra (by decide)]
  · show Spec.Cbc.blocksAt s₄.mem (Dp s₀) (N s₀) = _
    rw [r₄.mem]
    show Spec.Cbc.blocksAt s₂.mem (Dp s₀) (N s₀) = _
    rw [h₂.data]; simp only [outK, hall, hnil, List.append_nil]
  · show bytesAt s₄.mem (Iv s₀) 16 = _
    rw [r₄.mem]
    show bytesAt s₂.mem (Iv s₀) 16 = _
    rw [h₂.iv]; simp only [chainK, hall]

/-- The registers saved and the arguments set up, `mid` run unless there are
no blocks, and the registers restored, when `mid` takes the invariant from no
blocks to all of them (as `body`'s loop does, `whole_wp`). -/
theorem ends_wp {M : Mode} {mid : Prog isa} {s₀ : State} (h0 : (modeRISCV64 M).pre s₀)
    (hm : UPre s₀ → 0 < N s₀ → ∀ {s₁ : State}, LInv M s₀ 0 s₁ → WP isa mid s₁ (LInv M s₀ (N s₀))) :
    WP isa (.seq (.block (save ++ setup)) (.seq (.ite (.zero .s5) (.block []) mid) (.block restore)))
      s₀ (Done M s₀) := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ h₁ =>
    WP.seq (WP.mono (ends_mid_wp (fun hn => hm hp hn h₁) h₁) fun _ h₂ => epilogue_wp hp h₂))

theorem whole_wp {M : Mode} {body : Prog isa} (hb : BodyOk M body) {s₀ : State}
    (h0 : (modeRISCV64 M).pre s₀) : WP isa (whole body) s₀ (Done M s₀) :=
  ends_wp h0 fun hp hn _ h => loop_ok hb hp hn h

end VG.Proof.AesCbc.RISCV64
