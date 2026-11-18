module

public import VerifiedGarbage.Impl.AesCtr.X86_64
public import VerifiedGarbage.Proof.AesCtr.Rounds
public import VerifiedGarbage.Proof.Aes.X86_64.Variant
public import VerifiedGarbage.Proof.AesCbc.X86_64.Call
public import VerifiedGarbage.Proof.AesCtr.Spec
public import VerifiedGarbage.Spec.Ctr.Contract
import VerifiedGarbage.Proof.AesCbc.X86_64.Verified
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.AesCbc.X86_64.CT
meta import VerifiedGarbage.Proof.AesCbc.X86_64.CT
import VerifiedGarbage.Proof.AesCbc.X86_64.Body
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
public import VerifiedGarbage.Proof.AesCbc.X86_64.Loop
public import VerifiedGarbage.Proof.AesCtr.Ctr32
import Lean.DocString.Parser
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.AesCtr.Inc
import VerifiedGarbage.Proof.AesCbc.X86_64.Block
import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.AesCbc.X86_64.Body
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
meta import VerifiedGarbage.Impl.AesCtr.X86_64
meta import VerifiedGarbage.Proof.AesCbc.X86_64.Loop
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.AesCtr.Spec
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import Lean.DocString.Parser
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.AesCtr.Inc
meta import VerifiedGarbage.Proof.AesCbc.X86_64.Block
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.Mem

/-! ### `AesCtr.X86_64.CT`, which this module and modules that import it used -/

section

/-! ### `AesCtr.X86_64.Iter`, which this module and modules that import it used -/

section

/-! ### `AesCtr.X86_64.Body`, which this module and modules that import it used -/

section

/-! ### `AesCtr.X86_64.Steps`, which this module and modules that import it used -/

section

/-!
# AES-CTR on x86-64: the code between the calls

The straight-line pieces of an iteration, run once each: the number of
blocks of the call (`count`, `min left (2³² − lo32 t)`), its arguments
(`args`), the advance past them with ZF set if the counter's last 32 bits
wrapped around (`adv`), and the carry into the first 96 bits (`carry`, whose
block is `t + 2³²`: `carryMem_bytes`).
-/

@[expose] public section

namespace VG.Proof.AesCtr.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCtr.X86_64
open VG.Impl.AesCbc.X86_64 (at_ cOff)
open VG.Proof.AesCbc.X86_64 (offset_nat)
open VG.Spec.Aes (bytesAt)

theorem countA_ok (s : State) {Q : Addr} (hq : s.gpr .r12 = Q)
    (rq : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 12) 4) :
    ∃ s', runBlock isa [.mov32 .rax (.mem (at_ .r12 12)), .bswap32 .rax] s = some s' ∧
      s'.gpr .rax = (rv32 (s.mem.readW (Q + BitVec.ofNat 64 12) 32)).setWidth 64 ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [runBlock_cons, at_, exec, readSrc32, State.load32, State.ea, offset_nat, State.setReg32, hq, rq]
    rfl, ?_⟩
  refine ⟨?_, fun r hr => by simp [gpr_setReg, State.setReg32, hr], rfl, rfl, rfl⟩
  simp only [gpr_setReg, ite_true, State.setReg32]
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  rfl

theorem countB1_ok (s : State) {c : BitVec 32} (ha : s.gpr .rax = c.setWidth 64) :
    ∃ s', runBlock isa [.movImm64 .rcx 0x100000000, .alu .sub .rcx (.reg .rax)] s = some s' ∧
      s'.gpr .rcx = 0x100000000 - c.setWidth 64 ∧
      (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
    exact rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, ha]
  · intro r hr; simp [gpr_setReg, hr]
  all_goals rfl

theorem countB2_ok (s : State) {a b : BitVec 64} (h14 : s.gpr .r14 = a) (hc : s.gpr .rcx = b) :
    ∃ s', runBlock isa [.alu .cmp .r14 (.reg .rcx), .cmov .b .rcx (.reg .r14)] s = some s' ∧
      s'.gpr .rcx = (if a.toNat < b.toNat then a else b) ∧
      (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, execCmov, eval,
      cf_arithFlags, Option.bind_some, Option.map_some]
    exact rfl, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases h : a.toNat < b.toNat <;> simp [gpr_setReg, h14, hc, h]
  · intro r hr
    by_cases h : (s.gpr .r14).toNat < (s.gpr .rcx).toNat <;> simp [gpr_setReg, hr, h]
  all_goals
    by_cases h : (s.gpr .r14).toNat < (s.gpr .rcx).toNat <;> simp [h] <;> rfl

/-- The counter block plus `2³²`: a carry into its first 96 bits. -/
theorem carry_ok (s : State) {Q : Addr} (hq : s.gpr .r12 = Q)
    (r0 : InRegions (s.rd ++ s.wr) Q 8) (r8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (w0 : InRegions s.wr Q 8) (w8 : InRegions s.wr (Q + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa carry s = some s' ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      bytesAt s'.mem Q 16 = Spec.Ctr.ofNat (Spec.Ctr.toNat (bytesAt s.mem Q 16) + 2 ^ 32) 16 ∧
      Frame [⟨Q, 16⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, carry, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      State.load64, State.store64, State.ea, offset_nat, execAlu, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, cf_setReg, cf_arithFlags, hq, BitVec.add_zero, r0, r8, w0, w8]
    exact rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro r h₁ h₂ h₃
    simp [gpr_setReg, h₁, h₂, h₃]
  · have e : (4294967296 : BitVec 64).toNat = 2 ^ 32 := rfl
    apply AesCtr.add_words64
    · rw [BitVec.toNat_add, e]; rfl
    · rw [show ∀ x, rv64 x = bswap64 x from fun _ => rfl, show ∀ x, rv64 x = bswap64 x from fun _ => rfl]
      generalize bswap64 (s.mem.readW (Q + BitVec.ofNat 64 8) 64) = L
      generalize bswap64 (s.mem.readW Q 64) = H
      have hL := L.isLt
      rw [BitVec.toNat_add, BitVec.toNat_add, e]
      have e₀ : (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 := rfl
      rw [e₀]
      by_cases h : 2 ^ 64 ≤ L.toNat + 2 ^ 32
      · rw [show (L.toNat + 2 ^ 32) / 2 ^ 64 = 1 by omega_using [h]]
        simp only [h, decide_true, BitVec.ofBool_true]
        have e₁ : (BitVec.setWidth 64 (1 : BitVec 1)).toNat = 1 := rfl
        rw [e₁]
        omega_using []
      · rw [show (L.toNat + 2 ^ 32) / 2 ^ 64 = 0 by omega_using [h]]
        simp only [h, decide_false, BitVec.ofBool_false]
        have e₁ : (BitVec.setWidth 64 (0 : BitVec 1)).toNat = 0 := rfl
        rw [e₁]
        omega_using []
  · exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base Q (d := 8) (n := 8) (k := 16) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (by simpa using Offset.contains_base Q (d := 0) (n := 8) (k := 16) (by decide) (by decide))
  all_goals rfl


theorem args_ok (s : State) :
    ∃ s', runBlock isa args s = some s' ∧
      s'.gpr .rdi = s.gpr .rbx ∧ s'.gpr .rsi = s.gpr .rbp ∧ s'.gpr .rdx = s.gpr .r12 ∧
      s'.gpr .r8 = s.gpr .rcx ∧ s'.gpr .rcx = s.gpr .r13 ∧ s'.gpr .r9 = s.gpr .r15 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [args, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]; rfl, ?_⟩
  refine ⟨by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg],
    by simp [gpr_setReg], by simp [gpr_setReg], fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]

theorem store_ok (s : State) {S : Addr} (hs : s.gpr .r15 = S) (ws : InRegions s.wr (S + BitVec.ofNat 64 2048) 8) :
    ∃ s', runBlock isa [.store (at_ .r15 cOff) .rcx] s = some s' ∧ s'.gpr = s.gpr ∧
      s'.mem = s.mem.writeW (S + BitVec.ofNat 64 2048) (s.gpr .rcx) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [cOff, runBlock_cons, runStep_some, runBlock_nil, at_, exec, State.store64, State.ea, offset_nat, hs, ws,
      ite_true]
    exact rfl, ?_, ?_, ?_, ?_⟩
  all_goals rfl

theorem advA_ok (s : State) {S P : Addr} {left m : Nat} (hs : s.gpr .r15 = S) (h13 : s.gpr .r13 = P)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 left) (hm : s.mem.readW (S + BitVec.ofNat 64 2048) 64 = BitVec.ofNat 64 m)
    (hml : m ≤ left) (h16 : 16 * m < 2 ^ 64)
    (rs : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 2048) 8) :
    ∃ s', runBlock isa [.mov .rax (.mem (at_ .r15 cOff)), .alu .sub .r14 (.reg .rax), .shift .shl .rax 4,
        .alu .add .r13 (.reg .rax)] s = some s' ∧
      s'.gpr .r14 = BitVec.ofNat 64 (left - m) ∧ s'.gpr .r13 = P + BitVec.ofNat 64 (16 * m) ∧
      (∀ r, r ≠ .rax → r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by
    simp only [cOff, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.load64, State.ea, offset_nat,
      execAlu, execShift, hs, rs, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
      gpr_setFlags, reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, and_self]
    exact rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ↓reduceIte, h14, hm]
    rw [Offset.ofNat_sub_ofNat hml]
  · simp only [gpr_setReg, ↓reduceIte, h13, hm]
    congr 1
    apply BitVec.eq_of_toNat_eq
    have hm' : m < 2 ^ 64 := by omega_using [h16]
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm', Nat.shiftLeft_eq]
    omega_using []
  · intro r h₁ h₂ h₃
    simp [gpr_setReg, gpr_setFlags, h₁, h₂, h₃]
  all_goals rfl

theorem advB_ok (s : State) {Q : Addr} (hq : s.gpr .r12 = Q)
    (rq : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 12) 4) :
    ∃ s', runBlock isa [.mov32 .rax (.mem (at_ .r12 12)), .alu32 .test .rax (.reg .rax)] s = some s' ∧
      s'.zf = some (s.mem.readW (Q + BitVec.ofNat 64 12) 32 == 0) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc32, State.load32, State.ea, offset_nat,
      State.setReg32, execAlu32, hq, rq, ite_true, Option.bind_some, Option.map_some]
    exact rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [zf_arithFlags, gpr_setReg, ite_true, BitVec.and_self]
    rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  · intro r hr; simp [gpr_setReg, hr]
  all_goals rfl

end VG.Proof.AesCtr.X86_64

end

end

/-!
# AES-CTR on x86-64: one call

`iter_wp`: one run of `body` takes AES-CBC's loop invariant for `ctrMode`
(`Proof/AesCbc/X86_64/Loop.lean`) from `k` blocks to `k + mOf s₀ k`, the
blocks of the call, for any implementation of `vg_aes_ctr32` (`Ctr32Impl`),
and sets ZF if no blocks are left. The call gives CTR's output on its
blocks (`AesCtr.ctr32_crypt`), and the counter block it leaves, with the
carry into the first 96 bits if its last 32 bits wrapped around, is CTR's
(`AesCtr.ctr32_next`, `AesCtr.ctr32_wrap`).
-/

@[expose] public section

namespace VG.Proof.AesCtr.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCtr.X86_64
open VG.Impl.AesCbc.X86_64 (save setup restore at_ cOff)
open VG.Proof.AesCbc (Mode)
open VG.Proof.AesCbc.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.AesGcm.X86_64 (CtrCall CtrPost ctr_call)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (next toNat ofNat)

/-- The blocks of the call after `k` blocks: what is left, but no further
than where the last 32 bits of the counter block wrap around. -/
def mOf (s₀ : State) (k : Nat) : Nat := min (N s₀ - k) (2 ^ 32 - (toNat (iv0 s₀) + k) % 2 ^ 32)

theorem length_iv0 (s₀ : State) : (iv0 s₀).length = 16 := Proof.Cmac.bytesAt_length _ _ _

theorem mOf_pos {s₀ : State} {k : Nat} (hk : k < N s₀) : 0 < mOf s₀ k := by
  unfold mOf; have := Nat.mod_lt (toNat (iv0 s₀) + k) (show 0 < 2 ^ 32 by decide); omega_using [hk]

theorem mOf_le (s₀ : State) (k : Nat) : mOf s₀ k ≤ N s₀ - k := Nat.min_le_left _ _

theorem lo32_mOf (s₀ : State) (k : Nat) : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k ≤ 2 ^ 32 := by
  rw [AesCtr.lo32_next (length_iv0 s₀)]; unfold mOf; omega_using []

theorem chainK_ctr (s₀ : State) {k : Nat} (hk : k ≤ N s₀) : chainK AesCtr.ctrMode s₀ k = next (iv0 s₀) k := by
  rw [chainK, AesCtr.ctrMode_chain, List.length_take, Proof.AesCbc.length_blocksAt, Nat.min_eq_left hk]

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.seg_wrap {k m : Nat} (hk : k < N s₀) (hkm : k + m ≤ N s₀) : (blk s₀ k).toNat + 16 * m ≤ 2 ^ 64 := by
  have := hp.data_wrap
  have : (blk s₀ k).toNat = (Dp s₀).toNat + 16 * k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * k) (by omega_using [hk, this]),
      Nat.mod_eq_of_lt (by omega_using [hk, this])]
  omega_arith

omit hp in
theorem UPre.seg_sub {k m : Nat} (hkm : k + m ≤ N s₀) : Region.Sub ⟨blk s₀ k, 16 * m⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega_using [hkm])

/-- The arguments of the call after `k` blocks. -/
theorem UPre.ctrCall {k : Nat} (hk : k < N s₀) {s : State}
    (rdi : s.gpr .rdi = W s₀) (rsi : s.gpr .rsi = s₀.gpr .rsi) (rdx : s.gpr .rdx = Iv s₀)
    (rcx : s.gpr .rcx = blk s₀ k) (r8 : s.gpr .r8 = BitVec.ofNat 64 (mOf s₀ k)) (r9 : s.gpr .r9 = S s₀)
    (rsp : s.gpr .rsp = s₀.gpr .rsp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    CtrCall s (W s₀) (Iv s₀) (blk s₀ k) (S s₀) (R s₀) (mOf s₀ k) where
  rdi := rdi
  rsi := by rw [rsi, rsi_ofNat]
  rdx := rdx
  rcx := rcx
  r8 := r8
  r9 := r9
  rounds := hp.rounds
  wrap := UPre.seg_wrap hp hk (by have := mOf_le s₀ k; omega_using [hk, this])
  kc := hp.sch_iv
  kd := hp.sch_data.sub_right (UPre.seg_sub (s₀ := s₀) (by have := mOf_le s₀ k; omega_using [hk, this]))
  ks := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  cd := hp.iv_data.sub_right (UPre.seg_sub (s₀ := s₀) (by have := mOf_le s₀ k; omega_using [hk, this]))
  cs := hp.iv_scr.sub_right (Region.sub_prefix (by decide))
  ds := (hp.data_scr.sub_left (UPre.seg_sub (s₀ := s₀) (by have := mOf_le s₀ k; omega_using [hk, this]))).sub_right (Region.sub_prefix (by decide))
  stkK := by rw [rsp]; exact hp.stk_sch
  stkC := by rw [rsp]; exact hp.stk_iv
  stkD := by rw [rsp]; exact hp.stk_data.sub_right (UPre.seg_sub (s₀ := s₀) (by have := mOf_le s₀ k; omega_using [hk, this]))
  stkS := by rw [rsp]; exact hp.stk_scr.sub_right (Region.sub_prefix (by decide))
  reads := by
    rw [hrd, hwr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨ivR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; have := mOf_le s₀ k; omega_using [hk, this]⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  writes := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; have := mOf_le s₀ k; omega_using [hk, this]⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

/-- What the code before the call leaves. -/
structure Pre (s₀ : State) (k : Nat) (s s₁ : State) : Prop where
  call : CtrCall s₁ (W s₀) (Iv s₀) (blk s₀ k) (S s₀) (R s₀) (mOf s₀ k)
  saved : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r
  mem : s₁.mem = s.mem.writeW (S s₀ + BitVec.ofNat 64 2048) (BitVec.ofNat 64 (mOf s₀ k))
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

omit hp in
theorem count_eq : count ++ args = ([.mov32 .rax (.mem (at_ .r12 12)), .bswap32 .rax] : List Instr) ++
    (([.movImm64 .rcx 0x100000000, .alu .sub .rcx (.reg .rax)] : List Instr) ++
      (([.alu .cmp .r14 (.reg .rcx), .cmov .b .rcx (.reg .r14)] : List Instr) ++
        (([.store (at_ .r15 cOff) .rcx] : List Instr) ++ args))) := rfl

theorem pre_wp {k : Nat} (hk : k < N s₀) {s : State} (h : LInv AesCtr.ctrMode s₀ k s) :
    WP isa (.block (count ++ args)) s (Pre s₀ k s) := by
  have hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  have hb : N s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt
  obtain ⟨s₁, run₁, rax₁, g₁, mem₁, rd₁, wr₁⟩ := countA_ok s h.r12
    (by rw [hR]; exact in_rw (r := ivR s₀) (by simp) (Offset.contains_base _ (by decide) (by decide)))
  obtain ⟨s₂, run₂, rcx₂, g₂, mem₂, rd₂, wr₂⟩ := countB1_ok s₁ rax₁
  obtain ⟨s₃, run₃, rcx₃, g₃, mem₃, rd₃, wr₃⟩ := countB2_ok s₂
    (by rw [g₂ _ (by decide), g₁ _ (by decide), h.r14]) rcx₂
  obtain ⟨s₄, run₄, gpr₄, mem₄, rd₄, wr₄⟩ := store_ok s₃ (S := S s₀)
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), h.r15])
    (by rw [wr₃, wr₂, wr₁, hW]; exact in_rw (by simp) cSv0)
  obtain ⟨s₅, run₅, rdi₅, rsi₅, rdx₅, r8₅, rcx₅, r9₅, cs₅, mem₅, rd₅, wr₅⟩ := args_ok s₄
  rw [count_eq, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₄, run₄, WP.of_runBlock ⟨s₅, run₅, ?_⟩⟩
  -- The number of blocks.
  have hiv : bytesAt s.mem (Iv s₀) 16 = next (iv0 s₀) k := by rw [h.iv, chainK_ctr s₀ (by omega_using [hk])]
  have hlo := lo32_bytesAt s.mem (Iv s₀)
  rw [hiv, AesCtr.lo32_next (length_iv0 s₀)] at hlo
  have hm : s₃.gpr .rcx = BitVec.ofNat 64 (mOf s₀ k) := by
    rw [rcx₃]
    generalize hc : rv32 (s.mem.readW (Iv s₀ + BitVec.ofNat 64 12) 32) = c at hlo
    have e := sub32_toNat c
    have hl : (BitVec.ofNat 64 (N s₀ - k)).toNat = N s₀ - k := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hb])]
    unfold mOf
    rw [e, hl, hlo]
    have hcl := c.isLt
    by_cases hlt : N s₀ - k < 2 ^ 32 - c.toNat
    · simp only [hlt, ↓reduceIte]
      rw [Nat.min_eq_left (by omega_using [hlt])]
    · simp only [hlt, ↓reduceIte]
      rw [Nat.min_eq_right (by omega_using [hlt])]
      apply BitVec.eq_of_toNat_eq
      rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [])]
  have keep (r : Reg) (hr : r ∈ calleeSaved) : s₅.gpr r = s.gpr r := by
    have h1 : r ≠ .rax := calleeSaved_ne_rax hr
    have h2 : r ≠ .rcx := by rintro rfl; simp [calleeSaved] at hr
    rw [cs₅ r hr, gpr₄, g₃ r h2, g₂ r h2, g₁ r h1]
  have g4 (r : Reg) (hr : r ∈ calleeSaved) : s₄.gpr r = s.gpr r := by
    have h1 : r ≠ .rax := calleeSaved_ne_rax hr
    have h2 : r ≠ .rcx := by rintro rfl; simp [calleeSaved] at hr
    rw [gpr₄, g₃ r h2, g₂ r h2, g₁ r h1]
  refine ⟨UPre.ctrCall hp hk
    (by rw [rdi₅, g4 .rbx (by simp [calleeSaved]), h.rbx]) (by rw [rsi₅, g4 .rbp (by simp [calleeSaved]), h.rbp])
    (by rw [rdx₅, g4 .r12 (by simp [calleeSaved]), h.r12]) (by rw [rcx₅, g4 .r13 (by simp [calleeSaved]), h.r13])
    (by rw [r8₅, gpr₄, hm]) (by rw [r9₅, g4 .r15 (by simp [calleeSaved]), h.r15])
    (by rw [keep .rsp (by simp [calleeSaved]), h.rsp]) (by rw [rd₅, rd₄, rd₃, rd₂, rd₁, h.rd])
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁, h.wr]), keep, ?_, by rw [rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  rw [mem₅, mem₄, hm, mem₃, mem₂, mem₁]

end

end VG.Proof.AesCtr.X86_64

end

end

/-!
# AES-CTR on x86-64: one iteration

`iter_wp`: one run of `body` takes AES-CBC's loop invariant for `ctrMode`
from `k` blocks to `k + mOf s₀ k`, and sets ZF if no blocks are left.
-/

@[expose] public section

namespace VG.Proof.AesCtr.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCtr.X86_64
open VG.Impl.AesCbc.X86_64 (at_ cOff)
open VG.Proof.AesCbc.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.AesGcm.X86_64 (CtrCall CtrPost ctr_call)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (next toNat ofNat)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- What the call leaves, after `k` blocks. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = W s₀
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r12 : s.gpr .r12 = Iv s₀
  r13 : s.gpr .r13 = blk s₀ k
  r14 : s.gpr .r14 = BitVec.ofNat 64 (N s₀ - k)
  r15 : s.gpr .r15 = S s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩, gR s₀, stkR s₀] (savedMem s₀) s.mem
  slot : s.mem.readW (S s₀ + BitVec.ofNat 64 2048) 64 = BitVec.ofNat 64 (mOf s₀ k)
  data : Spec.Cbc.blocksAt s.mem (Dp s₀) (N s₀) =
    outK AesCtr.ctrMode s₀ (k + mOf s₀ k) ++ (blks s₀).drop (k + mOf s₀ k)
  /-- The counter block: `t + k + m`, less `2³²` if its last 32 bits
  wrapped around. -/
  iv : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k < 2 ^ 32 →
    bytesAt s.mem (Iv s₀) 16 = next (iv0 s₀) (k + mOf s₀ k)
  ivw : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32 →
    bytesAt s.mem (Iv s₀) 16 = ofNat (toNat (next (iv0 s₀) k) + mOf s₀ k - 2 ^ 32) 16

/-- The call, after the code before it. -/
theorem mid_wp (v : Ctr32Impl) {k : Nat} (hk : k < N s₀) {s s₁ : State} (h : LInv AesCtr.ctrMode s₀ k s)
    (a : Pre s₀ k s s₁) : WP isa (.call v.callee.name v.callee.code) s₁ (Mid s₀ k) := by
  refine WP.mono (ctr_call v a.call) fun s₂ c => ?_
  have g (r : Reg) (hr : r ∈ calleeSaved) : s₂.gpr r = s.gpr r := by rw [c.saved r hr, a.saved r hr]
  obtain hm0 := mOf_pos hk
  obtain hle := mOf_le s₀ k
  have hdw := hp.data_wrap
  have hsw := hp.scr_wrap
  generalize hmd : mOf s₀ k = m at hm0 hle a c
  obtain hrsp : s₁.gpr .rsp = s₀.gpr .rsp := by rw [a.saved .rsp (by simp [calleeSaved]), h.rsp]
  -- The memory before the call: the slot written.
  obtain f₁ : Frame [⟨S s₀ + BitVec.ofNat 64 2048, 8⟩] s.mem s₁.mem := by
    rw [a.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain slotSub : Region.Sub ⟨S s₀ + BitVec.ofNat 64 2048, 8⟩ ⟨S s₀, 2064⟩ := Offset.sub_base _ (by decide)
  obtain segSub : Region.Sub ⟨blk s₀ k, 16 * m⟩ (dataR s₀) := UPre.seg_sub (by omega_arith)
  have fc : Frame [⟨Iv s₀, 16⟩, ⟨blk s₀ k, 16 * m⟩, ⟨S s₀, 2048⟩, below (s₁.gpr .rsp) 8] s₁.mem s₂.mem := c.frame
  rw [hrsp] at fc
  obtain fAll : Frame [ivR s₀, dataR s₀, ⟨S s₀, 2064⟩, gR s₀, stkR s₀] s.mem s₂.mem :=
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, slotSub⟩).trans
    (fc.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨dataR s₀, by simp, segSub⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  -- The slot after the call.
  obtain dSlot : ∀ r ∈ [⟨Iv s₀, 16⟩, ⟨blk s₀ k, 16 * m⟩, ⟨S s₀, 2048⟩, stkR s₀],
      (⟨S s₀ + BitVec.ofNat 64 2048, 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.iv_scr.symm.sub_left (UPre.scr_sub (by decide))
    · exact (hp.data_scr.symm.sub_left (UPre.scr_sub (by decide))).sub_right segSub
    · exact Offset.disjoint_base _ (by decide) (by omega_arith)
    · exact hp.stk_scr.symm.sub_left (UPre.scr_sub (by decide))
  obtain slot : s₂.mem.readW (S s₀ + BitVec.ofNat 64 2048) 64 = BitVec.ofNat 64 m := by
    rw [fc.readW (r := ⟨S s₀ + BitVec.ofNat 64 2048, 8⟩) (Region.contains_self _ _) dSlot (by decide),
      a.mem, Mem.readW_writeW_self64, hmd]
  -- The data and the counter block before the call.
  obtain hiv : bytesAt s.mem (Iv s₀) 16 = next (iv0 s₀) k := by rw [h.iv, chainK_ctr s₀ (by omega_arith)]
  obtain ivIn : bytesAt s₁.mem (Iv s₀) 16 = next (iv0 s₀) k := by
    rw [Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.iv_scr.sub_right (UPre.scr_sub (by decide))) (by decide), hiv]
  obtain big₁ : Frame (Big s₀) s₀.mem s₁.mem := (UPre.big_ofG h.frame).trans (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩)
  obtain sched : bytesAt s₁.mem (W s₀) (16 * (R s₀ + 1)) = wK s₀ := UPre.sched_bytes hp big₁
  obtain hlen : (blks s₀).length = N s₀ := Proof.AesCbc.length_blocksAt _ _ _
  obtain hlk : (outK AesCtr.ctrMode s₀ k).length = k := by
    rw [outK, AesCtr.ctrMode_out, AesCtr.length_crypt, List.length_take, hlen, Nat.min_eq_left (by omega_arith)]
  -- Blocks outside the call's.
  have outside (j : Nat) (hj : j < N s₀) (ho : j < k ∨ k + m ≤ j) :
      ∀ r ∈ [⟨S s₀ + BitVec.ofNat 64 2048, 8⟩, ⟨Iv s₀, 16⟩, ⟨blk s₀ k, 16 * m⟩, ⟨S s₀, 2048⟩, stkR s₀],
        (⟨Dp s₀ + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint r := by
    intro r hr
    obtain dj : Region.Sub ⟨Dp s₀ + BitVec.ofNat 64 (16 * j), 16⟩ (dataR s₀) := Offset.sub_base _ (by omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.data_scr.sub_left dj).sub_right (UPre.scr_sub (by decide))
    · exact (hp.iv_data.symm.sub_left dj)
    · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    · exact (hp.data_scr.sub_left dj).sub_right (Region.sub_prefix (by decide))
    · exact hp.stk_data.symm.sub_left dj
  have keepBlocks {p : Addr} {a n : Nat} (hp' : p = Dp s₀ + BitVec.ofNat 64 (16 * a)) (hn : a + n ≤ N s₀)
      (ho : a + n ≤ k ∨ k + m ≤ a) : Spec.Cbc.blocksAt s₂.mem p n = Spec.Cbc.blocksAt s.mem p n := by
    subst hp'
    obtain hd : ∀ j < n, ∀ r ∈ [⟨S s₀ + BitVec.ofNat 64 2048, 8⟩, ⟨Iv s₀, 16⟩, ⟨blk s₀ k, 16 * m⟩, ⟨S s₀, 2048⟩,
        stkR s₀], (⟨Dp s₀ + BitVec.ofNat 64 (16 * a) + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint r :=
      fun j hj => by
        rw [Offset.add_add, show 16 * a + 16 * j = 16 * (a + j) by omega_arith]
        exact outside (a + j) (by omega_arith) (by omega_arith)
    rw [AesCtr.blocksAt_frame fc (fun j hj r hr => hd j hj r (List.mem_cons_of_mem _ hr)),
      AesCtr.blocksAt_frame f₁ (fun j hj r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hd j hj _ (by simp))]
  have dataS := h.data
  rw [outK, AesCtr.ctrMode_out] at dataS
  -- The call's blocks.
  obtain segIn : Spec.Cbc.blocksAt s₁.mem (blk s₀ k) m = ((blks s₀).drop k).take m := by
    rw [AesCtr.blocksAt_frame f₁ (fun j hj r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [Offset.add_add, show 16 * k + 16 * j = 16 * (k + j) by omega_arith]
      exact (hp.data_scr.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (UPre.scr_sub (by decide))),
      ← AesCtr.blocksAt_take _ _ (show m ≤ N s₀ - k by omega_arith), ← AesCtr.blocksAt_drop _ _ (by omega_arith), dataS,
      List.drop_left' (by rw [AesCtr.length_crypt, List.length_take, hlen, Nat.min_eq_left (by omega_arith)])]
  obtain seg := AesCtr.ctr32_crypt (k := m) (by rw [ivIn, ← hmd]; exact lo32_mOf s₀ k) c.out
  rw [sched, ivIn, segIn] at seg
  have hctr := c.ctr
  rw [show Spec.Gcm.blockAt s₁.mem (Iv s₀) = Spec.Gcm.ofBytes (bytesAt s₁.mem (Iv s₀) 16) from rfl] at hctr
  refine ⟨by rw [g .rbx (by simp [calleeSaved]), h.rbx], by rw [g .rbp (by simp [calleeSaved]), h.rbp],
    by rw [g .r12 (by simp [calleeSaved]), h.r12], by rw [g .r13 (by simp [calleeSaved]), h.r13],
    by rw [g .r14 (by simp [calleeSaved]), h.r14], by rw [g .r15 (by simp [calleeSaved]), h.r15],
    by rw [g .rsp (by simp [calleeSaved]), h.rsp], by rw [c.rd, a.rd, h.rd], by rw [c.wr, a.wr, h.wr],
    h.frame.trans fAll, by rw [hmd]; exact slot, ?_, ?_, ?_⟩
  · -- The data: the first `k` blocks and those after the call's as they were, and the call's.
    obtain hlc : (Spec.Ctr.crypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀) ((blks s₀).take k)).length = k := by
      rw [AesCtr.length_crypt, List.length_take, hlen, Nat.min_eq_left (by omega_arith)]
    obtain hA : Spec.Cbc.blocksAt s.mem (Dp s₀) k =
        Spec.Ctr.crypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀) ((blks s₀).take k) := by
      rw [← AesCtr.blocksAt_take _ _ (show k ≤ N s₀ by omega_arith), dataS, List.take_left' hlc]
    obtain hC : Spec.Cbc.blocksAt s.mem (Dp s₀ + BitVec.ofNat 64 (16 * (k + m))) (N s₀ - (k + m)) =
        (blks s₀).drop (k + m) := by
      rw [← AesCtr.blocksAt_drop _ _ (show k + m ≤ N s₀ by omega_arith), dataS]
      conv => lhs; rw [show k + m = (Spec.Ctr.crypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀)
        ((blks s₀).take k)).length + m by rw [hlc]]
      rw [List.drop_append, List.drop_eq_nil_of_le (by omega_arith), List.nil_append, hlc, Nat.add_sub_cancel_left]
      exact List.drop_drop
    rw [hmd, AesCtr.blocksAt_three s₂.mem (Dp s₀) (a := k) (b := m) (by omega_arith),
      keepBlocks (a := 0) (by simp) (by omega_arith) (by omega_arith), keepBlocks (a := k + m) rfl (by omega_arith) (by omega_arith),
      show Dp s₀ + BitVec.ofNat 64 (16 * k) = blk s₀ k from rfl, seg, hA, hC, outK, AesCtr.ctrMode_out]
    exact AesCtr.crypt_step _ _ _ (by omega_arith)
  · intro hw
    rw [hmd] at hw
    rw [hmd, AesCtr.ctr32_next (by rw [ivIn]; omega_arith) c.ctr, ivIn, AesCtr.next_add]
  · intro hw
    rw [hmd] at hw
    rw [hmd, AesCtr.ctr32_wrap (by rw [ivIn]; omega_arith) c.ctr, ivIn]

omit hp in
theorem test_ok (s : State) :
    ∃ s', runBlock isa [.alu .test .r14 (.reg .r14)] s = some s' ∧ s'.zf = some (s.gpr .r14 == 0) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]; exact rfl,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [zf_arithFlags, BitVec.and_self]
  all_goals rfl

/-- The invariant after `k + m` blocks, from the facts the iteration ends with. -/
theorem finish {k m : Nat} (hkm : k + m ≤ N s₀) {s s' : State} (h : Mid s₀ k s) (hmd : mOf s₀ k = m)
    (g : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r)
    (r13 : s'.gpr .r13 = blk s₀ (k + m)) (r14 : s'.gpr .r14 = BitVec.ofNat 64 (N s₀ - (k + m)))
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame [ivR s₀] s.mem s'.mem)
    (hiv : bytesAt s'.mem (Iv s₀) 16 = next (iv0 s₀) (k + m)) :
    LInv AesCtr.ctrMode s₀ (k + m) s' where
  rbx := by rw [g .rbx (by decide) (by decide) (by decide) (by decide) (by decide), h.rbx]
  rbp := by rw [g .rbp (by decide) (by decide) (by decide) (by decide) (by decide), h.rbp]
  r12 := by rw [g .r12 (by decide) (by decide) (by decide) (by decide) (by decide), h.r12]
  r13 := r13
  r14 := r14
  r15 := by rw [g .r15 (by decide) (by decide) (by decide) (by decide) (by decide), h.r15]
  rsp := by rw [g .rsp (by decide) (by decide) (by decide) (by decide) (by decide), h.rsp]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  frame := h.frame.trans (hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨ivR s₀, by simp, fun _ h => h⟩)
  data := by
    rw [AesCtr.blocksAt_frame hf (fun j hj r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.iv_data.symm.sub_left (Offset.sub_base _ (by omega_arith))), h.data, hmd]
  iv := by rw [hiv, chainK_ctr s₀ hkm]

omit hp in
theorem adv_eq : adv = ([.mov .rax (.mem (at_ .r15 cOff)), .alu .sub .r14 (.reg .rax), .shift .shl .rax 4,
    .alu .add .r13 (.reg .rax)] : List Instr) ++
      ([.mov32 .rax (.mem (at_ .r12 12)), .alu32 .test .rax (.reg .rax)] : List Instr) := rfl

/-- What `adv` leaves. -/
structure After (s₀ : State) (k : Nat) (s s₂ : State) : Prop where
  gpr : ∀ r, r ≠ .rax → r ≠ .r13 → r ≠ .r14 → s₂.gpr r = s.gpr r
  r13 : s₂.gpr .r13 = blk s₀ (k + mOf s₀ k)
  r14 : s₂.gpr .r14 = BitVec.ofNat 64 (N s₀ - (k + mOf s₀ k))
  mem : s₂.mem = s.mem
  rd : s₂.rd = s.rd
  wr : s₂.wr = s.wr
  zf : s₂.zf = some (decide (AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32))

/-- On past the call's blocks, and ZF set if the counter wrapped around. -/
theorem adv_wp {k : Nat} (hk : k < N s₀) {s : State} (h : Mid s₀ k s) : WP isa (.block adv) s (After s₀ k s) := by
  obtain hm0 := mOf_pos hk
  obtain hle := mOf_le s₀ k
  obtain hlo := lo32_mOf s₀ k
  have hdw := hp.data_wrap
  obtain hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  obtain hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  obtain ⟨s₁, run₁, r14₁, r13₁, g₁, mem₁, rd₁, wr₁⟩ := advA_ok s h.r15 h.r13 h.r14 h.slot (by omega_arith) (by omega_arith)
    (by rw [hR]; exact in_rw (by simp) cSv0)
  obtain ⟨s₂, run₂, zf₂, g₂, mem₂, rd₂, wr₂⟩ := advB_ok s₁ (Q := Iv s₀)
    (by rw [g₁ _ (by decide) (by decide) (by decide), h.r12])
    (by rw [rd₁, wr₁, hR]; exact in_rw (r := ivR s₀) (by simp) (Offset.contains_base _ (by decide) (by decide)))
  rw [adv_eq, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩
  have g (r : Reg) (h1 : r ≠ .rax) (h13 : r ≠ .r13) (h14 : r ≠ .r14) : s₂.gpr r = s.gpr r := by
    rw [g₂ r h1, g₁ r h1 h13 h14]
  obtain r13₂ : s₂.gpr .r13 = blk s₀ (k + mOf s₀ k) := by
    rw [g₂ _ (by decide), r13₁, Offset.add_add, show 16 * k + 16 * mOf s₀ k = 16 * (k + mOf s₀ k) by omega_arith]
  obtain r14₂ : s₂.gpr .r14 = BitVec.ofNat 64 (N s₀ - (k + mOf s₀ k)) := by rw [g₂ _ (by decide), r14₁, Nat.sub_sub]
  obtain m₂ : s₂.mem = s.mem := by rw [mem₂, mem₁]
  obtain hb := AesCtr.toNat_lt (show (next (iv0 s₀) k).length = 16 by
    rw [AesCtr.next_eq (length_iv0 s₀)]; exact AesCtr.length_ofNat _ _)
  obtain hlo2 := lo32_bytesAt s.mem (Iv s₀)
  obtain zfE : s₂.zf = some (decide (AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32)) := by
    rw [zf₂, mem₁]
    by_cases hw : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32
    · have e := h.ivw hw
      rw [e, AesCtr.lo32, AesCtr.toNat_ofNat] at hlo2
      have hw' := hw
      unfold AesCtr.lo32 at hw'
      have : (rv32 (s.mem.readW (Iv s₀ + BitVec.ofNat 64 12) 32)).toNat = 0 := by rw [← hlo2]; omega_arith
      obtain h0 := AesCtr.rv32_eq_zero.mp (BitVec.eq_of_toNat_eq this)
      simp [h0, hw]
    · have e := h.iv (by omega_arith)
      rw [e, AesCtr.lo32_next (length_iv0 s₀)] at hlo2
      rw [AesCtr.lo32_next (length_iv0 s₀)] at hw hlo
      have : (rv32 (s.mem.readW (Iv s₀ + BitVec.ofNat 64 12) 32)).toNat ≠ 0 := by rw [← hlo2]; omega_arith
      obtain h0 : s.mem.readW (Iv s₀ + BitVec.ofNat 64 12) 32 ≠ 0 := fun h0 => this (by rw [h0]; rfl)
      rw [AesCtr.lo32_next (length_iv0 s₀)]
      simp only [hw, decide_false, Option.some.injEq, beq_eq_false_iff_ne]
      exact h0
  exact ⟨g, r13₂, r14₂, m₂, by rw [rd₂, rd₁], by rw [wr₂, wr₁], zfE⟩

/-- The carry if the counter wrapped around, and ZF set if no blocks are
left. -/
theorem fin_wp {k : Nat} (hk : k < N s₀) {s s₂ : State} (h : Mid s₀ k s) (a : After s₀ k s s₂) :
    WP isa (.seq (.ite .e (.block carry) (.block [])) (.block [.alu .test .r14 (.reg .r14)])) s₂
      fun s' => LInv AesCtr.ctrMode s₀ (k + mOf s₀ k) s' ∧ s'.zf = some (decide (k + mOf s₀ k = N s₀)) := by
  obtain hm0 := mOf_pos hk
  obtain hle := mOf_le s₀ k
  have hdw := hp.data_wrap
  obtain hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  obtain hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  have g := a.gpr
  have r13₂ := a.r13
  have r14₂ := a.r14
  have m₂ := a.mem
  have zfE := a.zf
  obtain hNb : N s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt
  obtain r12₂ : s₂.gpr .r12 = Iv s₀ := by rw [g _ (by decide) (by decide) (by decide), h.r12]
  have rd₂' : s₂.rd = s.rd := a.rd
  have wr₂' : s₂.wr = s.wr := a.wr
  have zfEnd (t : State) (h14 : t.gpr .r14 = BitVec.ofNat 64 (N s₀ - (k + mOf s₀ k))) :
      some (t.gpr .r14 == 0) = some (decide (k + mOf s₀ k = N s₀)) := by
    rw [h14, AesCbc.X86_64.beq_zero (by omega_arith)]
    simp only [Option.some.injEq, decide_eq_decide]
    omega_arith
  refine WP.seq ?_
  by_cases hw : AesCtr.lo32 (next (iv0 s₀) k) + mOf s₀ k = 2 ^ 32
  · have ev : isa.eval .e s₂ = some true := by
      show s₂.zf = _; rw [zfE]; simp [hw]
    refine WP.ite true ev (fun _ => ?_) (fun h => by cases h)
    obtain ⟨s₃, run₃, g₃, bytes₃, f₃, rd₃, wr₃⟩ := carry_ok s₂ r12₂
      (by rw [rd₂', wr₂', hR]; exact in_rw (r := ivR s₀) (by simp) cIv0)
      (by rw [rd₂', wr₂', hR]; exact in_rw (r := ivR s₀) (by simp) cIv8)
      (by rw [wr₂', hW]; exact in_rw (r := ivR s₀) (by simp) cIv0)
      (by rw [wr₂', hW]; exact in_rw (r := ivR s₀) (by simp) cIv8)
    obtain ⟨s₄, run₄, zf₄, gpr₄, mem₄, rd₄, wr₄⟩ := test_ok s₃
    refine WP.of_runBlock ⟨s₃, run₃, WP.of_runBlock ⟨s₄, run₄, ?_⟩⟩
    have g4 (r : Reg) (h1 : r ≠ .rax) (h2 : r ≠ .rcx) (h3 : r ≠ .rdx) : s₄.gpr r = s₂.gpr r := by
      rw [gpr₄, g₃ r h1 h2 h3]
    refine ⟨finish hp (by omega_arith) h rfl (fun r h1 h2 h3 h13 h14 => by rw [g4 r h1 h2 h3, g r h1 h13 h14])
      (by rw [g4 _ (by decide) (by decide) (by decide), r13₂]) (by rw [g4 _ (by decide) (by decide) (by decide), r14₂])
      (by rw [rd₄, rd₃, rd₂']) (by rw [wr₄, wr₃, wr₂']) ?_ ?_, ?_⟩
    · rw [mem₄, ← m₂]; exact f₃
    · rw [mem₄, bytes₃, m₂, h.ivw hw]
      exact AesCtr.carry_next (length_iv0 s₀) hw
    · rw [zf₄, zfEnd s₃ (by rw [g₃ _ (by decide) (by decide) (by decide), r14₂])]
  · have ev : isa.eval .e s₂ = some false := by
      show s₂.zf = _; rw [zfE]; simp [hw]
    refine WP.ite false ev (fun h => by cases h) (fun _ => WP.block_nil ?_)
    obtain ⟨s₄, run₄, zf₄, gpr₄, mem₄, rd₄, wr₄⟩ := test_ok s₂
    refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
    refine ⟨finish hp (by omega_arith) h rfl (fun r h1 h2 h3 h13 h14 => by rw [gpr₄, g r h1 h13 h14])
      (by rw [gpr₄, r13₂]) (by rw [gpr₄, r14₂]) (by rw [rd₄, rd₂']) (by rw [wr₄, wr₂'])
      (by rw [mem₄, m₂]; exact Frame.refl _ _) ?_, ?_⟩
    · rw [mem₄, m₂, h.iv (by have := lo32_mOf s₀ k; omega_arith)]
    · rw [zf₄, zfEnd s₂ r14₂]

/-- On past the call's blocks, the carry if the counter wrapped around, and
ZF set if no blocks are left. -/
theorem tail_wp {k : Nat} (hk : k < N s₀) {s : State} (h : Mid s₀ k s) :
    WP isa (.seq (.block adv) (.seq (.ite .e (.block carry) (.block [])) (.block [.alu .test .r14 (.reg .r14)]))) s
      fun s' => LInv AesCtr.ctrMode s₀ (k + mOf s₀ k) s' ∧ s'.zf = some (decide (k + mOf s₀ k = N s₀)) :=
  WP.seq (WP.mono (adv_wp hp hk h) fun _ a => fin_wp hp hk h a)

/-- One iteration. -/
theorem iter_wp (v : Ctr32Impl) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv AesCtr.ctrMode s₀ k s) :
    WP isa (body v.callee) s
      fun s' => LInv AesCtr.ctrMode s₀ (k + mOf s₀ k) s' ∧ s'.zf = some (decide (k + mOf s₀ k = N s₀)) :=
  WP.seq (WP.mono (pre_wp hp hk h) fun _ a =>
    WP.seq (WP.mono (mid_wp hp v hk h a) fun _ hm => tail_wp hp hk hm))

/-- The loop, from `k` blocks to all of them. -/
theorem loop_wp (v : Ctr32Impl) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv AesCtr.ctrMode s₀ k s) :
    WP isa (.loop (body v.callee) .ne) s (LInv AesCtr.ctrMode s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := body v.callee) (c := .ne) (Q := LInv AesCtr.ctrMode s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv AesCtr.ctrMode s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨j, rfl, hj, h⟩
  refine WP.mono (iter_wp hp v hj h) fun s' ⟨h', hz⟩ => ?_
  obtain hm0 := mOf_pos hj
  obtain hle := mOf_le s₀ j
  obtain ev : isa.eval .ne s' = some !decide (j + mOf s₀ j = N s₀) := by
    show VG.X86_64.eval .ne s' = _; simp [VG.X86_64.eval, hz]
  by_cases hz' : j + mOf s₀ j = N s₀
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [← hz']
  · right
    refine ⟨by rw [ev]; simp [hz'], N s₀ - (j + mOf s₀ j), by omega_arith, j + mOf s₀ j, rfl, by omega_arith, h'⟩

end

/-- The whole function. -/
theorem crypt_wp (v : Ctr32Impl) {s₀ : State} (h0 : (modeX86_64 AesCtr.ctrMode).pre s₀) :
    WP isa (crypt v.callee) s₀ fun s' => gprPreserved s₀ s' ∧ (modeX86_64 AesCtr.ctrMode).post s₀ s' :=
  ends_wp h0 fun hp hN _ h => loop_wp hp v hN h

end VG.Proof.AesCtr.X86_64

end

end

/-!
# AES-CTR on x86-64: constant time

Two runs from states that agree on the public arguments and on the last 32
bits of the counter block (`ctrPub`, which the contract's `leak` declares)
are related piece by piece (`RelCT`): the taint analysis covers the code
between the call and the branches, from the registers the correctness proof
pins to the public arguments; the call is constant time by its own proof
(AES-GCM's `ctr_rel`), with the same arguments in both runs, since the
number of blocks it takes depends only on the public data (`mOf_eq`); and
the branches (the carry, the loop) are on facts the correctness proof gives
in terms of the public data (`After.zf`, `iter_wp`).
-/

@[expose] public section

namespace VG.Proof.AesCtr.X86_64

open VG VG.X86_64 VG.Impl.AesCtr.X86_64
open VG.Impl.AesCbc.X86_64 (save setup restore)
open VG.Proof.AesCbc.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.AesGcm.X86_64 (ctr_rel)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (next toNat)

/-- What two runs agree on: the public arguments, and the last 32 bits of the
counter block. -/
def ctrPub (s₀ s₀' : State) : Prop :=
  (modeX86_64 AesCtr.ctrMode).pub s₀ s₀' ∧ AesCtr.lo32 (iv0 s₀) = AesCtr.lo32 (iv0 s₀')

/-- A piece of code the taint analysis checks from the registers `rs`, which
agree in two runs, with what each run reaches. -/
theorem taint_rel {P : State → State → Prop} {c : Prog isa} {F₁ F₂ : State → Prop} (rs : List Reg)
    (ht : ∃ h, (taint.check (Taint.ofRegs rs) c h).isSome = true)
    (ha : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hw : ∀ s₁ s₂, P s₁ s₂ → WP isa c s₁ F₁ ∧ WP isa c s₂ F₂) :
    RelCT isa P c fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂ := by
  obtain ⟨_, ht⟩ := ht
  exact ((RelCT.taint (A := taint) (P := P) _ (fun s₁ s₂ h => Taint.agree_ofRegs (ha s₁ s₂ h)) ht).wp hw).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
    (.block (count ++ args)) h).isSome = true := ⟨_, by taint_decide⟩

theorem adv_taint : ∃ h, (taint.check (Taint.ofRegs [.r12, .r13, .r14, .r15, .rsp]) (.block adv) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem carry_taint : ∃ h, (taint.check (Taint.ofRegs [.r12]) (.block carry) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem nil_taint : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true := ⟨_, by taint_decide⟩

theorem test_taint : ∃ h, (taint.check (Taint.ofRegs []) (.block [.alu .test .r14 (.reg .r14)]) h).isSome = true :=
  ⟨_, by taint_decide⟩

section
variable {s₀ s₀' : State} (hq : (modeX86_64 AesCtr.ctrMode).pub s₀ s₀')
  (hl : AesCtr.lo32 (iv0 s₀) = AesCtr.lo32 (iv0 s₀'))
include hq hl

omit hq in
theorem lo32_next_eq (k : Nat) : AesCtr.lo32 (next (iv0 s₀) k) = AesCtr.lo32 (next (iv0 s₀') k) := by
  rw [AesCtr.lo32_next (length_iv0 _), AesCtr.lo32_next (length_iv0 _)]
  unfold AesCtr.lo32 at hl
  omega_using [hl]

theorem mOf_eq (k : Nat) : mOf s₀ k = mOf s₀' k := by
  have e := lo32_next_eq hl k
  rw [AesCtr.lo32_next (length_iv0 _), AesCtr.lo32_next (length_iv0 _)] at e
  unfold mOf
  rw [e, pub_N hq]

/-- One iteration, in two runs. -/
theorem body_rel (v : Ctr32Impl) (hp : UPre s₀) (hp' : UPre s₀') {k : Nat} (hk : k < N s₀) :
    RelCT isa (fun a b => LInv AesCtr.ctrMode s₀ k a ∧ LInv AesCtr.ctrMode s₀' k b) (body v.callee)
      fun a b => (LInv AesCtr.ctrMode s₀ (k + mOf s₀ k) a ∧ a.zf = some (decide (k + mOf s₀ k = N s₀))) ∧
        (LInv AesCtr.ctrMode s₀' (k + mOf s₀' k) b ∧ b.zf = some (decide (k + mOf s₀' k = N s₀'))) := by
  have hk' : k < N s₀' := by rw [← pub_N hq]; exact hk
  -- The code before the call.
  have p1 := taint_rel _ pre_taint (P := fun a b => LInv AesCtr.ctrMode s₀ k a ∧ LInv AesCtr.ctrMode s₀' k b)
    (fun _ _ h => LInv.agree hq h.1 h.2)
    (F₁ := fun s₁ => ∃ s, LInv AesCtr.ctrMode s₀ k s ∧ Pre s₀ k s s₁)
    (F₂ := fun s₁ => ∃ s, LInv AesCtr.ctrMode s₀' k s ∧ Pre s₀' k s s₁)
    fun a b h => ⟨WP.mono (pre_wp hp hk h.1) fun _ x => ⟨a, h.1, x⟩,
      WP.mono (pre_wp hp' hk' h.2) fun _ x => ⟨b, h.2, x⟩⟩
  -- The call, with the same arguments in both runs.
  have p2 := (ctr_rel v (P := fun a b => (∃ s, LInv AesCtr.ctrMode s₀ k s ∧ Pre s₀ k s a) ∧
      (∃ s, LInv AesCtr.ctrMode s₀' k s ∧ Pre s₀' k s b)) fun a b h => by
    obtain ⟨⟨s, hs, pa⟩, ⟨t, ht, pb⟩⟩ := h
    refine ⟨_, _, _, _, _, _, pa.call, ?_, ?_⟩
    · rw [pub_W hq, pub_Iv hq, pub_blk hq, pub_S hq, pub_R hq, mOf_eq hq hl]; exact pb.call
    · rw [pa.saved .rsp (by simp [calleeSaved]), pb.saved .rsp (by simp [calleeSaved]), hs.rsp, ht.rsp,
        pub_rsp hq]).wp
    (F₁ := Mid s₀ k) (F₂ := Mid s₀' k) fun a b h => by
      obtain ⟨⟨s, hs, pa⟩, ⟨t, ht, pb⟩⟩ := h
      exact ⟨mid_wp hp v hk hs pa, mid_wp hp' v hk' ht pb⟩
  -- On past the call's blocks.
  have p3 := taint_rel _ adv_taint (P := fun a b => Mid s₀ k a ∧ Mid s₀' k b)
    (fun a b h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.1.r12, h.2.r12, pub_Iv hq]
      · rw [h.1.r13, h.2.r13, pub_blk hq]
      · rw [h.1.r14, h.2.r14, pub_N hq]
      · rw [h.1.r15, h.2.r15, pub_S hq]
      · rw [h.1.rsp, h.2.rsp, pub_rsp hq])
    (F₁ := fun s₂ => ∃ s, Mid s₀ k s ∧ After s₀ k s s₂) (F₂ := fun s₂ => ∃ s, Mid s₀' k s ∧ After s₀' k s s₂)
    fun a b h => ⟨WP.mono (adv_wp hp hk h.1) fun _ x => ⟨a, h.1, x⟩,
      WP.mono (adv_wp hp' hk' h.2) fun _ x => ⟨b, h.2, x⟩⟩
  -- The carry if the counter wrapped around in both runs, and the test.
  have p4 : RelCT isa (fun a b => (∃ s, Mid s₀ k s ∧ After s₀ k s a) ∧ (∃ s, Mid s₀' k s ∧ After s₀' k s b))
      (.seq (.ite .e (.block carry) (.block [])) (.block [.alu .test .r14 (.reg .r14)])) fun _ _ => True := by
    obtain ⟨_, hc⟩ := carry_taint
    obtain ⟨_, hn⟩ := nil_taint
    obtain ⟨_, ht⟩ := test_taint
    refine RelCT.seq (R := fun _ _ => True) (RelCT.ite (fun a b h => ?_)
      (RelCT.taint (A := taint) _ (fun a b h => Taint.agree_ofRegs fun r hr => ?_) hc)
      (RelCT.taint (A := taint) _ (fun _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) hn))
      (RelCT.taint (A := taint) _ (fun _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) ht)
    · obtain ⟨⟨s, hs, xa⟩, ⟨t, ht', xb⟩⟩ := h
      show a.zf = b.zf
      rw [xa.zf, xb.zf, lo32_next_eq hl, mOf_eq hq hl]
    · obtain ⟨⟨⟨s, hs, xa⟩, ⟨t, ht', xb⟩⟩, _⟩ := h
      simp only [List.mem_singleton] at hr; subst hr
      rw [xa.gpr _ (by decide) (by decide) (by decide), xb.gpr _ (by decide) (by decide) (by decide), hs.r12, ht'.r12,
        pub_Iv hq]
  have p5 := p4.wp
    (F₁ := fun (s' : State) => LInv AesCtr.ctrMode s₀ (k + mOf s₀ k) s' ∧ s'.zf = some (decide (k + mOf s₀ k = N s₀)))
    (F₂ := fun (s' : State) => LInv AesCtr.ctrMode s₀' (k + mOf s₀' k) s' ∧ s'.zf = some (decide (k + mOf s₀' k = N s₀')))
    fun a b h => by
      obtain ⟨⟨s, hs, xa⟩, ⟨t, ht', xb⟩⟩ := h
      exact ⟨fin_wp hp hk hs xa, fin_wp hp' hk' ht' xb⟩
  exact p1.seq ((p2.mono (fun _ _ h => h) fun _ _ h => h.2).seq (p3.seq (p5.mono (fun _ _ h => h) fun _ _ h => h.2)))

/-- The loop's relation, with the number of blocks left. -/
def LRel (s₀ s₀' : State) (n : Nat) (a b : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ LInv AesCtr.ctrMode s₀ k a ∧ LInv AesCtr.ctrMode s₀' k b

theorem loop_rel (v : Ctr32Impl) (hp : UPre s₀) (hp' : UPre s₀') (n : Nat) :
    RelCT isa (LRel s₀ s₀' n) (.loop (body v.callee) .ne)
      fun a b => LInv AesCtr.ctrMode s₀ (N s₀) a ∧ LInv AesCtr.ctrMode s₀' (N s₀') b := by
  refine RelCT.loop (M := isa) (LRel s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : LRel s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k < N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have hm := mOf_eq hq hl k
  have hm0 := mOf_pos hk
  have hle := mOf_le s₀ k
  refine (body_rel hq hl v hp hp' hk).mono (fun _ _ h => ⟨h.2.2.1, h.2.2.2⟩)
    fun s₁ s₂ ⟨⟨l₁, z₁⟩, ⟨l₂, z₂⟩⟩ => ?_
  rw [← hm] at l₂
  rw [← hm, ← hN] at z₂
  have e₁ : isa.eval .ne s₁ = some !decide (k + mOf s₀ k = N s₀) := by
    show VG.X86_64.eval .ne s₁ = _; simp [VG.X86_64.eval, z₁]
  have e₂ : isa.eval .ne s₂ = some !decide (k + mOf s₀ k = N s₀) := by
    show VG.X86_64.eval .ne s₂ = _; simp [VG.X86_64.eval, z₂]
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : k + mOf s₀ k = N s₀ := by simpa using hf
    exact ⟨h0 ▸ l₁, by rw [← hN, ← h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : k + mOf s₀ k ≠ N s₀ := by simpa using ht
    exact ⟨N s₀ - (k + mOf s₀ k), by omega_using [hk, hm0], k + mOf s₀ k, rfl, by omega_using [hk, hle, h0], l₁, l₂⟩

end

/-- The whole function, in two runs that agree on the public data. -/
theorem crypt_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : (modeX86_64 AesCtr.ctrMode).pre s₀)
    (h0' : (modeX86_64 AesCtr.ctrMode).pre s₀') (hq : ctrPub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (crypt v.callee) fun _ _ => True :=
  ends_rel h0 h0' hq.1 fun hp hp' hN =>
    (loop_rel hq.1 hq.2 v hp hp' (N s₀ - 0)).mono (fun _ _ h => ⟨0, rfl, hN, h.1, h.2⟩) fun _ _ h => h

theorem crypt_ct (v : Ctr32Impl) :
    ConstantTime isa (modeX86_64 AesCtr.ctrMode).pre ctrPub (crypt v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (crypt_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesCtr.X86_64

end

end

/-!
# AES-CTR on x86-64: `Verified`

Correctness and constant time (for any implementation `v` of
`vg_aes_ctr32`), from `crypt_wp` and `crypt_ct`, a state satisfying the
precondition, and the shared contract of `Spec/Ctr/Contract.lean` (with 8
bytes of stack, for the return address of the call of `vg_aes_ctr32`),
whose `leak` (the counter block's last four bytes) gives the agreement on
the last 32 bits of the counter block `crypt_ct` assumes (`ctrPub`).
-/

@[expose] public section

namespace VG.Proof.AesCtr.X86_64

open VG VG.X86_64 VG.Impl.AesCtr.X86_64
open VG.Proof.AesCbc.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

theorem crypt_mx (v : Ctr32Impl) : (crypt v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [crypt, body, Code.allInstrs, v.mxcsr]; decide +kernel

theorem crypt_spSafe (v : Ctr32Impl) : (crypt v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [crypt, body, Code.all, v.spSafe]; decide +kernel

theorem crypt_correct (v : Ctr32Impl) (s : State) (hs : (modeX86_64 AesCtr.ctrMode).pre s) :
    ∃ t s', Exec isa (crypt v.callee) s t s' ∧ abiPreserved s s' ∧ (modeX86_64 AesCtr.ctrMode).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := crypt_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (crypt_mx v) he hg, hp⟩

theorem crypt_verified (v : Ctr32Impl) :
    Verified X86_64.target (crypt v.callee) (Proof.AesCtr.roundsContract X86_64.abi 8) :=
  Verified.of_correct (k := { modeX86_64 AesCtr.ctrMode with pub := ctrPub }) (crypt_correct v) (crypt_ct v)
    { pre := by sig_implies_pre [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, modeX86_64, X86_64.abi, X86_64.argRegs]
      -- `ctrMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, modeX86_64, AesCtr.ctrMode, X86_64.abi, X86_64.argRegs]
        sig_reduce [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, modeX86_64, AesCtr.ctrMode, X86_64.abi,
          X86_64.argRegs] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by
        have hm : ∀ s₁ s₂, (Proof.AesCtr.roundsContract X86_64.abi 8).pre s₁ → (Proof.AesCtr.roundsContract X86_64.abi 8).pre s₂ →
            (Proof.AesCtr.roundsContract X86_64.abi 8).pub s₁ s₂ → (modeX86_64 AesCtr.ctrMode).pub s₁ s₂ := by
          sig_implies_pub [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, modeX86_64, X86_64.abi, X86_64.argRegs]
        intro s₁ s₂ h₁ h₂ h
        refine ⟨hm s₁ s₂ h₁ h₂ h, ?_⟩
        sig_pub [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, Spec.Ctr.ctrLeak, X86_64.abi, X86_64.argRegs] at h
        sig_split h
        exact AesCtr.lo32_of_leak (Proof.Cmac.bytesAt_length _ _ _) (Proof.Cmac.bytesAt_length _ _ _)
          (by assumption)
      sat := by sig_implies_sat [Proof.AesCtr.roundsContract, Spec.Ctr.aesSig, modeX86_64, X86_64.abi,
        X86_64.argRegs] [sat] using sat }

end VG.Proof.AesCtr.X86_64
