module

public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemLoopOneD
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchR
import VerifiedGarbage.Proof.Framework.X86_64.Lane0Zero
import VerifiedGarbage.Proof.Framework.X86_64.ZFrame
import VerifiedGarbage.Proof.Gcm.X86_64.StitchTo.Base
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Base
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemBodyD
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# The blocks after the last group, two at a time: the decryption's loads

`StitchR.remD` decrypts the `r` blocks after the last group of the 256-bit
loop as `StitchZH.remLoopD1_ok` does one at a time, but in pairs, one in each
lane: `pairMem_ok` and `pairLanes_ok` are what `remPairD` does, the products of
block `i + l` in lane `l`, and `foldLanes_run` adds the products of the upper
lanes into the lower ones. The steps themselves, with the powers read from the
key context, are `RemPairE.lean`'s (`pairStepDC_ok`, `oneStepDC_ok`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchR

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod acc_ok eval_pxor)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.StitchZTo (atIx)
open VG.Impl.Gcm.X86_64.StitchR (remPairD remNextPair foldLanes)
open VG.Impl.Gcm.X86_64.StitchZH (remBodyD remNext)
open VG.Proof.Gcm.X86_64.StitchZTo (ea_atIx)
open VG.Proof.Gcm.X86_64.StitchTo (blockAt_writeW_lane2 load256_lane ymm_lane2)
open VG.Proof.Gcm.X86_64.StitchZH (REnv RInvD accR remStepD_ok addr0 addr768 lane0_remBodyD remBodyD_dst)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame)
open VG.Proof.Gcm.X86_64.Stitch (blockAt_writeW_sep')
open VG.Proof.Gcm.X86_64 (revMask blockAt_eq pshufb_rev_xor)
open VG.Spec.Gcm (Block blockAt)

/-- The loads and the store of `remPairD`. -/
abbrev pairMem : List Instr :=
  [.vmovdquLoad .l256 .xmm13 (atIx .rdx .r10 0), .vmovdquLoad .l256 .xmm12 (atIx .r11 .r10 768),
   .vop (.vbin .vpxor .l256 .xmm12 .xmm12 .xmm13), .vmovdquStore .l256 (atIx .rdx .r10 0) .xmm12,
   .vmovdquLoad .l256 .xmm12 (atIx .rax .r10 0)]

/-- The lane-wise rest of `remPairD`. -/
abbrev pairLanes : List Instr :=
  ([.vop (.vbin .vpshufb .l256 .xmm13 .xmm13 .xmm0), .vop (.vbin .vpxor .l256 .xmm13 .xmm13 .xmm2),
    .vop (.vbin .vpxor .l256 .xmm2 .xmm2 .xmm2)] : List Instr) ++
  Impl.Gcm.X86_64.Vpclmul.acc .xmm13 .xmm12

/-- Its SSE block, in each lane. -/
abbrev pairSse : List Instr :=
  ([.xop (.bin .pshufb .xmm13 .xmm0), .xop (.bin .pxor .xmm13 .xmm2), .xop (.bin .pxor .xmm2 .xmm2)] :
    List Instr) ++ Impl.Gcm.X86_64.Pclmul.acc .xmm13 .xmm12

theorem remPairD_eq : remPairD = pairMem ++ pairLanes := rfl

theorem laneSse_pair : laneSseBlock pairLanes = some pairSse := rfl

/-- The two blocks at `rdx + r10` loaded into `ymm13`, their keystream at
`r11 + r10 + 768` added and stored back, and the powers at `rax + r10` loaded
into `ymm12`. -/
theorem pairMem_ok (t : State)
    (hinS : InRegions (t.rd ++ t.wr) (t.gpr .rdx + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 32)
    (hinK : InRegions (t.rd ++ t.wr) (t.gpr .r11 + t.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int)) 32)
    (hinD : InRegions t.wr (t.gpr .rdx + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 32)
    (hinP : InRegions (t.rd ++ t.wr) (t.gpr .rax + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) 32) :
    WP isa (.block pairMem) t fun t' =>
      (∃ v : BitVec 256, t'.mem = t.mem.writeW (t.gpr .rdx + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)) v) ∧
      (∀ l < 2, blockAt t'.mem (t.gpr .rdx + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) + BitVec.ofNat 64 (16 * l)) =
        blockAt t.mem (t.gpr .rdx + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) + BitVec.ofNat 64 (16 * l)) ^^^
        blockAt t.mem (t.gpr .r11 + t.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int) + BitVec.ofNat 64 (16 * l))) ∧
      (∀ l < 2, t'.lane .xmm13 l =
        t.mem.readW (t.gpr .rdx + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128) ∧
      (∀ l < 2, t'.lane .xmm12 l =
        t'.mem.readW (t.gpr .rax + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128) ∧
      t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm12 → ∀ l < 2, t'.lane r l = t.lane r l) := by
  let aS := t.gpr .rdx + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)
  let aK := t.gpr .r11 + t.gpr .r10 + BitVec.ofInt 64 ((768 : Nat) : Int)
  let aW := t.gpr .rax + t.gpr .r10 + BitVec.ofInt 64 ((0 : Nat) : Int)
  let v := t.mem.readW aS 256
  let k := t.mem.readW aK 256
  let s₁ := t.setV .l256 .xmm13 (v.extractLsb' 0 128) (v.extractLsb' 128 128)
  let s₂ := s₁.setV .l256 .xmm12 (k.extractLsb' 0 128) (k.extractLsb' 128 128)
  let s₃ := (VOp.vbin .vpxor .l256 .xmm12 .xmm12 .xmm13).exec s₂
  let s₄ := s₃.setMem (t.mem.writeW aS (s₃.ymm .xmm12))
  let w := s₄.mem.readW aW 256
  let s₅ := s₄.setV .l256 .xmm12 (w.extractLsb' 0 128) (w.extractLsb' 128 128)
  have l₁ : ∀ l < 2, s₁.lane .xmm13 l = t.mem.readW (aS + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rw [← load256_lane _ _ hl]
    rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;> simp [s₁, State.lane_setV256, v]
  have l₂ : ∀ l < 2, s₂.lane .xmm12 l = t.mem.readW (aK + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    rw [← load256_lane _ _ hl]
    rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;> simp [s₂, State.lane_setV256, k]
  have l₃ : ∀ l < 2, s₃.lane .xmm12 l =
      t.mem.readW (aK + BitVec.ofNat 64 (16 * l)) 128 ^^^ t.mem.readW (aS + BitVec.ofNat 64 (16 * l)) 128 :=
    fun l hl => by
      simp only [s₃, lane_vbin256, ite_true, VBinOp.sse, ← l₁ l hl, ← l₂ l hl, eval_pxor]
      simp [s₂, State.lane_setV256]
  rw [WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load256, ea_atIx, hinS, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₂, by simp only [isa, exec, State.load256, ea_atIx, s₁, State.setV_gpr, State.setV_rd, State.setV_wr,
    hinK, ite_true, Option.map_some, State.setV_mem]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₃, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₄, by simp only [isa, exec, State.store256_eq, ea_atIx, s₃, s₂, s₁, VOp.exec_gpr, State.setV_gpr,
    VOp.exec_wr, State.setV_wr, VOp.exec_mem, State.setV_mem, hinD, ite_true, s₄, aS], ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₅, by simp only [isa, exec, State.load256, ea_atIx, s₄, s₃, s₂, s₁, State.setMem_gpr, State.setMem_rd,
    State.setMem_wr, VOp.exec_gpr, VOp.exec_rd, VOp.exec_wr, State.setV_gpr, State.setV_rd, State.setV_wr, hinP,
    ite_true, Option.map_some]; rfl, WP.block_nil ?_⟩
  have m₅ : s₅.mem = t.mem.writeW aS (s₃.ymm .xmm12) := by simp [s₅, s₄]
  refine ⟨⟨_, m₅⟩, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, by simp [s₅, s₄, s₃, s₂, s₁],
    by simp [s₅, s₄, s₃, s₂, s₁], by simp [s₅, s₄, s₃, s₂, s₁], fun r h13 h12 l hl => ?_⟩
  · rw [m₅, blockAt_writeW_lane2 _ _ _ hl, ymm_lane2 _ _ hl, l₃ l hl, pshufb_rev_xor, BitVec.xor_comm,
      ← blockAt_eq, ← blockAt_eq]
  · rw [← l₁ l hl]
    simp [s₅, s₄, s₃, s₂, s₁, lane_vbin256, State.lane_setV256]
  · rw [← load256_lane _ _ hl]
    rcases (by omega_arith : l = 0 ∨ l = 1) with rfl | rfl <;> simp [s₅, State.lane_setV256, w, aW]
  · simp [s₅, s₄, s₃, s₂, s₁, lane_vbin256, State.lane_setV256, h13, h12]

/-- The block in `xmm13` byte-reversed and `Y` added, `Y` cleared, and the
product with `xmm12` added. -/
theorem pairSse_ok (t : State) (h0 : t.xmm .xmm0 = revMask) :
    WP isa (.block pairSse) t fun t' =>
      prod t' = (prod t).acc (XBinOp.eval .pshufb (t.xmm .xmm13) revMask ^^^ t.xmm .xmm2) (t.xmm .xmm12) ∧
      t'.xmm .xmm2 = 0 ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm2 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm11 → t'.xmm r = t.xmm r) := by
  rw [WP.block_append_iff]
  have hp : WP isa (.block [.xop (.bin .pshufb .xmm13 .xmm0), .xop (.bin .pxor .xmm13 .xmm2),
      .xop (.bin .pxor .xmm2 .xmm2)]) t fun t' =>
      t'.xmm .xmm13 = XBinOp.eval .pshufb (t.xmm .xmm13) revMask ^^^ t.xmm .xmm2 ∧ t'.xmm .xmm2 = 0 ∧
      Pclmul.Only [.xmm13, .xmm2] t t' := by
    apply WP.of_runBlock
    simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, isa, State.setXmm,
      h0, eval_pxor, reduceCtorEq, BitVec.xor_self, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, rfl, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2, ite_false]
  refine WP.mono hp fun t₁ ⟨x13, x2, o₁⟩ => ?_
  refine WP.mono (acc_ok .xmm13 .xmm12 t₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun t' ⟨p', o'⟩ => ⟨?_, ?_, fun r h13 h2 h8 h9 h10 h11 => ?_⟩
  · rw [p', x13, o₁.prod (by decide) (by decide) (by decide), o₁.xmm _ (by decide)]
  · rw [o'.xmm _ (by decide), x2]
  · rw [o'.xmm r (by simp [h8, h9, h10, h11]), o₁.xmm r (by simp [h13, h2])]

/-- `pairLanes`, in each lane. -/
theorem pairLanes_ok (t : State) (h0 : ∀ l < 2, t.lane .xmm0 l = revMask) :
    WP isa (.block pairLanes) t fun t' => VKeep t t' ∧ ∀ l < 2,
      prod (t'.proj l) = (prod (t.proj l)).acc (XBinOp.eval .pshufb (t.lane .xmm13 l) revMask ^^^ t.lane .xmm2 l)
        (t.lane .xmm12 l) ∧ t'.lane .xmm2 l = 0 ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm2 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm11 → t'.lane r l = t.lane r l) :=
  WP.mono (WP.lanes laneSse_pair fun l hl => pairSse_ok (t.proj l) (by simpa using h0 l hl))
    fun t' ⟨k, q⟩ => ⟨k, fun l hl => by
      obtain ⟨a, b, c⟩ := q l hl
      exact ⟨by simpa using a, by simpa using b, fun r h1 h2 h3 h4 h5 h6 => by simpa using c r h1 h2 h3 h4 h5 h6⟩⟩

/-- `add r10, 32`, `sub r9, 2`, `cmp r9, 16`. -/
theorem remNextPair_ok (s : State) {m : Nat} (h2 : 2 ≤ m) (h15 : m ≤ 15) {i : Nat}
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (16 + m)) (h10 : s.gpr .r10 = BitVec.ofNat 64 (16 * i)) :
    WP isa (.block remNextPair) s fun s' =>
      s'.gpr .r10 = BitVec.ofNat 64 (16 * (i + 2)) ∧ s'.gpr .r9 = BitVec.ofNat 64 (16 + (m - 2)) ∧
      s'.zf = some (decide (m = 2)) ∧ (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      (∀ r l, s'.lane r l = s.lane r l) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e32 : BitVec.signExtend 64 (32 : BitVec 32) = 32 := by decide
  have e2 : BitVec.signExtend 64 (2 : BitVec 32) = 2 := by decide
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have a10 : BitVec.ofNat 64 (16 * i) + 32 = BitVec.ofNat 64 (16 * (i + 2)) := by
    rw [show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, ← BitVec.ofNat_add]; congr 1
  have s9 : BitVec.ofNat 64 (16 + m) - 2 = BitVec.ofNat 64 (16 + (m - 2)) := by
    rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl,
      VG.Proof.Gcm.X86_64.Pclmul.ofNat_sub_ofNat (by omega_arith) (by omega_arith)]
    congr 1; omega_arith
  have z9 : (BitVec.ofNat 64 (16 + (m - 2)) - 16 == 0) = decide (m = 2) := by
    rw [show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      VG.Proof.Gcm.X86_64.Pclmul.ofNat_sub_ofNat (by omega_arith) (by omega_arith)]
    by_cases h : m = 2
    · subst h; rfl
    · have : BitVec.ofNat 64 (16 + (m - 2) - 16) ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 16 + (m - 2) - 16 < 2 ^ 64 by omega_arith)] at this
        have h0 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
        omega_arith
      rw [beq_false_of_ne this, decide_eq_false h]
  apply WP.of_runBlock
  simp only [remNextPair, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e32, e2, e16, h9, h10, a10, s9, z9,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, fun r h1 h2 => by simp only [h1, h2, ite_false], fun _ _ => rfl, trivial,
    trivial, trivial⟩

/-- The products of two lanes, each with one more block, added. -/
theorem xor_acc_acc (p q : Prod) (a b c d : BitVec 128) :
    (p.acc a b).xor (q.acc c d) = ((p.xor q).acc a b).acc c d := by
  cases p; cases q
  simp only [Prod.xor, Prod.acc, Pclmul.Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ac_rfl

theorem xor_zero (p : Prod) : p.xor Prod.zero = p := by
  cases p
  simp [Prod.xor, Prod.zero]

/-- What the pair loop needs of the regions of two blocks. -/
structure Ok2 (E : REnv) : Prop where
  inS : ∀ j, j + 2 ≤ E.r → InRegions (E.rd ++ E.wr) (E.aS j) 32
  inK : ∀ j, j + 2 ≤ E.r → InRegions (E.rd ++ E.wr) (E.aK j) 32
  inD : ∀ j, j + 2 ≤ E.r → InRegions E.wr (E.aD j) 32
  inW : ∀ j, j + 2 ≤ E.r → InRegions (E.rd ++ E.wr) (E.aW j) 32

theorem aOff (p : Addr) (j l : Nat) :
    p + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 (16 * l) = p + BitVec.ofNat 64 (16 * (j + l)) := by
  rw [Offset.add_add, Nat.mul_add]

theorem aOffK (p : Addr) (j l : Nat) :
    p + BitVec.ofNat 64 (768 + 16 * j) + BitVec.ofNat 64 (16 * l) = p + BitVec.ofNat 64 (768 + 16 * (j + l)) := by
  rw [Offset.add_add, Nat.mul_add, Nat.add_assoc]

theorem wp_and_run {is : List Instr} {s : State} {Q R : State → Prop} (h : WP isa (.block is) s Q)
    (hR : ∀ s', runBlock isa is s = some s' → R s') : WP isa (.block is) s fun s' => Q s' ∧ R s' := by
  obtain ⟨s', e, q⟩ := WP.runBlock_of h
  exact WP.of_runBlock ⟨s', e, q, hR s' e⟩

theorem remNext_lanes {t t' : State} (e : runBlock isa remNext t = some t') : ∀ r l, t'.lane r l = t.lane r l := by
  simp only [remNext, runBlock_cons, runStep_some, runBlock_nil, isa, exec, execAlu, readSrc, arithFlags,
    State.setFlags, State.setReg, Option.bind_some, Option.some.injEq] at e
  subst e
  intro r l; rfl

/-- `foldLanes`: the upper lanes of the products added into the lower. -/
theorem foldLanes_run (t : State) :
    WP isa (.block foldLanes) t fun t' =>
      t'.lane .xmm8 0 = t.lane .xmm8 0 ^^^ t.lane .xmm8 1 ∧ t'.lane .xmm9 0 = t.lane .xmm9 0 ^^^ t.lane .xmm9 1 ∧
      t'.lane .xmm10 0 = t.lane .xmm10 0 ^^^ t.lane .xmm10 1 ∧
      (∀ r, r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → r ≠ .xmm11 → t'.lane r 0 = t.lane r 0) ∧
      t'.gpr = t.gpr ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  simp only [foldLanes]
  repeat (rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩)
  refine WP.block_nil ⟨?_, ?_, ?_, fun r h8 h9 h10 h11 => ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [VBinOp.sse, Pclmul.eval_pxor, VOp.exec, State.setV, State.lane, *]

/-- `test r9, 1`. -/
theorem test91_ok (s : State) :
    WP isa (.block [.alu .test .r9 (.imm 1)]) s fun s' =>
      s'.zf = some (s.gpr .r9 &&& 1 == 0) ∧ s'.gpr = s.gpr ∧ (∀ x l, s'.lane x l = s.lane x l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    e1, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun _ _ => rfl, trivial, trivial, trivial⟩

/-- `cmp r9, 16`. -/
theorem cmp916_ok (s : State) :
    WP isa (.block [.alu .cmp .r9 (.imm 16)]) s fun s' =>
      s'.zf = some (s.gpr .r9 - 16 == 0) ∧ s'.gpr = s.gpr ∧ (∀ x l, s'.lane x l = s.lane x l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    e16, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun _ _ => rfl, trivial, trivial, trivial⟩

theorem parity16 : ∀ r < 16, (BitVec.ofNat 64 (16 + r) &&& 1 == 0) = decide (r % 2 = 0) := by decide

theorem zero16 : ∀ r < 16, (BitVec.ofNat 64 (16 + r) - 16 == 0) = decide (r = 0) := by decide

end VG.Proof.Gcm.X86_64.StitchR
