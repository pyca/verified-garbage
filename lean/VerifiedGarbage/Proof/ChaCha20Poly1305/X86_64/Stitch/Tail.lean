module

import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.TailRounds
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Bulk
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.TailK
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Pad
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.XorBufX
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Xor
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# ChaCha20 and Poly1305 together (x86-64): the last bytes of `seal`

`Stitch.tailS`, after the whole chunks (`LI`), with 1 to 256 bytes left:
the constants stored, `Avx2Tail`'s setup (`tailA_ok`), the rounds absorbing
the last chunk (`trounds_ok`), the accumulator stored and the registers
restored (`leaveT`), the keystream into `buf` (`Avx2Tail.last_ok`,
`last1_ok`), and from there into the bytes left (`xorBufX_ok`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Proof.ChaCha20.X86_64.Avx2 (Consts stR bufR storeAll pairs_ok pairsCode constPairs constPairs_le
  tPairs tPairs_le tconsts_eq consts_eq consts_mem tincs_mem storeAll_frame)
open VG.Proof.ChaCha20.X86_64.Avx2Tail (HB YM Incs)
open VG.Proof.ChaCha20.X86_64.Avx512Tail (Ctx regn baseR bsize wregs S0)
open VG.Proof.ChaCha20 (CState ctr)
open VG.Spec.ChaCha20 (stateAt)

section
variable {c : Addr}

/-- Where `Avx2Tail`'s code around the rounds runs: the ChaCha20 state at
`rdi`, `buf` at `r9`, and no data. -/
theorem ctx0 {s : State} (hrdi : s.gpr .rdi = stA c) (hr9 : s.gpr .r9 = bfA c) (hst : stR (stA c) ∈ s.wr)
    (hb : bufR (bfA c) ∈ s.wr) : Ctx 0 s := by
  have r0 : regn 0 s 0 = stR (stA c) := by simp only [regn, baseR, bsize, hrdi, Nat.reduceMul]
  have r1 : regn 0 s 1 = bufR (bfA c) := by simp only [regn, baseR, bsize, hr9, Nat.reduceMul]
  have r2 : (regn 0 s 2).len = 0 := by simp only [regn, bsize, Nat.mul_zero]
  have z : ∀ r : Region, r.len = 0 → ∀ r', r.Disjoint r' ∧ r'.Disjoint r := fun r hr r' =>
    ⟨fun a ha => absurd ha (by simp only [Region.Contains, hr]; omega),
     fun a _ ha => absurd ha (by simp only [Region.Contains, hr]; omega)⟩
  refine ⟨fun b i n hb3 h hn => ?_, fun b b' hb hb' ne => ?_, by decide⟩
  · rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;> simp only [bsize] at h
    · rw [r0]; exact ⟨_, hst, Offset.contains_base _ (by omega) (by lit_omega)⟩
    · rw [r1]; exact ⟨_, hb, Offset.contains_base _ (by omega) (by lit_omega)⟩
    · omega
  · have d01 : (regn 0 s 0).Disjoint (regn 0 s 1) := by rw [r0, r1]; exact st_bf (c := c)
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
      rcases (by omega : b' = 0 ∨ b' = 1 ∨ b' = 2) with rfl | rfl | rfl
    · exact absurd rfl ne
    · exact d01
    · exact (z _ r2 _).2
    · exact d01.symm
    · exact absurd rfl ne
    · exact (z _ r2 _).2
    · exact (z _ r2 _).1
    · exact (z _ r2 _).1
    · exact absurd rfl ne

theorem movs_ok {s : State} :
    WP isa (.block [.mov .r12 (.reg .r9), .mov .r9 (.reg .rcx)]) s fun s' =>
      s'.gpr .r12 = s.gpr .r9 ∧ s'.gpr .r9 = s.gpr .rcx ∧ (∀ r, r ≠ .r12 → r ≠ .r9 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, Option.map_some, Option.some.injEq, exists_eq_left', reduceCtorEq,
    ite_true, ite_false]
  refine ⟨trivial, trivial, fun r h₁ h₂ => by simp [h₁, h₂], trivial, trivial, trivial, rfl, rfl⟩

theorem mov9_ok {s : State} :
    WP isa (.block [.mov .r9 (.reg .r12)]) s fun s' =>
      s'.gpr .r9 = s.gpr .r12 ∧ (∀ r, r ≠ .r9 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, Option.map_some, Option.some.injEq, exists_eq_left', ite_true]
  refine ⟨trivial, fun r h₁ => by simp [h₁], trivial, trivial, trivial, rfl, rfl⟩

/-- The memory after `tailA`'s stores. -/
abbrev tMem (c : Addr) (m : Mem) : Mem := storeAll (bfA c) constPairs (storeAll (bfA c) tPairs m)

theorem tMem_frame (m : Mem) : Frame [bufR (bfA c)] m (tMem c m) :=
  (storeAll_frame (List.mem_singleton_self _) _ tPairs_le _).trans
    (storeAll_frame (List.mem_singleton_self _) _ constPairs_le _)

theorem tailA_eq (two : Bool) : tailA two = pairsCode tPairs ++ (pairsCode constPairs ++
    (([.mov .r12 (.reg .r9), .mov .r9 (.reg .rcx)] : List Instr) ++
    ((if two then Impl.ChaCha20.X86_64.Avx2Tail.setup else Impl.ChaCha20.X86_64.Avx2Tail.setup1) ++
    ([.mov .r9 (.reg .r12)] : List Instr)))) := by
  simp only [tailA, tconsts_eq, consts_eq, List.append_assoc]

/-- `tailA`: the constants stored, and the input states of the blocks after
the counter of the state at `stA c` in the vector registers. -/
theorem tailA_ok (two : Bool) {S : Nat} (hS : S = if two then 2 else 1) {s : State}
    (hrcx : s.gpr .rcx = bfA c) (hrdi : s.gpr .rdi = stA c) (hst : stR (stA c) ∈ s.wr)
    (hb : bufR (bfA c) ∈ s.wr) :
    WP isa (.block (tailA two)) s fun s' =>
      HB S (fun j => ctr (stateAt s.mem (stA c)) j) s' ∧ YM s' ∧ s'.mem = tMem c s.mem ∧
      (∀ r, r ≠ .rax → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.gpr .r12 = s.gpr .r9 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [tailA_eq]
  refine WP.block_append (WP.mono (pairs_ok tPairs tPairs_le hrcx hb) fun s₁ ⟨m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.block_append (WP.mono (pairs_ok (buf := bfA c) constPairs constPairs_le (s := s₁)
    (by rw [g₁ _ (by decide), hrcx]) (by rw [wr₁]; exact hb)) fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_)
  refine WP.block_append (WP.mono movs_ok fun s₃ ⟨r12₃, r9₃, g₃, m₃, rd₃, wr₃, _, _⟩ => ?_)
  have mm : s₃.mem = tMem c s.mem := by rw [m₃, m₂, m₁]
  have rdi₃ : s₃.gpr .rdi = stA c := by
    rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), g₁ _ (by decide), hrdi]
  have r9₃' : s₃.gpr .r9 = bfA c := by rw [r9₃, g₂ _ (by decide), g₁ _ (by decide), hrcx]
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂, wr₁]
  have hc : Ctx 0 s₃ := ctx0 rdi₃ r9₃' (by rw [wr₃']; exact hst) (by rw [wr₃']; exact hb)
  have cst : Consts s₃.mem (s₃.gpr .r9) := by rw [mm, r9₃']; exact consts_mem _ _
  have inc : Incs s₃.mem (s₃.gpr .r9) := by rw [mm, r9₃']; exact tincs_mem _ _
  have S₃ : S0 s₃ = stateAt s.mem (stA c) := by
    simp only [S0, rdi₃, mm]
    exact Proof.ChaCha20.X86_64.Xor.stateAt_frame (tMem_frame _) (by simpa using st_bf)
  have fin : ∀ {s₄ : State}, HB S (fun j => ctr (S0 s₃) j) s₄ → YM s₄ → s₄.mem = s₃.mem → s₄.gpr = s₃.gpr →
      s₄.rd = s₃.rd → s₄.wr = s₃.wr → WP isa (.block [.mov .r9 (.reg .r12)]) s₄ fun s' =>
        HB S (fun j => ctr (stateAt s.mem (stA c)) j) s' ∧ YM s' ∧ s'.mem = tMem c s.mem ∧
        (∀ r, r ≠ .rax → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.gpr .r12 = s.gpr .r9 ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
    intro s₄ hz ym m₄ g₄ rd₄ wr₄
    refine WP.mono mov9_ok fun s₅ ⟨r9₅, g₅, m₅, rd₅, wr₅, x₅, y₅⟩ => ⟨?_, ?_, by rw [m₅, m₄, mm], fun r h₁ h₂ => ?_,
      by rw [g₅ _ (by decide), g₄, r12₃, g₂ _ (by decide), g₁ _ (by decide)], by rw [rd₅, rd₄, rd₃, rd₂, rd₁],
      by rw [wr₅, wr₄, wr₃']⟩
    · intro k hk l hl i hi
      simp only [State.lane, x₅, y₅]
      rw [← S₃]; exact hz k hk l hl i hi
    · intro l; simp only [State.lane, x₅, y₅]; exact ym l
    · by_cases h9 : r = .r9
      · subst h9; rw [r9₅, g₄, r12₃, g₂ _ (by decide), g₁ _ (by decide)]
      · rw [g₅ r h9, g₄, g₃ r h₂ h9, g₂ r h₁, g₁ r h₁]
  cases two
  · simp only [Bool.false_eq_true, ite_false] at hS ⊢
    subst hS
    exact WP.block_append (WP.mono (Proof.ChaCha20.X86_64.Avx2Tail.setup1_ok hc cst inc)
      fun s₄ ⟨hz, ym, m₄, g₄, rd₄, wr₄⟩ => fin hz ym m₄ g₄ rd₄ wr₄)
  · simp only [ite_true] at hS ⊢
    subst hS
    exact WP.block_append (WP.mono (Proof.ChaCha20.X86_64.Avx2Tail.setup_ok hc cst inc)
      fun s₄ ⟨hz, ym, m₄, g₄, rd₄, wr₄⟩ => fin hz ym m₄ g₄ rd₄ wr₄)

end

/-! ## Leaving: the accumulator stored, the registers restored, the keystream into `buf` -/

open VG.Proof.Poly1305.X86_64 (hval Keeps)
open VG.Spec.Poly1305 (P bytesAt leNum)
open VG.Spec.ChaCha20 (serialize)

/-- The stores and moves of `leaveT`. -/
def storeTL (pre : Bool) : List Instr :=
  [.store (at_ .rcx accOff) .r11, .store (at_ .rcx (accOff + 8)) .rbx,
   .store (at_ .rcx (accOff + 16)) .rbp,
   .mov .rbx (.reg .rsi), .alu .add .rbx (.imm (BitVec.ofNat 32 (16 * total pre))),
   .mov .rbp (.mem (at_ .rcx lenOff)),
   .mov .r12 (.mem (at_ .rcx r12Off)), .mov .r13 (.mem (at_ .rcx r13Off)),
   .mov .r14 (.mem (at_ .rcx r14Off)), .mov .r15 (.reg .rcx), .alu .sub .r15 (.imm 128)]

theorem leaveT_eq (pre : Bool) : leaveT pre = Impl.Poly1305.X86_64.reduce ++ storeTL pre := rfl

theorem storeT_ok (pre : Bool) {c : Addr} {s : State} (hrcx : s.gpr .rcx = bfA c) (hw : psR c ∈ s.wr) :
    WP isa (.block (storeTL pre)) s fun s' =>
      s'.mem = accMem s.mem c (s.gpr .r11) (s.gpr .rbx) (s.gpr .rbp) ∧
      s'.gpr .rbx = s.gpr .rsi + tot pre ∧ s'.gpr .rbp = s.mem.readW (c + BitVec.ofNat 64 544) 64 ∧
      s'.gpr .r12 = s.mem.readW (c + BitVec.ofNat 64 520) 64 ∧
      s'.gpr .r13 = s.mem.readW (c + BitVec.ofNat 64 528) 64 ∧
      s'.gpr .r14 = s.mem.readW (c + BitVec.ofNat 64 536) 64 ∧ s'.gpr .r15 = c ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o : ∀ d, 448 ≤ d → d + 8 ≤ 576 → InRegions s.wr (c + BitVec.ofNat 64 d) 8 := fun d h₁ h₂ =>
    ⟨_, hw, Offset.contains c (by omega_arith) (by omega_arith) (by decide)⟩
  have i : ∀ d, 448 ≤ d → d + 8 ≤ 576 → InRegions (s.rd ++ s.wr) (c + BitVec.ofNat 64 d) 8 := fun d h₁ h₂ =>
    ⟨_, List.mem_append_right _ hw, Offset.contains c (by omega_arith) (by omega_arith) (by decide)⟩
  have o0 := o 448 (by decide) (by decide); have o1 := o 456 (by decide) (by decide)
  have o2 := o 464 (by decide) (by decide)
  have i0 := i 544 (by decide) (by decide); have i1 := i 520 (by decide) (by decide)
  have i2 := i 528 (by decide) (by decide); have i3 := i 536 (by decide) (by decide)
  apply WP.of_runBlock
  have se128 : BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 128 := by decide
  simp only [storeTL, runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.ChaCha20.X86_64.ea_at,
    State.store64, State.load64, readSrc, execAlu, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    hrcx, accOff, r12Off, r13Off, r14Off, lenOff, ofInt_bf, Nat.reduceAdd, reduceCtorEq, o0, o1, o2, i0, i1, i2,
    i3, ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 => by
    simp only [h1, h2, h3, h4, h5, h6, ite_false], trivial, trivial⟩
  all_goals simp (disch := decide) only [readW_writeW_ofNat, se_tot, se128, bfA, BitVec.add_sub_cancel]

theorem scal_reduce : scalCode (.block Impl.Poly1305.X86_64.reduce) = true := by decide
theorem scal_storeTL (pre : Bool) : scalCode (.block (storeTL pre)) = true := by cases pre <;> decide

theorem movR_ok (d src : Reg) {s : State} :
    WP isa (.block [.mov d (.reg src)]) s fun s' =>
      s'.gpr d = s.gpr src ∧ (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, Option.map_some, Option.some.injEq, exists_eq_left', ite_true]
  exact ⟨trivial, fun r h₁ => by simp [h₁], trivial, trivial, trivial, rfl, rfl⟩

theorem hb_of_vec {S : Nat} {vs : Nat → CState} {s s' : State} (h : HB S vs s) (hx : s'.xmm = s.xmm)
    (hy : s'.ymmHi = s.ymmHi) : HB S vs s' := fun k hk l hl i hi => by
  simpa only [State.lane, hx, hy] using h k hk l hl i hi

/-- A frame with a region that contains no byte is one without it. -/
theorem Frame.drop0 {rs : List Region} {m m' : Mem} {a : Addr} (h : Frame (rs ++ [⟨a, 0⟩]) m m') :
    Frame rs m m' := fun x hx => h x fun r hr => by
  rcases List.mem_append.mp hr with hr | hr
  · exact hx r hr
  · simp only [List.mem_singleton] at hr; subst hr; simp [Region.Contains]

theorem tailB_eq (two pre : Bool) : tailB two pre = Impl.Poly1305.X86_64.reduce ++ (storeTL pre ++
    (([.mov .r9 (.reg .rcx)] : List Instr) ++
    ((if two then Impl.ChaCha20.X86_64.Avx2Tail.addIn ++ Impl.ChaCha20.X86_64.Avx2Tail.storeSet .xmm0 .xmm1 .xmm2 .xmm3 0 ++
      Impl.ChaCha20.X86_64.Avx2Tail.storeSet .xmm4 .xmm5 .xmm6 .xmm7 128
    else Impl.ChaCha20.X86_64.Avx2Tail.addIn1 ++ Impl.ChaCha20.X86_64.Avx2Tail.storeSet .xmm0 .xmm1 .xmm2 .xmm3 0) ++
    ([.mov .rsi (.reg .r9), .mov .rdx (.reg .rbp)] : List Instr)))) := by
  simp only [tailB, leaveT_eq, List.append_assoc]

theorem movRB_ok {s : State} :
    WP isa (.block [.mov .rsi (.reg .r9), .mov .rdx (.reg .rbp)]) s fun s' =>
      s'.gpr .rsi = s.gpr .r9 ∧ s'.gpr .rdx = s.gpr .rbp ∧ (∀ r, r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, Option.map_some, Option.some.injEq, exists_eq_left', reduceCtorEq,
    ite_true, ite_false]
  exact ⟨trivial, trivial, fun r h₁ h₂ => by simp [h₁, h₂], trivial, trivial, trivial⟩

section
variable {c : Addr}

/-- `tailB`: the accumulator reduced and stored, the registers restored, and
the keystream of the `S` sets into `buf`, with `rsi` at it and `rdx` the
bytes left. -/
theorem tailB_ok (two pre : Bool) {S : Nat} (hS : S = if two then 2 else 1) {vs : Nat → CState} {s : State}
    (hz : HB S vs s) (hrcx : s.gpr .rcx = bfA c) (hrdi : s.gpr .rdi = stA c) (hst : stR (stA c) ∈ s.wr)
    (hb : bufR (bfA c) ∈ s.wr) (hps : psR c ∈ s.wr) (hi : Incs s.mem (bfA c)) (h2 : (s.gpr .rbp).toNat ≤ 4) :
    WP isa (.block (tailB two pre)) s fun s' =>
      (∀ k < 128 * S, s'.mem (bfA c + BitVec.ofNat 64 k) =
        (serialize (Proof.ChaCha20.X86_64.Avx2.plus vs (stateAt s.mem (stA c)) (k / 64))).getD (k % 64) 0) ∧
      leNum (bytesAt s'.mem (psA c) 24) = hval s % P ∧
      Frame [accR c, bufR (bfA c)] s.mem s'.mem ∧
      s'.gpr .rbx = s.gpr .rsi + tot pre ∧ s'.gpr .rbp = s.mem.readW (c + BitVec.ofNat 64 544) 64 ∧
      s'.gpr .rdx = s.mem.readW (c + BitVec.ofNat 64 544) 64 ∧ s'.gpr .rsi = bfA c ∧ s'.gpr .r9 = bfA c ∧
      s'.gpr .r12 = s.mem.readW (c + BitVec.ofNat 64 520) 64 ∧
      s'.gpr .r13 = s.mem.readW (c + BitVec.ofNat 64 528) 64 ∧
      s'.gpr .r14 = s.mem.readW (c + BitVec.ofNat 64 536) 64 ∧ s'.gpr .r15 = c ∧
      s'.gpr .rcx = bfA c ∧ s'.gpr .rsp = s.gpr .rsp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [tailB_eq]
  refine WP.block_append (WP.mono (WP.vecKeep scal_reduce (Proof.Poly1305.X86_64.reduce_ok s))
    fun s₁ ⟨⟨red, k₁⟩, x₁, y₁⟩ => ?_)
  refine WP.block_append (WP.mono (WP.vecKeep (scal_storeTL pre) (storeT_ok pre (c := c) (s := s₁)
    (by rw [k₁.gpr', hrcx]) (by rw [k₁.2.2.2]; exact hps)))
    fun s₂ ⟨⟨m₂, rbx₂, rbp₂, r12₂, r13₂, r14₂, r15₂, g₂, rd₂, wr₂⟩, x₂, y₂⟩ => ?_)
  refine WP.block_append (WP.mono (movR_ok .r9 .rcx) fun s₃ ⟨r9₃, g₃, m₃, rd₃, wr₃, x₃, y₃⟩ => ?_)
  have k12 : ∀ r, r = .rdi ∨ r = .rcx ∨ r = .rsi ∨ r = .rsp → s₂.gpr r = s.gpr r := by
    intro r hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k₁.gpr']
  have rdi₃ : s₃.gpr .rdi = stA c := by rw [g₃ _ (by decide), k12 _ (.inl rfl), hrdi]
  have rcx₃ : s₃.gpr .rcx = bfA c := by rw [g₃ _ (by decide), k12 _ (.inr (.inl rfl)), hrcx]
  have r9₃' : s₃.gpr .r9 = bfA c := by rw [r9₃, k12 _ (.inr (.inl rfl)), hrcx]
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂, k₁.2.2.2]
  have rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂, k₁.2.2.1]
  have m₃' : s₃.mem = accMem s.mem c (s₁.gpr .r11) (s₁.gpr .rbx) (s₁.gpr .rbp) := by rw [m₃, m₂, k₁.2.1]
  have fa : Frame [accR c] s.mem s₃.mem := by rw [m₃']; exact accMem_frame _ _ _ _ _
  have hc : Ctx 0 s₃ := ctx0 rdi₃ r9₃' (by rw [wr₃']; exact hst) (by rw [wr₃']; exact hb)
  have hi₃ : Incs s₃.mem (s₃.gpr .r9) := by
    rw [r9₃']
    refine Proof.ChaCha20.X86_64.Avx2Tail.incs_frame hi fa ?_
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    have e : Proof.ChaCha20.X86_64.Avx2.hiR (bfA c) = ⟨c + BitVec.ofNat 64 256, 192⟩ := by
      simp only [Proof.ChaCha20.X86_64.Avx2.hiR, bfA, Offset.add_add]
    rw [e]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  have hz₃ : HB S vs s₃ := hb_of_vec hz (by rw [x₃, x₂, x₁]) (by rw [y₃, y₂, y₁])
  have S₃ : S0 s₃ = stateAt s.mem (stA c) := by
    simp only [S0, rdi₃]
    exact Proof.ChaCha20.X86_64.Xor.stateAt_frame fa (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide))
  have acc₃ : leNum (bytesAt s₃.mem (psA c) 24) = hval s % P := by
    rw [m₃', accMem_acc]; exact red h2
  have fin : ∀ {s₄ : State}, (∀ k < 128 * S, s₄.mem (s₃.gpr .r9 + BitVec.ofNat 64 k) =
        (serialize (Proof.ChaCha20.X86_64.Avx2.plus vs (S0 s₃) (k / 64))).getD (k % 64) 0) →
      Frame (wregs 0 s₃) s₃.mem s₄.mem → s₄.gpr = s₃.gpr → s₄.rd = s₃.rd → s₄.wr = s₃.wr →
      WP isa (.block [.mov .rsi (.reg .r9), .mov .rdx (.reg .rbp)]) s₄ fun s' =>
        (∀ k < 128 * S, s'.mem (bfA c + BitVec.ofNat 64 k) =
          (serialize (Proof.ChaCha20.X86_64.Avx2.plus vs (stateAt s.mem (stA c)) (k / 64))).getD (k % 64) 0) ∧
        leNum (bytesAt s'.mem (psA c) 24) = hval s % P ∧
        Frame [accR c, bufR (bfA c)] s.mem s'.mem ∧
        s'.gpr .rbx = s.gpr .rsi + tot pre ∧ s'.gpr .rbp = s.mem.readW (c + BitVec.ofNat 64 544) 64 ∧
        s'.gpr .rdx = s.mem.readW (c + BitVec.ofNat 64 544) 64 ∧ s'.gpr .rsi = bfA c ∧ s'.gpr .r9 = bfA c ∧
        s'.gpr .r12 = s.mem.readW (c + BitVec.ofNat 64 520) 64 ∧
        s'.gpr .r13 = s.mem.readW (c + BitVec.ofNat 64 528) 64 ∧
        s'.gpr .r14 = s.mem.readW (c + BitVec.ofNat 64 536) 64 ∧ s'.gpr .r15 = c ∧
        s'.gpr .rcx = bfA c ∧ s'.gpr .rsp = s.gpr .rsp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    intro s₄ b₄ f₄ g₄ rd₄ wr₄
    have ws : wregs 0 s₃ = [⟨bfA c, 256⟩] ++ [⟨s₃.gpr .rsi, 0⟩] := by
      simp only [wregs, r9₃', Nat.mul_zero, List.cons_append, List.nil_append]
    rw [ws] at f₄
    have f₄' := Frame.drop0 f₄
    refine WP.mono movRB_ok fun s₅ ⟨rsi₅, rdx₅, g₅, m₅, rd₅, wr₅⟩ => ?_
    have gg : ∀ r, r ≠ .rsi → r ≠ .rdx → s₅.gpr r = s₃.gpr r := fun r h₁ h₂ => by rw [g₅ r h₁ h₂, g₄]
    have hb9 : bytesAt s₅.mem (psA c) 24 = bytesAt s₃.mem (psA c) 24 := by
      rw [m₅]
      refine bytesAt_frame f₄' (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
    refine ⟨fun k hk => ?_, by rw [hb9, acc₃], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [m₅, ← r9₃', b₄ k hk, S₃]
    · have f45 : Frame [bufR (bfA c)] s₃.mem s₅.mem := by
        rw [m₅]
        refine f₄'.sub fun r hr => ?_
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨bufR (bfA c), by simp, Region.sub_prefix (by decide)⟩
      exact (fa.mono (by simp)).trans (f45.mono (by simp))
    · rw [gg _ (by decide) (by decide), g₃ _ (by decide), rbx₂, k₁.gpr']
    · rw [gg _ (by decide) (by decide), g₃ _ (by decide), rbp₂, k₁.2.1]
    · rw [rdx₅, g₄, g₃ _ (by decide), rbp₂, k₁.2.1]
    · rw [rsi₅, g₄, r9₃']
    · rw [gg _ (by decide) (by decide), r9₃']
    · rw [gg _ (by decide) (by decide), g₃ _ (by decide), r12₂, k₁.2.1]
    · rw [gg _ (by decide) (by decide), g₃ _ (by decide), r13₂, k₁.2.1]
    · rw [gg _ (by decide) (by decide), g₃ _ (by decide), r14₂, k₁.2.1]
    · rw [gg _ (by decide) (by decide), g₃ _ (by decide), r15₂]
    · rw [gg _ (by decide) (by decide), rcx₃]
    · rw [gg _ (by decide) (by decide), g₃ _ (by decide), k12 _ (.inr (.inr (.inr rfl)))]
    · rw [rd₅, rd₄, rd₃']
    · rw [wr₅, wr₄, wr₃']
  cases two
  · simp only [Bool.false_eq_true, ite_false] at hS ⊢
    subst hS
    exact WP.block_append (WP.mono (Proof.ChaCha20.X86_64.Avx2Tail.last1_ok hc hi₃ hz₃)
      fun s₄ ⟨b₄, f₄, g₄, rd₄, wr₄⟩ => fin b₄ f₄ g₄ rd₄ wr₄)
  · simp only [ite_true] at hS ⊢
    subst hS
    exact WP.block_append (WP.mono (Proof.ChaCha20.X86_64.Avx2Tail.last_ok hc hi₃ hz₃)
      fun s₄ ⟨b₄, f₄, g₄, rd₄, wr₄⟩ => fin b₄ f₄ g₄ rd₄ wr₄)

end

/-- `rdx` tested. -/
theorem testRdx_ok (s : State) :
    WP isa (.block [.alu .test .rdx (.reg .rdx)]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.zf = some (s.gpr .rdx == 0) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', BitVec.and_self]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem tailEndB_ok {s : State} :
    WP isa (.block [.mov .rcx (.reg .r9), .mov32 .rdx (.imm 0)]) s fun s' =>
      s'.gpr .rcx = s.gpr .r9 ∧ s'.gpr .rdx = 0 ∧ (∀ r, r ≠ .rcx → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, State.setReg32,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, Option.map_some,
    Option.some.injEq, exists_eq_left', reduceCtorEq, ite_true, ite_false]
  exact ⟨trivial, rfl, fun r h₁ h₂ => by simp [h₁, h₂], trivial, trivial, trivial⟩

theorem tailEnd_ok {s : State} :
    WP isa (.block [.vop .vzeroupper, .mov .rcx (.reg .r9), .mov32 .rdx (.imm 0)]) s fun s' =>
      s'.gpr .rcx = s.gpr .r9 ∧ s'.gpr .rdx = 0 ∧ (∀ r, r ≠ .rcx → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [show ([.vop .vzeroupper, .mov .rcx (.reg .r9), .mov32 .rdx (.imm 0)] : List Instr) =
    [.vop .vzeroupper] ++ [.mov .rcx (.reg .r9), .mov32 .rdx (.imm 0)] from rfl]
  refine WP.block_append (WP.mono (Proof.ChaCha20.X86_64.Avx2.vz_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁⟩ => ?_)
  exact WP.mono tailEndB_ok fun s₂ ⟨c₂, d₂, g₂, m₂, rd₂, wr₂⟩ =>
    ⟨by rw [c₂, g₁], d₂, fun r h₁ h₂ => by rw [g₂ r h₁ h₂, g₁], by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

/-! ## The tail -/

open VG.Spec.ChaCha20 (keystream)
open VG.Proof.Poly1305 (absorbAll)

/-- Before `tailAB`: in the data `⟨dp, L⟩`, the `N` bytes at offset `o`
(the last chunk, or the 448 bytes before the first) to absorb, and the `n`
after them to encrypt; the kernel's registers, the bytes left `n` stored, and
the accumulator `X`. -/
structure TP (c dp : Addr) (L o N n : Nat) (R0 R1 : BitVec 64) (X : Nat) (sp : Addr) (s : State) : Prop where
  st : stR (stA c) ∈ s.wr
  bf : bufR (bfA c) ∈ s.wr
  ps : psR c ∈ s.wr
  dw : (⟨dp, L⟩ : Region) ∈ s.wr
  le : o + N + n ≤ L
  rdi : s.gpr .rdi = stA c
  rcx : s.gpr .rcx = bfA c
  rsi : s.gpr .rsi = dp + BitVec.ofNat 64 o
  rsp : s.gpr .rsp = sp
  left : s.mem.readW (slot (bfA c)) 64 = BitVec.ofNat 64 n
  acc : Acc R0 R1 X s

/-- After `tailAB`, from `s` (`TP`, with `1` to `256` bytes left): the
keystream of the bytes left in `buf`, the `N` bytes before them absorbed, the
accumulator stored, `rbx`, `rbp`, `rdx` the bytes left, `rsi` at `buf`. -/
structure TailMidG (c dp : Addr) (o N n : Nat) (R0 R1 : BitVec 64) (X : Nat) (sp : Addr)
    (s s' : State) : Prop where
  ks : ∀ k < n, s'.mem (bfA c + BitVec.ofNat 64 k) = (keystream (stateAt s.mem (stA c)) n).getD k 0
  acc : leNum (bytesAt s'.mem (psA c) 24) = absorbAll (rN R0 R1) X (bytesAt s.mem (dp + BitVec.ofNat 64 o) N) % P
  frame : Frame [accR c, bufR (bfA c)] s.mem s'.mem
  rbx : s'.gpr .rbx = dp + BitVec.ofNat 64 (o + N)
  rbp : s'.gpr .rbp = BitVec.ofNat 64 n
  rdx : s'.gpr .rdx = BitVec.ofNat 64 n
  rsi : s'.gpr .rsi = bfA c
  r9 : s'.gpr .r9 = bfA c
  rcx : s'.gpr .rcx = bfA c
  r12 : s'.gpr .r12 = s.mem.readW (c + BitVec.ofNat 64 520) 64
  r13 : s'.gpr .r13 = s.mem.readW (c + BitVec.ofNat 64 528) 64
  r14 : s'.gpr .r14 = s.mem.readW (c + BitVec.ofNat 64 536) 64
  r15 : s'.gpr .r15 = c
  rsp : s'.gpr .rsp = sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- `tailAB`, with `1` to `128 S` bytes left. -/
theorem tailABg_ok {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} (hk : Key R0 R1) {X : Nat}
    {o N n : Nat} {sp : Addr} (two pre : Bool) (hN : N = 16 * total pre)
    (hhi : n ≤ 128 * (if two then 2 else 1)) {s : State} (h : TP c dp L o N n R0 R1 X sp s) :
    WP isa (tailAB two pre) s (TailMidG c dp o N n R0 R1 X sp s) := by
  have hLe := hl.L_lt
  have hTL := h.le
  have htot := total_le pre
  -- The bytes of data the stores of `tailA` keep.
  have bd : ∀ k < L, (tMem c s.mem) (dp + BitVec.ofNat 64 k) = s.mem (dp + BitVec.ofNat 64 k) := fun k hk => by
    refine tMem_frame _ _ fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact fun hc => hl.bf_d _ hc (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega) (by omega))
  unfold tailAB
  -- The constants and the setup.
  refine WP.seq (WP.mono (tailA_ok two rfl h.rcx h.rdi h.st h.bf)
    fun s₁ ⟨hz₁, ym₁, m₁, gk₁, _, rd₁, wr₁⟩ => ?_)
  have tb₁ : TB s₁ (if two then 2 else 1) (fun j => ctr (stateAt s.mem (stA c)) j)
      (AccTo (dp + BitVec.ofNat 64 o) R0 R1 X s₁ 0) s₁ := by
    refine ⟨hz₁, ym₁, rfl, fun _ _ => rfl, rfl, rfl, ?_⟩
    simp only [AccTo, Nat.mul_zero]
    rw [show bytesAt s₁.mem (dp + BitVec.ofNat 64 o) 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil]
    have a := h.acc
    exact ⟨by rw [gk₁ _ (by decide) (by decide)]; exact a.r8, by rw [gk₁ _ (by decide) (by decide)]; exact a.r9,
      by rw [gk₁ _ (by decide) (by decide)]; exact a.r10, by rw [gk₁ _ (by decide) (by decide)]; exact a.h2,
      by simp only [hval, gk₁ (Reg.r11) (by decide) (by decide), gk₁ (Reg.rbx) (by decide) (by decide),
        gk₁ (Reg.rbp) (by decide) (by decide)]; exact a.val⟩
  have hrsi₁ : s₁.gpr .rsi = dp + BitVec.ofNat 64 o := by rw [gk₁ _ (by decide) (by decide), h.rsi]
  have hin : ∀ off n', off + n' ≤ N →
      InRegions (s₁.rd ++ s₁.wr) (dp + BitVec.ofNat 64 o + BitVec.ofNat 64 off) n' := by
    intro off n' hn
    refine ⟨_, List.mem_append_right _ (by rw [wr₁]; exact h.dw), ?_⟩
    rw [Offset.add_add]
    exact Offset.contains_base _ (by omega) (by omega)
  -- The rounds.
  refine WP.seq (WP.mono (trounds_ok hk hrsi₁ hin (by omega) rfl tb₁ 10 (by decide)) fun s₂ tb₂ => ?_)
  have hrcx₂ : s₂.gpr .rcx = bfA c := by rw [tb₂.gpr _ (by decide), gk₁ _ (by decide) (by decide), h.rcx]
  have hrdi₂ : s₂.gpr .rdi = stA c := by rw [tb₂.gpr _ (by decide), gk₁ _ (by decide) (by decide), h.rdi]
  have hrsi₂ : s₂.gpr .rsi = dp + BitVec.ofNat 64 o := by rw [tb₂.gpr _ (by decide), hrsi₁]
  have wr₂ : s₂.wr = s.wr := by rw [tb₂.wr, wr₁]
  have m₂ : s₂.mem = tMem c s.mem := by rw [tb₂.mem, m₁]
  have hi₂ : Incs s₂.mem (bfA c) := by rw [m₂]; exact tincs_mem _ _
  refine (WP.mono (tailB_ok two pre rfl tb₂.hb hrcx₂ hrdi₂ (by rw [wr₂]; exact h.st) (by rw [wr₂]; exact h.bf)
    (by rw [wr₂]; exact h.ps) hi₂ tb₂.poly.h2)
    fun s₃ ⟨ks₃, acc₃, f₃, rbx₃, rbp₃, rdx₃, rsi₃, r9₃, r12₃, r13₃, r14₃, r15₃, rcx₃, rsp₃, rd₃, wr₃⟩ => ?_)
  -- What the stores of `tailA` keep in the context.
  have ctxk : ∀ d, 520 ≤ d → d + 8 ≤ 552 →
      s₂.mem.readW (c + BitVec.ofNat 64 d) 64 = s.mem.readW (c + BitVec.ofNat 64 d) 64 := by
    intro d h₁ h₂
    rw [m₂]
    refine (tMem_frame _).readW (r := ⟨c + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint c (Or.inr (by omega)) (by omega) (by decide)
  have hslot : s₂.mem.readW (c + BitVec.ofNat 64 544) 64 = BitVec.ofNat 64 n := by
    rw [ctxk 544 (by decide) (by decide), ← slot_eq, h.left]
  have S₂ : stateAt s₂.mem (stA c) = stateAt s.mem (stA c) := by
    rw [m₂]
    exact Proof.ChaCha20.X86_64.Xor.stateAt_frame (tMem_frame _) (by simpa using st_bf)
  refine ⟨fun k hk => ?_, ?_, ?_, by rw [rbx₃, hrsi₂, hN, Offset.add_add], by rw [rbp₃, hslot], by rw [rdx₃, hslot],
    rsi₃, r9₃, rcx₃, by rw [r12₃, ctxk 520 (by decide) (by decide)], by rw [r13₃, ctxk 528 (by decide) (by decide)],
    by rw [r14₃, ctxk 536 (by decide) (by decide)], r15₃,
    by rw [rsp₃, tb₂.gpr _ (by decide), gk₁ _ (by decide) (by decide), h.rsp], by rw [rd₃, tb₂.rd, rd₁],
    by rw [wr₃, wr₂]⟩
  · have k1 : k < 128 * (if two then 2 else 1) := by omega
    rw [ks₃ k k1, S₂, Proof.ChaCha20.X86_64.Avx2.plus_block, VG.Proof.ChaCha20.keystream_getD _ hk]
  · -- The accumulator: the `N` bytes absorbed.
    have hb1 : bytesAt s₁.mem (dp + BitVec.ofNat 64 o) N = bytesAt s.mem (dp + BitVec.ofNat 64 o) N := by
      rw [m₁]
      refine bytesAt_frame (tMem_frame _) (fun r hr => ?_) (by omega)
      simp only [List.mem_singleton] at hr; subst hr
      exact (hl.bf_d.symm.sub_left (Offset.sub_base _ (by omega)))
    have v := tb₂.poly.val
    rw [firstBlock_ten, ← hN, hb1] at v
    rw [acc₃, v]
  · have f1 : Frame [bufR (bfA c)] s.mem s₂.mem := by rw [m₂]; exact tMem_frame _
    exact (f1.mono (by simp)).trans f₃

/-- `tailS`, with `1` to `128 S` bytes left: those bytes encrypted, the `N`
before them absorbed, the accumulator stored, `rbx`, `rbp` the bytes left,
and the stashed registers restored. -/
theorem tailSg_ok {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} (hk : Key R0 R1) {X : Nat}
    {o N n : Nat} {sp : Addr} (two pre : Bool) (hN : N = 16 * total pre) (hlo : 1 ≤ n)
    (hhi : n ≤ 128 * (if two then 2 else 1)) {s : State} (h : TP c dp L o N n R0 R1 X sp s) :
    WP isa (tailS two pre) s fun s' =>
      (∀ k < n, s'.mem (dp + BitVec.ofNat 64 (o + N) + BitVec.ofNat 64 k) =
        s.mem (dp + BitVec.ofNat 64 (o + N) + BitVec.ofNat 64 k) ^^^
          (keystream (stateAt s.mem (stA c)) n).getD k 0) ∧
      leNum (bytesAt s'.mem (psA c) 24) = absorbAll (rN R0 R1) X (bytesAt s.mem (dp + BitVec.ofNat 64 o) N) % P ∧
      Frame [accR c, bufR (bfA c), ⟨dp + BitVec.ofNat 64 (o + N), n⟩] s.mem s'.mem ∧
      s'.gpr .rbx = dp + BitVec.ofNat 64 (o + N) ∧ s'.gpr .rbp = BitVec.ofNat 64 n ∧
      s'.gpr .rdx = 0 ∧ s'.gpr .rcx = bfA c ∧
      s'.gpr .r12 = s.mem.readW (c + BitVec.ofNat 64 520) 64 ∧
      s'.gpr .r13 = s.mem.readW (c + BitVec.ofNat 64 528) 64 ∧
      s'.gpr .r14 = s.mem.readW (c + BitVec.ofNat 64 536) 64 ∧ s'.gpr .r15 = c ∧
      s'.gpr .rsp = sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hLe := hl.L_lt
  have hTL := h.le
  have hrS : n ≤ 256 := by cases two <;> simp at hhi <;> omega
  have dsub : Region.Sub ⟨dp + BitVec.ofNat 64 (o + N), n⟩ ⟨dp, L⟩ := Offset.sub_base _ (by omega)
  have hDB : (⟨dp + BitVec.ofNat 64 (o + N), n⟩ : Region).Disjoint ⟨bfA c, n⟩ :=
    (hl.bf_d.symm.sub_left dsub).sub_right (Region.sub_prefix (by omega))
  unfold tailS
  refine WP.seq (WP.mono (tailABg_ok hl hk two pre hN hhi h) fun s₃' t₃' => ?_)
  refine WP.seq (WP.mono (testRdx_ok s₃') fun s₃ ⟨g₃, m₃, rd₃, wr₃, _⟩ => ?_)
  have t₃ : TailMidG c dp o N n R0 R1 X sp s s₃ :=
    ⟨fun k hk => by rw [m₃]; exact t₃'.ks k hk, by rw [m₃]; exact t₃'.acc, by rw [m₃]; exact t₃'.frame,
      by rw [g₃]; exact t₃'.rbx, by rw [g₃]; exact t₃'.rbp, by rw [g₃]; exact t₃'.rdx, by rw [g₃]; exact t₃'.rsi,
      by rw [g₃]; exact t₃'.r9, by rw [g₃]; exact t₃'.rcx, by rw [g₃]; exact t₃'.r12, by rw [g₃]; exact t₃'.r13,
      by rw [g₃]; exact t₃'.r14, by rw [g₃]; exact t₃'.r15, by rw [g₃]; exact t₃'.rsp, by rw [rd₃]; exact t₃'.rd,
      by rw [wr₃]; exact t₃'.wr⟩
  -- The bytes left.
  refine WP.seq (WP.mono (XorBufX.xorBufX_ok (w := 5) (by decide) (d := .rbx) (by decide)
    (D := dp + BitVec.ofNat 64 (o + N)) (B := bfA c) (n := n)
    t₃.rbx t₃.rsi t₃.rdx (by omega) hDB
    ⟨_, by rw [t₃.wr]; exact h.dw, Offset.contains_base _ (by omega) (by omega)⟩
    ⟨_, List.mem_append_right _ (by rw [t₃.wr]; exact h.bf),
      by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩)
    fun s₄ x₄ => ?_)
  refine WP.mono tailEnd_ok fun s₅ ⟨rcx₅, rdx₅, g₅, m₅, rd₅, wr₅⟩ => ?_
  have g45 : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .rdi → s₅.gpr r = s₃.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 => by rw [g₅ r h3 h4, x₄.keep r h1 h2 h3 h4 h5 h6]
  -- The bytes left are apart from what `tailAB` writes.
  have nd : ∀ k < n, ∀ x ∈ [accR c, bufR (bfA c)],
      ¬ x.Contains (dp + BitVec.ofNat 64 (o + N) + BitVec.ofNat 64 k) 1 := by
    intro k hk x hx hc
    have hin' : (⟨dp, L⟩ : Region).Contains (dp + BitVec.ofNat 64 (o + N) + BitVec.ofNat 64 k) 1 := by
      rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hl.cd (d := 448) (n := 24) (by decide) _ hc hin'
    · exact hl.bf_d _ hc hin'
  have gg : ∀ r, r = .rbx ∨ r = .rbp ∨ r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .r15 ∨ r = .rsp →
      s₅.gpr r = s₃.gpr r := by
    intro r hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact g45 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨fun k hk => ?_, ?_, ?_, by rw [gg _ (.inl rfl), t₃.rbx], by rw [gg _ (.inr (.inl rfl)), t₃.rbp], rdx₅,
    by rw [rcx₅, x₄.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), t₃.r9],
    by rw [gg _ (by simp), t₃.r12], by rw [gg _ (by simp), t₃.r13], by rw [gg _ (by simp), t₃.r14],
    by rw [gg _ (by simp), t₃.r15], by rw [gg _ (by simp), t₃.rsp],
    by rw [rd₅, x₄.rd, t₃.rd], by rw [wr₅, x₄.wr, t₃.wr]⟩
  · -- The data.
    rw [m₅, x₄.data k hk, t₃.frame _ (nd k hk), t₃.ks k hk]
  · -- The accumulator.
    have hb4 : bytesAt s₄.mem (psA c) 24 = bytesAt s₃.mem (psA c) 24 := by
      refine bytesAt_frame x₄.frame (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact (hl.cd (d := 448) (n := 24) (by decide)).sub_right dsub
    rw [m₅, hb4, t₃.acc]
  · -- The frame.
    rw [m₅]
    exact (t₃.frame.mono (by simp)).trans (x₄.frame.mono (by simp))

/-- `TP` after the whole chunks: the last chunk to absorb. -/
theorem TP.of_LI {c dp : Addr} {L : Nat} {R0 R1 : BitVec 64} {A : Nat} {m₀ : Mem} {sp : Addr} {T : Nat}
    {s : State} (h : LI c dp L R0 R1 A m₀ sp T s) :
    TP c dp L (512 * (T - 1)) 512 (L - 512 * T) R0 R1
      (absorbAll (rN R0 R1) A (bytesAt s.mem dp (512 * (T - 1)))) sp s := by
  have ht := h.t1
  have hTL := h.le
  exact ⟨by rw [h.wr]; simp, by rw [h.wr]; simp, by rw [h.wr]; simp, by rw [h.wr]; simp, by omega, h.rdi, h.rcx,
    h.rsi, h.rsp, h.left, h.acc⟩

/-- The chunks before the tail and the last one, absorbed. -/
theorem absorb_last (m : Mem) (dp : Addr) {R0 R1 : BitVec 64} {A T : Nat} (ht : 1 ≤ T) :
    absorbAll (rN R0 R1) (absorbAll (rN R0 R1) A (bytesAt m dp (512 * (T - 1))))
      (bytesAt m (dp + BitVec.ofNat 64 (512 * (T - 1))) 512) = absorbAll (rN R0 R1) A (bytesAt m dp (512 * T)) := by
  rw [show 512 * T = 512 * (T - 1) + 512 by omega, VG.Proof.Poly1305.bytesAt_add,
    VG.Proof.Poly1305.absorbAll_append (by rw [VG.Proof.Poly1305.length_bytesAt]; omega)]

/-- After `tailAB`, from `s` (`LI` with `1` to `256` bytes left): the
keystream of the bytes left in `buf`, the last chunk absorbed, the
accumulator stored, `rbx`, `rbp`, `rdx` the bytes left, `rsi` at `buf`. -/
structure TailMid (c dp : Addr) (L : Nat) (R0 R1 : BitVec 64) (A : Nat) (sp : Addr) (T : Nat)
    (s s' : State) : Prop where
  ks : ∀ k < L - 512 * T, s'.mem (bfA c + BitVec.ofNat 64 k) =
    (keystream (stateAt s.mem (stA c)) (L - 512 * T)).getD k 0
  acc : leNum (bytesAt s'.mem (psA c) 24) = absorbAll (rN R0 R1) A (bytesAt s.mem dp (512 * T)) % P
  frame : Frame [accR c, bufR (bfA c)] s.mem s'.mem
  rbx : s'.gpr .rbx = dp + BitVec.ofNat 64 (512 * T)
  rbp : s'.gpr .rbp = BitVec.ofNat 64 (L - 512 * T)
  rdx : s'.gpr .rdx = BitVec.ofNat 64 (L - 512 * T)
  rsi : s'.gpr .rsi = bfA c
  r9 : s'.gpr .r9 = bfA c
  rcx : s'.gpr .rcx = bfA c
  r12 : s'.gpr .r12 = s.mem.readW (c + BitVec.ofNat 64 520) 64
  r13 : s'.gpr .r13 = s.mem.readW (c + BitVec.ofNat 64 528) 64
  r14 : s'.gpr .r14 = s.mem.readW (c + BitVec.ofNat 64 536) 64
  r15 : s'.gpr .r15 = c
  rsp : s'.gpr .rsp = sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- `tailAB`, after the whole chunks with `1` to `128 S` bytes left. -/
theorem tailAB_ok {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} (hk : Key R0 R1) {A : Nat}
    {m₀ : Mem} {sp : Addr} {T : Nat} (two : Bool)
    (hhi : L - 512 * T ≤ 128 * (if two then 2 else 1)) {s : State} (h : LI c dp L R0 R1 A m₀ sp T s) :
    WP isa (tailAB two false) s (TailMid c dp L R0 R1 A sp T s) := by
  have ht := h.t1
  have e : 512 * (T - 1) + 512 = 512 * T := by omega
  refine WP.mono (tailABg_ok hl hk two false (N := 512) rfl hhi (TP.of_LI h)) fun s' t => ?_
  exact ⟨t.ks, by rw [t.acc, absorb_last _ _ ht], t.frame, by rw [t.rbx, e], t.rbp, t.rdx, t.rsi, t.r9, t.rcx,
    t.r12, t.r13, t.r14, t.r15, t.rsp, t.rd, t.wr⟩

/-- `tailS`, after the whole chunks with `1` to `128 S` bytes left: those
bytes encrypted, the last chunk absorbed (so all the chunks' ciphertext),
the accumulator stored, `rbx`, `rbp` the bytes left, and the stashed
registers restored. -/
theorem tailS_ok {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} (hk : Key R0 R1) {A : Nat}
    {m₀ : Mem} {sp : Addr} {T : Nat} (two : Bool) (hlo : 1 ≤ L - 512 * T)
    (hhi : L - 512 * T ≤ 128 * (if two then 2 else 1)) {s : State} (h : LI c dp L R0 R1 A m₀ sp T s) :
    WP isa (tailS two false) s fun s' =>
      (∀ k < L - 512 * T, s'.mem (dp + BitVec.ofNat 64 (512 * T) + BitVec.ofNat 64 k) =
        s.mem (dp + BitVec.ofNat 64 (512 * T) + BitVec.ofNat 64 k) ^^^
          (keystream (stateAt s.mem (stA c)) (L - 512 * T)).getD k 0) ∧
      leNum (bytesAt s'.mem (psA c) 24) = absorbAll (rN R0 R1) A (bytesAt s.mem dp (512 * T)) % P ∧
      Frame [accR c, bufR (bfA c), ⟨dp + BitVec.ofNat 64 (512 * T), L - 512 * T⟩] s.mem s'.mem ∧
      s'.gpr .rbx = dp + BitVec.ofNat 64 (512 * T) ∧ s'.gpr .rbp = BitVec.ofNat 64 (L - 512 * T) ∧
      s'.gpr .rdx = 0 ∧ s'.gpr .rcx = bfA c ∧
      s'.gpr .r12 = s.mem.readW (c + BitVec.ofNat 64 520) 64 ∧
      s'.gpr .r13 = s.mem.readW (c + BitVec.ofNat 64 528) 64 ∧
      s'.gpr .r14 = s.mem.readW (c + BitVec.ofNat 64 536) 64 ∧ s'.gpr .r15 = c ∧
      s'.gpr .rsp = sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ht := h.t1
  have e : 512 * (T - 1) + 512 = 512 * T := by omega
  refine WP.mono (tailSg_ok hl hk two false (N := 512) rfl hlo hhi (TP.of_LI h)) fun s' t => ?_
  rw [e] at t
  obtain ⟨d, a, f, rest⟩ := t
  exact ⟨d, by rw [a, absorb_last _ _ ht], f, rest⟩

/-! ## 257 to 448 bytes left: `tailK` -/

open VG.Proof.ChaCha20.X86_64.Avx2 (slotsR slotsR_sub plus_block)
open VG.Proof.ChaCha20 (keystream_getD)

theorem movK_ok (s : State) :
    WP isa (.block movK) s fun s' =>
      s'.gpr .r9 = s.gpr .rcx ∧ s'.gpr .rsi = s.gpr .rcx + BitVec.ofNat 64 608 ∧ s'.gpr .rdx = s.gpr .rbp ∧
      (∀ r, r ≠ .r9 → r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  have e : BitVec.signExtend 64 (BitVec.ofNat 32 608) = BitVec.ofNat 64 608 := by decide
  simp only [movK, kOff, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, e,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', reduceCtorEq, ite_true, ite_false]
  exact ⟨trivial, trivial, trivial, fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃], trivial, trivial, trivial⟩

/-- After `tailKAB`, from `s` (`TP`, with up to 512 bytes left): the
keystream of the bytes left at `kA`, the `N` bytes before them absorbed, the
accumulator stored, `rbx`, `rbp`, `rdx` the bytes left, `rsi` at `kA`. -/
structure TailMidKg (c dp : Addr) (o N n : Nat) (R0 R1 : BitVec 64) (X : Nat) (sp : Addr)
    (s s' : State) : Prop where
  ks : ∀ k < n, s'.mem (kA (bfA c) + BitVec.ofNat 64 k) = (keystream (stateAt s.mem (stA c)) n).getD k 0
  acc : leNum (bytesAt s'.mem (psA c) 24) = absorbAll (rN R0 R1) X (bytesAt s.mem (dp + BitVec.ofNat 64 o) N) % P
  frame : Frame [slotsR (bfA c), kR (bfA c), accR c] s.mem s'.mem
  rbx : s'.gpr .rbx = dp + BitVec.ofNat 64 (o + N)
  rbp : s'.gpr .rbp = BitVec.ofNat 64 n
  rdx : s'.gpr .rdx = BitVec.ofNat 64 n
  rsi : s'.gpr .rsi = kA (bfA c)
  r9 : s'.gpr .r9 = bfA c
  r12 : s'.gpr .r12 = s.mem.readW (c + BitVec.ofNat 64 520) 64
  r13 : s'.gpr .r13 = s.mem.readW (c + BitVec.ofNat 64 528) 64
  r14 : s'.gpr .r14 = s.mem.readW (c + BitVec.ofNat 64 536) 64
  r15 : s'.gpr .r15 = c
  rsp : s'.gpr .rsp = sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- `tailKAB`, with up to 512 bytes left after the `N` at `dp + o` (the last
chunk, or, `pre`, the 448 bytes before the first). -/
theorem tailKABg_ok (vl pre : Bool) {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64}
    (hk : Key R0 R1) {X : Nat} {o N n : Nat} {sp : Addr} (hN : N = 16 * total pre) (ho : o + 512 ≤ L)
    (hn : n ≤ 512) {s : State} (h : TP c dp L o N n R0 R1 X sp s) (hc : Consts s.mem (bfA c))
    (mk : kR (bfA c) ∈ s.wr) :
    WP isa (tailKAB vl pre) s (TailMidKg c dp o N n R0 R1 X sp s) := by
  have hLe := hl.L_lt
  have hq : dp + BitVec.ofNat 64 o + tot pre = dp + BitVec.ofNat 64 (o + N) := by
    rw [hN]; exact Offset.add_add _ _ _
  have wsub : Region.Sub (Proof.ChaCha20.X86_64.Avx2.dR5 (dp + BitVec.ofNat 64 o)) ⟨dp, L⟩ :=
    Offset.sub_base dp ho
  have hin : ∀ off n, off + n ≤ 512 →
      InRegions (s.rd ++ s.wr) (dp + BitVec.ofNat 64 o + BitVec.ofNat 64 off) n := by
    intro off n hn'
    exact ⟨_, List.mem_append_right _ h.dw, by
      rw [Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have dqs : (Proof.ChaCha20.X86_64.Avx2.dR5 (dp + BitVec.ofNat 64 o)).Disjoint
      (Proof.ChaCha20.X86_64.Avx2.slotsR (bfA c)) :=
    ((hl.cd (d := 128) (n := 128) (by decide)).sub_right wsub).symm
  have kc : kR (bfA c) = ⟨c + BitVec.ofNat 64 736, 512⟩ := by simp only [kR, kA, bfA, Offset.add_add]
  have dsk : (stR (stA c)).Disjoint (kR (bfA c)) := by
    rw [kc]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  have dbk : (bufR (bfA c)).Disjoint (kR (bfA c)) := by
    rw [kc]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  have dak : (accR c).Disjoint (kR (bfA c)) := by
    rw [kc]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  unfold tailKAB
  refine WP.seq (WP.mono (tailKMain_ok vl pre hk h.rdi h.rcx h.rsi h.st h.bf mk
    (fun o n h => hin o n (Nat.le_trans h (Nat.mul_le_mul_left 16 (total_le pre)))) hc st_bf dsk dbk
    (dqs.sub_left (Region.sub_prefix (by cases pre <;> decide))) h.acc)
    fun s₁ ⟨d₁, a₁, f₁, g₁, rd₁, wr₁⟩ => ?_)
  rw [leaveT_eq, List.append_assoc]
  refine WP.block_append (WP.mono (Proof.Poly1305.X86_64.reduce_ok s₁) fun s₂ ⟨red, k₂⟩ => ?_)
  refine WP.block_append (WP.mono (storeT_ok pre (c := c) (s := s₂) (by rw [k₂.gpr', g₁ _ (by decide), h.rcx])
    (by rw [k₂.2.2.2, wr₁]; exact h.ps)) fun s₃ ⟨m₃, rbx₃, rbp₃, r12₃, r13₃, r14₃, r15₃, g₃, rd₃, wr₃⟩ => ?_)
  refine WP.mono (movK_ok s₃) fun s₄ ⟨r9₄, rsi₄, rdx₄, g₄, m₄, rd₄, wr₄⟩ => ?_
  have rcx₂ : s₂.gpr .rcx = bfA c := by rw [k₂.gpr', g₁ _ (by decide), h.rcx]
  have rcx₃ : s₃.gpr .rcx = bfA c := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rcx₂]
  have rsp₃ : s₃.gpr .rsp = sp := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k₂.gpr', g₁ _ (by decide),
      h.rsp]
  have mA : s₃.mem = accMem s₁.mem c (s₂.gpr .r11) (s₂.gpr .rbx) (s₂.gpr .rbp) := by rw [m₃, k₂.2.1]
  have fa : Frame [accR c] s₁.mem s₃.mem := by rw [mA]; exact accMem_frame _ _ _ _ _
  have F₃ : Frame [slotsR (bfA c), kR (bfA c), accR c] s.mem s₃.mem := (f₁.mono (by simp)).trans (fa.mono (by simp))
  have nst : ∀ d, 520 ≤ d → d + 8 ≤ 552 → ∀ r ∈ [slotsR (bfA c), kR (bfA c), accR c],
      (⟨c + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    intro d h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint c (Or.inr (by omega_arith)) (by omega_arith) (by decide)
    · rw [kc]; exact Offset.disjoint c (Or.inl (by omega_arith)) (by omega_arith) (by decide)
    · exact Offset.disjoint c (Or.inr (by omega_arith)) (by omega_arith) (by decide)
  have rd₁' : ∀ d, 520 ≤ d → d + 8 ≤ 552 →
      s₁.mem.readW (c + BitVec.ofNat 64 d) 64 = s.mem.readW (c + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    f₁.readW (Region.contains_self _ _) (fun r hr => nst d h₁ h₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)) (by decide)
  have rbp₄ : s₄.gpr .rbp = BitVec.ofNat 64 n := by
    rw [g₄ _ (by decide) (by decide) (by decide), rbp₃, k₂.2.1, rd₁' 544 (by decide) (by decide), ← slot_eq, h.left]
  have rbx₄ : s₄.gpr .rbx = dp + BitVec.ofNat 64 (o + N) := by
    rw [g₄ _ (by decide) (by decide) (by decide), rbx₃, k₂.gpr', g₁ _ (by decide), h.rsi, hq]
  have rsi₄' : s₄.gpr .rsi = kA (bfA c) := by rw [rsi₄, rcx₃]
  have rdx₄' : s₄.gpr .rdx = BitVec.ofNat 64 n := by rw [rdx₄, ← rbp₄, g₄ _ (by decide) (by decide) (by decide)]
  have ks₄ : ∀ k < n, s₄.mem (kA (bfA c) + BitVec.ofNat 64 k) =
      (keystream (stateAt s.mem (stA c)) n).getD k 0 := by
    intro k hk'
    rw [m₄, fa _ (fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dak _ hc (kR_contains _ (by omega))), d₁ k (by omega), plus_block, keystream_getD _ hk']
  have gk : ∀ r, r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .r15 ∨ r = .rsp → s₄.gpr r = s₃.gpr r := by
    intro r hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide) (by decide)
  refine ⟨ks₄, ?_, by rw [m₄]; exact F₃, rbx₄, rbp₄, rdx₄', rsi₄', by rw [r9₄, rcx₃],
    by rw [gk _ (by simp), r12₃, k₂.2.1, rd₁' 520 (by decide) (by decide)],
    by rw [gk _ (by simp), r13₃, k₂.2.1, rd₁' 528 (by decide) (by decide)],
    by rw [gk _ (by simp), r14₃, k₂.2.1, rd₁' 536 (by decide) (by decide)],
    by rw [gk _ (by simp), r15₃], by rw [gk _ (by simp), rsp₃],
    by rw [rd₄, rd₃, k₂.2.2.1, rd₁], by rw [wr₄, wr₃, k₂.2.2.2, wr₁]⟩
  rw [m₄, mA, accMem_acc]
  show hval s₂ = _
  rw [red a₁.h2, a₁.val, ← hN]

/-- `tailKX`, with 1 to 512 bytes left after the `N` at `dp + o`: those bytes
encrypted from the keystream stored at `kA`, the `N` absorbed, the
accumulator stored, `rbx`, `rbp` the bytes left, and the stashed registers
restored, as `tailSg_ok`. -/
theorem tailKXg_ok (vl pre : Bool) {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64}
    (hk : Key R0 R1) {X : Nat} {o N n : Nat} {sp : Addr} (hN : N = 16 * total pre) (ho : o + 512 ≤ L)
    (hlo : 1 ≤ n) (hn : n ≤ 512) {s : State} (h : TP c dp L o N n R0 R1 X sp s) (hc : Consts s.mem (bfA c))
    (mk : kR (bfA c) ∈ s.wr) :
    WP isa (tailKX vl pre) s fun s' =>
      (∀ k < n, s'.mem (dp + BitVec.ofNat 64 (o + N) + BitVec.ofNat 64 k) =
        s.mem (dp + BitVec.ofNat 64 (o + N) + BitVec.ofNat 64 k) ^^^
          (keystream (stateAt s.mem (stA c)) n).getD k 0) ∧
      leNum (bytesAt s'.mem (psA c) 24) = absorbAll (rN R0 R1) X (bytesAt s.mem (dp + BitVec.ofNat 64 o) N) % P ∧
      Frame [accR c, bufR (bfA c), kR (bfA c), ⟨dp + BitVec.ofNat 64 (o + N), n⟩] s.mem s'.mem ∧
      s'.gpr .rbx = dp + BitVec.ofNat 64 (o + N) ∧ s'.gpr .rbp = BitVec.ofNat 64 n ∧
      s'.gpr .rdx = 0 ∧ s'.gpr .rcx = bfA c ∧
      s'.gpr .r12 = s.mem.readW (c + BitVec.ofNat 64 520) 64 ∧
      s'.gpr .r13 = s.mem.readW (c + BitVec.ofNat 64 528) 64 ∧
      s'.gpr .r14 = s.mem.readW (c + BitVec.ofNat 64 536) 64 ∧ s'.gpr .r15 = c ∧
      s'.gpr .rsp = sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hLe := hl.L_lt
  have hTL := h.le
  have md := h.dw
  have kc : kR (bfA c) = ⟨c + BitVec.ofNat 64 736, 512⟩ := by simp only [kR, kA, bfA, Offset.add_add]
  have dsub : Region.Sub ⟨dp + BitVec.ofNat 64 (o + N), n⟩ ⟨dp, L⟩ := Offset.sub_base _ (by omega)
  have hDK : (⟨dp + BitVec.ofNat 64 (o + N), n⟩ : Region).Disjoint ⟨kA (bfA c), n⟩ := by
    have e : (⟨kA (bfA c), n⟩ : Region) = ⟨c + BitVec.ofNat 64 736, n⟩ := by
      simp only [kA, bfA, Offset.add_add]
    rw [e]; exact (hl.cd (d := 736) (n := n) (by omega)).symm.sub_left dsub
  unfold tailKX
  refine WP.seq (WP.mono (tailKABg_ok vl pre hl hk hN ho hn h hc mk) fun s₃' t₃' => ?_)
  refine WP.seq (WP.mono (testRdx_ok s₃') fun s₃ ⟨g₃, m₃, rd₃, wr₃, _⟩ => ?_)
  have t₃ : TailMidKg c dp o N n R0 R1 X sp s s₃ :=
    ⟨fun k hk => by rw [m₃]; exact t₃'.ks k hk, by rw [m₃]; exact t₃'.acc, by rw [m₃]; exact t₃'.frame,
      by rw [g₃]; exact t₃'.rbx, by rw [g₃]; exact t₃'.rbp, by rw [g₃]; exact t₃'.rdx, by rw [g₃]; exact t₃'.rsi,
      by rw [g₃]; exact t₃'.r9, by rw [g₃]; exact t₃'.r12, by rw [g₃]; exact t₃'.r13,
      by rw [g₃]; exact t₃'.r14, by rw [g₃]; exact t₃'.r15, by rw [g₃]; exact t₃'.rsp, by rw [rd₃]; exact t₃'.rd,
      by rw [wr₃]; exact t₃'.wr⟩
  -- The bytes left.
  refine WP.seq (WP.mono (XorBufX.xorBufX_ok (w := 5) (by decide) (d := .rbx) (by decide)
    (D := dp + BitVec.ofNat 64 (o + N)) (B := kA (bfA c)) (n := n)
    t₃.rbx t₃.rsi t₃.rdx (by omega) hDK
    ⟨_, by rw [t₃.wr]; exact md, Offset.contains_base _ (by omega) (by omega)⟩
    ⟨_, List.mem_append_right _ (by rw [t₃.wr]; exact mk),
      by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩)
    fun s₄ x₄ => ?_)
  refine WP.mono tailEnd_ok fun s₅ ⟨rcx₅, rdx₅, g₅, m₅, rd₅, wr₅⟩ => ?_
  have g45 : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .rdi → s₅.gpr r = s₃.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 => by rw [g₅ r h3 h4, x₄.keep r h1 h2 h3 h4 h5 h6]
  -- The bytes left are apart from what `tailKAB` writes.
  have nd : ∀ k < n, ∀ x ∈ [slotsR (bfA c), kR (bfA c), accR c],
      ¬ x.Contains (dp + BitVec.ofNat 64 (o + N) + BitVec.ofNat 64 k) 1 := by
    intro k hk' x hx hc'
    have hin' : (⟨dp, L⟩ : Region).Contains (dp + BitVec.ofNat 64 (o + N) + BitVec.ofNat 64 k) 1 := by
      rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hl.cd (d := 128) (n := 128) (by decide) _ (by simpa [bfA, Offset.add_add] using hc') hin'
    · exact hl.cd (d := 736) (n := 512) (by decide) _ (by rw [kc] at hc'; exact hc') hin'
    · exact hl.cd (d := 448) (n := 24) (by decide) _ hc' hin'
  have gg : ∀ r, r = .rbx ∨ r = .rbp ∨ r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .r15 ∨ r = .rsp →
      s₅.gpr r = s₃.gpr r := by
    intro r hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact g45 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨fun k hk => ?_, ?_, ?_, by rw [gg _ (.inl rfl), t₃.rbx], by rw [gg _ (.inr (.inl rfl)), t₃.rbp], rdx₅,
    by rw [rcx₅, x₄.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), t₃.r9],
    by rw [gg _ (by simp), t₃.r12], by rw [gg _ (by simp), t₃.r13], by rw [gg _ (by simp), t₃.r14],
    by rw [gg _ (by simp), t₃.r15], by rw [gg _ (by simp), t₃.rsp],
    by rw [rd₅, x₄.rd, t₃.rd], by rw [wr₅, x₄.wr, t₃.wr]⟩
  · -- The data.
    rw [m₅, x₄.data k hk, t₃.frame _ (nd k hk), t₃.ks k hk]
  · -- The accumulator.
    have hb4 : bytesAt s₄.mem (psA c) 24 = bytesAt s₃.mem (psA c) 24 := by
      refine bytesAt_frame x₄.frame (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact (hl.cd (d := 448) (n := 24) (by decide)).sub_right dsub
    rw [m₅, hb4, t₃.acc]
  · -- The frame.
    rw [m₅]
    refine (t₃.frame.sub fun r hr => ?_).trans (x₄.frame.mono (by simp))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨bufR (bfA c), by simp, slotsR_sub _⟩
    · exact ⟨kR (bfA c), by simp, fun _ h => h⟩
    · exact ⟨accR c, by simp, fun _ h => h⟩

/-- After `tailKAB`, from `s` (`LI` with 257 to 448 bytes left): the
keystream of the bytes left at `kA`, the last chunk absorbed, the accumulator
stored, `rbx`, `rbp`, `rdx` the bytes left, `rsi` at `kA`. -/
structure TailMidK (c dp : Addr) (L : Nat) (R0 R1 : BitVec 64) (A : Nat) (sp : Addr) (T : Nat)
    (s s' : State) : Prop where
  ks : ∀ k < L - 512 * T, s'.mem (kA (bfA c) + BitVec.ofNat 64 k) =
    (keystream (stateAt s.mem (stA c)) (L - 512 * T)).getD k 0
  acc : leNum (bytesAt s'.mem (psA c) 24) = absorbAll (rN R0 R1) A (bytesAt s.mem dp (512 * T)) % P
  frame : Frame [slotsR (bfA c), kR (bfA c), accR c] s.mem s'.mem
  rbx : s'.gpr .rbx = dp + BitVec.ofNat 64 (512 * T)
  rbp : s'.gpr .rbp = BitVec.ofNat 64 (L - 512 * T)
  rdx : s'.gpr .rdx = BitVec.ofNat 64 (L - 512 * T)
  rsi : s'.gpr .rsi = kA (bfA c)
  r9 : s'.gpr .r9 = bfA c
  r12 : s'.gpr .r12 = s.mem.readW (c + BitVec.ofNat 64 520) 64
  r13 : s'.gpr .r13 = s.mem.readW (c + BitVec.ofNat 64 528) 64
  r14 : s'.gpr .r14 = s.mem.readW (c + BitVec.ofNat 64 536) 64
  r15 : s'.gpr .r15 = c
  rsp : s'.gpr .rsp = sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- `tailKAB`, after the whole chunks with 257 to 448 bytes left. -/
theorem tailKAB_ok (vl : Bool) {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} (hk : Key R0 R1)
    {A : Nat} {m₀ : Mem} {sp : Addr} {T : Nat} (hlo : 257 ≤ L - 512 * T) (hhi : L - 512 * T ≤ 448) {s : State}
    (h : LI c dp L R0 R1 A m₀ sp T s) :
    WP isa (tailKAB vl false) s (TailMidK c dp L R0 R1 A sp T s) := by
  have ht := h.t1
  have hTL := h.le
  have e : 512 * (T - 1) + 512 = 512 * T := by omega_arith
  refine WP.mono (tailKABg_ok vl false hl hk (N := 512) rfl (by omega_arith) (by omega_arith) (TP.of_LI h)
    h.consts (by rw [h.wr]; simp)) fun s' t => ?_
  exact ⟨t.ks, by rw [t.acc, absorb_last _ _ ht], t.frame, by rw [t.rbx, e], t.rbp, t.rdx, t.rsi, t.r9,
    t.r12, t.r13, t.r14, t.r15, t.rsp, t.rd, t.wr⟩

/-- `tailK`, after the whole chunks with 257 to 448 bytes left: those bytes
encrypted from the keystream stored at `kA`, the last chunk absorbed, the
accumulator stored, `rbx`, `rbp` the bytes left, and the stashed registers
restored, as `tailS_ok`. -/
theorem tailKX_ok (vl : Bool) {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} (hk : Key R0 R1)
    {A : Nat} {m₀ : Mem} {sp : Addr} {T : Nat} (hlo : 257 ≤ L - 512 * T) (hhi : L - 512 * T ≤ 448) {s : State}
    (h : LI c dp L R0 R1 A m₀ sp T s) :
    WP isa (tailKX vl false) s fun s' =>
      (∀ k < L - 512 * T, s'.mem (dp + BitVec.ofNat 64 (512 * T) + BitVec.ofNat 64 k) =
        s.mem (dp + BitVec.ofNat 64 (512 * T) + BitVec.ofNat 64 k) ^^^
          (keystream (stateAt s.mem (stA c)) (L - 512 * T)).getD k 0) ∧
      leNum (bytesAt s'.mem (psA c) 24) = absorbAll (rN R0 R1) A (bytesAt s.mem dp (512 * T)) % P ∧
      Frame [accR c, bufR (bfA c), kR (bfA c), ⟨dp + BitVec.ofNat 64 (512 * T), L - 512 * T⟩] s.mem s'.mem ∧
      s'.gpr .rbx = dp + BitVec.ofNat 64 (512 * T) ∧ s'.gpr .rbp = BitVec.ofNat 64 (L - 512 * T) ∧
      s'.gpr .rdx = 0 ∧ s'.gpr .rcx = bfA c ∧
      s'.gpr .r12 = s.mem.readW (c + BitVec.ofNat 64 520) 64 ∧
      s'.gpr .r13 = s.mem.readW (c + BitVec.ofNat 64 528) 64 ∧
      s'.gpr .r14 = s.mem.readW (c + BitVec.ofNat 64 536) 64 ∧ s'.gpr .r15 = c ∧
      s'.gpr .rsp = sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ht := h.t1
  have hTL := h.le
  have e : 512 * (T - 1) + 512 = 512 * T := by omega_arith
  refine WP.mono (tailKXg_ok vl false hl hk (N := 512) rfl (by omega_arith) (by omega_arith) (by omega_arith)
    (TP.of_LI h) h.consts (by rw [h.wr]; simp)) fun s' t => ?_
  rw [e] at t
  obtain ⟨d, a, f, rest⟩ := t
  exact ⟨d, by rw [a, absorb_last _ _ ht], f, rest⟩

/-- `tailK`: `tailKX` and its padding, which writes only `rax`. -/
theorem tailK_ok (vl : Bool) {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} (hk : Key R0 R1)
    {A : Nat} {m₀ : Mem} {sp : Addr} {T : Nat} (hlo : 257 ≤ L - 512 * T) (hhi : L - 512 * T ≤ 448) {s : State}
    (h : LI c dp L R0 R1 A m₀ sp T s) :
    WP isa (tailK vl) s fun s' =>
      (∀ k < L - 512 * T, s'.mem (dp + BitVec.ofNat 64 (512 * T) + BitVec.ofNat 64 k) =
        s.mem (dp + BitVec.ofNat 64 (512 * T) + BitVec.ofNat 64 k) ^^^
          (keystream (stateAt s.mem (stA c)) (L - 512 * T)).getD k 0) ∧
      leNum (bytesAt s'.mem (psA c) 24) = absorbAll (rN R0 R1) A (bytesAt s.mem dp (512 * T)) % P ∧
      Frame [accR c, bufR (bfA c), kR (bfA c), ⟨dp + BitVec.ofNat 64 (512 * T), L - 512 * T⟩] s.mem s'.mem ∧
      s'.gpr .rbx = dp + BitVec.ofNat 64 (512 * T) ∧ s'.gpr .rbp = BitVec.ofNat 64 (L - 512 * T) ∧
      s'.gpr .rdx = 0 ∧ s'.gpr .rcx = bfA c ∧
      s'.gpr .r12 = s.mem.readW (c + BitVec.ofNat 64 520) 64 ∧
      s'.gpr .r13 = s.mem.readW (c + BitVec.ofNat 64 528) 64 ∧
      s'.gpr .r14 = s.mem.readW (c + BitVec.ofNat 64 536) 64 ∧ s'.gpr .r15 = c ∧
      s'.gpr .rsp = sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold tailK
  refine WP.seq (WP.mono (tailKX_ok vl hl hk hlo hhi h)
    fun t ⟨d, a, f, rbx, rbp, rdx, rcx, r12, r13, r14, r15, rsp, rd, wr⟩ => ?_)
  refine WP.mono (padIns_ok .rax (by decide) t) fun u p => ?_
  exact ⟨fun k hk => by rw [p.mem]; exact d k hk, by rw [p.mem]; exact a, by rw [p.mem]; exact f,
    by rw [p.gpr _ (by decide)]; exact rbx, by rw [p.gpr _ (by decide)]; exact rbp,
    by rw [p.gpr _ (by decide)]; exact rdx, by rw [p.gpr _ (by decide)]; exact rcx,
    by rw [p.gpr _ (by decide)]; exact r12, by rw [p.gpr _ (by decide)]; exact r13,
    by rw [p.gpr _ (by decide)]; exact r14, by rw [p.gpr _ (by decide)]; exact r15,
    by rw [p.gpr _ (by decide)]; exact rsp, by rw [p.rd]; exact rd, by rw [p.wr]; exact wr⟩

/-! ## Choosing the last bytes' path -/

/-- `LI` reads no flag, and of the registers only the kernel's and Poly1305's
key and accumulator. -/
theorem LI.of_rdx {c dp : Addr} {L : Nat} {R0 R1 : BitVec 64} {A : Nat} {m₀ : Mem} {sp : Addr} {T : Nat}
    {s s' : State} (h : LI c dp L R0 R1 A m₀ sp T s) (hg : ∀ r, r ≠ .rdx → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : LI c dp L R0 R1 A m₀ sp T s' :=
  ⟨by rw [hrd, h.rd], by rw [hwr, h.wr], by rw [hg _ (by decide), h.rdi], by rw [hg _ (by decide), h.rcx],
    by rw [hg _ (by decide), h.rsi], by rw [hg _ (by decide), h.rsp], h.t1, h.le, by rw [hm, h.left],
    by rw [hm, h.cnt], fun k hk => by rw [hm, h.data k hk], by rw [hm]; exact h.consts,
    ⟨by rw [hg _ (by decide)]; exact h.acc.r8, by rw [hg _ (by decide)]; exact h.acc.r9,
      by rw [hg _ (by decide)]; exact h.acc.r10, by rw [hg _ (by decide)]; exact h.acc.h2,
      by simp only [hval, hg Reg.r11 (by decide), hg Reg.rbx (by decide), hg Reg.rbp (by decide)]
         rw [hm]; exact h.acc.val⟩,
    by rw [hm]; exact h.fr⟩

/-- `LI` reads no flag, and of the registers only the kernel's and Poly1305's
key and accumulator. -/
theorem LI.of_rax {c dp : Addr} {L : Nat} {R0 R1 : BitVec 64} {A : Nat} {m₀ : Mem} {sp : Addr} {T : Nat}
    {s s' : State} (h : LI c dp L R0 R1 A m₀ sp T s) (hg : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : LI c dp L R0 R1 A m₀ sp T s' :=
  ⟨by rw [hrd, h.rd], by rw [hwr, h.wr], by rw [hg _ (by decide), h.rdi], by rw [hg _ (by decide), h.rcx],
    by rw [hg _ (by decide), h.rsi], by rw [hg _ (by decide), h.rsp], h.t1, h.le, by rw [hm, h.left],
    by rw [hm, h.cnt], fun k hk => by rw [hm, h.data k hk], by rw [hm]; exact h.consts,
    ⟨by rw [hg _ (by decide)]; exact h.acc.r8, by rw [hg _ (by decide)]; exact h.acc.r9,
      by rw [hg _ (by decide)]; exact h.acc.r10, by rw [hg _ (by decide)]; exact h.acc.h2,
      by simp only [hval, hg Reg.r11 (by decide), hg Reg.rbx (by decide), hg Reg.rbp (by decide)]
         rw [hm]; exact h.acc.val⟩,
    by rw [hm]; exact h.fr⟩

theorem restPre_ok {c dp : Addr} {L : Nat} {R0 R1 : BitVec 64} {A : Nat} {m₀ : Mem} {sp : Addr} {T : Nat}
    (hL : L < 2 ^ 64) {s : State} (h : LI c dp L R0 R1 A m₀ sp T s) :
    WP isa (.block [.mov .rdx (.mem (at_ .rcx lenOff)), .alu .sub .rdx (.imm 1), .alu .cmp .rdx (.imm 256)]) s
      fun s' => LI c dp L R0 R1 A m₀ sp T s' ∧
        s'.cf = some (decide (1 ≤ L - 512 * T ∧ L - 512 * T ≤ 256)) ∧
        s'.gpr .rdx = BitVec.ofNat 64 (L - 512 * T) - 1 := by
  have hsl : InRegions (s.rd ++ s.wr) (slot (bfA c)) 8 :=
    ⟨psR c, List.mem_append_right _ (by rw [h.wr]; simp), slot_in⟩
  have hv := h.left
  simp only [slot, lenOff] at hsl hv
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.ChaCha20.X86_64.ea_at, readSrc, execAlu,
    arithFlags, State.load64, State.setReg, State.setFlags, lenOff, h.rcx, hsl, hv, ite_true, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = BitVec.ofNat 64 256 := by decide
  refine ⟨LI.of_rdx h (fun r hr => by simp [hr]) rfl rfl rfl, ?_, by simp⟩
  rw [e1, e256, Proof.Poly1305.X86_64.toNat_ofNat_lt (by decide)]
  congr 1
  apply propext
  rw [BitVec.toNat_sub, Proof.Poly1305.X86_64.toNat_ofNat_lt (by omega), show (1 : BitVec 64).toNat = 1 from rfl]
  constructor
  · intro hc
    by_cases h0 : L - 512 * T = 0
    · rw [h0] at hc; simp at hc
    · rw [show 2 ^ 64 - 1 + (L - 512 * T) = 2 ^ 64 + (L - 512 * T - 1) by omega, Nat.add_mod_left,
        Nat.mod_eq_of_lt (by omega)] at hc
      omega
  · intro ⟨h1, h2⟩
    rw [show 2 ^ 64 - 1 + (L - 512 * T) = 2 ^ 64 + (L - 512 * T - 1) by omega, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega)]
    omega

theorem cmp128_ok {c dp : Addr} {L : Nat} {R0 R1 : BitVec 64} {A : Nat} {m₀ : Mem} {sp : Addr} {T : Nat}
    (hlo : 1 ≤ L - 512 * T) (hhi : L - 512 * T ≤ 256) {s : State} (h : LI c dp L R0 R1 A m₀ sp T s)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 (L - 512 * T) - 1) :
    WP isa (.block [.alu .cmp .rdx (.imm 128)]) s fun s' =>
      LI c dp L R0 R1 A m₀ sp T s' ∧ s'.cf = some (decide (L - 512 * T ≤ 128)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags, State.setFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨LI.of_rdx h (fun _ _ => rfl) rfl rfl rfl, ?_⟩
  have e128 : BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 128 := by decide
  rw [hrdx, e128, Proof.Poly1305.X86_64.toNat_ofNat_lt (by decide),
    show BitVec.ofNat 64 (L - 512 * T) - 1 = BitVec.ofNat 64 (L - 512 * T - 1) by
      rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)],
    Proof.Poly1305.X86_64.toNat_ofNat_lt (by omega)]
  congr 1
  apply propext
  constructor <;> intro <;> omega

theorem cmp448_ok₀ {c dp : Addr} {L : Nat} {R0 R1 : BitVec 64} {A : Nat} {m₀ : Mem} {sp : Addr} {T : Nat}
    (hL : L < 2 ^ 64) {s : State} (h : LI c dp L R0 R1 A m₀ sp T s)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 (L - 512 * T) - 1) :
    WP isa (.block [.alu .cmp .rdx (.imm 448)]) s fun s' =>
      LI c dp L R0 R1 A m₀ sp T s' ∧ s'.cf = some (decide (1 ≤ L - 512 * T ∧ L - 512 * T ≤ 448)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags, State.setFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨LI.of_rdx h (fun _ _ => rfl) rfl rfl rfl, ?_⟩
  have e448 : BitVec.signExtend 64 (448 : BitVec 32) = BitVec.ofNat 64 448 := by decide
  rw [hrdx, e448, Proof.Poly1305.X86_64.toNat_ofNat_lt (by decide)]
  congr 1
  apply propext
  rw [BitVec.toNat_sub, Proof.Poly1305.X86_64.toNat_ofNat_lt (by omega), show (1 : BitVec 64).toNat = 1 from rfl]
  constructor
  · intro hc
    by_cases h0 : L - 512 * T = 0
    · rw [h0] at hc; simp at hc
    · rw [show 2 ^ 64 - 1 + (L - 512 * T) = 2 ^ 64 + (L - 512 * T - 1) by omega, Nat.add_mod_left,
        Nat.mod_eq_of_lt (by omega)] at hc
      omega
  · intro ⟨h1, h2⟩
    rw [show 2 ^ 64 - 1 + (L - 512 * T) = 2 ^ 64 + (L - 512 * T - 1) by omega, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega)]
    omega

/-- The comparison with 448 after its padding, which writes only `rax`. -/
theorem cmp448_ok {c dp : Addr} {L : Nat} {R0 R1 : BitVec 64} {A : Nat} {m₀ : Mem} {sp : Addr} {T : Nat}
    (hL : L < 2 ^ 64) {s : State} (h : LI c dp L R0 R1 A m₀ sp T s)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 (L - 512 * T) - 1) :
    WP isa (.block (padIns .rax 19 ++ ([.alu .cmp .rdx (.imm 448)] : List Instr))) s fun s' =>
      LI c dp L R0 R1 A m₀ sp T s' ∧ s'.cf = some (decide (1 ≤ L - 512 * T ∧ L - 512 * T ≤ 448)) :=
  WP.block_append (WP.mono (padIns_ok .rax (by decide) s) fun _ p =>
    cmp448_ok₀ hL (LI.of_rax h p.gpr p.mem p.rd p.wr) (by rw [p.gpr _ (by decide), hrdx]))

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

/-!
# ChaCha20 and Poly1305 together (x86-64): `bulk`

`Stitch.bulk`, with the permissions it needs (`bulkWr`): `enter`, the first
chunk, the later ones while 512 bytes remain, and the rest. Of `L ≥ 512`
bytes of data, the first `512 T` are encrypted. If none or more than 448 are
left, `leave` ends it (`BulkL`): the first `512 (T - 1)` are absorbed into
the Poly1305 state, which represents the message before them followed by
them, `rbx`, `rbp` are the ciphertext not yet absorbed and `rsi`, `rdx` the
data not yet encrypted. Otherwise `tailS` or `tailK` encrypts the rest too and absorbs
the first `512 T` (`BulkT`), with `rbx`, `rbp` the rest and `rdx` 0.
-/

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64.Avx2 (Consts stR bufR)
open VG.Proof.ChaCha20 (ctr)
open VG.Proof.Poly1305.X86_64 (hval Keeps off)
open VG.Spec.ChaCha20 (stateAt keystream)
open VG.Spec.Poly1305 (P bytesAt leNum clamp accumulate Repr)
open VG.Proof.Poly1305 (absorbAll)

/-- After `bulk`, ended by `leave`. -/
def BulkL (c dp : Addr) (L : Nat) (s : State) (key msg : List Byte) (T : Nat) (s' : State) : Prop :=
  1 ≤ T ∧ 512 * T ≤ L ∧ L - 512 * T < 512 ∧ (L - 512 * T = 0 ∨ 448 < L - 512 * T) ∧
      (∀ k < L, s'.mem (dp + BitVec.ofNat 64 k) = if k < 512 * T then
        s.mem (dp + BitVec.ofNat 64 k) ^^^ (keystream (stateAt s.mem (stA c)) L).getD k 0
        else s.mem (dp + BitVec.ofNat 64 k)) ∧
      stateAt s'.mem (stA c) = ctr (stateAt s.mem (stA c)) (8 * T) ∧
      Repr s'.mem (psA c) key (msg ++ bytesAt s'.mem dp (512 * (T - 1))) ∧
      s'.gpr .rbx = dp + BitVec.ofNat 64 (512 * (T - 1)) ∧
      s'.gpr .rbp = BitVec.ofNat 64 (L - 512 * (T - 1)) ∧
      s'.gpr .rsi = dp + BitVec.ofNat 64 (512 * T) ∧ s'.gpr .rdx = BitVec.ofNat 64 (L - 512 * T) ∧
      s'.gpr .rdi = stA c ∧ s'.gpr .rcx = bfA c ∧ s'.gpr .r12 = s.gpr .r12 ∧
      s'.gpr .r13 = s.gpr .r13 ∧ s'.gpr .r14 = s.gpr .r14 ∧ s'.gpr .r15 = c ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.rd = s.rd ∧ s'.wr = s.wr

/-- After `bulk`, ended by `tailS` or `tailK`. -/
def BulkT (c dp : Addr) (L : Nat) (s : State) (key msg : List Byte) (T : Nat) (s' : State) : Prop :=
  1 ≤ T ∧ 512 * T ≤ L ∧ 1 ≤ L - 512 * T ∧ L - 512 * T ≤ 448 ∧
      (∀ k < L, s'.mem (dp + BitVec.ofNat 64 k) =
        s.mem (dp + BitVec.ofNat 64 k) ^^^ (keystream (stateAt s.mem (stA c)) L).getD k 0) ∧
      Repr s'.mem (psA c) key (msg ++ bytesAt s'.mem dp (512 * T)) ∧
      s'.gpr .rbx = dp + BitVec.ofNat 64 (512 * T) ∧ s'.gpr .rbp = BitVec.ofNat 64 (L - 512 * T) ∧
      s'.gpr .rdx = 0 ∧ s'.gpr .rcx = bfA c ∧ s'.gpr .r12 = s.gpr .r12 ∧
      s'.gpr .r13 = s.gpr .r13 ∧ s'.gpr .r14 = s.gpr .r14 ∧ s'.gpr .r15 = c ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.rd = s.rd ∧ s'.wr = s.wr

/-- The keystream from block `j`. -/
theorem ks_from (S : Proof.ChaCha20.CState) {L E k : Nat} (hE : E % 64 = 0) (hk : k < L) (hEk : E ≤ k) :
    (keystream (ctr S (E / 64)) (L - E)).getD (k - E) 0 = (keystream S L).getD k 0 := by
  rw [VG.Proof.ChaCha20.keystream_getD _ (by omega), VG.Proof.ChaCha20.keystream_getD _ hk,
    Proof.ChaCha20.X86_64.Avx2.ctr_ctr, show E / 64 + (k - E) / 64 = k / 64 by omega,
    show (k - E) % 64 = k % 64 by omega]

/-- `enter`'s stores keep the data. -/
theorem enter_data {c dp : Addr} {L : Nat} (hl : Lay c dp L) {m m' : Mem}
    (F : Frame [bufR (bfA c), stashR c] m m') : ∀ k < L, m' (dp + BitVec.ofNat 64 k) = m (dp + BitVec.ofNat 64 k) := by
  have hLe := hl.L_lt
  intro k hk
  have ds : ∀ d n, d + n ≤ 1248 → ¬ (⟨c + BitVec.ofNat 64 d, n⟩ : Region).Contains (dp + BitVec.ofNat 64 k) 1 :=
    fun d n h hc => hl.cd h _ hc (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega_arith) (by omega_arith))
  exact F _ (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ds 128 320 (by decide)
    · exact ds 520 32 (by decide))

/-- `enter`'s stores keep the one-time key. -/
theorem enter_key {c : Addr} {m m' : Mem} (F : Frame [bufR (bfA c), stashR c] m m') :
    bytesAt m' (c + BitVec.ofNat 64 472) 32 = bytesAt m (c + BitVec.ofNat 64 472) 32 :=
  bytesAt_frame (p := c + BitVec.ofNat 64 472) (n := 32) F (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
    · exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)) (by decide)

/-- After the first chunk (`LI` at 1, from the memory `m₀`): the later
chunks and the rest, as `bulk` ends them, relative to the state `σ` it starts
from, whose memory `m₀` is but for `enter`'s stores. -/
theorem restLI_ok (vl : Bool) {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} (hk : Key R0 R1) {A : Nat}
    {m₀ : Mem} {σ s₂ : State} (hrd : σ.rd = []) (hwr : σ.wr = bulkWr c dp L)
    {key msg : List Byte} (hlen : msg.length % 16 = 0) (hK : bytesAt σ.mem (psA c + 24) 32 = key)
    (hr : clamp (leNum (key.take 16)) = rN R0 R1) (hAm : A = accumulate (rN R0 R1) msg)
    (S₁ : stateAt m₀ (stA c) = stateAt σ.mem (stA c))
    (e₁ : ∀ k < L, m₀ (dp + BitVec.ofNat 64 k) = σ.mem (dp + BitVec.ofNat 64 k))
    (K₁ : bytesAt m₀ (c + BitVec.ofNat 64 472) 32 = bytesAt σ.mem (c + BitVec.ofNat 64 472) 32)
    (v12 : m₀.readW (c + BitVec.ofNat 64 520) 64 = σ.gpr .r12)
    (v13 : m₀.readW (c + BitVec.ofNat 64 528) 64 = σ.gpr .r13)
    (v14 : m₀.readW (c + BitVec.ofNat 64 536) 64 = σ.gpr .r14)
    (L₂ : LI c dp L R0 R1 A m₀ (σ.gpr .rsp) 1 s₂) (cf₂ : s₂.cf = some (decide (L - 512 * 1 < 512))) :
    WP isa (.seq (.ite .b (.block []) (.loop (chunk vl false) .ae)) (restT vl)) s₂
      fun s' => ∃ T, BulkL c dp L σ key msg T s' ∨ BulkT c dp L σ key msg T s' := by
  have hLe := hl.L_lt
  have hAP : A < P := hAm ▸ VG.Proof.Poly1305.accumulate_lt _ _
  refine WP.seq (WP.mono (chunks_ok vl hl hk L₂ cf₂) fun s₃ ⟨T, L₃, hT⟩ => ?_)
  have ht := L₃.t1
  have hTL := L₃.le
  unfold restT
  refine WP.seq (WP.mono (restPre_ok hLe L₃) fun s₄ ⟨L₄, cf₄, rdx₄⟩ => ?_)
  have stk : ∀ {s' : State}, LI c dp L R0 R1 A m₀ (σ.gpr .rsp) T s' → ∀ d, 520 ≤ d → d + 8 ≤ 544 →
      s'.mem.readW (c + BitVec.ofNat 64 d) 64 = m₀.readW (c + BitVec.ofNat 64 d) 64 := by
    intro s' L' d h₁ h₂
    refine L'.fr.readW (r := ⟨c + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint c (Or.inr (by omega_arith)) (by omega_arith) (by decide)
    · exact hl.cd (by omega_arith)
    · exact Offset.disjoint c (Or.inr (by omega_arith)) (by omega_arith) (by decide)
    · rw [slot_eq]; exact Offset.disjoint c (Or.inl (by omega_arith)) (by omega_arith) (by decide)
  have key₁ : ∀ {s' : State}, LI c dp L R0 R1 A m₀ (σ.gpr .rsp) T s' →
      bytesAt s'.mem (c + BitVec.ofNat 64 472) 32 = bytesAt σ.mem (c + BitVec.ofNat 64 472) 32 := by
    intro s' L'
    have e₂ := bytesAt_frame (p := c + BitVec.ofNat 64 472) (n := 32) L'.fr (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
      · exact hl.cd (by decide)
      · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
      · rw [slot_eq]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)) (by decide)
    rw [e₂, K₁]
  -- What a tail leaves (`tailS_ok`, `tailK_ok`), as `bulk` ends.
  have post : ∀ {s₅ s₆ : State}, LI c dp L R0 R1 A m₀ (σ.gpr .rsp) T s₅ → 1 ≤ L - 512 * T → L - 512 * T ≤ 448 →
      (∀ k < L - 512 * T, s₆.mem (dp + BitVec.ofNat 64 (512 * T) + BitVec.ofNat 64 k) =
        s₅.mem (dp + BitVec.ofNat 64 (512 * T) + BitVec.ofNat 64 k) ^^^
          (keystream (stateAt s₅.mem (stA c)) (L - 512 * T)).getD k 0) →
      leNum (bytesAt s₆.mem (psA c) 24) = absorbAll (rN R0 R1) A (bytesAt s₅.mem dp (512 * T)) % P →
      Frame [accR c, bufR (bfA c), kR (bfA c), ⟨dp + BitVec.ofNat 64 (512 * T), L - 512 * T⟩] s₅.mem s₆.mem →
      s₆.gpr .rbx = dp + BitVec.ofNat 64 (512 * T) → s₆.gpr .rbp = BitVec.ofNat 64 (L - 512 * T) →
      s₆.gpr .rdx = 0 → s₆.gpr .rcx = bfA c →
      s₆.gpr .r12 = s₅.mem.readW (c + BitVec.ofNat 64 520) 64 →
      s₆.gpr .r13 = s₅.mem.readW (c + BitVec.ofNat 64 528) 64 →
      s₆.gpr .r14 = s₅.mem.readW (c + BitVec.ofNat 64 536) 64 → s₆.gpr .r15 = c →
      s₆.gpr .rsp = σ.gpr .rsp → s₆.rd = s₅.rd → s₆.wr = s₅.wr →
      ∃ T, BulkL c dp L σ key msg T s₆ ∨ BulkT c dp L σ key msg T s₆ := by
    intro s₅ s₆ L₅ hlo hhi d₆ acc₆ f₆ rbx₆ rbp₆ rdx₆ rcx₆ r12₆ r13₆ r14₆ r15₆ rsp₆ rd₆ wr₆
    have dsub : Region.Sub ⟨dp, 512 * T⟩ ⟨dp, L⟩ := Region.sub_prefix (by omega_arith)
    have kc : kR (bfA c) = ⟨c + BitVec.ofNat 64 736, 512⟩ := by simp only [kR, kA, bfA, Offset.add_add]
    have hb6 : bytesAt s₆.mem dp (512 * T) = bytesAt s₅.mem dp (512 * T) := by
      refine bytesAt_frame f₆ ?_ (by omega_arith)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (hl.cd (d := 448) (n := 24) (by decide)).symm.sub_left dsub
      · exact (hl.bf_d.symm.sub_left dsub)
      · rw [kc]; exact (hl.cd (d := 736) (n := 512) (by decide)).symm.sub_left dsub
      · exact Offset.base_disjoint dp (Nat.le_refl _) (by omega_arith)
    refine ⟨T, .inr ⟨ht, hTL, hlo, hhi, fun k hk => ?_, ⟨?_, ?_, ?_⟩, rbx₆, rbp₆, rdx₆, rcx₆, ?_, ?_, ?_, r15₆,
      by rw [rsp₆], by rw [rd₆, L₅.rd, hrd], by rw [wr₆, L₅.wr, hwr]⟩⟩
    · by_cases hkT : k < 512 * T
      · have nd : ∀ r ∈ [accR c, bufR (bfA c), kR (bfA c), ⟨dp + BitVec.ofNat 64 (512 * T), L - 512 * T⟩],
            ¬ r.Contains (dp + BitVec.ofNat 64 k) 1 := by
          intro r hr hcn
          have hin' : (⟨dp, L⟩ : Region).Contains (dp + BitVec.ofNat 64 k) 1 :=
            Offset.contains_base _ (by omega_arith) (by omega_arith)
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact hl.cd (d := 448) (n := 24) (by decide) _ hcn hin'
          · exact hl.bf_d _ hcn hin'
          · rw [kc] at hcn; exact hl.cd (d := 736) (n := 512) (by decide) _ hcn hin'
          · simp only [Region.Contains] at hcn
            rw [Offset.sub_toNat' _ (by omega_arith) (by omega_arith)] at hcn
            split at hcn <;> omega_arith
        rw [f₆ _ nd, L₅.data k hk, ite_eq_left hkT, e₁ k hk, S₁]
      · have x := d₆ (k - 512 * T) (by omega_arith)
        rw [Offset.add_add, Nat.add_sub_cancel' (by omega_arith), L₅.cnt, S₁, L₅.data k hk,
          ite_eq_right hkT, e₁ k hk, show 8 * T = 512 * T / 64 by omega_arith,
          ks_from _ (by omega_arith) hk (by omega_arith)] at x
        exact x
    · rw [List.length_append, VG.Proof.Poly1305.length_bytesAt]; have := hlen; omega_arith
    · rw [psA_24]
      have e₁' := bytesAt_frame (p := c + BitVec.ofNat 64 472) (n := 32) f₆ (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
        · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
        · rw [kc]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
        · exact (hl.cd (by decide)).sub_right (Offset.sub_base _ (by omega_arith))) (by decide)
      rw [e₁', key₁ L₅, ← psA_24]; exact hK
    · rw [acc₆, hb6, hr, VG.Proof.Poly1305.accumulate_append hlen, ← hAm,
        Nat.mod_eq_of_lt (VG.Proof.Poly1305.absorbAll_lt hAP _)]
    · rw [r12₆, stk L₅ 520 (by decide) (by decide), v12]
    · rw [r13₆, stk L₅ 528 (by decide) (by decide), v13]
    · rw [r14₆, stk L₅ 536 (by decide) (by decide), v14]
  refine WP.ite (decide (1 ≤ L - 512 * T ∧ L - 512 * T ≤ 256)) (by simp only [eval, cf₄]) (fun hc => ?_) (fun hc => ?_)
  · -- 1 to 256 bytes left: the tail.
    simp only [decide_eq_true_eq] at hc
    obtain ⟨hlo, hhi⟩ := hc
    refine WP.seq (WP.mono (cmp128_ok hlo hhi L₄ rdx₄) fun s₅ ⟨L₅, cf₅⟩ => ?_)
    have fin : ∀ two : Bool, L - 512 * T ≤ 128 * (if two then 2 else 1) → WP isa (tailS two false) s₅ fun s' =>
        ∃ T, BulkL c dp L σ key msg T s' ∨ BulkT c dp L σ key msg T s' := by
      intro two hh
      exact WP.mono (tailS_ok hl hk two hlo hh L₅)
        fun s₆ ⟨d₆, acc₆, f₆, rbx₆, rbp₆, rdx₆, rcx₆, r12₆, r13₆, r14₆, r15₆, rsp₆, rd₆, wr₆⟩ =>
          post L₅ hlo (by omega) d₆ acc₆ (f₆.mono (by simp)) rbx₆ rbp₆ rdx₆ rcx₆ r12₆ r13₆ r14₆ r15₆ rsp₆ rd₆ wr₆
    refine WP.ite (decide (L - 512 * T ≤ 128)) (by simp only [eval, cf₅]) (fun hc => ?_) (fun hc => ?_)
    · simp only [decide_eq_true_eq] at hc
      exact fin false (by simp only [Bool.false_eq_true, ite_false]; omega)
    · exact fin true (by simp only [ite_true]; omega)
  · -- 257 to 448 bytes left: `tailK`; none or more than 448: `leave`.
    simp only [decide_eq_false_iff_not] at hc
    refine WP.seq (WP.mono (cmp448_ok hLe L₄ rdx₄) fun s₄ ⟨L₄, cf₅⟩ => ?_)
    refine WP.ite (decide (1 ≤ L - 512 * T ∧ L - 512 * T ≤ 448)) (by simp only [eval, cf₅])
      (fun hc' => ?_) (fun hc' => ?_)
    · simp only [decide_eq_true_eq] at hc'
      exact WP.mono (tailK_ok vl hl hk (by omega) hc'.2 L₄)
        fun s₆ ⟨d₆, acc₆, f₆, rbx₆, rbp₆, rdx₆, rcx₆, r12₆, r13₆, r14₆, r15₆, rsp₆, rd₆, wr₆⟩ =>
          post L₄ hc'.1 hc'.2 d₆ acc₆ f₆ rbx₆ rbp₆ rdx₆ rcx₆ r12₆ r13₆ r14₆ r15₆ rsp₆ rd₆ wr₆
    simp only [decide_eq_false_iff_not] at hc'
    have hx : L - 512 * T = 0 ∨ 448 < L - 512 * T := by omega
    rw [leave_eq]
    refine WP.block_append (WP.mono (Proof.Poly1305.X86_64.reduce_ok s₄) fun s₅ ⟨red, k₄⟩ => ?_)
    refine WP.mono (store_ok (c := c) (s := s₅) (by rw [k₄.gpr', L₄.rcx]) (by rw [k₄.2.2.2, L₄.wr]; simp))
      fun s₆ ⟨m₅, rbx₅, rbp₅, rdx₅, rsi₅, r12₅, r13₅, r14₅, r15₅, g₅, rd₅, wr₅⟩ => ?_
    have m₄ : s₅.mem = s₄.mem := k₄.2.1
    have FA : Frame [accR c] s₄.mem s₆.mem := by rw [m₅, ← m₄]; exact accMem_frame _ _ _ _ _
    have S₅ : stateAt s₆.mem (stA c) = stateAt s₄.mem (stA c) :=
      Proof.ChaCha20.X86_64.Xor.stateAt_frame FA (by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide))
    have st3 : ∀ d, 520 ≤ d → d + 8 ≤ 544 →
        s₄.mem.readW (c + BitVec.ofNat 64 d) 64 = m₀.readW (c + BitVec.ofNat 64 d) 64 := by
      intro d h₁ h₂
      refine L₄.fr.readW (r := ⟨c + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Offset.disjoint c (Or.inr (by omega_arith)) (by omega_arith) (by decide)
      · exact hl.cd (by omega_arith)
      · exact Offset.disjoint c (Or.inr (by omega_arith)) (by omega_arith) (by decide)
      · rw [slot_eq]; exact Offset.disjoint c (Or.inl (by omega_arith)) (by omega_arith) (by decide)
    have dsub : Region.Sub ⟨dp, 512 * (T - 1)⟩ ⟨dp, L⟩ := Region.sub_prefix (by omega_arith)
    have hb : bytesAt s₆.mem dp (512 * (T - 1)) = bytesAt s₄.mem dp (512 * (T - 1)) := by
      refine bytesAt_frame FA ?_ (by omega_arith)
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact (hl.cd (d := 448) (n := 24) (by decide)).symm.sub_left dsub
    have hkey : bytesAt s₆.mem (c + BitVec.ofNat 64 472) 32 = bytesAt σ.mem (c + BitVec.ofNat 64 472) 32 := by
      have e₁ := bytesAt_frame (p := c + BitVec.ofNat 64 472) (n := 32) FA (by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)) (by decide)
      have e₂ := bytesAt_frame (p := c + BitVec.ofNat 64 472) (n := 32) L₄.fr (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
        · exact hl.cd (by decide)
        · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
        · rw [slot_eq]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)) (by decide)
      rw [e₁, e₂, K₁]
    have hslot : s₅.mem.readW (c + BitVec.ofNat 64 544) 64 = BitVec.ofNat 64 (L - 512 * T) := by
      rw [m₄, ← slot_eq, L₄.left]
    have e512 : ∀ n, n + 512 < 2 ^ 64 →
        BitVec.ofNat 64 n + 512 = BitVec.ofNat 64 (n + 512) := fun n _ => by
      rw [show (512 : Addr) = BitVec.ofNat 64 512 from rfl, ← BitVec.ofNat_add]
    have g5 : ∀ r : Reg, r = .rdi ∨ r = .rcx ∨ r = .rsp → s₆.gpr r = s₄.gpr r := by
      intro r hr
      rcases hr with rfl | rfl | rfl <;>
        rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          k₄.gpr']
    refine ⟨T, .inl ⟨ht, hTL, hT, hx, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, by rw [g5 _ (.inl rfl), L₄.rdi],
      by rw [g5 _ (.inr (.inl rfl)), L₄.rcx], ?_, ?_, ?_, r15₅, by rw [g5 _ (.inr (.inr rfl)), L₄.rsp],
      by rw [rd₅, k₄.2.2.1, L₄.rd, hrd], by rw [wr₅, k₄.2.2.2, L₄.wr, hwr]⟩⟩
    · intro k hk
      have ds : ∀ d n, d + n ≤ 1248 → ¬ (⟨c + BitVec.ofNat 64 d, n⟩ : Region).Contains (dp + BitVec.ofNat 64 k) 1 :=
        fun d n h hc => hl.cd h _ hc (Proof.ChaCha20.X86_64.Xor.contains_ofNat (by omega_arith) (by omega_arith))
      rw [FA _ (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact ds 448 24 (by decide)),
        L₄.data k hk, e₁ k hk, S₁]
    · rw [S₅, L₄.cnt, S₁]
    · rw [List.length_append, VG.Proof.Poly1305.length_bytesAt]; have := hlen; omega_arith
    · rw [psA_24, hkey, ← psA_24]; exact hK
    · rw [m₅, accMem_acc, ← m₅]
      show hval s₅ = _
      rw [red L₄.acc.h2, L₄.acc.val, hb, hr, VG.Proof.Poly1305.accumulate_append hlen, ← hAm,
        Nat.mod_eq_of_lt (VG.Proof.Poly1305.absorbAll_lt hAP _)]
    · rw [rbx₅, k₄.gpr', L₄.rsi]
    · rw [rbp₅, hslot, e512 _ (by omega_arith), show L - 512 * T + 512 = L - 512 * (T - 1) by omega_arith]
    · rw [rsi₅, k₄.gpr', L₄.rsi, window_eq dp ht]
    · rw [rdx₅, hslot]
    · rw [r12₅, m₄, st3 520 (by decide) (by decide), v12]
    · rw [r13₅, m₄, st3 528 (by decide) (by decide), v13]
    · rw [r14₅, m₄, st3 536 (by decide) (by decide), v14]


theorem bulk_ok (vl : Bool) {c dp : Addr} {L : Nat} (hl : Lay c dp L) (hge : 512 ≤ L) {s : State}
    (hrd : s.rd = []) (hwr : s.wr = bulkWr c dp L) (hrsi : s.gpr .rsi = dp)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 L) (hrcx : s.gpr .rcx = bfA c)
    {key msg : List Byte} (hrep : Repr s.mem (psA c) key msg) :
    WP isa (bulk vl) s fun s' => ∃ T, BulkL c dp L s key msg T s' ∨ BulkT c dp L s key msg T s' := by
  have hLe := hl.L_lt
  unfold bulk
  refine WP.seq (WP.mono (enter_ok hwr hrcx)
    fun s₁ ⟨rdi₁, g₁, rd₁, wr₁, F₁, C₁, sl₁, v12, v13, v14, r8₁, r9₁, r10₁, r11₁, rbx₁, rbp₁⟩ => ?_)
  have gk : ∀ r : Reg, r = .rcx ∨ r = .rsi ∨ r = .rsp → s₁.gpr r = s.gpr r := by
    intro r hr
    rcases hr with rfl | rfl | rfl <;>
      exact g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- The key and the accumulator.
  obtain ⟨R0, hR0⟩ : ∃ R0, s.mem.readW (off (psA c) 24) 64 &&& Proof.Poly1305.X86_64.M0 = R0 := ⟨_, rfl⟩
  obtain ⟨R1, hR1⟩ : ∃ R1, s.mem.readW (off (psA c) 32) 64 &&& Proof.Poly1305.X86_64.M1 = R1 := ⟨_, rfl⟩
  have hk : Key R0 R1 := ⟨hR0 ▸ Proof.Poly1305.X86_64.r0_lt _, hR1 ▸ Proof.Poly1305.X86_64.r1_lt _,
    hR1 ▸ Proof.Poly1305.X86_64.r1_mod _⟩
  have hr : clamp (leNum (key.take 16)) = rN R0 R1 := by
    rw [← hrep.2.1, ← Proof.Poly1305.X86_64.off_24, Proof.Poly1305.X86_64.clamp_key, hR0, hR1]
  obtain ⟨A, hA⟩ : ∃ A, leNum (bytesAt s.mem (psA c) 24) = A := ⟨_, rfl⟩
  have hAm : A = accumulate (rN R0 R1) msg := by rw [← hA, hrep.2.2, hr]
  have hAP : A < P := hAm ▸ VG.Proof.Poly1305.accumulate_lt _ _
  have hA' := hA
  rw [Proof.Poly1305.X86_64.leNum_acc] at hA'
  have acc₁ : Acc R0 R1 A s₁ := by
    refine ⟨r8₁.trans hR0, r9₁.trans hR1, by rw [r10₁, r9₁, hR1], ?_, ?_⟩
    · have hP : P = 2 ^ 130 - 5 := rfl
      rw [rbp₁]; omega_using [hA', hAP, hP]
    · simp only [hval, r11₁, rbx₁, rbp₁, hA']
  refine WP.seq (WP.mono (firstChunk_ok vl hl (R0 := R0) (R1 := R1) (A := A) (m₀ := s₁.mem) (sp := s.gpr .rsp)
    hge (by rw [rd₁, hrd]) (by rw [wr₁, hwr]) rdi₁ (by rw [gk _ (.inl rfl), hrcx])
    (by rw [gk _ (.inr (.inl rfl)), hrsi]) (gk _ (.inr (.inr rfl))) (by rw [sl₁, hrdx]) rfl C₁ acc₁)
    fun s₂ ⟨L₂, cf₂⟩ => ?_)
  have dst : ∀ r ∈ [bufR (bfA c), stashR c], (stR (stA c)).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact st_bf
    · exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  exact restLI_ok vl hl hk hrd hwr hrep.1 hrep.2.1 hr hAm (Proof.ChaCha20.X86_64.Xor.stateAt_frame F₁ dst)
    (enter_data hl F₁) (enter_key F₁) v12 v13 v14 L₂ cf₂

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
