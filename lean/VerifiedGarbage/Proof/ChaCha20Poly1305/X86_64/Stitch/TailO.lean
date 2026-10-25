module

import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Tail
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.TailRounds
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Out
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Bulk
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep

/-!
# ChaCha20 and Poly1305 together (x86-64): the last bytes of `open`

`Stitch.tailO two k`, after `open`'s whole chunks, with `n` bytes left (at
least `16 k`, at most `128` or, `two`, `256`): the constants stored and
`Avx2Tail`'s setup (`tailA_ok`), the rounds absorbing the first `k` blocks
of those bytes (`troundsG_ok`, on `oblocks`), the accumulator stored and the
registers restored, `rbx`, `rbp` at the bytes after those blocks
(`leaveTO`), and the keystream into `buf` (`tailOg_ok`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Proof.ChaCha20.X86_64.Avx2 (stR bufR)
open VG.Proof.ChaCha20.X86_64.Avx2Tail (HB Incs)
open VG.Proof.ChaCha20.X86_64.Avx512Tail (Ctx wregs S0)
open VG.Proof.ChaCha20 (CState ctr)
open VG.Spec.ChaCha20 (stateAt serialize keystream)
open VG.Spec.Poly1305 (P bytesAt leNum)
open VG.Proof.Poly1305 (absorbAll)
open VG.Proof.Poly1305.X86_64 (hval)

/-- The blocks `tailO` absorbs: 4, 8 or 12. -/
abbrev OK (k : Nat) : Prop := k = 4 ∨ k = 8 ∨ k = 12

/-- `tailO`'s schedule: four blocks in each of the first `k / 4` rounds. -/
theorem schedOk_o {k : Nat} (hk : OK k) : SchedOk (oblocks k) (ofirst k) k := by
  rcases hk with rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem ofirst_ten {k : Nat} (hk : OK k) : ofirst k 10 = k := by
  rcases hk with rfl | rfl | rfl <;> rfl

/-- The stores and moves of `leaveTO`. -/
def storeTO (k : Nat) : List Instr :=
  [.store (at_ .rcx accOff) .r11, .store (at_ .rcx (accOff + 8)) .rbx,
   .store (at_ .rcx (accOff + 16)) .rbp,
   .mov .rbx (.reg .rsi), .alu .add .rbx (.imm (BitVec.ofNat 32 (16 * k))),
   .mov .rbp (.mem (at_ .rcx lenOff)), .alu .sub .rbp (.imm (BitVec.ofNat 32 (16 * k))),
   .mov .r12 (.mem (at_ .rcx r12Off)), .mov .r13 (.mem (at_ .rcx r13Off)),
   .mov .r14 (.mem (at_ .rcx r14Off)), .mov .r15 (.reg .rcx), .alu .sub .r15 (.imm 128)]

theorem leaveTO_eq (k : Nat) : leaveTO k = Impl.Poly1305.X86_64.reduce ++ storeTO k := rfl

theorem se_k {k : Nat} (hk : OK k) :
    BitVec.signExtend 64 (BitVec.ofNat 32 (16 * k)) = BitVec.ofNat 64 (16 * k) := by
  rcases hk with rfl | rfl | rfl <;> decide

theorem storeTO_ok {k : Nat} (sk : BitVec.signExtend 64 (BitVec.ofNat 32 (16 * k)) = BitVec.ofNat 64 (16 * k))
    {c : Addr} {s : State} (hrcx : s.gpr .rcx = bfA c)
    (hw : psR c ∈ s.wr) :
    WP isa (.block (storeTO k)) s fun s' =>
      s'.mem = accMem s.mem c (s.gpr .r11) (s.gpr .rbx) (s.gpr .rbp) ∧
      s'.gpr .rbx = s.gpr .rsi + BitVec.ofNat 64 (16 * k) ∧
      s'.gpr .rbp = s.mem.readW (c + BitVec.ofNat 64 544) 64 - BitVec.ofNat 64 (16 * k) ∧
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
  simp only [storeTO, runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.ChaCha20.X86_64.ea_at,
    State.store64, State.load64, readSrc, execAlu, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    hrcx, accOff, r12Off, r13Off, r14Off, lenOff, ofInt_bf, Nat.reduceAdd, reduceCtorEq, o0, o1, o2, i0, i1, i2,
    i3, sk, ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 => by
    simp only [h1, h2, h3, h4, h5, h6, ite_false], trivial, trivial⟩
  all_goals simp (disch := decide) only [readW_writeW_ofNat, se128, bfA, BitVec.add_sub_cancel]

theorem scal_storeTO {k : Nat} (hk : OK k) : scalCode (.block (storeTO k)) = true := by
  rcases hk with rfl | rfl | rfl <;> decide

theorem tailBO_eq (two : Bool) (k : Nat) : tailBO two k = Impl.Poly1305.X86_64.reduce ++ (storeTO k ++
    (([.mov .r9 (.reg .rcx)] : List Instr) ++
    ((if two then Impl.ChaCha20.X86_64.Avx2Tail.addIn ++ Impl.ChaCha20.X86_64.Avx2Tail.storeSet .xmm0 .xmm1 .xmm2 .xmm3 0 ++
      Impl.ChaCha20.X86_64.Avx2Tail.storeSet .xmm4 .xmm5 .xmm6 .xmm7 128
    else Impl.ChaCha20.X86_64.Avx2Tail.addIn1 ++ Impl.ChaCha20.X86_64.Avx2Tail.storeSet .xmm0 .xmm1 .xmm2 .xmm3 0) ++
    ([.vop .vzeroupper] : List Instr)))) := by
  simp only [tailBO, leaveTO_eq, List.append_assoc]

section
variable {c : Addr}

/-- `tailBO`: the accumulator reduced and stored, the registers restored,
`rbx`, `rbp` past the first `k` blocks, and the keystream of the `S` sets
into `buf`. -/
theorem tailBO_ok (two : Bool) {k : Nat} (hk : OK k) {S : Nat} (hS : S = if two then 2 else 1)
    {vs : Nat → CState} {s : State}
    (hz : HB S vs s) (hrcx : s.gpr .rcx = bfA c) (hrdi : s.gpr .rdi = stA c) (hst : stR (stA c) ∈ s.wr)
    (hb : bufR (bfA c) ∈ s.wr) (hps : psR c ∈ s.wr) (hi : Incs s.mem (bfA c)) (h2 : (s.gpr .rbp).toNat ≤ 4) :
    WP isa (.block (tailBO two k)) s fun s' =>
      (∀ k' < 128 * S, s'.mem (bfA c + BitVec.ofNat 64 k') =
        (serialize (Proof.ChaCha20.X86_64.Avx2.plus vs (stateAt s.mem (stA c)) (k' / 64))).getD (k' % 64) 0) ∧
      leNum (bytesAt s'.mem (psA c) 24) = hval s % P ∧
      Frame [accR c, bufR (bfA c)] s.mem s'.mem ∧
      s'.gpr .rbx = s.gpr .rsi + BitVec.ofNat 64 (16 * k) ∧
      s'.gpr .rbp = s.mem.readW (c + BitVec.ofNat 64 544) 64 - BitVec.ofNat 64 (16 * k) ∧
      s'.gpr .r12 = s.mem.readW (c + BitVec.ofNat 64 520) 64 ∧
      s'.gpr .r13 = s.mem.readW (c + BitVec.ofNat 64 528) 64 ∧
      s'.gpr .r14 = s.mem.readW (c + BitVec.ofNat 64 536) 64 ∧ s'.gpr .r15 = c ∧
      s'.gpr .rcx = bfA c ∧ s'.gpr .rsp = s.gpr .rsp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [tailBO_eq]
  refine WP.block_append (WP.mono (WP.vecKeep scal_reduce (Proof.Poly1305.X86_64.reduce_ok s))
    fun s₁ ⟨⟨red, k₁⟩, x₁, y₁⟩ => ?_)
  refine WP.block_append (WP.mono (WP.vecKeep (scal_storeTO hk) (storeTO_ok (se_k hk) (c := c) (s := s₁)
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
  have fin : ∀ {s₄ : State}, (∀ k' < 128 * S, s₄.mem (s₃.gpr .r9 + BitVec.ofNat 64 k') =
        (serialize (Proof.ChaCha20.X86_64.Avx2.plus vs (S0 s₃) (k' / 64))).getD (k' % 64) 0) →
      Frame (wregs 0 s₃) s₃.mem s₄.mem → s₄.gpr = s₃.gpr → s₄.rd = s₃.rd → s₄.wr = s₃.wr →
      WP isa (.block [.vop .vzeroupper]) s₄ fun s' =>
        (∀ k' < 128 * S, s'.mem (bfA c + BitVec.ofNat 64 k') =
          (serialize (Proof.ChaCha20.X86_64.Avx2.plus vs (stateAt s.mem (stA c)) (k' / 64))).getD (k' % 64) 0) ∧
        leNum (bytesAt s'.mem (psA c) 24) = hval s % P ∧
        Frame [accR c, bufR (bfA c)] s.mem s'.mem ∧
        s'.gpr .rbx = s.gpr .rsi + BitVec.ofNat 64 (16 * k) ∧
        s'.gpr .rbp = s.mem.readW (c + BitVec.ofNat 64 544) 64 - BitVec.ofNat 64 (16 * k) ∧
        s'.gpr .r12 = s.mem.readW (c + BitVec.ofNat 64 520) 64 ∧
        s'.gpr .r13 = s.mem.readW (c + BitVec.ofNat 64 528) 64 ∧
        s'.gpr .r14 = s.mem.readW (c + BitVec.ofNat 64 536) 64 ∧ s'.gpr .r15 = c ∧
        s'.gpr .rcx = bfA c ∧ s'.gpr .rsp = s.gpr .rsp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    intro s₄ b₄ f₄ g₄ rd₄ wr₄
    have ws : wregs 0 s₃ = [⟨bfA c, 256⟩] ++ [⟨s₃.gpr .rsi, 0⟩] := by
      simp only [wregs, r9₃', Nat.mul_zero, List.cons_append, List.nil_append]
    rw [ws] at f₄
    have f₄' := Frame.drop0 f₄
    refine WP.mono (Proof.ChaCha20.X86_64.Avx2.vz_ok s₄) fun s₅ ⟨g₅, m₅, rd₅, wr₅⟩ => ?_
    have gg : ∀ r, s₅.gpr r = s₃.gpr r := fun r => by rw [g₅, g₄]
    have hb9 : bytesAt s₅.mem (psA c) 24 = bytesAt s₃.mem (psA c) 24 := by
      rw [m₅]
      refine bytesAt_frame f₄' (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
    refine ⟨fun k' hk' => ?_, by rw [hb9, acc₃], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [m₅, ← r9₃', b₄ k' hk', S₃]
    · have f45 : Frame [bufR (bfA c)] s₃.mem s₅.mem := by
        rw [m₅]
        refine f₄'.sub fun r hr => ?_
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨bufR (bfA c), by simp, Region.sub_prefix (by decide)⟩
      exact (fa.mono (by simp)).trans (f45.mono (by simp))
    · rw [gg, g₃ _ (by decide), rbx₂, k₁.gpr']
    · rw [gg, g₃ _ (by decide), rbp₂, k₁.2.1]
    · rw [gg, g₃ _ (by decide), r12₂, k₁.2.1]
    · rw [gg, g₃ _ (by decide), r13₂, k₁.2.1]
    · rw [gg, g₃ _ (by decide), r14₂, k₁.2.1]
    · rw [gg, g₃ _ (by decide), r15₂]
    · rw [gg, rcx₃]
    · rw [gg, g₃ _ (by decide), k12 _ (.inr (.inr (.inr rfl)))]
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

/-! ## The tail -/

/-- Before `tailO`: in the data `⟨dp, L⟩`, the `n` bytes at offset `o` left,
the kernel's registers, `n` stored, and the accumulator `X`. -/
structure TPO (c dp : Addr) (L o n : Nat) (R0 R1 : BitVec 64) (X : Nat) (sp : Addr) (s : State) : Prop where
  st : stR (stA c) ∈ s.wr
  bf : bufR (bfA c) ∈ s.wr
  ps : psR c ∈ s.wr
  dw : (⟨dp, L⟩ : Region) ∈ s.wr
  le : o + n ≤ L
  rdi : s.gpr .rdi = stA c
  rcx : s.gpr .rcx = bfA c
  rsi : s.gpr .rsi = dp + BitVec.ofNat 64 o
  rsp : s.gpr .rsp = sp
  left : s.mem.readW (slot (bfA c)) 64 = BitVec.ofNat 64 n
  acc : Acc R0 R1 X s

/-- After `tailO`, from `s`: the keystream of the `n` bytes left in `buf`,
their first `k` blocks absorbed, the accumulator stored, `rbx`, `rbp` the
bytes after those blocks, and the stashed registers restored. -/
structure TailMidO (c dp : Addr) (o n k : Nat) (R0 R1 : BitVec 64) (X : Nat) (sp : Addr)
    (s s' : State) : Prop where
  ks : ∀ i < n, s'.mem (bfA c + BitVec.ofNat 64 i) = (keystream (stateAt s.mem (stA c)) n).getD i 0
  acc : leNum (bytesAt s'.mem (psA c) 24) =
    absorbAll (rN R0 R1) X (bytesAt s.mem (dp + BitVec.ofNat 64 o) (16 * k)) % P
  frame : Frame [accR c, bufR (bfA c)] s.mem s'.mem
  rbx : s'.gpr .rbx = dp + BitVec.ofNat 64 (o + 16 * k)
  rbp : s'.gpr .rbp = BitVec.ofNat 64 (n - 16 * k)
  r12 : s'.gpr .r12 = s.mem.readW (c + BitVec.ofNat 64 520) 64
  r13 : s'.gpr .r13 = s.mem.readW (c + BitVec.ofNat 64 528) 64
  r14 : s'.gpr .r14 = s.mem.readW (c + BitVec.ofNat 64 536) 64
  r15 : s'.gpr .r15 = c
  rcx : s'.gpr .rcx = bfA c
  rsp : s'.gpr .rsp = sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- `tailO`, with `16 k` to `128 S` bytes left. -/
theorem tailOg_ok {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} (hk : Key R0 R1) {X : Nat}
    {o n : Nat} {sp : Addr} (two : Bool) {k : Nat} (hok : OK k) (hkn : 16 * k ≤ n)
    (hhi : n ≤ 128 * (if two then 2 else 1)) {s : State} (h : TPO c dp L o n R0 R1 X sp s) :
    WP isa (tailO two k) s (TailMidO c dp o n k R0 R1 X sp s) := by
  have hLe := hl.L_lt
  have hTL := h.le
  unfold tailO
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
  have hin : ∀ off n', off + n' ≤ 16 * k →
      InRegions (s₁.rd ++ s₁.wr) (dp + BitVec.ofNat 64 o + BitVec.ofNat 64 off) n' := by
    intro off n' hn
    refine ⟨_, List.mem_append_right _ (by rw [wr₁]; exact h.dw), ?_⟩
    rw [Offset.add_add]
    exact Offset.contains_base _ (by omega) (by omega)
  -- The rounds.
  refine WP.seq (WP.mono (troundsG_ok hk hrsi₁ hin (schedOk_o hok) (Nat.le_refl _) rfl tb₁ 10 (by decide))
    fun s₂ tb₂ => ?_)
  have hrcx₂ : s₂.gpr .rcx = bfA c := by rw [tb₂.gpr _ (by decide), gk₁ _ (by decide) (by decide), h.rcx]
  have hrdi₂ : s₂.gpr .rdi = stA c := by rw [tb₂.gpr _ (by decide), gk₁ _ (by decide) (by decide), h.rdi]
  have hrsi₂ : s₂.gpr .rsi = dp + BitVec.ofNat 64 o := by rw [tb₂.gpr _ (by decide), hrsi₁]
  have wr₂ : s₂.wr = s.wr := by rw [tb₂.wr, wr₁]
  have m₂ : s₂.mem = tMem c s.mem := by rw [tb₂.mem, m₁]
  have hi₂ : Incs s₂.mem (bfA c) := by rw [m₂]; exact Proof.ChaCha20.X86_64.Avx2.tincs_mem _ _
  refine (WP.mono (tailBO_ok two hok rfl tb₂.hb hrcx₂ hrdi₂ (by rw [wr₂]; exact h.st) (by rw [wr₂]; exact h.bf)
    (by rw [wr₂]; exact h.ps) hi₂ tb₂.poly.h2)
    fun s₃ ⟨ks₃, acc₃, f₃, rbx₃, rbp₃, r12₃, r13₃, r14₃, r15₃, rcx₃, rsp₃, rd₃, wr₃⟩ => ?_)
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
  refine ⟨fun i hi => ?_, ?_, ?_, by rw [rbx₃, hrsi₂, Offset.add_add],
    by rw [rbp₃, hslot, Offset.ofNat_sub_ofNat hkn],
    by rw [r12₃, ctxk 520 (by decide) (by decide)], by rw [r13₃, ctxk 528 (by decide) (by decide)],
    by rw [r14₃, ctxk 536 (by decide) (by decide)], r15₃, rcx₃,
    by rw [rsp₃, tb₂.gpr _ (by decide), gk₁ _ (by decide) (by decide), h.rsp], by rw [rd₃, tb₂.rd, rd₁],
    by rw [wr₃, wr₂]⟩
  · have k1 : i < 128 * (if two then 2 else 1) := by omega
    rw [ks₃ i k1, S₂, Proof.ChaCha20.X86_64.Avx2.plus_block, VG.Proof.ChaCha20.keystream_getD _ hi]
  · -- The accumulator: the first `k` blocks absorbed.
    have hb1 : bytesAt s₁.mem (dp + BitVec.ofNat 64 o) (16 * k) =
        bytesAt s.mem (dp + BitVec.ofNat 64 o) (16 * k) := by
      rw [m₁]
      refine bytesAt_frame (tMem_frame _) (fun r hr => ?_) (by omega)
      simp only [List.mem_singleton] at hr; subst hr
      exact (hl.bf_d.symm.sub_left (Offset.sub_base _ (by omega)))
    have v := tb₂.poly.val
    rw [ofirst_ten hok, hb1] at v
    rw [acc₃, v]
  · have f1 : Frame [bufR (bfA c)] s.mem s₂.mem := by rw [m₂]; exact tMem_frame _
    exact (f1.mono (by simp)).trans f₃

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
