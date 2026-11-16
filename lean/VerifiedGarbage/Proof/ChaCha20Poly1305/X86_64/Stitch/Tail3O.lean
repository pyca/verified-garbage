module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Tail
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.TailRounds
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Out
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Bulk
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Rounds3
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Last3
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Stitch
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Chunk
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.StoreRow
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Loop
import VerifiedGarbage.Proof.ChaCha20.X86_64.Xor

/-! ### `ChaCha20Poly1305.X86_64.Stitch.TailO`, which only this module used -/

section

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
  obtain o : ∀ d, 448 ≤ d → d + 8 ≤ 576 → InRegions s.wr (c + BitVec.ofNat 64 d) 8 := fun d h₁ h₂ =>
    ⟨_, hw, Offset.contains c (by omega_arith) (by omega_arith) (by decide)⟩
  obtain i : ∀ d, 448 ≤ d → d + 8 ≤ 576 → InRegions (s.rd ++ s.wr) (c + BitVec.ofNat 64 d) 8 := fun d h₁ h₂ =>
    ⟨_, List.mem_append_right _ hw, Offset.contains c (by omega_arith) (by omega_arith) (by decide)⟩
  obtain o0 := o 448 (by decide) (by decide); have o1 := o 456 (by decide) (by decide)
  obtain o2 := o 464 (by decide) (by decide)
  obtain i0 := i 544 (by decide) (by decide); have i1 := i 520 (by decide) (by decide)
  obtain i2 := i 528 (by decide) (by decide); have i3 := i 536 (by decide) (by decide)
  apply WP.of_runBlock
  obtain se128 : BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 128 := by decide
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
  obtain k12 : ∀ r, r = .rdi ∨ r = .rcx ∨ r = .rsi ∨ r = .rsp → s₂.gpr r = s.gpr r := by
    intro r hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k₁.gpr']
  obtain rdi₃ : s₃.gpr .rdi = stA c := by rw [g₃ _ (by decide), k12 _ (.inl rfl), hrdi]
  obtain rcx₃ : s₃.gpr .rcx = bfA c := by rw [g₃ _ (by decide), k12 _ (.inr (.inl rfl)), hrcx]
  obtain r9₃' : s₃.gpr .r9 = bfA c := by rw [r9₃, k12 _ (.inr (.inl rfl)), hrcx]
  obtain wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂, k₁.2.2.2]
  obtain rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂, k₁.2.2.1]
  obtain m₃' : s₃.mem = accMem s.mem c (s₁.gpr .r11) (s₁.gpr .rbx) (s₁.gpr .rbp) := by rw [m₃, m₂, k₁.2.1]
  obtain fa : Frame [accR c] s.mem s₃.mem := by rw [m₃']; exact accMem_frame _ _ _ _ _
  obtain hc : Ctx 0 s₃ := ctx0 rdi₃ r9₃' (by rw [wr₃']; exact hst) (by rw [wr₃']; exact hb)
  obtain hi₃ : Incs s₃.mem (s₃.gpr .r9) := by
    rw [r9₃']
    refine Proof.ChaCha20.X86_64.Avx2Tail.incs_frame hi fa ?_
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    obtain e : Proof.ChaCha20.X86_64.Avx2.hiR (bfA c) = ⟨c + BitVec.ofNat 64 256, 192⟩ := by
      simp only [Proof.ChaCha20.X86_64.Avx2.hiR, bfA, Offset.add_add]
    rw [e]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  obtain hz₃ : HB S vs s₃ := hb_of_vec hz (by rw [x₃, x₂, x₁]) (by rw [y₃, y₂, y₁])
  obtain S₃ : S0 s₃ = stateAt s.mem (stA c) := by
    simp only [S0, rdi₃]
    exact Proof.ChaCha20.X86_64.Xor.stateAt_frame fa (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide))
  obtain acc₃ : leNum (bytesAt s₃.mem (psA c) 24) = hval s % P := by
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
    obtain ws : wregs 0 s₃ = [⟨bfA c, 256⟩] ++ [⟨s₃.gpr .rsi, 0⟩] := by
      simp only [wregs, r9₃', Nat.mul_zero, List.cons_append, List.nil_append]
    rw [ws] at f₄
    obtain f₄' := Frame.drop0 f₄
    refine WP.mono (Proof.ChaCha20.X86_64.Avx2.vz_ok s₄) fun s₅ ⟨g₅, m₅, rd₅, wr₅⟩ => ?_
    obtain gg : ∀ r, s₅.gpr r = s₃.gpr r := fun r => by rw [g₅, g₄]
    obtain hb9 : bytesAt s₅.mem (psA c) 24 = bytesAt s₃.mem (psA c) 24 := by
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
  dw : (⟨dp, L⟩ : Region) ∈ s.rd ++ s.wr
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
  obtain tb₁ : TB s₁ (if two then 2 else 1) (fun j => ctr (stateAt s.mem (stA c)) j)
      (AccTo (dp + BitVec.ofNat 64 o) R0 R1 X s₁ 0) s₁ := by
    refine ⟨hz₁, ym₁, rfl, fun _ _ => rfl, rfl, rfl, ?_⟩
    simp only [AccTo, Nat.mul_zero]
    rw [show bytesAt s₁.mem (dp + BitVec.ofNat 64 o) 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil]
    have a := h.acc
    exact ⟨by rw [gk₁ _ (by decide) (by decide)]; exact a.r8, by rw [gk₁ _ (by decide) (by decide)]; exact a.r9,
      by rw [gk₁ _ (by decide) (by decide)]; exact a.r10, by rw [gk₁ _ (by decide) (by decide)]; exact a.h2,
      by simp only [hval, gk₁ (Reg.r11) (by decide) (by decide), gk₁ (Reg.rbx) (by decide) (by decide),
        gk₁ (Reg.rbp) (by decide) (by decide)]; exact a.val⟩
  obtain hrsi₁ : s₁.gpr .rsi = dp + BitVec.ofNat 64 o := by rw [gk₁ _ (by decide) (by decide), h.rsi]
  obtain hin : ∀ off n', off + n' ≤ 16 * k →
      InRegions (s₁.rd ++ s₁.wr) (dp + BitVec.ofNat 64 o + BitVec.ofNat 64 off) n' := by
    intro off n' hn
    refine ⟨_, by rw [rd₁, wr₁]; exact h.dw, ?_⟩
    rw [Offset.add_add]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  -- The rounds.
  refine WP.seq (WP.mono (troundsG_ok hk hrsi₁ hin (schedOk_o hok) (Nat.le_refl _) rfl tb₁ 10 (by decide))
    fun s₂ tb₂ => ?_)
  obtain hrcx₂ : s₂.gpr .rcx = bfA c := by rw [tb₂.gpr _ (by decide), gk₁ _ (by decide) (by decide), h.rcx]
  obtain hrdi₂ : s₂.gpr .rdi = stA c := by rw [tb₂.gpr _ (by decide), gk₁ _ (by decide) (by decide), h.rdi]
  obtain hrsi₂ : s₂.gpr .rsi = dp + BitVec.ofNat 64 o := by rw [tb₂.gpr _ (by decide), hrsi₁]
  obtain wr₂ : s₂.wr = s.wr := by rw [tb₂.wr, wr₁]
  obtain m₂ : s₂.mem = tMem c s.mem := by rw [tb₂.mem, m₁]
  obtain hi₂ : Incs s₂.mem (bfA c) := by rw [m₂]; exact Proof.ChaCha20.X86_64.Avx2.tincs_mem _ _
  refine (WP.mono (tailBO_ok two hok rfl tb₂.hb hrcx₂ hrdi₂ (by rw [wr₂]; exact h.st) (by rw [wr₂]; exact h.bf)
    (by rw [wr₂]; exact h.ps) hi₂ tb₂.poly.h2)
    fun s₃ ⟨ks₃, acc₃, f₃, rbx₃, rbp₃, r12₃, r13₃, r14₃, r15₃, rcx₃, rsp₃, rd₃, wr₃⟩ => ?_)
  -- What the stores of `tailA` keep in the context.
  obtain ctxk : ∀ d, 520 ≤ d → d + 8 ≤ 552 →
      s₂.mem.readW (c + BitVec.ofNat 64 d) 64 = s.mem.readW (c + BitVec.ofNat 64 d) 64 := by
    intro d h₁ h₂
    rw [m₂]
    refine (tMem_frame _).readW (r := ⟨c + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint c (Or.inr (by omega_arith)) (by omega_arith) (by decide)
  obtain hslot : s₂.mem.readW (c + BitVec.ofNat 64 544) 64 = BitVec.ofNat 64 n := by
    rw [ctxk 544 (by decide) (by decide), ← slot_eq, h.left]
  obtain S₂ : stateAt s₂.mem (stA c) = stateAt s.mem (stA c) := by
    rw [m₂]
    exact Proof.ChaCha20.X86_64.Xor.stateAt_frame (tMem_frame _) (by simpa using st_bf)
  refine ⟨fun i hi => ?_, ?_, ?_, by rw [rbx₃, hrsi₂, Offset.add_add],
    by rw [rbp₃, hslot, Offset.ofNat_sub_ofNat hkn],
    by rw [r12₃, ctxk 520 (by decide) (by decide)], by rw [r13₃, ctxk 528 (by decide) (by decide)],
    by rw [r14₃, ctxk 536 (by decide) (by decide)], r15₃, rcx₃,
    by rw [rsp₃, tb₂.gpr _ (by decide), gk₁ _ (by decide) (by decide), h.rsp], by rw [rd₃, tb₂.rd, rd₁],
    by rw [wr₃, wr₂]⟩
  · have k1 : i < 128 * (if two then 2 else 1) := by omega_arith
    rw [ks₃ i k1, S₂, Proof.ChaCha20.X86_64.Avx2.plus_block, VG.Proof.ChaCha20.keystream_getD _ hi]
  · -- The accumulator: the first `k` blocks absorbed.
    obtain hb1 : bytesAt s₁.mem (dp + BitVec.ofNat 64 o) (16 * k) =
        bytesAt s.mem (dp + BitVec.ofNat 64 o) (16 * k) := by
      rw [m₁]
      refine bytesAt_frame (tMem_frame _) (fun r hr => ?_) (by omega_arith)
      simp only [List.mem_singleton] at hr; subst hr
      exact (hl.bf_d.symm.sub_left (Offset.sub_base _ (by omega_arith)))
    have v := tb₂.poly.val
    rw [ofirst_ten hok, hb1] at v
    rw [acc₃, v]
  · have f1 : Frame [bufR (bfA c)] s.mem s₂.mem := by rw [m₂]; exact tMem_frame _
    exact (f1.mono (by simp)).trans f₃

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

end

end

/-! ### `ChaCha20Poly1305.X86_64.Stitch.TailRounds3`, which only this module used -/

section

/-!
# ChaCha20 and Poly1305 together (x86-64): the rounds of three sets

`Stitch.troundsG3`: `Avx2Tail`'s double rounds on three sets of two blocks
(`last3`'s, the masks in `ymm14`, `ymm15`), absorbing the blocks of a
schedule at `rsi` between their halves, as `troundsG` does on one set or
two (`TailRounds.lean`): a double round is six parts (`trH3`), each a list
of `Avx2Tail`'s instructions of three sets (`ymmOf3`), which together are
the double round on the words (`Avx2Tail.block3_ok`, `dr3_words`); the
blocks of Poly1305 between them write only Poly1305's registers and no
vector register or memory, and the parts write only vector registers.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64.Avx2Tail (HY3 YM3 HB ymmOf3 hiOk3 block3_ok hy3_wordsOf hb_of3 blk_wordsOf
  wordsOf half3H cols3H diags3H dr3_words)
open VG.Proof.ChaCha20.X86_64.Avx512Tail (HI W hstep rotH)
open VG.Proof.Poly1305.X86_64 (Keeps absorbRegs)
open VG.Proof.ChaCha20 (CState)
open VG.Spec.ChaCha20 (innerBlock)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.Poly1305 (absorbAll)

/-- The six parts of a double round on three sets. -/
def trH3 : Nat → List HI
  | 0 => half3H 16 12
  | 1 => half3H 8 7
  | 2 => rotH .xmm1 .xmm2 .xmm3 0x39 0x4e 0x93 ++ rotH .xmm5 .xmm6 .xmm7 0x39 0x4e 0x93 ++
    rotH .xmm9 .xmm10 .xmm11 0x39 0x4e 0x93
  | 3 => half3H 16 12
  | 4 => half3H 8 7
  | _ => rotH .xmm1 .xmm2 .xmm3 0x93 0x4e 0x39 ++ rotH .xmm5 .xmm6 .xmm7 0x93 0x4e 0x39 ++
    rotH .xmm9 .xmm10 .xmm11 0x93 0x4e 0x39

theorem drH3_eq : cols3H ++ diags3H = trH3 0 ++ trH3 1 ++ trH3 2 ++ trH3 3 ++ trH3 4 ++ trH3 5 := by
  simp only [cols3H, diags3H, trH3, List.append_assoc]

theorem trH3_ok (i : Nat) : (trH3 i).all hiOk3 = true := by
  unfold trH3; split <;> decide

theorem half3_eq :
    Impl.ChaCha20.X86_64.Avx2Tail.half3 .xmm14 12 = (trH3 0).flatMap ymmOf3 ∧
    Impl.ChaCha20.X86_64.Avx2Tail.half3 .xmm15 7 = (trH3 1).flatMap ymmOf3 ∧
    Impl.ChaCha20.X86_64.Avx2Tail.rot3 0x39 0x4e 0x93 = (trH3 2).flatMap ymmOf3 ∧
    Impl.ChaCha20.X86_64.Avx2Tail.rot3 0x93 0x4e 0x39 = (trH3 5).flatMap ymmOf3 := by
  decide +kernel

/-- A double round of three sets with the blocks between its parts. -/
theorem troundG3_eq (bl fb : Nat → Nat) (n : Nat) (h0 : bl n ≠ 0) :
    troundG3 bl fb n = (trH3 0).flatMap ymmOf3 ++
      ((if bl n = 4 then piece (fb n + bl n - 4) else []) ++
      ((trH3 1).flatMap ymmOf3 ++ (piece (fb n + bl n - 4 + 1) ++
      ((trH3 2).flatMap ymmOf3 ++ ((trH3 3).flatMap ymmOf3 ++ (piece (fb n + bl n - 4 + 2) ++
      ((trH3 4).flatMap ymmOf3 ++ (piece (fb n + bl n - 4 + 3) ++
      (trH3 5).flatMap ymmOf3)))))))) := by
  obtain ⟨e0, e1, e2, e5⟩ := half3_eq
  simp only [troundG3, h0, ite_false, e0, e1, e2, e5, show trH3 3 = trH3 0 from rfl,
    show trH3 4 = trH3 1 from rfl, List.append_assoc]

/-- A double round of three sets absorbing nothing. -/
theorem troundG3_eq0 (bl fb : Nat → Nat) (n : Nat) (h0 : bl n = 0) :
    troundG3 bl fb n = (trH3 0).flatMap ymmOf3 ++ ((trH3 1).flatMap ymmOf3 ++
      ((trH3 2).flatMap ymmOf3 ++ ((trH3 3).flatMap ymmOf3 ++ ((trH3 4).flatMap ymmOf3 ++
      (trH3 5).flatMap ymmOf3)))) := by
  obtain ⟨e0, e1, e2, e5⟩ := half3_eq
  simp only [troundG3, h0, ite_true, e0, e1, e2, e5, show trH3 3 = trH3 0 from rfl,
    show trH3 4 = trH3 1 from rfl, List.append_assoc]

/-- During the rounds of three sets: their states `vs` in the vector
registers, the masks, the memory, the permissions and the registers but
Poly1305's as in `s₁`, and Poly1305's satisfying `Q`. -/
structure TB3 (s₁ : State) (vs : Nat → CState) (Q : State → Prop) (s : State) : Prop where
  hb : HB 3 vs s
  ym : YM3 s
  mem : s.mem = s₁.mem
  gpr : ∀ r, r ∉ absorbRegs → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  poly : Q s

/-- As `TB3`, with the words of the vector registers `ws`. -/
structure TW3 (s₁ : State) (ws : Nat → W) (Q : State → Prop) (s : State) : Prop where
  hy : HY3 ws s
  ym : YM3 s
  mem : s.mem = s₁.mem
  gpr : ∀ r, r ∉ absorbRegs → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  poly : Q s

section
variable {s₁ : State}

/-- A part of the double round. -/
theorem seg_tw3 {is : List HI} (hok : is.all hiOk3 = true) {ws : Nat → W} {Q : State → Prop}
    (hQ : ∀ s s' : State, s'.gpr = s.gpr → Q s → Q s') {s : State} (h : TW3 s₁ ws Q s) :
    WP isa (.block (is.flatMap ymmOf3)) s (TW3 s₁ (fun l => is.foldl hstep (ws l)) Q) :=
  WP.mono (block3_ok is hok h.hy h.ym) fun s' ⟨hy, ym, f⟩ =>
    ⟨hy, ym, f.mem.trans h.mem, fun r hr => by rw [f.gpr, h.gpr r hr], f.rd.trans h.rd, f.wr.trans h.wr,
      hQ s s' f.gpr h.poly⟩

/-- Code that keeps the vector registers and Poly1305's frame keeps `TW3`. -/
theorem TW3.piece {ws : Nat → W} {Q Q' : State → Prop} {s s' : State} (h : TW3 s₁ ws Q s) (hq : Q' s')
    (k : Keeps absorbRegs s s') (hx : s'.xmm = s.xmm) (hy : s'.ymmHi = s.ymmHi) : TW3 s₁ ws Q' s' :=
  ⟨fun r l q hr hl hq' => by simpa only [State.lane, hx, hy] using h.hy r l q hr hl hq',
    fun l => by simpa only [State.lane, hx, hy] using h.ym l, by rw [k.2.1, h.mem],
    fun r hr => by rw [k.1 r hr, h.gpr r hr], by rw [k.2.2.1, h.rd], by rw [k.2.2.2, h.wr], hq⟩

variable {q : Addr} {N : Nat} {R0 R1 : BitVec 64} {X : Nat} (hk : Key R0 R1) (hrsi : s₁.gpr .rsi = q)
  (hin : ∀ off n, off + n ≤ N → InRegions (s₁.rd ++ s₁.wr) (q + BitVec.ofNat 64 off) n)
include hk hrsi hin

/-- Block `j` of the `N` bytes at `q`. -/
theorem piece_tw3 {j : Nat} (hj : 16 * j + 16 ≤ N) {ws : Nat → W} {s : State}
    (h : TW3 s₁ ws (AccTo q R0 R1 X s₁ j) s) :
    WP isa (.block (piece j)) s (TW3 s₁ ws (AccTo q R0 R1 X s₁ (j + 1))) := by
  unfold piece
  refine WP.block_append (WP.mono (addProd_ok hk h.poly (p := q) (by rw [h.gpr _ (by decide), hrsi]) (j := j)
    fun e he => by rw [h.rd, h.wr]; exact hin _ _ (by omega_using [hj, he])) fun s' ⟨a, k, x, y⟩ => ?_)
  obtain a' : HalfTo q R0 R1 X s₁ j s' := by
    show Half R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * (j + 1)))) s'
    rw [h.mem] at a
    rw [Nat.mul_add, Nat.mul_one, VG.Proof.Poly1305.bytesAt_add,
      VG.Proof.Poly1305.absorbAll_append (by rw [VG.Proof.Poly1305.length_bytesAt]; omega_using [])]
    exact a
  exact WP.mono (carry1_ok hk a') fun s'' ⟨a₂, k₂, x₂, y₂⟩ =>
    (h.piece a' k x y).piece a₂ k₂ x₂ y₂

/-- A double round on three sets, absorbing its blocks. -/
theorem troundG3_ok {bl fb : Nat → Nat} {tot : Nat} (sc : SchedOk bl fb tot)
    (hN : 16 * tot ≤ N) {n : Nat} (hn : n < 10)
    {vs : Nat → CState} {s : State} (h : TB3 s₁ vs (AccTo q R0 R1 X s₁ (fb n)) s) :
    WP isa (.block (troundG3 bl fb n)) s
      (TB3 s₁ (fun j => innerBlock (vs j)) (AccTo q R0 R1 X s₁ (fb (n + 1)))) := by
  obtain hb32 : fb n + bl n ≤ tot := by
    rw [← sc.succ n hn]; exact sc.le _ (by omega_using [hn])
  obtain hfb : bl n ≠ 0 → 4 ≤ fb n + bl n := sc.four n hn
  -- The parts, as steps of `TW3`.
  obtain tw : TW3 s₁ (wordsOf s) (AccTo q R0 R1 X s₁ (fb n)) s :=
    ⟨hy3_wordsOf s, h.ym, h.mem, h.gpr, h.rd, h.wr, h.poly⟩
  obtain hwords : ∀ {s' : State}, TW3 s₁ (fun l => (cols3H ++ diags3H).foldl hstep (wordsOf s l))
      (AccTo q R0 R1 X s₁ (fb (n + 1))) s' →
      TB3 s₁ (fun j => innerBlock (vs j)) (AccTo q R0 R1 X s₁ (fb (n + 1))) s' := fun h' =>
    ⟨hb_of3 h'.hy (fun k hk l hl => by rw [dr3_words _ hk, blk_wordsOf h.hb hk hl]) (by decide), h'.ym,
      h'.mem, h'.gpr, h'.rd, h'.wr, h'.poly⟩
  by_cases e0 : bl n = 0
  · -- No blocks.
    obtain ef : fb (n + 1) = fb n := by rw [sc.succ n hn, e0, Nat.add_zero]
    rw [troundG3_eq0 bl fb n e0]
    simp only [drH3_eq, List.foldl_append] at hwords
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 0) acc_gpr tw) fun t₁ h₁ => ?_)
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 1) acc_gpr h₁) fun t₂ h₂ => ?_)
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 2) acc_gpr h₂) fun t₃ h₃ => ?_)
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 3) acc_gpr h₃) fun t₄ h₄ => ?_)
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 4) acc_gpr h₄) fun t₅ h₅ => ?_)
    exact WP.mono (seg_tw3 (trH3_ok 5) acc_gpr h₅) fun _ h' => hwords (by rw [ef]; exact h')
  obtain hfb' := hfb e0
  obtain ⟨j, hj⟩ : ∃ j, j = fb n + bl n - 4 := ⟨_, rfl⟩
  obtain hfin : ∀ {s' : State}, TW3 s₁ (fun l => (cols3H ++ diags3H).foldl hstep (wordsOf s l))
      (AccTo q R0 R1 X s₁ (j + 3 + 1)) s' →
      TB3 s₁ (fun j => innerBlock (vs j)) (AccTo q R0 R1 X s₁ (fb (n + 1))) s' := fun h' =>
    hwords (by rw [sc.succ n hn, show fb n + bl n = j + 3 + 1 by omega_using [hfb, e0, hj]]; exact h')
  rw [troundG3_eq bl fb n e0, ← hj]
  simp only [drH3_eq, List.foldl_append] at hfin
  rcases sc.cases n hn with e4 | e3 | e0'
  rotate_left 2
  · exact absurd e0' e0
  · -- Four blocks: one after each half.
    obtain ej : fb n = j := by omega_using [hj, e4]
    rw [ite_eq_left e4]
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 0) acc_gpr tw) fun t₁ h₁ => ?_)
    rw [ej] at h₁
    refine WP.block_append (WP.mono (piece_tw3 hk hrsi hin (by omega_using [hN, hb32, e0, hj]) h₁) fun t₂ h₂ => ?_)
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 1) acc_gpr h₂) fun t₃ h₃ => ?_)
    refine WP.block_append (WP.mono (piece_tw3 hk hrsi hin (by omega_using [hN, hb32, hfb, e0, hj]) h₃) fun t₄ h₄ => ?_)
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 2) acc_gpr h₄) fun t₅ h₅ => ?_)
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 3) acc_gpr h₅) fun t₆ h₆ => ?_)
    refine WP.block_append (WP.mono (piece_tw3 hk hrsi hin (by omega_using [hN, hb32, hfb, e0, hj]) h₆) fun t₇ h₇ => ?_)
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 4) acc_gpr h₇) fun t₈ h₈ => ?_)
    refine WP.block_append (WP.mono (piece_tw3 hk hrsi hin (by omega_using [hN, hb32, hfb, e0, hj]) h₈) fun t₉ h₉ => ?_)
    exact WP.mono (seg_tw3 (trH3_ok 5) acc_gpr h₉) fun _ h' => hfin h'
  · -- Three blocks: none after the first half.
    obtain ej : fb n = j + 1 := by omega_using [hfb, hj, e3]
    rw [ite_eq_right (by omega_using [e3]), List.nil_append]
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 0) acc_gpr tw) fun t₁ h₁ => ?_)
    rw [ej] at h₁
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 1) acc_gpr h₁) fun t₃ h₃ => ?_)
    refine WP.block_append (WP.mono (piece_tw3 hk hrsi hin (by omega_using [hN, hb32, hfb, e0, hj]) h₃) fun t₄ h₄ => ?_)
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 2) acc_gpr h₄) fun t₅ h₅ => ?_)
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 3) acc_gpr h₅) fun t₆ h₆ => ?_)
    refine WP.block_append (WP.mono (piece_tw3 hk hrsi hin (by omega_using [hN, hb32, hfb, e0, hj]) h₆) fun t₇ h₇ => ?_)
    refine WP.block_append (WP.mono (seg_tw3 (trH3_ok 4) acc_gpr h₇) fun t₈ h₈ => ?_)
    refine WP.block_append (WP.mono (piece_tw3 hk hrsi hin (by omega_using [hN, hb32, hfb, e0, hj]) h₈) fun t₉ h₉ => ?_)
    exact WP.mono (seg_tw3 (trH3_ok 5) acc_gpr h₉) fun _ h' => hfin h'

end

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

end

end

/-! ### `ChaCha20Poly1305.X86_64.Stitch.Out3`, which only this module used -/

section

/-!
# ChaCha20 and Poly1305 together (x86-64): `tail3O`'s straight-line code

`Avx2Tail.setup3` with no data (`setup3_ok0`, as `Avx2Tail.setup3_ok`), and
`tail3O`'s output: the rounds' result plus the input states of the three
sets, stored to the 384 bytes at `rsi` (`out3_ok`, as `Avx2Tail.last3_ok`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Impl.ChaCha20.X86_64.Avx2Tail (setup3 addIn3)
open VG.Proof.ChaCha20.X86_64.Avx2Tail (HB YM3 Incs inT3 outT3 masks3Ok inT3_eval outT3_eval ym3_of yw run SRel
  SRel.init srun_ok)
open VG.Proof.ChaCha20.X86_64.Avx512 (Sym Sym.init xidx_zreg)
open VG.Proof.ChaCha20.X86_64.Avx512Tail (bsize regn baseR wregs Ctx S0 byte_out)
open VG.Impl.ChaCha20.X86_64.Avx512 (zreg)
open VG.Proof.ChaCha20.X86_64.Avx2 (plus Consts)
open VG.Proof.ChaCha20 (CState ctr)
open VG.Spec.ChaCha20 (serialize)

/-- `setup3`'s check with no data. -/
def setup3Check0 : Bool :=
  match run 0 Sym.init setup3 with
  | some σ => !σ.dirty && masks3Ok σ && (List.range 3).all fun k => (List.range 4).all fun r =>
      (List.range 8).all fun p => σ.reg (4 * k + r) p == inT3 k (4 * r + p % 4) (p / 4)
  | none => false

/-- The output of the three sets, stored to the 96 doublewords at `rsi`. -/
def out3Check : Bool :=
  match run 96 Sym.init (addIn3 ++ (storeSetS .xmm0 .xmm1 .xmm2 .xmm3 0 ++
      (storeSetS .xmm4 .xmm5 .xmm6 .xmm7 128 ++ storeSetS .xmm8 .xmm9 .xmm10 .xmm11 256))) with
  | some σ => (List.range 6).all fun j => (List.range 16).all fun i =>
      σ.mem 2 (16 * j + i) == outT3 (j / 2) i (j % 2)
  | none => false

theorem setup3Check0_eq : setup3Check0 = true := by decide +kernel
theorem out3Check_eq : out3Check = true := by decide +kernel

theorem setup3_ok0 {s : State} (hc : Ctx 0 s) (hm : Consts s.mem (s.gpr .r9)) (hi : Incs s.mem (s.gpr .r9)) :
    WP isa (.block setup3) s fun s' =>
      HB 3 (fun j => ctr (S0 s) j) s' ∧ YM3 s' ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  have e := setup3Check0_eq
  unfold setup3Check0 at e
  split at e
  · rename_i σ hr
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc setup3 (SRel.init 0 s) hr) fun s' h => ⟨fun k hk l hl i hi16 => ?_,
      ym3_of h e.1.2 hm, h.clean e.1.1, h.gpr, h.rd, h.wr⟩
    obtain r := h.reg (zreg (4 * k + i / 4)) (4 * l + i % 4) (by omega_using [hl])
    rw [xidx_zreg _ (by omega_using [hk, hi16]), e.2 k hk _ (by omega_using [hi16]) _ (by omega_using [hl])] at r
    simp only [yw, show (4 * l + i % 4) / 4 = l by omega_using [], show (4 * l + i % 4) % 4 = i % 4 by omega_using [],
      show 4 * (i / 4) + i % 4 = i by omega_using []] at r
    rw [r, inT3_eval hi hk hi16 hl]
  · cases e

theorem out3_ok {s : State} (hc : Ctx 96 s) (hi : Incs s.mem (s.gpr .r9)) {vs : Nat → CState}
    (hz : HB 3 vs s) :
    WP isa (.block (addIn3 ++ (storeSetS .xmm0 .xmm1 .xmm2 .xmm3 0 ++ (storeSetS .xmm4 .xmm5 .xmm6 .xmm7 128 ++
      storeSetS .xmm8 .xmm9 .xmm10 .xmm11 256)))) s fun s' =>
      (∀ k < 384, s'.mem (s.gpr .rsi + BitVec.ofNat 64 k) =
        (serialize (plus vs (S0 s) (k / 64))).getD (k % 64) 0) ∧
      Frame (wregs 96 s) s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := out3Check_eq
  unfold out3Check at e
  split at e
  · rename_i σ hr
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at e
    refine WP.mono (srun_ok hc _ (SRel.init 96 s) hr) fun s' h => ⟨fun k hk => ?_, h.frame, h.gpr, h.rd, h.wr⟩
    refine byte_out (f := fun j => plus vs (S0 s) j) ?_
    obtain d := h.mem 2 (k / 4) (by decide) (by simp only [bsize]; omega_using [hk])
    rw [show k / 4 = 16 * (k / 64) + k % 64 / 4 by omega_using [], e _ (by omega_using [hk]) _ (by omega_using []),
      outT3_eval hz hi (by omega_using [hk]) (by omega_using []) (by omega_using []),
      show 2 * (k / 64 / 2) + k / 64 % 2 = k / 64 by omega_using []] at d
    simp only [regn, baseR] at d
    rw [show 4 * (16 * (k / 64) + k % 64 / 4) = 4 * (k / 4) by omega_using []] at d
    exact d
  · cases e

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

end

end

/-! ### `ChaCha20Poly1305.X86_64.Stitch.TailKL`, which only this module used -/

section

/-!
# ChaCha20 and Poly1305 together (x86-64): `tailKO`'s rounds

`Stitch.tailKO`'s eight blocks are `tailKMain`'s (`tailKMain_ok`) but for
their rounds, two loops (`roundsLK`, by `roundsL_ok`) that absorb only the
first `k` blocks at `rsi`: from `rsi` at the next four blocks, a double round
absorbing them (`sround4_ok`, `sround4V_ok`, from the state the round starts
at: `KL.round4`, `KLV.round4`), then double rounds absorbing none.
`tailKL_ok` is `tailKMain_ok` for them.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64.Avx2 (Holds HoldsV M8 M16 Consts Incs stR bufR slotsR dR5 plus
  setup_ok W2_frame incs_frame hiR_slots slotsR_sub slots_m8 loadV_ok storeV_ok)
open VG.Proof.ChaCha20 (CState ctr)
open VG.Proof.Poly1305.X86_64 (hval absorbRegs)
open VG.Spec.ChaCha20 (stateAt serialize innerBlock)
open VG.Spec.Poly1305 (P bytesAt)
open VG.Proof.Poly1305 (absorbAll)

/-- After `n` of the kernel's double rounds from `s₁`, the first `j` blocks
at `q` absorbed: as `SR`, with `rsi` and `rdi` free. -/
structure KL (buf q : Addr) (R0 R1 : BitVec 64) (X : Nat) (V : Nat → CState) (s₁ : State)
    (n j : Nat) (s : State) : Prop where
  holds : Holds buf false (fun l => Nat.repeat innerBlock n (V l)) s
  m16 : ∀ l, s.lane .xmm15 l = rot16Mask
  frame : Frame [slotsR buf] s₁.mem s.mem
  gpr : ∀ r, r ∉ absorbRegs → r ≠ .rsi → r ≠ .rdi → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  acc : Acc R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * j))) s

/-- As `KL`, with `vprold`: the states in their registers (`SIV`). -/
structure KLV (q : Addr) (R0 R1 : BitVec 64) (X : Nat) (V : Nat → CState) (s₁ : State)
    (n j : Nat) (s : State) : Prop where
  holds : HoldsV (fun l => Nat.repeat innerBlock n (V l)) s
  mem : s.mem = s₁.mem
  gpr : ∀ r, r ∉ absorbRegs → r ≠ .rsi → r ≠ .rdi → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  acc : Acc R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * j))) s

theorem acc_keep {R0 R1 : BitVec 64} {X : Nat} {s s' : State} (h : Acc R0 R1 X s)
    (g : ∀ r, r ≠ .rsi → r ≠ .rdi → s'.gpr r = s.gpr r) : Acc R0 R1 X s' :=
  ⟨by rw [g _ (by decide) (by decide)]; exact h.r8, by rw [g _ (by decide) (by decide)]; exact h.r9,
    by rw [g _ (by decide) (by decide)]; exact h.r10, by rw [g _ (by decide) (by decide)]; exact h.h2,
    by simp only [hval, g Reg.r11 (by decide) (by decide), g Reg.rbx (by decide) (by decide),
      g Reg.rbp (by decide) (by decide)]; exact h.val⟩

/-- The blocks after `j` absorbed from a state `s`, whose memory has the
bytes of `s₁` there. -/
theorem acc_next {R0 R1 : BitVec 64} {X : Nat} {m₁ m : Mem} {q : Addr} {j d : Nat} {s : State}
    (hm : bytesAt m (q + BitVec.ofNat 64 (16 * j)) (16 * d) = bytesAt m₁ (q + BitVec.ofNat 64 (16 * j)) (16 * d))
    (h : Acc R0 R1 (absorbAll (rN R0 R1) (absorbAll (rN R0 R1) X (bytesAt m₁ q (16 * j)))
      (bytesAt m (q + BitVec.ofNat 64 (16 * j)) (16 * d))) s) :
    Acc R0 R1 (absorbAll (rN R0 R1) X (bytesAt m₁ q (16 * (j + d)))) s := by
  rw [hm, ← VG.Proof.Poly1305.absorbAll_append (by rw [VG.Proof.Poly1305.length_bytesAt]; omega_using []),
    ← VG.Proof.Poly1305.bytesAt_add, ← Nat.mul_add] at h
  exact h

section
variable {buf q : Addr} {R0 R1 : BitVec 64} {X : Nat} {V : Nat → CState} {s₁ : State} {k : Nat}
  (hk : Key R0 R1) (hrcx : s₁.gpr .rcx = buf) (hb : bufR buf ∈ s₁.wr)
  (hk32 : 16 * k ≤ 512)
  (hd : (⟨q, 16 * k⟩ : Region).Disjoint (slotsR buf))
  (hin : ∀ off n, off + n ≤ 16 * k → InRegions (s₁.rd ++ s₁.wr) (q + BitVec.ofNat 64 off) n)

include hk hrcx hb hk32 hd hin in
/-- A double round absorbing the four blocks at `rsi`. -/
theorem KL.round4 (h8 : M8 s₁.mem buf) {n j : Nat} (hj : j + 4 ≤ k) {s : State}
    (h : KL buf q R0 R1 X V s₁ n j s) (hrsi : s.gpr .rsi = q + BitVec.ofNat 64 (16 * j)) :
    WP isa (sround4 0) s fun s' => KL buf q R0 R1 X V s₁ (n + 1) (j + 4) s' ∧
      s'.gpr .rsi = s.gpr .rsi ∧ s'.gpr .rdi = s.gpr .rdi := by
  obtain h8' : M8 s.mem buf := by
    obtain e : s.mem.readW (buf + BitVec.ofNat 64 160) 256 = s₁.mem.readW (buf + BitVec.ofNat 64 160) 256 :=
      h.frame.readW (Region.contains_self _ _) (by simpa using slots_m8 buf) (by decide)
    exact ⟨by rw [e]; exact h8.1, by rw [e]; exact h8.2⟩
  obtain hd' : (⟨q + BitVec.ofNat 64 (16 * j), 16 * 4⟩ : Region).Disjoint (slotsR buf) :=
    hd.sub_left (Offset.sub_base _ (by omega_using [hj]))
  obtain hin' : ∀ off n', off + n' ≤ 16 * 4 →
      InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 off) n' := by
    intro off n' hn
    rw [h.rd, h.wr, Offset.add_add]
    exact hin _ _ (by omega_using [hj, hn])
  obtain i₀ : SI buf s false (fun l => Nat.repeat innerBlock n (V l))
      (AccTo (q + BitVec.ofNat 64 (16 * j)) R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * j))) s 0) s :=
    ⟨h.holds, h.m16, Frame.refl _ _, fun _ _ => rfl, rfl, rfl, by
      simp only [AccTo, Nat.mul_zero]
      rw [show bytesAt s.mem (q + BitVec.ofNat 64 (16 * j)) 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil]
      exact h.acc⟩
  refine WP.mono (sround4_ok hk (by rw [h.gpr _ (by decide) (by decide) (by decide), hrcx]) hrsi
    (by rw [h.wr]; exact hb) h8' hd' (by decide) hin' (j := 0) (by decide) i₀) fun s' h' => ?_
  obtain hm : bytesAt s.mem (q + BitVec.ofNat 64 (16 * j)) (16 * 4) =
      bytesAt s₁.mem (q + BitVec.ofNat 64 (16 * j)) (16 * 4) :=
    bytes_frame h.frame hd hk32 (by omega_using [hj])
  refine ⟨⟨h'.holds, h'.m16, h.frame.trans h'.frame,
    fun r hr h₁ h₂ => by rw [h'.gpr r hr, h.gpr r hr h₁ h₂], by rw [h'.rd, h.rd], by rw [h'.wr, h.wr],
    acc_next hm h'.poly⟩, h'.gpr _ (by decide), h'.gpr _ (by decide)⟩

include hrcx hb in
/-- A double round absorbing nothing. -/
theorem KL.round0 (h8 : M8 s₁.mem buf) {n j : Nat} {s : State} (h : KL buf q R0 R1 X V s₁ n j s) :
    WP isa Impl.ChaCha20.X86_64.Avx2.doubleRound s fun s' => KL buf q R0 R1 X V s₁ (n + 1) j s' ∧
      s'.gpr .rsi = s.gpr .rsi ∧ s'.gpr .rdi = s.gpr .rdi := by
  obtain h8' : M8 s.mem buf := by
    obtain e : s.mem.readW (buf + BitVec.ofNat 64 160) 256 = s₁.mem.readW (buf + BitVec.ofNat 64 160) 256 :=
      h.frame.readW (Region.contains_self _ _) (by simpa using slots_m8 buf) (by decide)
    exact ⟨by rw [e]; exact h8.1, by rw [e]; exact h8.2⟩
  obtain i₀ : SI buf s false (fun l => Nat.repeat innerBlock n (V l))
      (AccTo q R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * j))) s 0) s :=
    ⟨h.holds, h.m16, Frame.refl _ _, fun _ _ => rfl, rfl, rfl, by
      simp only [AccTo, Nat.mul_zero]
      rw [show bytesAt s.mem q 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil]
      exact h.acc⟩
  refine WP.mono (sround0_ok (by rw [h.gpr _ (by decide) (by decide) (by decide), hrcx]) (by rw [h.wr]; exact hb)
    h8' i₀) fun s' h' => ?_
  have a := h'.poly
  simp only [AccTo, Nat.mul_zero] at a
  rw [show bytesAt s.mem q 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil] at a
  exact ⟨⟨h'.holds, h'.m16, h.frame.trans h'.frame,
    fun r hr h₁ h₂ => by rw [h'.gpr r hr, h.gpr r hr h₁ h₂], by rw [h'.rd, h.rd], by rw [h'.wr, h.wr], a⟩,
    h'.gpr _ (by decide), h'.gpr _ (by decide)⟩

include hk hin in
/-- `KL.round4` with `vprold`. -/
theorem KLV.round4 {n j : Nat} (hj : j + 4 ≤ k) {s : State}
    (h : KLV q R0 R1 X V s₁ n j s) (hrsi : s.gpr .rsi = q + BitVec.ofNat 64 (16 * j)) :
    WP isa (sround4V 0) s fun s' => KLV q R0 R1 X V s₁ (n + 1) (j + 4) s' ∧
      s'.gpr .rsi = s.gpr .rsi ∧ s'.gpr .rdi = s.gpr .rdi := by
  obtain hin' : ∀ off n', off + n' ≤ 16 * 4 →
      InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 off) n' := by
    intro off n' hn
    rw [h.rd, h.wr, Offset.add_add]
    exact hin _ _ (by omega_using [hj, hn])
  obtain i₀ : SIV s (fun l => Nat.repeat innerBlock n (V l))
      (AccTo (q + BitVec.ofNat 64 (16 * j)) R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * j))) s 0) s :=
    ⟨h.holds, rfl, fun _ _ => rfl, rfl, rfl, by
      simp only [AccTo, Nat.mul_zero]
      rw [show bytesAt s.mem (q + BitVec.ofNat 64 (16 * j)) 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil]
      exact h.acc⟩
  refine WP.mono (sround4V_ok hk hrsi hin' (j := 0) (by decide) i₀) fun s' h' => ?_
  obtain hm : bytesAt s.mem (q + BitVec.ofNat 64 (16 * j)) (16 * 4) =
      bytesAt s₁.mem (q + BitVec.ofNat 64 (16 * j)) (16 * 4) := by rw [h.mem]
  exact ⟨⟨h'.holds, by rw [h'.mem, h.mem], fun r hr h₁ h₂ => by rw [h'.gpr r hr, h.gpr r hr h₁ h₂],
    by rw [h'.rd, h.rd], by rw [h'.wr, h.wr], acc_next hm h'.poly⟩, h'.gpr _ (by decide), h'.gpr _ (by decide)⟩

/-- `KL.round0` with `vprold`. -/
theorem KLV.round0 {n j : Nat} {s : State} (h : KLV q R0 R1 X V s₁ n j s) :
    WP isa Impl.ChaCha20.X86_64.Avx2.doubleRoundV s fun s' => KLV q R0 R1 X V s₁ (n + 1) j s' ∧
      s'.gpr .rsi = s.gpr .rsi ∧ s'.gpr .rdi = s.gpr .rdi := by
  obtain i₀ : SIV s (fun l => Nat.repeat innerBlock n (V l))
      (AccTo q R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * j))) s 0) s :=
    ⟨h.holds, rfl, fun _ _ => rfl, rfl, rfl, by
      simp only [AccTo, Nat.mul_zero]
      rw [show bytesAt s.mem q 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil]
      exact h.acc⟩
  refine WP.mono (sround0V_ok i₀) fun s' h' => ?_
  have a := h'.poly
  simp only [AccTo, Nat.mul_zero] at a
  rw [show bytesAt s.mem q 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil] at a
  exact ⟨⟨h'.holds, by rw [h'.mem, h.mem], fun r hr h₁ h₂ => by rw [h'.gpr r hr, h.gpr r hr h₁ h₂],
    by rw [h'.rd, h.rd], by rw [h'.wr, h.wr], a⟩, h'.gpr _ (by decide), h'.gpr _ (by decide)⟩

theorem KL.keep {n j : Nat} {s s' : State} (h : KL buf q R0 R1 X V s₁ n j s)
    (g : ∀ r, r ≠ .rsi → r ≠ .rdi → s'.gpr r = s.gpr r) (hx : s'.xmm = s.xmm) (hy : s'.ymmHi = s.ymmHi)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : KL buf q R0 R1 X V s₁ n j s' := by
  refine ⟨fun k' hk' l q' hl hq' => ?_, fun l => by simpa only [State.lane, hx, hy] using h.m16 l,
    by rw [hm]; exact h.frame, fun r hr h₁ h₂ => by rw [g r h₁ h₂, h.gpr r hr h₁ h₂], by rw [hrd, h.rd],
    by rw [hwr, h.wr], acc_keep h.acc g⟩
  obtain e := h.holds k' hk' l q' hl hq'
  split
  · rename_i hreg
    simp only [hreg, ite_true] at e
    simpa only [Proof.ChaCha20.X86_64.Avx2.vw, State.lane, hx, hy] using e
  · rename_i hreg
    simp only [hreg] at e
    rw [hm]; exact e

theorem KLV.keep {n j : Nat} {s s' : State} (h : KLV q R0 R1 X V s₁ n j s)
    (g : ∀ r, r ≠ .rsi → r ≠ .rdi → s'.gpr r = s.gpr r) (hx : s'.xmm = s.xmm) (hy : s'.ymmHi = s.ymmHi)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : KLV q R0 R1 X V s₁ n j s' :=
  ⟨fun k' hk' l q' hl hq' => by
      simpa only [Proof.ChaCha20.X86_64.Avx2.vw, State.lane, hx, hy] using h.holds k' hk' l q' hl hq',
    by rw [hm, h.mem], fun r hr h₁ h₂ => by rw [g r h₁ h₂, h.gpr r hr h₁ h₂], by rw [hrd, h.rd],
    by rw [hwr, h.wr], acc_keep h.acc g⟩

include hk hrcx hb hk32 hd hin in
/-- `roundsLK`: the kernel's ten double rounds, the first `k` blocks at `q`
absorbed, `rsi` back at `q` and `rdi` at `buf - 64`. -/
theorem roundsLK_ok (vl : Bool) (h1 : 1 ≤ k / 4) (h10 : k / 4 < 10) (hk4 : 4 * (k / 4) = k)
    (sk : BitVec.signExtend 64 (BitVec.ofNat 32 (16 * k)) = BitVec.ofNat 64 (16 * k))
    (h8 : M8 s₁.mem buf) (h16 : M16 s₁.mem buf) (hrsi : s₁.gpr .rsi = q)
    (h : KL buf q R0 R1 X V s₁ 0 0 s₁) :
    WP isa (roundsLK vl k) s₁ fun s' => KL buf q R0 R1 X V s₁ 10 k s' ∧ s'.gpr .rsi = q ∧
      s'.gpr .rdi = buf - 64 := by
  obtain hc : ∀ {s : State}, KL buf q R0 R1 X V s₁ 10 k s → s.gpr .rcx = buf := fun h' => by
    rw [h'.gpr _ (by decide) (by decide) (by decide), hrcx]
  unfold roundsLK
  cases vl
  · refine WP.mono (roundsL_ok (KL buf q R0 R1 X V s₁) h1 h10 hk4 sk
      (fun _ _ _ _ h' g x y m rd wr => h'.keep g x y m rd wr)
      (fun n s hn h' hr => KL.round4 hk hrcx hb hk32 hd hin h8 (j := 4 * n) (show 4 * n + 4 ≤ k by omega_using [hn]) h' hr)
      (fun n s _ _ h' _ => KL.round0 hrcx hb h8 h') h hrsi) fun s' ⟨h', r', d'⟩ => ⟨h', r', by rw [d', hc h']⟩
  · simp only [ite_true]
    refine WP.seq (WP.mono (loadV_ok h.holds hrcx hb) fun s₂ ⟨h₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
    obtain i₂ : KLV q R0 R1 X V s₁ 0 0 s₂ :=
      ⟨h₂, m₂, fun r _ _ _ => by rw [g₂], rd₂, wr₂, acc_keep h.acc fun r _ _ => by rw [g₂]⟩
    refine WP.seq (WP.mono (roundsL_ok (KLV q R0 R1 X V s₁) h1 h10 hk4 sk
      (fun _ _ _ _ h' g x y m rd wr => h'.keep g x y m rd wr)
      (fun n s hn h' hr => KLV.round4 hk hin (j := 4 * n) (show 4 * n + 4 ≤ k by omega_using [hn]) h' hr)
      (fun n s _ _ h' _ => KLV.round0 h') i₂ (by rw [g₂, hrsi])) fun s₃ ⟨h₃, r₃, d₃⟩ => ?_)
    obtain c₃ : s₃.gpr .rcx = buf := by rw [h₃.gpr _ (by decide) (by decide) (by decide), hrcx]
    refine WP.mono (storeV_ok (s₀ := s₃) ⟨h₃.holds, rfl, rfl, rfl, rfl⟩ c₃ (by rw [h₃.wr]; exact hb)
      (by rw [h₃.mem]; exact h16)) fun s₄ h₄ => ?_
    refine ⟨⟨h₄.holds, h₄.m16, by rw [← h₃.mem]; exact h₄.frame,
      fun r hr h₁ h₂ => by rw [h₄.gpr, h₃.gpr r hr h₁ h₂], by rw [h₄.rd, h₃.rd], by rw [h₄.wr, h₃.wr],
      acc_keep h₃.acc fun r _ _ => by rw [h₄.gpr]⟩, by rw [h₄.gpr, r₃], by rw [h₄.gpr, d₃, c₃]⟩

end

/-- `tailKMain_ok` for `roundsLK`: the eight blocks of keystream from the
state at `st` (`buf - 64`) stored at `kA buf`, while the first `k` blocks at
`q` are absorbed. -/
theorem tailKL_ok (vl : Bool) {k : Nat} (h1 : 1 ≤ k / 4) (h10 : k / 4 < 10) (hk4 : 4 * (k / 4) = k)
    (hk32 : 16 * k ≤ 512)
    (sk : BitVec.signExtend 64 (BitVec.ofNat 32 (16 * k)) = BitVec.ofNat 64 (16 * k))
    {R0 R1 : BitVec 64} (hk : Key R0 R1) {X : Nat} {st buf q : Addr} {s : State}
    (hrdi : s.gpr .rdi = st) (hrcx : s.gpr .rcx = buf) (hrsi : s.gpr .rsi = q) (hsb : buf - 64 = st)
    (hst : stR st ∈ s.wr) (hb : bufR buf ∈ s.wr) (hkr : kR buf ∈ s.wr)
    (hin : ∀ off n, off + n ≤ 16 * k → InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 off) n)
    (hc : Consts s.mem buf) (dsb : (stR st).Disjoint (bufR buf)) (dsk : (stR st).Disjoint (kR buf))
    (dbk : (bufR buf).Disjoint (kR buf)) (dqs : (⟨q, 16 * k⟩ : Region).Disjoint (slotsR buf))
    (hacc : Acc R0 R1 X s) :
    WP isa (.seq (.block Impl.ChaCha20.X86_64.Avx2.setup)
        (.seq (roundsLK vl k) (.block (Impl.ChaCha20.X86_64.Avx2.finishWith (storeRow kOff))))) s fun s' =>
        (∀ i < 512, s'.mem (kA buf + BitVec.ofNat 64 i) =
          (serialize (plus (fun j => Nat.repeat innerBlock 10 (ctr (stateAt s.mem st) j))
            (stateAt s.mem st) (i / 64))).getD (i % 64) 0) ∧
        Acc R0 R1 (absorbAll (rN R0 R1) X (bytesAt s.mem q (16 * k))) s' ∧
        Frame [slotsR buf, kR buf] s.mem s'.mem ∧
        (∀ r, r ∉ absorbRegs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (WP.mono (setup_ok hrdi hrcx hst hb hc)
    fun s₁ ⟨hh, h15, g₁, rd₁, wr₁, y₁, y₂, m₁⟩ => ?_)
  obtain c₁ : Consts s₁.mem buf := by rw [m₁]; exact hc.w2 (by decide) y₁ y₂
  obtain F₁ : Frame [slotsR buf] s.mem s₁.mem := by
    rw [m₁]; exact W2_frame _ (by decide) y₁ y₂ (Frame.refl _ _)
  obtain q₁ : bytesAt s₁.mem q (16 * k) = bytesAt s.mem q (16 * k) := by
    have := bytes_frame F₁ dqs hk32 (j := 0) (n := 16 * k) (by omega_using [])
    simpa using this
  obtain h0 : KL buf q R0 R1 X (fun j => ctr (stateAt s.mem st) j) s₁ 0 0 s₁ :=
    ⟨hh, h15, Frame.refl _ _, fun _ _ _ _ => rfl, rfl, rfl, by
      rw [show 16 * 0 = 0 from rfl, show bytesAt s₁.mem q 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil]
      exact ⟨by rw [g₁]; exact hacc.r8, by rw [g₁]; exact hacc.r9, by rw [g₁]; exact hacc.r10,
        by rw [g₁]; exact hacc.h2, by simp only [hval, g₁]; exact hacc.val⟩⟩
  refine WP.seq (WP.mono (roundsLK_ok hk (by rw [g₁, hrcx]) (by rw [wr₁]; exact hb) hk32 dqs
    (by rw [rd₁, wr₁]; exact hin) vl h1 h10 hk4 sk c₁.m8 ⟨c₁.lo16, c₁.hi16⟩ (by rw [g₁, hrsi]) h0)
    fun s₂ ⟨h₂, r₂, d₂⟩ => ?_)
  obtain F₂ : Frame [slotsR buf] s.mem s₂.mem := F₁.trans h₂.frame
  obtain gk : ∀ r, r ∉ absorbRegs → s₂.gpr r = s.gpr r := fun r hr => by
    by_cases e₁ : r = .rsi
    · subst e₁; rw [r₂, hrsi]
    by_cases e₂ : r = .rdi
    · subst e₂; rw [d₂, hsb, hrdi]
    rw [h₂.gpr r hr e₁ e₂, g₁]
  obtain wr₂ : s₂.wr = s.wr := by rw [h₂.wr, wr₁]
  obtain inc₂ : Incs buf s₂.mem := incs_frame hc.inc F₂ (by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hiR_slots _)
  refine WP.mono (finishK_ok h₂.holds (st := st) (by rw [gk _ (by decide), hrdi]) (by rw [gk _ (by decide), hrcx])
    (by rw [wr₂]; exact hst) (by rw [wr₂]; exact hb) (by rw [wr₂]; exact hkr) inc₂ dsb dsk dbk)
    fun s₃ ⟨d₃, f₃, g₃, rd₃, wr₃⟩ => ?_
  obtain hS : stateAt s₂.mem st = stateAt s.mem st :=
    Proof.ChaCha20.X86_64.Xor.stateAt_frame F₂ (by simpa using dsb.sub_right (slotsR_sub buf))
  refine ⟨fun i hi => by rw [d₃ i hi, hS], ?_, (F₂.mono (by simp)).trans f₃,
    fun r hr => by rw [g₃, gk r hr], by rw [rd₃, h₂.rd, rd₁], by rw [wr₃, wr₂]⟩
  have a₂ := h₂.acc
  rw [q₁] at a₂
  exact ⟨by rw [g₃]; exact a₂.r8, by rw [g₃]; exact a₂.r9, by rw [g₃]; exact a₂.r10, by rw [g₃]; exact a₂.h2,
    by simp only [hval, g₃]; exact a₂.val⟩

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch

end

end


/-!
# ChaCha20 and Poly1305 together (x86-64): the last 257 to 511 bytes of `open`

After `open`'s whole chunks, with `n` bytes left (at least `16 k`), their
keystream stored at `ctx + 736` (`kA buf`) while their first `k` blocks are
absorbed, the accumulator stored and the registers restored, `rbx`, `rbp` at
the bytes after those blocks (`TailMidKO`): up to 384 bytes by
`Stitch.tail3O` (`tail3Og_ok`): the constants stored and `Avx2Tail`'s setup
of three sets (`tailA3_ok`), the rounds (two loops, `roundsL_ok`, of
`K3.round4` and `K3.round0`), and the output through `rsi` (`tailBO3_ok`,
`out3_ok`); up to 512 by `Stitch.tailKO` (`tailKOg_ok`): the kernel's eight
blocks (`tailKL_ok`) and `leaveTO`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Proof.ChaCha20.X86_64.Avx2 (Consts stR bufR slotsR pairs_ok pairsCode constPairs constPairs_le tPairs
  tPairs_le tconsts_eq consts_eq consts_mem tincs_mem)
open VG.Proof.ChaCha20.X86_64.Avx2Tail (HB YM3 Incs)
open VG.Proof.ChaCha20.X86_64.Avx512Tail (Ctx regn baseR bsize wregs S0)
open VG.Proof.ChaCha20 (CState ctr)
open VG.Spec.ChaCha20 (stateAt serialize keystream innerBlock)
open VG.Spec.Poly1305 (P bytesAt leNum)
open VG.Proof.Poly1305 (absorbAll)
open VG.Proof.Poly1305.X86_64 (hval absorbRegs)

/-- The schedules of `tail3O`'s rounds: four blocks, and none. -/
theorem schedOk_o4 : SchedOk (oblocks 4) (ofirst 4) 4 :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩
theorem schedOk_o0 : SchedOk (oblocks 0) (ofirst 0) 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- After `n` double rounds of three sets from `s₁`, the first `j` blocks at
`q` absorbed: as `TB3`, with `rsi` and `rdi` free. -/
structure K3 (q : Addr) (R0 R1 : BitVec 64) (X : Nat) (V : Nat → CState) (s₁ : State)
    (n j : Nat) (s : State) : Prop where
  hb : HB 3 (fun l => Nat.repeat innerBlock n (V l)) s
  ym : YM3 s
  mem : s.mem = s₁.mem
  gpr : ∀ r, r ∉ absorbRegs → r ≠ .rsi → r ≠ .rdi → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  acc : Acc R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * j))) s

section
variable {q : Addr} {R0 R1 : BitVec 64} {X : Nat} {V : Nat → CState} {s₁ : State}

theorem K3.keep {n j : Nat} {s s' : State} (h : K3 q R0 R1 X V s₁ n j s)
    (g : ∀ r, r ≠ .rsi → r ≠ .rdi → s'.gpr r = s.gpr r) (hx : s'.xmm = s.xmm) (hy : s'.ymmHi = s.ymmHi)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : K3 q R0 R1 X V s₁ n j s' :=
  ⟨fun k hk l hl i hi => by simpa only [State.lane, hx, hy] using h.hb k hk l hl i hi,
    fun l => by simpa only [State.lane, hx, hy] using h.ym l, by rw [hm, h.mem],
    fun r hr h₁ h₂ => by rw [g r h₁ h₂, h.gpr r hr h₁ h₂], by rw [hrd, h.rd], by rw [hwr, h.wr],
    acc_keep h.acc g⟩

/-- A double round of three sets absorbing the four blocks at `rsi`. -/
theorem K3.round4 {k : Nat} (hk : Key R0 R1)
    (hin : ∀ off n, off + n ≤ 16 * k → InRegions (s₁.rd ++ s₁.wr) (q + BitVec.ofNat 64 off) n)
    {n j : Nat} (hj : j + 4 ≤ k) {s : State}
    (h : K3 q R0 R1 X V s₁ n j s) (hrsi : s.gpr .rsi = q + BitVec.ofNat 64 (16 * j)) :
    WP isa (.block (troundG3 (oblocks 4) (ofirst 4) 0)) s fun s' => K3 q R0 R1 X V s₁ (n + 1) (j + 4) s' ∧
      s'.gpr .rsi = s.gpr .rsi ∧ s'.gpr .rdi = s.gpr .rdi := by
  obtain hin' : ∀ off n', off + n' ≤ 16 * 4 →
      InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 off) n' := by
    intro off n' hn
    rw [h.rd, h.wr, Offset.add_add]
    exact hin _ _ (by omega_arith)
  obtain i₀ : TB3 s (fun l => Nat.repeat innerBlock n (V l))
      (AccTo (q + BitVec.ofNat 64 (16 * j)) R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * j))) s
        (ofirst 4 0)) s :=
    ⟨h.hb, h.ym, rfl, fun _ _ => rfl, rfl, rfl, by
      simp only [AccTo, show ofirst 4 0 = 0 from rfl, Nat.mul_zero]
      rw [show bytesAt s.mem (q + BitVec.ofNat 64 (16 * j)) 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil]
      exact h.acc⟩
  refine WP.mono (troundG3_ok hk hrsi hin' schedOk_o4 (Nat.le_refl _) (by decide) i₀) fun s' h' => ?_
  obtain hm : bytesAt s.mem (q + BitVec.ofNat 64 (16 * j)) (16 * 4) =
      bytesAt s₁.mem (q + BitVec.ofNat 64 (16 * j)) (16 * 4) := by rw [h.mem]
  exact ⟨⟨h'.hb, h'.ym, by rw [h'.mem, h.mem], fun r hr h₁ h₂ => by rw [h'.gpr r hr, h.gpr r hr h₁ h₂],
    by rw [h'.rd, h.rd], by rw [h'.wr, h.wr], acc_next hm h'.poly⟩, h'.gpr _ (by decide), h'.gpr _ (by decide)⟩

/-- A double round of three sets absorbing nothing. -/
theorem K3.round0 {k : Nat} (hk : Key R0 R1)
    (hin : ∀ off n, off + n ≤ 16 * k → InRegions (s₁.rd ++ s₁.wr) (q + BitVec.ofNat 64 off) n)
    {n j : Nat} {s : State} (h : K3 q R0 R1 X V s₁ n j s) (hrsi : s.gpr .rsi = q) :
    WP isa (.block (troundG3 (oblocks 0) (ofirst 0) 0)) s fun s' => K3 q R0 R1 X V s₁ (n + 1) j s' ∧
      s'.gpr .rsi = s.gpr .rsi ∧ s'.gpr .rdi = s.gpr .rdi := by
  obtain i₀ : TB3 s (fun l => Nat.repeat innerBlock n (V l))
      (AccTo q R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * j))) s (ofirst 0 0)) s :=
    ⟨h.hb, h.ym, rfl, fun _ _ => rfl, rfl, rfl, by
      simp only [AccTo, show ofirst 0 0 = 0 from rfl, Nat.mul_zero]
      rw [show bytesAt s.mem q 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil]
      exact h.acc⟩
  refine WP.mono (troundG3_ok hk hrsi (fun off n' hn => by rw [h.rd, h.wr]; exact hin off n' hn) schedOk_o0
    (Nat.zero_le _) (by decide) i₀) fun s' h' => ?_
  have a := h'.poly
  simp only [AccTo, show ofirst 0 1 = 0 from rfl, Nat.mul_zero] at a
  rw [show bytesAt s.mem q 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil] at a
  exact ⟨⟨h'.hb, h'.ym, by rw [h'.mem, h.mem], fun r hr h₁ h₂ => by rw [h'.gpr r hr, h.gpr r hr h₁ h₂],
    by rw [h'.rd, h.rd], by rw [h'.wr, h.wr], a⟩, h'.gpr _ (by decide), h'.gpr _ (by decide)⟩

end

section
variable {c : Addr}

/-- The state, 64 bytes below `buf`, where `roundsL` leaves `rdi`. -/
theorem bf_sub64 : bfA c - 64 = stA c := by
  simp only [bfA, stA]
  rw [show BitVec.ofNat 64 128 = BitVec.ofNat 64 64 + 64 from rfl, ← BitVec.add_assoc, BitVec.add_sub_cancel]

theorem tailA3_eq : tailA3 = pairsCode tPairs ++ (pairsCode constPairs ++
    (([.mov .r12 (.reg .r9), .mov .r9 (.reg .rcx)] : List Instr) ++
    (Impl.ChaCha20.X86_64.Avx2Tail.setup3 ++ ([.mov .r9 (.reg .r12)] : List Instr)))) := by
  simp only [tailA3, tconsts_eq, consts_eq, List.append_assoc]

/-- `tailA3`: the constants stored, and the input states of the six blocks
after the counter of the state at `stA c` in the vector registers. -/
theorem tailA3_ok {s : State} (hrcx : s.gpr .rcx = bfA c) (hrdi : s.gpr .rdi = stA c)
    (hst : stR (stA c) ∈ s.wr) (hb : bufR (bfA c) ∈ s.wr) :
    WP isa (.block tailA3) s fun s' =>
      HB 3 (fun j => ctr (stateAt s.mem (stA c)) j) s' ∧ YM3 s' ∧ s'.mem = tMem c s.mem ∧
      (∀ r, r ≠ .rax → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.gpr .r12 = s.gpr .r9 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [tailA3_eq]
  refine WP.block_append (WP.mono (pairs_ok tPairs tPairs_le hrcx hb) fun s₁ ⟨m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.block_append (WP.mono (pairs_ok (buf := bfA c) constPairs constPairs_le (s := s₁)
    (by rw [g₁ _ (by decide), hrcx]) (by rw [wr₁]; exact hb)) fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_)
  refine WP.block_append (WP.mono movs_ok fun s₃ ⟨r12₃, r9₃, g₃, m₃, rd₃, wr₃, _, _⟩ => ?_)
  obtain mm : s₃.mem = tMem c s.mem := by rw [m₃, m₂, m₁]
  obtain rdi₃ : s₃.gpr .rdi = stA c := by
    rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), g₁ _ (by decide), hrdi]
  obtain r9₃' : s₃.gpr .r9 = bfA c := by rw [r9₃, g₂ _ (by decide), g₁ _ (by decide), hrcx]
  obtain wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂, wr₁]
  obtain hc : Ctx 0 s₃ := ctx0 rdi₃ r9₃' (by rw [wr₃']; exact hst) (by rw [wr₃']; exact hb)
  obtain cst : Consts s₃.mem (s₃.gpr .r9) := by rw [mm, r9₃']; exact consts_mem _ _
  obtain inc : Incs s₃.mem (s₃.gpr .r9) := by rw [mm, r9₃']; exact tincs_mem _ _
  obtain S₃ : S0 s₃ = stateAt s.mem (stA c) := by
    simp only [S0, rdi₃, mm]
    exact Proof.ChaCha20.X86_64.Xor.stateAt_frame (tMem_frame _) (by simpa using st_bf)
  refine WP.block_append (WP.mono (setup3_ok0 hc cst inc) fun s₄ ⟨hz, ym, m₄, g₄, rd₄, wr₄⟩ => ?_)
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

/-- The regions of `tail3O`'s output: the ChaCha20 state at `rdi`, `buf` at
`r9`, and 384 bytes at `ctx + 736` (in `kA buf`) at `rsi`. -/
theorem ctx96 {s : State} (hrdi : s.gpr .rdi = stA c) (hr9 : s.gpr .r9 = bfA c)
    (hrsi : s.gpr .rsi = c + BitVec.ofNat 64 736) (hst : stR (stA c) ∈ s.wr)
    (hb : bufR (bfA c) ∈ s.wr) (hk : kR (bfA c) ∈ s.wr) : Ctx 96 s := by
  obtain r0 : regn 96 s 0 = stR (stA c) := by simp only [regn, baseR, bsize, hrdi, Nat.reduceMul]
  obtain r1 : regn 96 s 1 = bufR (bfA c) := by simp only [regn, baseR, bsize, hr9, Nat.reduceMul]
  obtain r2 : regn 96 s 2 = ⟨c + BitVec.ofNat 64 736, 384⟩ := by
    simp only [regn, baseR, bsize, hrsi, Nat.reduceMul]
  obtain kc : kR (bfA c) = ⟨c + BitVec.ofNat 64 736, 512⟩ := by simp only [kR, kA, bfA, Offset.add_add]
  obtain d01 : (regn 96 s 0).Disjoint (regn 96 s 1) := by rw [r0, r1]; exact st_bf (c := c)
  obtain d02 : (regn 96 s 0).Disjoint (regn 96 s 2) := by
    rw [r0, r2]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  obtain d12 : (regn 96 s 1).Disjoint (regn 96 s 2) := by
    rw [r1, r2]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  refine ⟨fun b i n hb3 h hn => ?_, fun b b' hb hb' ne => ?_, by decide⟩
  · rcases (by omega_arith : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;> simp only [bsize] at h
    · rw [r0]; exact ⟨_, hst, Offset.contains_base _ (by omega_arith) (by lit_omega)⟩
    · rw [r1]; exact ⟨_, hb, Offset.contains_base _ (by omega_arith) (by lit_omega)⟩
    · rw [r2]; refine ⟨_, hk, ?_⟩; rw [kc, Offset.add_add]
      exact Offset.contains c (by omega_arith) (by omega_arith) (by decide)
  · rcases (by omega_arith : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
      rcases (by omega_arith : b' = 0 ∨ b' = 1 ∨ b' = 2) with rfl | rfl | rfl
    · exact absurd rfl ne
    · exact d01
    · exact d02
    · exact d01.symm
    · exact absurd rfl ne
    · exact d12
    · exact d02.symm
    · exact d12.symm
    · exact absurd rfl ne

theorem rsi736_ok {s : State} (hr15 : s.gpr .r15 = c) :
    WP isa (.block (Impl.ChaCha20Poly1305.X86_64.ptr .rsi .r15 736)) s fun s' =>
      s'.gpr .rsi = c + BitVec.ofNat 64 736 ∧ (∀ r, r ≠ .rsi → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  obtain se : BitVec.signExtend 64 (BitVec.ofNat 32 736) = BitVec.ofNat 64 736 := by decide
  apply WP.of_runBlock
  simp only [Impl.ChaCha20Poly1305.X86_64.ptr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', ↓reduceIte, se, hr15]
  exact ⟨trivial, fun r hr => by simp [hr], trivial, trivial, trivial, rfl, rfl⟩

/-- `tailBO3`: the accumulator reduced and stored, the registers restored,
`rbx`, `rbp` past the first `k` blocks, and the keystream of the three sets
at `ctx + 736`. -/
theorem tailBO3_ok {k : Nat} (sk : BitVec.signExtend 64 (BitVec.ofNat 32 (16 * k)) = BitVec.ofNat 64 (16 * k))
    (sc : scalCode (.block (storeTO k)) = true) {vs : Nat → CState} {s : State}
    (hz : HB 3 vs s) (hrcx : s.gpr .rcx = bfA c) (hrdi : s.gpr .rdi = stA c) (hst : stR (stA c) ∈ s.wr)
    (hb : bufR (bfA c) ∈ s.wr) (hps : psR c ∈ s.wr) (hkr : kR (bfA c) ∈ s.wr) (hi : Incs s.mem (bfA c))
    (h2 : (s.gpr .rbp).toNat ≤ 4) :
    WP isa (.block (tailBO3 k)) s fun s' =>
      (∀ k' < 384, s'.mem (kA (bfA c) + BitVec.ofNat 64 k') =
        (serialize (Proof.ChaCha20.X86_64.Avx2.plus vs (stateAt s.mem (stA c)) (k' / 64))).getD (k' % 64) 0) ∧
      leNum (bytesAt s'.mem (psA c) 24) = hval s % P ∧
      Frame [accR c, bufR (bfA c), kR (bfA c)] s.mem s'.mem ∧
      s'.gpr .rbx = s.gpr .rsi + BitVec.ofNat 64 (16 * k) ∧
      s'.gpr .rbp = s.mem.readW (c + BitVec.ofNat 64 544) 64 - BitVec.ofNat 64 (16 * k) ∧
      s'.gpr .r12 = s.mem.readW (c + BitVec.ofNat 64 520) 64 ∧
      s'.gpr .r13 = s.mem.readW (c + BitVec.ofNat 64 528) 64 ∧
      s'.gpr .r14 = s.mem.readW (c + BitVec.ofNat 64 536) 64 ∧ s'.gpr .r15 = c ∧
      s'.gpr .rcx = bfA c ∧ s'.gpr .rsp = s.gpr .rsp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain kc : kR (bfA c) = ⟨c + BitVec.ofNat 64 736, 512⟩ := by simp only [kR, kA, bfA, Offset.add_add]
  obtain ka : kA (bfA c) = c + BitVec.ofNat 64 736 := by simp only [kA, bfA, Offset.add_add]
  simp only [tailBO3, leaveTO_eq, List.append_assoc]
  refine WP.block_append (WP.mono (WP.vecKeep scal_reduce (Proof.Poly1305.X86_64.reduce_ok s))
    fun s₁ ⟨⟨red, k₁⟩, x₁, y₁⟩ => ?_)
  refine WP.block_append (WP.mono (WP.vecKeep sc (storeTO_ok sk (c := c) (s := s₁)
    (by rw [k₁.gpr', hrcx]) (by rw [k₁.2.2.2]; exact hps)))
    fun s₂ ⟨⟨m₂, rbx₂, rbp₂, r12₂, r13₂, r14₂, r15₂, g₂, rd₂, wr₂⟩, x₂, y₂⟩ => ?_)
  refine WP.block_append (WP.mono (movR_ok .r9 .rcx) fun s₃ ⟨r9₃, g₃, m₃, rd₃, wr₃, x₃, y₃⟩ => ?_)
  refine WP.block_append (WP.mono (rsi736_ok (c := c) (s := s₃) (by rw [g₃ _ (by decide), r15₂]))
    fun s₄ ⟨rsi₄, g₄, m₄, rd₄, wr₄, x₄, y₄⟩ => ?_)
  obtain k12 : ∀ r, r = .rdi ∨ r = .rcx ∨ r = .rsi ∨ r = .rsp → s₂.gpr r = s.gpr r := by
    intro r hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k₁.gpr']
  obtain g34 : ∀ r, r ≠ .r9 → r ≠ .rsi → s₄.gpr r = s₂.gpr r := fun r h9 hs => by rw [g₄ r hs, g₃ r h9]
  obtain rdi₄ : s₄.gpr .rdi = stA c := by rw [g34 _ (by decide) (by decide), k12 _ (.inl rfl), hrdi]
  obtain rcx₄ : s₄.gpr .rcx = bfA c := by rw [g34 _ (by decide) (by decide), k12 _ (.inr (.inl rfl)), hrcx]
  obtain r9₄ : s₄.gpr .r9 = bfA c := by rw [g₄ _ (by decide), r9₃, k12 _ (.inr (.inl rfl)), hrcx]
  obtain wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, k₁.2.2.2]
  obtain rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, k₁.2.2.1]
  obtain m₄' : s₄.mem = accMem s.mem c (s₁.gpr .r11) (s₁.gpr .rbx) (s₁.gpr .rbp) := by rw [m₄, m₃, m₂, k₁.2.1]
  obtain fa : Frame [accR c] s.mem s₄.mem := by rw [m₄']; exact accMem_frame _ _ _ _ _
  obtain hc : Ctx 96 s₄ := ctx96 rdi₄ r9₄ rsi₄ (by rw [wr₄']; exact hst) (by rw [wr₄']; exact hb)
    (by rw [wr₄']; exact hkr)
  obtain hi₄ : Incs s₄.mem (s₄.gpr .r9) := by
    rw [r9₄]
    refine Proof.ChaCha20.X86_64.Avx2Tail.incs_frame hi fa ?_
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    obtain e : Proof.ChaCha20.X86_64.Avx2.hiR (bfA c) = ⟨c + BitVec.ofNat 64 256, 192⟩ := by
      simp only [Proof.ChaCha20.X86_64.Avx2.hiR, bfA, Offset.add_add]
    rw [e]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  obtain hz₄ : HB 3 vs s₄ := hb_of_vec hz (by rw [x₄, x₃, x₂, x₁]) (by rw [y₄, y₃, y₂, y₁])
  obtain S₄ : S0 s₄ = stateAt s.mem (stA c) := by
    simp only [S0, rdi₄]
    exact Proof.ChaCha20.X86_64.Xor.stateAt_frame fa (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide))
  obtain acc₄ : leNum (bytesAt s₄.mem (psA c) 24) = hval s % P := by
    rw [m₄', accMem_acc]; exact red h2
  rw [show Impl.ChaCha20.X86_64.Avx2Tail.addIn3 ++ (storeSetS .xmm0 .xmm1 .xmm2 .xmm3 0 ++
      (storeSetS .xmm4 .xmm5 .xmm6 .xmm7 128 ++ (storeSetS .xmm8 .xmm9 .xmm10 .xmm11 256 ++
      ([.vop .vzeroupper] : List Instr)))) = (Impl.ChaCha20.X86_64.Avx2Tail.addIn3 ++
      (storeSetS .xmm0 .xmm1 .xmm2 .xmm3 0 ++ (storeSetS .xmm4 .xmm5 .xmm6 .xmm7 128 ++
      storeSetS .xmm8 .xmm9 .xmm10 .xmm11 256))) ++ ([.vop .vzeroupper] : List Instr) by
    simp only [List.append_assoc]]
  refine WP.block_append (WP.mono (out3_ok hc hi₄ hz₄) fun s₅ ⟨b₅, f₅, g₅, rd₅, wr₅⟩ => ?_)
  refine WP.mono (Proof.ChaCha20.X86_64.Avx2.vz_ok s₅) fun s₆ ⟨g₆, m₆, rd₆, wr₆⟩ => ?_
  obtain gg : ∀ r, s₆.gpr r = s₄.gpr r := fun r => by rw [g₆, g₅]
  obtain f₄₆ : Frame [bufR (bfA c), kR (bfA c)] s₄.mem s₆.mem := by
    rw [m₆]
    refine f₅.sub fun r hr => ?_
    simp only [wregs, r9₄, rsi₄, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨bufR (bfA c), by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨kR (bfA c), by simp, by rw [kc]; exact Region.sub_prefix (by decide)⟩
  obtain hb9 : bytesAt s₆.mem (psA c) 24 = bytesAt s₄.mem (psA c) 24 :=
    bytesAt_frame f₄₆ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
      · rw [kc]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)) (by decide)
  refine ⟨fun k' hk' => ?_, by rw [hb9, acc₄], (fa.mono (by simp)).trans (f₄₆.mono (by simp)), ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, by rw [rd₆, rd₅, rd₄'], by rw [wr₆, wr₅, wr₄']⟩
  · rw [m₆, ka, ← rsi₄, b₅ k' hk', S₄]
  · rw [gg, g34 _ (by decide) (by decide), rbx₂, k₁.gpr']
  · rw [gg, g34 _ (by decide) (by decide), rbp₂, k₁.2.1]
  · rw [gg, g34 _ (by decide) (by decide), r12₂, k₁.2.1]
  · rw [gg, g34 _ (by decide) (by decide), r13₂, k₁.2.1]
  · rw [gg, g34 _ (by decide) (by decide), r14₂, k₁.2.1]
  · rw [gg, g34 _ (by decide) (by decide), r15₂]
  · rw [gg, rcx₄]
  · rw [gg, g34 _ (by decide) (by decide), k12 _ (.inr (.inr (.inr rfl)))]

end

/-- After `tail3O` or `tailKO`, from `s`: the keystream of the `n` bytes
left at `kA buf` (`ctx + 736`), their first `k` blocks absorbed, the
accumulator stored, `rbx`, `rbp` the bytes after those blocks, and the
stashed registers restored. -/
structure TailMidKO (c dp : Addr) (o n k : Nat) (R0 R1 : BitVec 64) (X : Nat) (sp : Addr)
    (s s' : State) : Prop where
  ks : ∀ i < n, s'.mem (kA (bfA c) + BitVec.ofNat 64 i) = (keystream (stateAt s.mem (stA c)) n).getD i 0
  acc : leNum (bytesAt s'.mem (psA c) 24) =
    absorbAll (rN R0 R1) X (bytesAt s.mem (dp + BitVec.ofNat 64 o) (16 * k)) % P
  frame : Frame [accR c, bufR (bfA c), kR (bfA c)] s.mem s'.mem
  rbx : s'.gpr .rbx = dp + BitVec.ofNat 64 (o + 16 * k)
  rbp : s'.gpr .rbp = BitVec.ofNat 64 (n - 16 * k)
  r12 : s'.gpr .r12 = s.mem.readW (c + BitVec.ofNat 64 520) 64
  r13 : s'.gpr .r13 = s.mem.readW (c + BitVec.ofNat 64 528) 64
  r14 : s'.gpr .r14 = s.mem.readW (c + BitVec.ofNat 64 536) 64
  r15 : s'.gpr .r15 = c
  rsp : s'.gpr .rsp = sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- `tail3O 16`, with 256 to 384 bytes left. -/
theorem tail3Og_ok {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} (hk : Key R0 R1) {X : Nat}
    {o n : Nat} {sp : Addr} (hkn : 256 ≤ n) (hhi : n ≤ 384) {s : State} (h : TPO c dp L o n R0 R1 X sp s)
    (hkr : kR (bfA c) ∈ s.wr) :
    WP isa (tail3O 16) s (TailMidKO c dp o n 16 R0 R1 X sp s) := by
  have hLe := hl.L_lt
  have hTL := h.le
  unfold tail3O
  -- The constants and the setup.
  refine WP.seq (WP.mono (tailA3_ok h.rcx h.rdi h.st h.bf)
    fun s₁ ⟨hz₁, ym₁, m₁, gk₁, _, rd₁, wr₁⟩ => ?_)
  obtain tb₁ : TB3 s₁ (fun j => ctr (stateAt s.mem (stA c)) j) (AccTo (dp + BitVec.ofNat 64 o) R0 R1 X s₁ 0) s₁ := by
    refine ⟨hz₁, ym₁, rfl, fun _ _ => rfl, rfl, rfl, ?_⟩
    simp only [AccTo, Nat.mul_zero]
    rw [show bytesAt s₁.mem (dp + BitVec.ofNat 64 o) 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil]
    have a := h.acc
    exact ⟨by rw [gk₁ _ (by decide) (by decide)]; exact a.r8, by rw [gk₁ _ (by decide) (by decide)]; exact a.r9,
      by rw [gk₁ _ (by decide) (by decide)]; exact a.r10, by rw [gk₁ _ (by decide) (by decide)]; exact a.h2,
      by simp only [hval, gk₁ (Reg.r11) (by decide) (by decide), gk₁ (Reg.rbx) (by decide) (by decide),
        gk₁ (Reg.rbp) (by decide) (by decide)]; exact a.val⟩
  obtain hrsi₁ : s₁.gpr .rsi = dp + BitVec.ofNat 64 o := by rw [gk₁ _ (by decide) (by decide), h.rsi]
  obtain hin : ∀ off n', off + n' ≤ 16 * 16 →
      InRegions (s₁.rd ++ s₁.wr) (dp + BitVec.ofNat 64 o + BitVec.ofNat 64 off) n' := by
    intro off n' hn
    refine ⟨_, by rw [rd₁, wr₁]; exact h.dw, ?_⟩
    rw [Offset.add_add]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  -- The rounds.
  obtain k₁ : K3 (dp + BitVec.ofNat 64 o) R0 R1 X (fun j => ctr (stateAt s.mem (stA c)) j) s₁ 0 0 s₁ :=
    ⟨tb₁.hb, tb₁.ym, rfl, fun _ _ _ _ => rfl, rfl, rfl, tb₁.poly⟩
  refine WP.seq (WP.mono (roundsL_ok (K3 (dp + BitVec.ofNat 64 o) R0 R1 X _ s₁) (k := 16) (by decide) (by decide)
    (by decide) (by decide) (fun _ _ _ _ h' g x y m rd wr => h'.keep g x y m rd wr)
    (fun n s hn h' hr => K3.round4 hk hin (j := 4 * n) (show 4 * n + 4 ≤ 16 by omega_arith) h' hr)
    (fun n s _ _ h' hr => K3.round0 hk hin h' hr) k₁ hrsi₁) fun s₂ ⟨tb₂, r₂, d₂⟩ => ?_)
  obtain hrcx₂ : s₂.gpr .rcx = bfA c := by
    rw [tb₂.gpr _ (by decide) (by decide) (by decide), gk₁ _ (by decide) (by decide), h.rcx]
  obtain hrdi₂ : s₂.gpr .rdi = stA c := by rw [d₂, hrcx₂, bf_sub64]
  have hrsi₂ : s₂.gpr .rsi = dp + BitVec.ofNat 64 o := r₂
  obtain wr₂ : s₂.wr = s.wr := by rw [tb₂.wr, wr₁]
  obtain m₂ : s₂.mem = tMem c s.mem := by rw [tb₂.mem, m₁]
  obtain hi₂ : Incs s₂.mem (bfA c) := by rw [m₂]; exact Proof.ChaCha20.X86_64.Avx2.tincs_mem _ _
  refine (WP.mono (tailBO3_ok (k := 16) (by decide) (by decide) tb₂.hb hrcx₂ hrdi₂ (by rw [wr₂]; exact h.st)
    (by rw [wr₂]; exact h.bf) (by rw [wr₂]; exact h.ps) (by rw [wr₂]; exact hkr) hi₂ tb₂.acc.h2)
    fun s₃ ⟨ks₃, acc₃, f₃, rbx₃, rbp₃, r12₃, r13₃, r14₃, r15₃, rcx₃, rsp₃, rd₃, wr₃⟩ => ?_)
  -- What the stores of `tailA3` keep in the context.
  obtain ctxk : ∀ d, 520 ≤ d → d + 8 ≤ 552 →
      s₂.mem.readW (c + BitVec.ofNat 64 d) 64 = s.mem.readW (c + BitVec.ofNat 64 d) 64 := by
    intro d h₁ h₂
    rw [m₂]
    refine (tMem_frame _).readW (r := ⟨c + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint c (Or.inr (by omega_arith)) (by omega_arith) (by decide)
  obtain hslot : s₂.mem.readW (c + BitVec.ofNat 64 544) 64 = BitVec.ofNat 64 n := by
    rw [ctxk 544 (by decide) (by decide), ← slot_eq, h.left]
  obtain S₂ : stateAt s₂.mem (stA c) = stateAt s.mem (stA c) := by
    rw [m₂]
    exact Proof.ChaCha20.X86_64.Xor.stateAt_frame (tMem_frame _) (by simpa using st_bf)
  refine ⟨fun i hi => ?_, ?_, ?_, by rw [rbx₃, hrsi₂, Offset.add_add],
    by rw [rbp₃, hslot, Offset.ofNat_sub_ofNat (by omega_arith)],
    by rw [r12₃, ctxk 520 (by decide) (by decide)], by rw [r13₃, ctxk 528 (by decide) (by decide)],
    by rw [r14₃, ctxk 536 (by decide) (by decide)], r15₃,
    by rw [rsp₃, tb₂.gpr _ (by decide) (by decide) (by decide), gk₁ _ (by decide) (by decide), h.rsp],
    by rw [rd₃, tb₂.rd, rd₁],
    by rw [wr₃, wr₂]⟩
  · rw [ks₃ i (by omega_arith), S₂, Proof.ChaCha20.X86_64.Avx2.plus_block, VG.Proof.ChaCha20.keystream_getD _ hi]
  · -- The accumulator: the first 16 blocks absorbed.
    obtain hb1 : bytesAt s₁.mem (dp + BitVec.ofNat 64 o) (16 * 16) =
        bytesAt s.mem (dp + BitVec.ofNat 64 o) (16 * 16) := by
      rw [m₁]
      refine bytesAt_frame (tMem_frame _) (fun r hr => ?_) (by omega_arith)
      simp only [List.mem_singleton] at hr; subst hr
      exact (hl.bf_d.symm.sub_left (Offset.sub_base _ (by omega_arith)))
    have v := tb₂.acc.val
    rw [hb1] at v
    rw [acc₃, v]
  · have f1 : Frame [bufR (bfA c)] s.mem s₂.mem := by rw [m₂]; exact tMem_frame _
    exact (f1.mono (by simp)).trans f₃

/-- `tailKO vl 24`, with 384 to 512 bytes left. -/
theorem tailKOg_ok (vl : Bool) {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} (hk : Key R0 R1)
    {X : Nat} {o n : Nat} {sp : Addr} (hkn : 384 ≤ n) (hhi : n ≤ 512) {s : State}
    (h : TPO c dp L o n R0 R1 X sp s) (hkr : kR (bfA c) ∈ s.wr) (hcs : Consts s.mem (bfA c)) :
    WP isa (tailKO vl 24) s (TailMidKO c dp o n 24 R0 R1 X sp s) := by
  have hLe := hl.L_lt
  have hTL := h.le
  obtain kc : kR (bfA c) = ⟨c + BitVec.ofNat 64 736, 512⟩ := by simp only [kR, kA, bfA, Offset.add_add]
  obtain dsk : (stR (stA c)).Disjoint (kR (bfA c)) := by
    rw [kc]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  obtain dbk : (bufR (bfA c)).Disjoint (kR (bfA c)) := by
    rw [kc]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  obtain dak : (accR c).Disjoint (kR (bfA c)) := by
    rw [kc]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  obtain dqs : (⟨dp + BitVec.ofNat 64 o, 16 * 24⟩ : Region).Disjoint (slotsR (bfA c)) :=
    ((hl.cd (d := 128) (n := 128) (by decide)).sub_right (Offset.sub_base _ (by omega_arith))).symm
  obtain hin : ∀ off n', off + n' ≤ 16 * 24 →
      InRegions (s.rd ++ s.wr) (dp + BitVec.ofNat 64 o + BitVec.ofNat 64 off) n' := by
    intro off n' hn
    refine ⟨_, h.dw, ?_⟩
    rw [Offset.add_add]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  unfold tailKO
  refine WP.seq (WP.mono (tailKL_ok vl (k := 24) (by decide) (by decide) (by decide) (by decide) (by decide) hk
    h.rdi h.rcx h.rsi bf_sub64 h.st h.bf hkr hin
    hcs st_bf dsk dbk dqs h.acc) fun s₂ ⟨d₂, a₂, f₂, g₂, rd₂, wr₂⟩ => ?_)
  rw [leaveTO_eq, List.append_assoc]
  refine WP.block_append (WP.mono (Proof.Poly1305.X86_64.reduce_ok s₂) fun s₃ ⟨red, k₃⟩ => ?_)
  refine WP.block_append (WP.mono (storeTO_ok (k := 24) (by decide) (c := c) (s := s₃)
    (by rw [k₃.gpr', g₂ _ (by decide), h.rcx]) (by rw [k₃.2.2.2, wr₂]; exact h.ps))
    fun s₄ ⟨m₄, rbx₄, rbp₄, r12₄, r13₄, r14₄, r15₄, g₄, rd₄, wr₄⟩ => ?_)
  refine WP.mono (Proof.ChaCha20.X86_64.Avx2.vz_ok s₄) fun s₅ ⟨g₅, m₅, rd₅, wr₅⟩ => ?_
  have m₃ : s₃.mem = s₂.mem := k₃.2.1
  obtain mA : s₅.mem = accMem s₂.mem c (s₃.gpr .r11) (s₃.gpr .rbx) (s₃.gpr .rbp) := by rw [m₅, m₄, m₃]
  obtain fa : Frame [accR c] s₂.mem s₅.mem := by rw [mA]; exact accMem_frame _ _ _ _ _
  obtain f₂' : Frame [bufR (bfA c), kR (bfA c)] s.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨bufR (bfA c), by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨kR (bfA c), by simp, fun _ h => h⟩
  obtain rd₂' : ∀ d, 520 ≤ d → d + 8 ≤ 552 →
      s₃.mem.readW (c + BitVec.ofNat 64 d) 64 = s.mem.readW (c + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [m₃]
    refine f₂'.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint c (Or.inr (by omega_arith)) (by omega_arith) (by decide)
    · rw [kc]; exact Offset.disjoint c (Or.inl (by omega_arith)) (by omega_arith) (by decide)
  obtain gs : ∀ r, r = .rsi ∨ r = .rsp → s₃.gpr r = s.gpr r := by
    intro r hr; rcases hr with rfl | rfl <;> rw [k₃.gpr', g₂ _ (by decide)]
  obtain hslot : s₃.mem.readW (c + BitVec.ofNat 64 544) 64 = BitVec.ofNat 64 n := by
    rw [rd₂' 544 (by decide) (by decide), ← slot_eq, h.left]
  refine ⟨fun i hi => ?_, ?_, (f₂'.mono (by simp)).trans (fa.mono (by simp)),
    by rw [g₅, rbx₄, gs _ (.inl rfl), h.rsi, Offset.add_add],
    by rw [g₅, rbp₄, hslot, Offset.ofNat_sub_ofNat (by omega_arith)],
    by rw [g₅, r12₄, rd₂' 520 (by decide) (by decide)], by rw [g₅, r13₄, rd₂' 528 (by decide) (by decide)],
    by rw [g₅, r14₄, rd₂' 536 (by decide) (by decide)], by rw [g₅, r15₄],
    by rw [g₅, g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), gs _ (.inr rfl), h.rsp],
    by rw [rd₅, rd₄, k₃.2.2.1, rd₂], by rw [wr₅, wr₄, k₃.2.2.2, wr₂]⟩
  · rw [fa _ (fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dak _ hc (kR_contains _ (by omega_arith))), d₂ i (by omega_arith),
      Proof.ChaCha20.X86_64.Avx2.plus_block, VG.Proof.ChaCha20.keystream_getD _ hi]
  · rw [mA, accMem_acc]
    show hval s₃ = _
    rw [red a₂.h2, a₂.val]

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
