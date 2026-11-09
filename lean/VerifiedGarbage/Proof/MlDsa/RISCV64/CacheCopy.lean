module

public import VerifiedGarbage.Impl.MlDsa.RISCV64.CacheCopy
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Base
public import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Piece
import VerifiedGarbage.Proof.MlKem.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.MlDsa.RISCV64.CacheCopy
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.KeyGen.Base
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

public import VerifiedGarbage.TCB.RISCV64.Target
/-!
# ML-DSA on RISC-V: polynomials copied from a key's cache

`cacheCopy off dst len` (`Impl/MlDsa/RISCV64/CacheCopy.lean`) moves
`s3 + off`, the pointer `dst` and `len` into `a0`–`a2` (`block_ok`), then
copies the `len` bytes (ML-KEM's `copy_loop`): what it keeps and writes
(`cacheCopy_ok`). Two runs whose stack pointers, `s3` and `dst`'s register
agree leak the same (`cacheCopy_tr`): the moves access no memory, and the
loop's addresses are `a0`, `a1` and its count `a2`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.CacheCopy

open VG VG.RISCV64 VG.RISCV64.RegUpd
open VG.Impl.MlDsa.RISCV64.KeyGen (Ptr Arg glue)
open VG.Impl.MlDsa.RISCV64.CacheCopy
open VG.Proof.MlDsa.RISCV64.KeyGen (glueOk glueSt argVal loadImm_ok glue_ok)
open VG.Spec.Sha3 (bytesAt)

/-- The moves after `a0`'s. -/
abbrev cArgs (dst : Ptr) (len : Nat) : List (Reg × Arg) := [(.a1, .ptr dst), (.a2, .imm len)]

/-- The copy's loop, from its pointers and count. -/
theorem loop_tr : RelCT isa (fun (x y : State) => x.sp = y.sp ∧ ∀ r ∈ [Reg.a0, .a1, .a2], x.gpr r = y.gpr r)
    (.loop (.block Impl.MlKem.RISCV64.copyBody) (.nonzero .a2)) fun _ _ => True :=
  RelCT.taint (A := VG.RISCV64.taint) (Taint.ofRegs [.a0, .a1, .a2])
    (fun x y h => ⟨h.1, fun r hr => h.2 r (Taint.mem_ofRegs.mp hr)⟩) (by taint_decide)

section
variable {off len : Nat} {dst : Ptr} (ho : off < 2 ^ 31 - 2048) (hg : glueOk (cArgs dst len) = true)
include ho hg

theorem block_ok (s : State) :
    WP isa (.block (Arg.instrs .a0 (.ptr (.s3, off)) ++ glue (cArgs dst len))) s fun u =>
      u.gpr .a0 = s.gpr .s3 + BitVec.ofNat 64 off ∧ u.gpr .a1 = s.gpr dst.1 + BitVec.ofNat 64 dst.2 ∧
      u.gpr .a2 = BitVec.ofNat 64 len ∧ (∀ r ∈ preserved, u.gpr r = s.gpr r) ∧ u.mem = s.mem ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
  have hd : dst.1 ≠ .a0 := by
    simp only [glueOk, List.all_cons, Bool.and_eq_true, KeyGen.argOk, Bool.or_eq_true, beq_iff_eq] at hg
    rcases hg.1.2.1 with ((h | h) | h) | h <;> rw [h] <;> decide
  rw [WP.block_append_iff, Arg.instrs, WP.block_append_iff]
  refine WP.mono (loadImm_ok .a0 ho s) fun s₁ e₁ => ?_
  subst e₁
  refine Steps.WP.cons exec_add (WP.block_nil ?_)
  refine WP.mono (glue_ok hg _) fun u e => ?_
  subst e
  simp only [glueSt, argVal]
  refine ⟨?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · rw [gpr_write_of_ne _ _ (by decide), gpr_write_of_ne _ _ (by decide), gpr_write_self,
      gpr_write_of_ne _ _ (by decide), gpr_write_self, BitVec.add_comm]
  · rw [gpr_write_of_ne _ _ (by decide), gpr_write_self, gpr_write_of_ne _ _ hd, gpr_write_of_ne _ _ hd]
  · rw [gpr_write_self]
  · obtain ⟨-, n1, n2, n3, -, -⟩ := Proof.MlKem.RISCV64.pres_ne hr
    rw [gpr_write_of_ne _ _ n3, gpr_write_of_ne _ _ n2, gpr_write_of_ne _ _ n1, gpr_write_of_ne _ _ n1]

/-- The copy: the `len` bytes at `s3 + off` at `dst`, which only they change. -/
theorem cacheCopy_ok (hl : len < 2 ^ 64) (hl0 : 0 < len) {s : State}
    (hd : Region.Disjoint ⟨s.gpr .s3 + BitVec.ofNat 64 off, len⟩ ⟨s.gpr dst.1 + BitVec.ofNat 64 dst.2, len⟩)
    (cr : Covers [⟨s.gpr .s3 + BitVec.ofNat 64 off, len⟩] (s.rd ++ s.wr))
    (cw : Covers [⟨s.gpr dst.1 + BitVec.ofNat 64 dst.2, len⟩] s.wr) :
    WP isa (cacheCopy off dst len) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨s.gpr dst.1 + BitVec.ofNat 64 dst.2, len⟩] s.mem s'.mem ∧
      bytesAt s'.mem (s.gpr dst.1 + BitVec.ofNat 64 dst.2) len =
        bytesAt s.mem (s.gpr .s3 + BitVec.ofNat 64 off) len := by
  unfold cacheCopy
  refine WP.seq (WP.mono (block_ok ho hg s) fun u ⟨g0, g1, g2, cs, m, rd, wr, sp⟩ => ?_)
  refine WP.mono (Proof.MlKem.RISCV64.copy_loop hl hl0 hd (by rw [rd, wr]; exact cr) (by rw [wr]; exact cw) g0 g1 g2)
    fun s' ⟨cs', rd', wr', sp', fr, hb⟩ => ⟨fun r hr => (cs' r hr).trans (cs r hr), rd'.trans rd, wr'.trans wr,
      sp'.trans sp, by rw [← m]; exact fr, by rw [hb, m]⟩

/-- Two runs that agree on the stack pointer, `s3` and `dst`'s register leak the same. -/
theorem cacheCopy_tr {P : State → State → Prop}
    (hP : ∀ x y, P x y → x.sp = y.sp ∧ x.gpr .s3 = y.gpr .s3 ∧ x.gpr dst.1 = y.gpr dst.1) :
    RelCT isa P (cacheCopy off dst len) fun _ _ => True := by
  unfold cacheCopy
  have hm : (Arg.instrs .a0 (.ptr (.s3, off)) ++ glue (cArgs dst len)).all Pack.noMem = true := by
    rw [List.all_append, KeyGen.glue_noMem, Bool.and_true]; rfl
  refine RelCT.seq (R := fun (x y : State) => x.sp = y.sp ∧ ∀ r ∈ [Reg.a0, .a1, .a2], x.gpr r = y.gpr r) ?_
    loop_tr
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := Pack.relct_noMem (P := P) hm s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨_, u₁, f₁, g₁⟩ := block_ok ho hg s₁
  obtain ⟨_, u₂, f₂, g₂⟩ := block_ok ho hg s₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  obtain ⟨hsp, h3, hb⟩ := hP _ _ hp
  refine ⟨ht, by rw [g₁.2.2.2.2.2.2.2, g₂.2.2.2.2.2.2.2, hsp], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [g₁.1, g₂.1, h3]
  · rw [g₁.2.1, g₂.2.1, hb]
  · rw [g₁.2.2.1, g₂.2.2.1]

end

/-! ## Copies between pointers of the layout -/

section
variable {src dst : Ptr} {len : Nat} (hg : glueOk [(.a0, .ptr src), (.a1, .ptr dst), (.a2, .imm len)] = true)
include hg

theorem copyN_ok (hl0 : 0 < len) {s : State}
    (hd : Region.Disjoint ⟨s.gpr src.1 + BitVec.ofNat 64 src.2, len⟩ ⟨s.gpr dst.1 + BitVec.ofNat 64 dst.2, len⟩)
    (cr : Covers [⟨s.gpr src.1 + BitVec.ofNat 64 src.2, len⟩] (s.rd ++ s.wr))
    (cw : Covers [⟨s.gpr dst.1 + BitVec.ofNat 64 dst.2, len⟩] s.wr) :
    WP isa (copyN src dst len) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨s.gpr dst.1 + BitVec.ofNat 64 dst.2, len⟩] s.mem s'.mem ∧
      bytesAt s'.mem (s.gpr dst.1 + BitVec.ofNat 64 dst.2) len =
        bytesAt s.mem (s.gpr src.1 + BitVec.ofNat 64 src.2) len := by
  have hlen : len < 2 ^ 31 - 2048 := by
    simp only [glueOk, List.all_cons, List.all_nil, Bool.and_eq_true, KeyGen.argOk, decide_eq_true_eq] at hg
    exact hg.2.2.1.2
  unfold copyN
  refine WP.seq (WP.mono (glue_ok hg s) fun u e => ?_)
  subst e
  have g0 : (glueSt s [(.a0, .ptr src), (.a1, .ptr dst), (.a2, .imm len)]).gpr .a0 =
      s.gpr src.1 + BitVec.ofNat 64 src.2 :=
    KeyGen.glueSt_arg (d := .a0) (a := .ptr src) s hg (by simp) (by simp)
  have g1 : (glueSt s [(.a0, .ptr src), (.a1, .ptr dst), (.a2, .imm len)]).gpr .a1 =
      s.gpr dst.1 + BitVec.ofNat 64 dst.2 :=
    KeyGen.glueSt_arg (d := .a1) (a := .ptr dst) s hg (by simp) (by simp)
  have g2 : (glueSt s [(.a0, .ptr src), (.a1, .ptr dst), (.a2, .imm len)]).gpr .a2 = BitVec.ofNat 64 len :=
    KeyGen.glueSt_arg (d := .a2) (a := .imm len) s hg (by simp) (by simp)
  refine WP.mono (Proof.MlKem.RISCV64.copy_loop (by omega) hl0 hd
    (by rw [KeyGen.glueSt_rd, KeyGen.glueSt_wr]; exact cr) (by rw [KeyGen.glueSt_wr]; exact cw) g0 g1 g2)
    fun s' ⟨cs, rd, wr, sp, fr, hb⟩ => ⟨fun r hr => (cs r hr).trans (KeyGen.glueSt_pres s hg r hr),
      rd.trans (KeyGen.glueSt_rd _ _), wr.trans (KeyGen.glueSt_wr _ _), sp.trans (KeyGen.glueSt_sp _ _),
      by rw [← KeyGen.glueSt_mem s [(.a0, .ptr src), (.a1, .ptr dst), (.a2, .imm len)]]; exact fr,
      by rw [hb, KeyGen.glueSt_mem]⟩

/-- Two runs that agree on the stack pointer and the pointers' registers leak the same. -/
theorem copyN_tr {P : State → State → Prop}
    (hP : ∀ x y, P x y → x.sp = y.sp ∧ x.gpr src.1 = y.gpr src.1 ∧ x.gpr dst.1 = y.gpr dst.1) :
    RelCT isa P (copyN src dst len) fun _ _ => True := by
  unfold copyN
  refine RelCT.seq (R := fun (x y : State) => x.sp = y.sp ∧ ∀ r ∈ [Reg.a0, .a1, .a2], x.gpr r = y.gpr r) ?_
    loop_tr
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := Pack.relct_noMem (P := P) (KeyGen.glue_noMem _) s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨_, u₁, f₁, g₁⟩ := glue_ok hg s₁
  obtain ⟨_, u₂, f₂, g₂⟩ := glue_ok hg s₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  subst g₁ g₂
  obtain ⟨hsp, hs, hd⟩ := hP _ _ hp
  refine ⟨ht, by rw [KeyGen.glueSt_sp, KeyGen.glueSt_sp, hsp], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [KeyGen.glueSt_arg (d := .a0) (a := .ptr src) _ hg (by simp) (by simp),
      KeyGen.glueSt_arg (d := .a0) (a := .ptr src) _ hg (by simp) (by simp)]
    simp only [argVal, hs]
  · rw [KeyGen.glueSt_arg (d := .a1) (a := .ptr dst) _ hg (by simp) (by simp),
      KeyGen.glueSt_arg (d := .a1) (a := .ptr dst) _ hg (by simp) (by simp)]
    simp only [argVal, hd]
  · rw [KeyGen.glueSt_arg (d := .a2) (a := .imm len) _ hg (by simp) (by simp),
      KeyGen.glueSt_arg (d := .a2) (a := .imm len) _ hg (by simp) (by simp)]
    rfl

end

/-- The selection of the cache pointer `a` by its length `b`, without a branch. -/
theorem sel_eq (a b : BitVec 64) :
    (a &&& (0#64 - if 0#64 < b then 1#64 else 0#64)) = if b = 0 then 0 else a := by
  by_cases h : b = 0
  · subst h; simp
  · have : (0#64 : BitVec 64) < b := by
      rw [BitVec.lt_def]; have := (BitVec.toNat_ne_iff_ne).mpr h; simp at this ⊢; omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_left_of_eq_true _ _ (eq_true this), show (0#64 : BitVec 64) - 1#64 = BitVec.allOnes 64 from rfl, BitVec.and_allOnes]

/-- A branch on `s3`, which the runs agree on, of the pieces of a function. -/
theorem pieceIte {Pre : State → Prop} {Pub : State → State → Prop} {I J : State → State → Prop}
    (hI : ∀ σ₁ σ₂ x y, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → I σ₁ x → I σ₂ y → x.gpr .s3 = y.gpr .s3) {c₁ c₂ : Prog isa}
    (h₁ : KeyGen.Piece Pre Pub (fun σ s => I σ s ∧ s.gpr .s3 ≠ 0) J c₁)
    (h₂ : KeyGen.Piece Pre Pub (fun σ s => I σ s ∧ s.gpr .s3 = 0) J c₂) :
    KeyGen.Piece Pre Pub I J (.ite (.nonzero .s3) c₁ c₂) := by
  refine ⟨fun σ s hp h => WP.ite _ (Steps.eval_nonzero s .s3) (fun hb => h₁.ok σ s hp ⟨h, by simpa using hb⟩)
    fun hb => h₂.ok σ s hp ⟨h, by simpa using hb⟩, ?_⟩
  have e3 : ∀ x y, KeyGen.Rel2 Pre Pub I x y → x.gpr .s3 = y.gpr .s3 :=
    fun x y ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ => hI σ₁ σ₂ x y p₁ p₂ pub i₁ i₂
  refine RelCT.ite (fun x y h => by rw [Steps.eval_nonzero, Steps.eval_nonzero, e3 x y h]) ?_ ?_
  · refine RelCT.mono h₁.tr (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩, hb⟩ => ?_) fun _ _ h => h
    have ex := e3 x y ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩
    rw [Steps.eval_nonzero] at hb
    have hx : x.gpr .s3 ≠ 0 := by simpa using hb
    exact ⟨σ₁, σ₂, p₁, p₂, pub, ⟨i₁, hx⟩, i₂, by rw [← ex]; exact hx⟩
  · refine RelCT.mono h₂.tr (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩, hb⟩ => ?_) fun _ _ h => h
    have ex := e3 x y ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩
    rw [Steps.eval_nonzero] at hb
    have hx : x.gpr .s3 = 0 := by simpa using hb
    exact ⟨σ₁, σ₂, p₁, p₂, pub, ⟨i₁, hx⟩, i₂, by rw [← ex]; exact hx⟩

end VG.Proof.MlDsa.RISCV64.CacheCopy
