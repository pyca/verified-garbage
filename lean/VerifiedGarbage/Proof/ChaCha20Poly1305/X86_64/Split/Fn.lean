module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Split.Head
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Split.Correct
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.LitSplit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic


/-!
# ChaCha20-Poly1305 with the data's first bytes from `src`, x86-64: the function

`sealSplitFor` is `head` (`Head.lean`), then `seal`'s body in a frame laid
out as `seal`'s entry (`framed`): it runs inline, from its contract, with
the state's permissions narrowed to `seal`'s regions (`WP.inlineF`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Split

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.SealSplit
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.Poly1305 (bytesAt)

theorem sealSplitBody_spSafe (b : Impl.Poly1305.X86_64.Blocks) (hb : b = .avx512 ∨ b = .ifma) :
    (sealSplitBody b).all (fun i => !isa.writesSp i) = true := by
  rcases hb with rfl | rfl <;> lit_decide

theorem xorSplit_xdepth : Impl.ChaCha20.X86_64.Avx512.xorSplit.x86_64Depth ≤ 24 := by
  rw [x86_64Depth_noSp xorSplit_nosp]; have := xorSplit_depth; omega

theorem sealSplitBody_xdepth (b : Impl.Poly1305.X86_64.Blocks) : (sealSplitBody b).x86_64Depth ≤ 24 := by
  have hx : Impl.ChaCha20.X86_64.Callee.avx512.code.x86_64Depth ≤ 16 := Proof.ChaCha20.X86_64.XorImpl.avx512.xdepth
  have hb := blocks_xdepth b
  have hs := xorSplit_xdepth
  simp only [sealSplitBody, prologue, prologueA, prologueB, foldM, zeroKs, macPad, macPadLengths, wholeBlocks,
    padTail, cryptSplit, cryptBigSplit, cryptPre, absorbLengths, finalizeTag, finalizeWith, Code.x86_64Depth,
    xorBuf_xdepth, splitM_xdepth, init_xdepth, finalize_xdepth, Nat.max_le] at hx ⊢
  omega

/-! ## The frame -/

/-- The bottom of the 64 bytes of stack below `rsp` that the frame and
`seal`'s calls use. -/
abbrev fB (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 64

/-- The registers the frame pushes. -/
abbrev frameRegs : List Reg := [.r9, .r8, .r10, .r11, .rax]

theorem add_ofNat_sub_ofNat' (B : Addr) {a b : Nat} (h : b ≤ a) :
    B + BitVec.ofNat 64 a - BitVec.ofNat 64 b = B + BitVec.ofNat 64 (a - b) := by
  rw [← Offset.ofNat_sub_ofNat h, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem stk_sub (s : State) {d n : Nat} (h : d + n ≤ 64) :
    Region.Sub ⟨fB s + BitVec.ofNat 64 d, n⟩ (estkR s) :=
  Offset.sub_base _ h

theorem rsp_eq (s : State) : s.gpr .rsp = fB s + BitVec.ofNat 64 64 := (BitVec.sub_add_cancel _ _).symm

namespace FPre

variable {s : State} (hs : FPre s)
include hs

theorem fB_lt : (fB s).toNat + 104 ≤ 2 ^ 64 := by
  have := hs.sp_lo; have := hs.sp_hi
  rw [toNat_sub_ofNat (by omega)]; omega

omit hs in
/-- A part of the 64 bytes of stack is apart from a region apart from all of
them. -/
theorem stk_disj {r : Region} (h : (estkR s).Disjoint r) {d n : Nat} (hd : d + n ≤ 64) :
    (⟨fB s + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r :=
  h.sub_left (stk_sub s hd)

/-- The return address, at `fB + 64`, is apart from the stack below it. -/
theorem ret_stk {d n : Nat} (hd : d + n ≤ 64) :
    (eretR s).Disjoint ⟨fB s + BitVec.ofNat 64 d, n⟩ := by
  have := hs.fB_lt
  show (⟨s.gpr .rsp, 8⟩ : Region).Disjoint _
  rw [rsp_eq s]; exact Offset.disjoint _ (.inr hd) (by omega) (by omega)

end FPre

/-- The state `seal`'s body starts in: after the frame's push and
`dataArgs`. -/
structure Body (whole : Bool) (s u : State) : Prop where
  rdi : u.gpr .rdi = s.gpr .rdi
  rsi : u.gpr .rsi = s.gpr .rsi
  rdx : u.gpr .rdx = s.gpr .rdx
  rcx : u.gpr .rcx = s.gpr .rcx
  r8 : u.gpr .r8 = eDst s
  r9 : u.gpr .r9 = stackArg s 1
  rsp : u.gpr .rsp = fB s + BitVec.ofNat 64 24
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → u.gpr r = s.gpr r
  a0 : u.mem.readW (fB s + BitVec.ofNat 64 32) 64 = eTg s
  a1 : u.mem.readW (fB s + BitVec.ofNat 64 40) 64 = eW s
  a2 : u.mem.readW (fB s + BitVec.ofNat 64 48) 64 = eSrc s
  a3 : u.mem.readW (fB s + BitVec.ofNat 64 56) 64 = s.gpr .r9
  mem : Frame [⟨fB s + BitVec.ofNat 64 24, 40⟩] (headM s (cntOf s whole)) u.mem
  rd : u.rd = s.rd
  wr : u.wr = ⟨fB s + BitVec.ofNat 64 24, 40⟩ :: s.wr
  mx : u.mxcsr = s.mxcsr

theorem argR_eq (s : State) : eargR s = ⟨fB s + BitVec.ofNat 64 72, 32⟩ := by
  show (⟨s.gpr .rsp + BitVec.ofNat 64 (8 * (0 + 1)), 32⟩ : Region) = _
  rw [rsp_eq s, Offset.add_ofNat_add_ofNat]

theorem arg_addr (s : State) (j : Nat) :
    off (s.gpr .rsp) (8 * (j + 1)) = fB s + BitVec.ofNat 64 (64 + 8 * (j + 1)) := by
  rw [off_eq, rsp_eq s, Offset.add_ofNat_add_ofNat]

theorem pushed_rsp' {s h : State} (hsp : h.gpr .rsp = s.gpr .rsp) :
    (pushed frameRegs h).gpr .rsp = fB s + BitVec.ofNat 64 24 := by
  rw [pushed_rsp, hsp, rsp_eq s, add_ofNat_sub_ofNat' _ (by decide)]; rfl

/-- `dataArgs`, after the push. -/
theorem body_ok {whole : Bool} {s h : State} (hs : FPre s) (hh : Headed whole s h) :
    WP isa (.block dataArgs) (pushed frameRegs h) (Body whole s) := by
  have hsp : h.gpr .rsp = s.gpr .rsp :=
    hh.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hB := hs.fB_lt
  have hn : 8 * frameRegs.length ≤ (h.gpr .rsp).toNat := by rw [hsp]; have := hs.sp_lo; simp; omega
  obtain ⟨pf, pw⟩ := pushRegs_mem h frameRegs (by decide) hn
  rw [hsp, rsp_eq s, add_ofNat_sub_ofNat' _ (by decide)] at pf
  rw [hsp, rsp_eq s] at pw
  replace pf : Frame [⟨fB s + BitVec.ofNat 64 24, 40⟩] h.mem (pushed frameRegs h).mem := pf
  have pw' : ∀ j (hj : j < 5) (d : Nat), d + 8 * (j + 1) = 64 →
      (pushed frameRegs h).mem.readW (fB s + BitVec.ofNat 64 d) 64 = h.gpr frameRegs[j] := by
    intro j hj d hd
    have := pw j hj
    rw [add_ofNat_sub_ofNat' _ (by omega), show 64 - 8 * (j + 1) = d by omega] at this
    exact this
  have fH := hs.headM_frame (cntOf s whole) (FPre.cnt_le whole)
  have sp' := pushed_rsp' hsp
  have ga : ∀ r, r ≠ .rsp → (pushed frameRegs h).gpr r = h.gpr r := fun r hr => pushed_gpr _ _ hr
  have a16 : off (fB s + BitVec.ofNat 64 24) 56 = off (s.gpr .rsp) (8 * (1 + 1)) := by
    rw [arg_addr s, off_eq, Offset.add_ofNat_add_ofNat]
  have r₅₆ : InRegions ((pushed frameRegs h).rd ++ (pushed frameRegs h).wr) (off (fB s + BitVec.ofNat 64 24) 56) 8 := by
    rw [pushed_rd, hh.rd, a16]
    exact ⟨eargR s, List.mem_append_left _ (by rw [hs.rd]; simp), FPre.arg_contains (j := 1) (by decide)⟩
  have v₅₆ : (pushed frameRegs h).mem.readW (off (fB s + BitVec.ofNat 64 24) 56) 64 = stackArg s 1 := by
    rw [a16, pf.readW (r := eargR s) (w := 64) (FPre.arg_contains (j := 1) (by decide)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [argR_eq s]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) (by decide),
      hh.mem]
    exact hs.arg_eq fH (j := 1) (by decide)
  apply WP.of_runBlock
  simp only [dataArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_at, sp',
    r₅₆, v₅₆, ↓reduceIte, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, mxcsr_setReg, reduceCtorEq,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr hr' => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [gpr_setReg, mem_setReg, rd_setReg, wr_setReg, mxcsr_setReg, reduceCtorEq, ↓reduceIte]
  · rw [ga _ (by decide), hh.rdi]
  · rw [ga _ (by decide), hh.rsi]
  · rw [ga _ (by decide)]
    exact hh.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [ga _ (by decide), hh.rcx]
  · rw [ga _ (by decide), hh.rax]
  · exact sp'
  · have h₁ : r ≠ .r8 := by rintro rfl; simp [calleeSaved] at hr
    have h₂ : r ≠ .r9 := by rintro rfl; simp [calleeSaved] at hr
    simp only [h₁, h₂, ↓reduceIte, ga r hr']
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    exact hh.keep r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) h₁
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  · rw [pw' 3 (by decide) 32 (by decide)]; exact hh.r11
  · rw [pw' 2 (by decide) 40 (by decide)]; exact hh.r10
  · rw [pw' 1 (by decide) 48 (by decide)]; exact hh.r8
  · rw [pw' 0 (by decide) 56 (by decide)]
    exact hh.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [← hh.mem]; exact pf
  · rw [pushed_rd, hh.rd]
  · rw [pushed_wr, hsp, rsp_eq s, add_ofNat_sub_ofNat' _ (show 8 * frameRegs.length ≤ 64 by decide), hh.wr]
    rfl
  · rw [pushed_mxcsr, hh.mx]

/-! ## `seal`'s precondition, narrowed -/

theorem stackArg_wr (s : State) (rd wr : List Region) (j : Nat) :
    stackArg (s.withRegions rd wr) j = stackArg s j := rfl
theorem stackArgAddr_wr (s : State) (rd wr : List Region) (j : Nat) :
    stackArgAddr (s.withRegions rd wr) j = stackArgAddr s j := rfl

/-- What `seal` may read and write, narrowed from the frame's state. -/
abbrev rdB (u : State) : List Region := [kR u, nR u, aR u, argR u]
abbrev wrB (u : State) : List Region := [dR u, tR u, ctxR u]

theorem FPre.stk0 {s : State} {r : Region} (h : (estkR s).Disjoint r) {n : Nat} (hn : n ≤ 64) :
    (⟨fB s, n⟩ : Region).Disjoint r :=
  h.sub_left (Region.sub_prefix hn)

theorem sub24 (B : Addr) : B + BitVec.ofNat 64 24 - 24 = B := BitVec.add_sub_cancel _ _

namespace Body

variable {whole : Bool} {s u : State} (hs : FPre s) (hb : Body whole s u)
include hb

theorem addr (j : Nat) : stackArgAddr u j = fB s + BitVec.ofNat 64 (24 + 8 * (j + 1)) := by
  show u.gpr .rsp + _ = _
  rw [hb.rsp, Offset.add_ofNat_add_ofNat]

theorem arg0 : stackArg u 0 = eTg s := by
  show u.mem.readW (stackArgAddr u 0) 64 = _; rw [hb.addr]; exact hb.a0
theorem arg1 : stackArg u 1 = eW s := by
  show u.mem.readW (stackArgAddr u 1) 64 = _; rw [hb.addr]; exact hb.a1
theorem arg2 : stackArg u 2 = eSrc s := by
  show u.mem.readW (stackArgAddr u 2) 64 = _; rw [hb.addr]; exact hb.a2
theorem arg3 : stackArg u 3 = s.gpr .r9 := by
  show u.mem.readW (stackArgAddr u 3) 64 = _; rw [hb.addr]; exact hb.a3

include hs

/-- `seal`'s precondition, narrowed. -/
theorem pre : preX86_64 true (u.withRegions (rdB u) (wrB u)) := by
  have e0 := hb.arg0
  have e1 := hb.arg1
  have eA := hb.addr 0
  simp only [preX86_64, stackArg_wr, stackArgAddr_wr, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, ite_true, kR, nR, aR, argR, dR, tR, ctxR, kp, np, ad, AL, dp, L, tp, cx, e0, e1, eA,
    hb.rdi, hb.rsi, hb.rdx, hb.rcx, hb.r8, hb.r9, hb.rsp, true_and, sub24, rdB, wrB,
    Nat.reduceAdd, Nat.reduceMul]
  refine ⟨hs.k_w.symm, hs.n_w.symm, hs.a_w.symm, hs.d_w.symm, hs.t_w.symm,
    (FPre.stk_disj hs.b_w (d := 32) (n := 16) (by decide)).symm, hs.k_d.symm, hs.n_d.symm, hs.a_d.symm, hs.d_t,
    (FPre.stk_disj hs.b_d (d := 32) (n := 16) (by decide)).symm,
    FPre.stk_disj hs.b_w (d := 24) (n := 8) (by decide), FPre.stk_disj hs.b_a (d := 24) (n := 8) (by decide),
    FPre.stk_disj hs.b_d (d := 24) (n := 8) (by decide), FPre.stk_disj hs.b_t (d := 24) (n := 8) (by decide),
    FPre.stk0 hs.b_w (by decide), FPre.stk0 hs.b_k (by decide), FPre.stk0 hs.b_n (by decide),
    FPre.stk0 hs.b_a (by decide), FPre.stk0 hs.b_d (by decide), FPre.stk0 hs.b_t (by decide),
    hs.o_w, hs.o_a, hs.o_d, hs.o_t, hs.o_k, hs.o_n⟩

end Body

/-- `APre` of a state that may read more. -/
theorem APre.of_more {e : Bool} {u : State} {rd wr more : List Region} (h : preX86_64 e (u.withRegions rd wr)) :
    APre e (u.withRegions (rd ++ more) wr) := by
  have h' := APre.of _ h
  obtain ⟨m', hm'⟩ := h'.rd
  have hrd : rd = (if e then [kR u, nR u, aR u, argR u] else [kR u, nR u, aR u, tR u, argR u]) ++ m' := hm'
  exact { h' with rd := ⟨m' ++ more, by simp only [State.withRegions_rd, hrd, List.append_assoc]; rfl⟩ }

/-- `sealSplitBody`'s precondition, narrowed. -/
theorem Body.spre {whole : Bool} {s u : State} (hs : FPre s) (hb : Body whole s u) :
    SPre (u.withRegions (rdB u ++ [arg2R u, spR u]) (wrB u)) := by
  have hp := APre.of_more (more := [arg2R u, spR u]) (hb.pre hs)
  have e1 := hb.arg1
  have e2 := hb.arg2
  have e3 := hb.arg3
  have eA := hb.addr 2
  have hB := hs.fB_lt
  refine ⟨hp, List.mem_append_right _ (List.mem_cons_self ..),
    List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [SL, L, spR, sp, arg2R, ctxR, dR, tR, stkR, cx, dp, tp, stackArg_wr, stackArgAddr_wr,
      State.withRegions_gpr, e1, e2, e3, eA, hb.r8, hb.r9, hb.rsp, hb.arg0, sub24, below, BitVec.add_sub_cancel, Nat.reduceAdd,
      Nat.reduceMul]
  · exact hs.le
  · exact hs.s_w
  · exact hs.s_d
  · exact (FPre.stk0 hs.b_s (by decide)).symm
  · exact FPre.stk_disj hs.b_w (d := 48) (n := 16) (by decide)
  · exact FPre.stk_disj hs.b_d (d := 48) (n := 16) (by decide)
  · exact FPre.stk_disj hs.b_t (d := 48) (n := 16) (by decide)
  · exact Offset.disjoint_base _ (by decide) (by decide)
  · exact hs.o_s

/-! ## The regions, within the frame's -/

namespace Body

variable {whole : Bool} {s u : State} (hb : Body whole s u)
include hb

/-- A part of the frame's words. -/
theorem in_frame {d n : Nat} (h : 24 ≤ d) (h' : d + n ≤ 64) :
    Covers [⟨fB s + BitVec.ofNat 64 d, n⟩] (u.rd ++ u.wr) :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨fB s + BitVec.ofNat 64 24, 40⟩, List.mem_append_right _ (by rw [hb.wr]; simp), d - 24,
      by simp only; rw [Offset.add_ofNat_add_ofNat, Nat.add_sub_cancel' h], by simp only; omega⟩

theorem rdB_cov (hs : FPre s) : Covers (rdB u) (u.rd ++ u.wr) := by
  have eA := hb.addr 0
  refine Covers.cons (Covers.of_mem ?_) (Covers.cons (Covers.of_mem ?_) (Covers.cons (Covers.of_mem ?_)
    (Covers.cons ?_ Covers.nil)))
  · intro r hr; simp only [List.mem_singleton] at hr; subst hr
    refine List.mem_append_left _ ?_
    show (⟨u.gpr .rdi, 32⟩ : Region) ∈ _; rw [hb.rd, hb.rdi, hs.rd]; simp
  · intro r hr; simp only [List.mem_singleton] at hr; subst hr
    refine List.mem_append_left _ ?_
    show (⟨u.gpr .rsi, 12⟩ : Region) ∈ _; rw [hb.rd, hb.rsi, hs.rd]; simp
  · intro r hr; simp only [List.mem_singleton] at hr; subst hr
    refine List.mem_append_left _ ?_
    show (⟨u.gpr .rdx, (u.gpr .rcx).toNat⟩ : Region) ∈ _; rw [hb.rd, hb.rdx, hb.rcx, hs.rd]; simp
  · show Covers [⟨stackArgAddr u 0, 16⟩] _
    rw [eA]; exact hb.in_frame (by decide) (by decide)

theorem more_cov (hs : FPre s) : Covers [arg2R u, spR u] (u.rd ++ u.wr) := by
  have eA := hb.addr 2
  refine Covers.cons ?_ (Covers.cons (Covers.of_mem ?_) Covers.nil)
  · show Covers [⟨stackArgAddr u 2, 16⟩] _
    rw [eA]; exact hb.in_frame (by decide) (by decide)
  · intro r hr; simp only [List.mem_singleton] at hr; subst hr
    refine List.mem_append_left _ ?_
    show (⟨stackArg u 2, (stackArg u 3).toNat⟩ : Region) ∈ u.rd
    rw [hb.rd, hb.arg2, hb.arg3, hs.rd]; simp

theorem wrB_cov (hs : FPre s) : Covers (wrB u) u.wr := by
  refine Covers.of_mem fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [hb.wr, hs.wr]
  rcases hr with rfl | rfl | rfl
  · show (⟨u.gpr .r8, (u.gpr .r9).toNat⟩ : Region) ∈ _; rw [hb.r8, hb.r9]; simp
  · show (⟨stackArg u 0, 16⟩ : Region) ∈ _; rw [hb.arg0]; simp
  · show (⟨stackArg u 1, 1696⟩ : Region) ∈ _; rw [hb.arg1]; simp

end Body

/-! ## The frame around `seal`'s body -/

/-- `framed c`, for verified code `c` that writes `rsp` only in its frames'
pushes and pops and uses at most 24 bytes of stack below `rsp`, run from
`seal`'s entry state in the frame with its permissions narrowed to `seal`'s
regions and `more`. -/
theorem framed_ok {whole : Bool} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : SpSafe c) (hd : c.x86_64Depth ≤ 24) (more : State → List Region)
    {s h : State} (hs : FPre s) (hh : Headed whole s h)
    (hpre : ∀ u, Body whole s u → k.pre (u.withRegions (rdB u ++ more u) (wrB u)))
    (hmore : ∀ u, Body whole s u → Covers (more u) (u.rd ++ u.wr)) :
    WP isa (framed c) h fun z => ∃ u s₂ : State, Body whole s u ∧
      k.post (u.withRegions (rdB u ++ more u) (wrB u)) (s₂.withRegions (rdB u ++ more u) (wrB u)) ∧
      z.mem = s₂.mem ∧ Frame (wrB u ++ [below (u.gpr .rsp) 24]) u.mem s₂.mem ∧
      (∀ r ∈ calleeSaved, z.gpr r = s.gpr r) ∧ z.rd = s.rd ∧ z.wr = s.wr ∧
      z.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  have hsp' : h.gpr .rsp = s.gpr .rsp :=
    hh.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hB := hs.fB_lt
  have hn : 8 * frameRegs.length ≤ (h.gpr .rsp).toNat := by rw [hsp']; have := hs.sp_lo; simp; omega
  refine WP.frame (by decide) (by decide) (by decide) hn ?_
  refine WP.seq (WP.mono (body_ok hs hh) fun u hu => ?_)
  refine WP.inlineF hv hsp (by omega) (hpre u hu)
    (Covers.append_left (Covers.append_left (hu.rdB_cov hs) (hmore u hu)) (hu.wrB_cov hs).right)
    (hu.wrB_cov hs)
    fun s₂ rd₂ wr₂ ab₂ f₂ _ post₂ => ?_
  have rsp₂ : s₂.gpr .rsp = u.gpr .rsp := ab₂.1 _ calleeSaved_rsp
  have pw : (pushed frameRegs h).wr = ⟨fB s + BitVec.ofNat 64 24, 40⟩ :: s.wr := by
    rw [pushed_wr, hsp', rsp_eq s, add_ofNat_sub_ofNat' _ (show 8 * frameRegs.length ≤ 64 by decide), hh.wr]
    rfl
  refine ⟨by rw [rsp₂, hu.rsp, pushed_rsp' hsp'], by rw [wr₂, hu.wr, pw], u, s₂, hu, post₂, popped_mem _ _ _,
    Frame.below_mono f₂ hd (by decide), fun r hr => ?_, by rw [popped_rd, rd₂, hu.rd],
    by rw [popped_wr, wr₂, hu.wr]; rfl, by rw [popped_mxcsr, ab₂.2.2, hu.mx]⟩
  by_cases hr' : r = .rsp
  · subst hr'
    rw [popped_rsp, rsp₂, hu.rsp, Offset.add_ofNat_add_ofNat, rsp_eq s]; rfl
  · have hra : r ≠ .rax := by rintro rfl; simp [calleeSaved] at hr
    rw [popped_gpr _ _ _ hr' hra, ab₂.1 r hr, hu.cs r hr hr']

end VG.Proof.ChaCha20Poly1305.X86_64.Split
