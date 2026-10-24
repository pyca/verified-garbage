module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.CallFacts
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.ReadOnly
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Search
public import VerifiedGarbage.Proof.Ffdh.ControlMemory
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Writes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Live
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Entry

/-! # The attempt's arguments (AArch64) -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.Control (writeController writeController_word writeController_frame_size
  controllerValue)
open VG.Impl.Ffdh.AArch64.KeyGeneration.Search (ldf stf terminal zeroOut zeroOutputs exhausted advance rejectedScalar rejectedPublic test classify request room entry arguments finish)
open VG.Impl.Ffdh.AArch64.Cached.Search

/-- The attempt's stack arguments: `rand_len` (`p_len`), `scratch` and
`scratch_len`. -/
def callValues (p : KeyPublic) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 p.len), (1, p.B), (2, BitVec.ofNat 64 (p.Z / 8)),(3,p.ctx),(4,BitVec.ofNat 64 p.ctxLen)]

theorem callValues_bound (p : KeyPublic) : ∀ e ∈ callValues p, e.1 < 16 := by
  simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

/-- The attempt's register arguments. -/
def KeyArgs (p : KeyPublic) (used : Nat) (t : State) : Prop :=
  t.gpr .x0 = p.xp ∧ t.gpr .x1 = BitVec.ofNat 64 p.len ∧ t.gpr .x2 = p.yp ∧
  t.gpr .x3 = BitVec.ofNat 64 p.len ∧ t.gpr .x4 = p.dp ∧ t.gpr .x5 = BitVec.ofNat 64 p.dlen ∧
  t.gpr .x6 = BitVec.ofNat 64 p.len ∧ t.gpr .x7 = p.rp + BitVec.ofNat 64 used

/-- The registers the arguments' block writes. -/
abbrev argRegsW : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x9, .x10, .x11,.x12,.x13]

theorem key_arguments_ok {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block cachedArguments) (allocated 48 s) fun u =>
      (KeyArgs p used u ∧ u.mem = writeController s.mem (callSp p) (callValues p)) ∧
      Keep argRegsW (allocated 48 s) u := by
  have a := h.access
  have hw : ∀ d, d + 8 ≤ 48 → InRegions (⟨callSp p, 48⟩ :: s.wr) (callSp p + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨⟨callSp p, 48⟩, List.mem_cons_self .., Offset.contains_base _ hd (by omega)⟩
  have hw0 : InRegions (⟨callSp p, 48⟩ :: s.wr) (callSp p) 8 := by
    simpa only [BitVec.add_zero] using hw 0 (by decide)
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ ⟨callSp p, 48⟩ :: s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun d hd => by
      obtain ⟨r, hr, hc⟩ := a.ld d hd
      refine ⟨r, ?_, hc⟩
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  have hv5 := h.header (j := 5) (v := p.xp) (by simp [KeyPublic.headers])
  have hv6 := h.header (j := 6) (v := p.yp) (by simp [KeyPublic.headers])
  have hv7 := h.header (j := 7) (v := p.dp) (by simp [KeyPublic.headers])
  have hv8 := h.header (j := 8) (v := BitVec.ofNat 64 p.dlen) (by simp [KeyPublic.headers])
  have hv9 := h.header (j := 9) (v := p.rp + BitVec.ofNat 64 used) (by simp [KeyPublic.headers])
  have hv12 := h.header (j := 12) (v := p.B) (by simp [KeyPublic.headers])
  have hv13 := h.header (j := 13) (v := BitVec.ofNat 64 (p.Z / 8)) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv2 hv5 hv6 hv7 hv8 hv9 hv12 hv13
  have contextArgs:=h.context_args
  have spEq (d : Nat) : (allocated 48 s).sp+BitVec.ofNat 64 (64+d)=p.sp+BitVec.ofNat 64 d :=by
    simp only [allocated,h.sp,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rw [show -(16 : BitVec 64)+(-BitVec.ofNat 64 48+BitVec.ofNat 64 (64+d))=BitVec.ofNat 64 d by
      rw [BitVec.ofNat_add]
      simp only [←BitVec.add_assoc]
      change (0 : BitVec 64)+BitVec.ofNat 64 d=BitVec.ofNat 64 d
      exact BitVec.zero_add _]
  have readOriginal (j : Nat) (hj : j<7) :
    InRegions ((allocated 48 s).rd++(allocated 48 s).wr) (p.sp+BitVec.ofNat 64 (8*j)) 8 :=by
    obtain ⟨r,hr,hc⟩:=input_args h.input j hj
    refine ⟨r,?_,?_⟩
    · rw [allocated,h.rd]
      rcases List.mem_append.mp hr with hr|hr
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ (by rw [h.wr];exact hr))
    · rw [h.input.sp_eq];exact hc
  have readCtx : InRegions ((allocated 48 s).rd++(allocated 48 s).wr) ((allocated 48 s).sp+104#64) 8 :=by
    change InRegions _ ((allocated 48 s).sp+BitVec.ofNat 64 (64+40)) 8
    rw [spEq 40]
    exact readOriginal 5 (by decide)
  have readLen : InRegions ((allocated 48 s).rd++(allocated 48 s).wr) ((allocated 48 s).sp+112#64) 8 :=by
    change InRegions _ ((allocated 48 s).sp+BitVec.ofNat 64 (64+48)) 8
    rw [spEq 48]
    exact readOriginal 6 (by decide)
  have ctxLoad :=exec_ldrSp_x' (t:=.x12) (allocated 48 s) (show 104%8=0 ∧ 104<32768 by decide) readCtx
  have lenLoad :=exec_ldrSp_x' (t:=.x13) ((allocated 48 s).write .x .x12 p.ctx) (show 112%8=0 ∧ 112<32768 by decide)
   (by simpa only [RegUpd.rd_write,RegUpd.wr_write,RegUpd.sp_write] using readLen)
  have ctxValue : s.mem.readW ((allocated 48 s).sp+104#64) 64=p.ctx :=by
    change s.mem.readW ((allocated 48 s).sp+BitVec.ofNat 64 (64+40)) 64=p.ctx
    rw [spEq 40];exact contextArgs.1
  have lenValue : s.mem.readW ((allocated 48 s).sp+112#64) 64=BitVec.ofNat 64 p.ctxLen :=by
    change s.mem.readW ((allocated 48 s).sp+BitVec.ofNat 64 (64+48)) 64=BitVec.ofNat 64 p.ctxLen
    rw [spEq 48];exact contextArgs.2
  simp only [allocated,h.sp] at ctxLoad lenLoad ctxValue lenValue
  refine WP.keep argRegsW ?_ (by decide) (by decide) (by decide +kernel)
  unfold cachedArguments arguments writeController callValues KeyArgs
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ctxLoad,lenLoad,ctxValue,lenValue,ldf, stf,allocated, h.sp, h.x19, exec_addSp (show 0 < 4096 by decide),
    hl 16 (by decide), hl 40 (by decide), hl 48 (by decide), hl 56 (by decide), hl 64 (by decide),
    hl 72 (by decide), hl 96 (by decide), hl 104 (by decide), hw0, hw 8 (by decide), hw 16 (by decide),hw 24 (by decide),hw 32 (by decide),
    hv2, hv5, hv6, hv7, hv8, hv9, hv12, hv13]
  simp only [off, Nat.mul_zero, BitVec.add_zero]

end VG.Proof.Ffdh.AArch64.Cached.SearchProof
