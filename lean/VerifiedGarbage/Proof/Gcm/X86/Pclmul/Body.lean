import VerifiedGarbage.Proof.Gcm.X86.Pclmul.Arith
import VerifiedGarbage.Proof.Gcm.X86.Rev
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Gcm.X86.GhashCT
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Offset

/-!
# GHASH with PCLMULQDQ on x86: the groups of four blocks, the constants, the
memory, the invariant, the prologue and the body

Untrusted: everything here is checked by Lean. One module for what were
`Groups`, `Const`, `Memory`, `Invariant`, `Prologue` and `Body`, a chain of
modules each importing the one before (so one module builds as fast), which
keeps the number of modules importing the algebra of `Proof/Gcm/Poly.lean`
low (`ci/check_lean_speed.py`).
-/

namespace VG.Proof.Gcm.X86.Pclmul
open VG.X86 VG.X86.RegUpd VG.Proof.Gcm.Poly
open VG.Impl.Gcm.X86.Pclmul (at_ poly xInv)

theorem eval_pxor (a b : BitVec 128) : XBinOp.eval .pxor a b = a ^^^ b := rfl

theorem psrldq8 (v : BitVec 128) : XShiftOp.eval .psrldq v 8 = v >>> 64 := rfl

theorem pslldq8 (v : BitVec 128) : XShiftOp.eval .pslldq v 8 = v <<< 64 := rfl

theorem rev_eq : Impl.Gcm.X86.Pclmul.revMask = VG.Proof.Gcm.X86.revMask := rfl

/-- `s'` differs from `s` at most in the SSE registers `rs`. -/
structure Only (rs : List XReg) (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  xmm : ∀ r, r ∉ rs → s'.xmm r = s.xmm r

theorem Only.trans {rs rs' : List XReg} {s s' s'' : State} (h : Only rs s s') (h' : Only rs' s' s'') :
    Only (rs ++ rs') s s'' :=
  ⟨h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd,
    h'.wr.trans h.wr, fun r hr => by
      simp only [List.mem_append, not_or] at hr
      exact (h'.xmm r hr.2).trans (h.xmm r hr.1)⟩

theorem Only.weaken {rs rs' : List XReg} {s s' : State} (h : Only rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    Only rs' s s' :=
  ⟨h.gpr, h.mem, h.rd, h.wr, fun r hr => h.xmm r fun h' => hr (hs r h')⟩

/-- The product registers. -/
def prod (s : State) : Prod := ⟨s.xmm .xmm4, s.xmm .xmm5, s.xmm .xmm6⟩

theorem zero_ok (s : State) :
    WP isa (.block Impl.Gcm.X86.Pclmul.zero) s fun s' =>
      prod s' = Prod.zero ∧ Only [.xmm4, .xmm5, .xmm6] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.Pclmul.zero]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, xmm_setXmm, eval_pxor, BitVec.xor_self, Option.some.injEq,
    exists_eq_left']
  refine ⟨rfl, by simp only [gpr_setXmm], by simp only [mem_setXmm],
    by simp only [rd_setXmm], by simp only [wr_setXmm], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [xmm_setXmm, hr.1, hr.2.1, hr.2.2, ite_false]

theorem acc_ok (s : State) :
    WP isa (.block Impl.Gcm.X86.Pclmul.acc) s fun s' =>
      prod s' = (prod s).acc (s.xmm .xmm2) (s.xmm .xmm3) ∧
      Only [.xmm4, .xmm5, .xmm6, .xmm7] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.Pclmul.acc]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, xmm_setXmm,
    eval_pxor, eval_movdqa, Option.some.injEq, exists_eq_left']
  refine ⟨?_, by simp only [gpr_setXmm], by simp only [mem_setXmm],
    by simp only [rd_setXmm], by simp only [wr_setXmm], fun r hr => ?_⟩
  · simp only [prod, Prod.acc, xmm_setXmm, ite_true, ite_false, reduceCtorEq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [xmm_setXmm, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem reduce_ok (s : State) (h1 : s.xmm .xmm1 = poly) :
    WP isa (.block Impl.Gcm.X86.Pclmul.reduce) s fun s' =>
      s'.xmm .xmm2 = reduce (prod s) ∧ Only [.xmm4, .xmm5, .xmm6, .xmm7, .xmm2] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.Pclmul.reduce, Impl.Gcm.X86.Pclmul.fold,
    List.cons_append, List.nil_append]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, xmm_setXmm,
    eval_pxor, eval_movdqa, h1, Option.some.injEq, exists_eq_left']
  refine ⟨?_, by simp only [gpr_setXmm], by simp only [mem_setXmm],
    by simp only [rd_setXmm], by simp only [wr_setXmm], fun r hr => ?_⟩
  · simp only [prod, psrldq8, pslldq8]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [xmm_setXmm, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- Multiply the accumulator by the transformed hash key. -/
theorem mul_ok (s : State) (h1 : s.xmm .xmm1 = poly) :
    WP isa (.block (Impl.Gcm.X86.Pclmul.zero ++ Impl.Gcm.X86.Pclmul.acc ++
      Impl.Gcm.X86.Pclmul.reduce)) s fun s' =>
      φ (s'.xmm .xmm2) = x * φ (s.xmm .xmm2) * φ (s.xmm .xmm3) ∧
      Only [.xmm4, .xmm5, .xmm6, .xmm7, .xmm2] s s' := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zero_ok s) fun s₁ ⟨p₁, o₁⟩ => ?_
  refine WP.mono (acc_ok s₁) fun s₂ ⟨p₂, o₂⟩ => ?_
  have e1 : s₂.xmm .xmm1 = poly := by
    rw [o₂.xmm _ (by decide), o₁.xmm _ (by decide), h1]
  refine WP.mono (reduce_ok s₂ e1) fun s₃ ⟨p₃, o₃⟩ => ⟨?_, ?_⟩
  · rw [p₃, φ_reduce, p₂, p₁, Prod.val_acc, Prod.val_zero, zero_add,
      o₁.xmm .xmm2 (by decide), o₁.xmm .xmm3 (by decide)]
  · exact (o₁.trans (o₂.trans o₃)).weaken fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (h | h | h) | (h | h | h | h) | (h | h | h | h | h) <;> simp [h]

end VG.Proof.Gcm.X86.Pclmul

namespace VG.Proof.Gcm.X86.Pclmul
open VG.X86 VG.X86.RegUpd VG.Proof.Gcm.Poly

/-- Append a low dword to the lower ninety-six bits of the previous value. -/
def catWord (v : BitVec 128) (d : BitVec 32) : BitVec 128 :=
  (v <<< 32) ||| ((0 : BitVec 96) ++ d)

def assembled (c : BitVec 128) : BitVec 128 :=
  catWord (catWord (catWord ((0 : BitVec 96) ++ c.extractLsb' 96 32)
    (c.extractLsb' 64 32)) (c.extractLsb' 32 32)) (c.extractLsb' 0 32)

theorem assembled_eq (c : BitVec 128) : assembled c = c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [assembled, catWord, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  rcases (by omega : i < 32 ∨ (32 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 96) ∨ 96 ≤ i)
    with h | h | h | h <;>
    simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true,
      decide_eq_false, Bool.true_and, Bool.false_and, Bool.not_true, Bool.not_false,
      Bool.false_or, BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero, Bool.or_false] <;>
    exact congrArg _ (by omega)

/-- Setup changes only eax and the listed vector registers. -/
structure SetupFrame (rs : List XReg) (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  xmm : ∀ r, r ∉ rs → s'.xmm r = s.xmm r

theorem const_ok (r : XReg) (c : BitVec 128) (s : State) (hr : r ≠ .xmm5) :
    WP isa (.block (Impl.Gcm.X86.Pclmul.const r c)) s fun s' =>
      s'.xmm r = c ∧ SetupFrame [r, .xmm5] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.Pclmul.const, List.range_succ, List.range_zero,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.cons_append, List.nil_append]
  simp only [↓reduceIte, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, runBlock_cons, runStep_some, runBlock_nil,
    exec, isa, readSrc, XOp.exec, gpr_setReg, xmm_setReg, xmm_setXmm,
    hr, Option.map_some, Option.some.injEq,
    exists_eq_left', XShiftOp.eval, XBinOp.eval]
  refine ⟨?_, fun a ha => ?_, ?_, ?_, ?_, fun a ha => ?_⟩
  · exact assembled_eq c
  · simp only [gpr_setXmm, gpr_setReg, ha, ite_false]
  · simp only [mem_setXmm, mem_setReg]
  · simp only [rd_setXmm, rd_setReg]
  · simp only [wr_setXmm, wr_setReg]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
    simp only [xmm_setXmm, xmm_setReg, ha.1, ha.2, ite_false]

theorem unpack_ones : XBinOp.eval .punpckldq
    ((0 : BitVec 96) ++ (0xffffffff : BitVec 32))
    ((0 : BitVec 96) ++ (0xffffffff : BitVec 32)) =
    ((0 : BitVec 64) ++ (0xffffffffffffffff : BitVec 64)) := rfl

theorem hInv_ok (s : State) :
    WP isa (.block Impl.Gcm.X86.Pclmul.hInv) s fun s' =>
      x * φ (s'.xmm .xmm3) = φ (s.xmm .xmm7) ∧
      SetupFrame [.xmm3, .xmm4, .xmm5, .xmm6] s s' := by
  rw [Impl.Gcm.X86.Pclmul.hInv, WP.block_append_iff]
  refine WP.mono (const_ok .xmm4 Impl.Gcm.X86.Pclmul.xInv s (by decide))
    fun s₁ ⟨hc, hf⟩ => ?_
  have h7 : s₁.xmm .xmm7 = s.xmm .xmm7 := hf.xmm _ (by decide)
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, runBlock_cons, runStep_some, runBlock_nil,
    exec, isa, readSrc, XOp.exec, gpr_setReg, xmm_setReg, xmm_setXmm,
    Option.map_some, Option.some.injEq, exists_eq_left',
    hc, h7, eval_movdqa, eval_pxor, unpack_ones]
  refine ⟨?_, fun a ha => ?_, ?_, ?_, ?_, fun a ha => ?_⟩
  · change x * φ ((XShiftOp.eval .psllq (s.xmm .xmm7) 1 |||
      XShiftOp.eval .pslldq (XShiftOp.eval .psrlq (s.xmm .xmm7) 63) 8) ^^^ _) = _
    rw [shl1, mask_eq, x_φ_hInv]
  · simp only [gpr_setXmm, gpr_setReg, ha, ite_false]
    exact hf.gpr a ha
  · simp only [mem_setXmm, mem_setReg]; exact hf.mem
  · simp only [rd_setXmm, rd_setReg]; exact hf.rd
  · simp only [wr_setXmm, wr_setReg]; exact hf.wr
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
    simp only [xmm_setXmm, xmm_setReg, ha.1, ha.2.2.1, ha.2.2.2, ite_false]
    exact hf.xmm a (by simp only [List.mem_cons, List.not_mem_nil,
      ha.2.1, ha.2.2.1, or_self, not_false_eq_true])

end VG.Proof.Gcm.X86.Pclmul

namespace VG.Proof.Gcm.X86.Pclmul
open VG.X86 VG.X86.RegUpd
open VG.Impl.Gcm.X86.Pclmul (at_ argOp)
open VG.Proof.Gcm.X86 (GPre aR)

theorem args_in {s : State} (hp : GPre s) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (argAddr s i) 4 := by
  refine ⟨aR s, by simp only [hp.rd, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_true, true_or], ?_⟩
  exact Proof.Aes.X86.part_contains (N := 24) (a := 4) (k := 20)
    hp.fSp (by decide) (by omega) (by omega) (by decide)

theorem ea_arg (s : State) (i : Nat) : s.ea (argOp i) = argAddr s i := rfl

theorem movArg_exec {s₀ s : State} (hp : GPre s₀) {i : Nat} (hi : i < 5)
    (hsp : s.gpr .esp = s₀.gpr .esp) (hm : s.mem = s₀.mem)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (d : Reg) :
    exec (.mov d (.mem (argOp i))) s = some (s.setReg d (arg s₀ i)) := by
  have he : s.ea (argOp i) = argAddr s₀ i := by
    simp only [State.ea, argOp, at_, argAddr, hsp]
  simp only [exec, readSrc, State.load32, he, hrd, hwr, args_in hp hi,
    ite_true, hm, Option.map_some, arg]

/-- Load a big-endian GHASH block, retaining every general-purpose register. -/
theorem ldrev_ok (r : XReg) (b : Reg) (d : Nat) (s : State) (hr : r ≠ .xmm0)
    (h0 : s.xmm .xmm0 = VG.Proof.Gcm.X86.revMask)
    (hin : InRegions (s.rd ++ s.wr) (s.ea (at_ b d)) 16) :
    WP isa (.block [.movdquLoad r (at_ b d), .xop (.bin .pshufb r .xmm0)]) s fun s' =>
      s'.xmm r = Spec.Gcm.blockAt s.mem (s.ea (at_ b d)) ∧ Only [r] s s' := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil,
    exec, isa, XOp.exec, State.load128, hin, xmm_setXmm, Ne.symm hr,
    h0, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, by simp only [gpr_setXmm], by simp only [mem_setXmm],
    by simp only [rd_setXmm], by simp only [wr_setXmm], fun a ha => ?_⟩
  · rw [VG.Proof.Gcm.X86.blockAt_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    simp only [xmm_setXmm, ha, ite_false]

end VG.Proof.Gcm.X86.Pclmul

namespace VG.Proof.Gcm.X86.Pclmul
open VG.X86 VG.X86.RegUpd VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86 (GPre hP yP dP nBlk)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

/-- Every instruction before the final Y store retains memory, regions and
all cdecl callee-saved registers. -/
structure Env (s₀ s : State) : Prop where
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r

theorem Env.refl (s : State) : Env s s := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Env.sp {s₀ s : State} (h : Env s₀ s) : s.gpr .esp = s₀.gpr .esp :=
  h.saved .esp (by decide)

theorem Env.of_setup {s₀ s s' : State} {rs : List XReg} (h : Env s₀ s)
    (hf : SetupFrame rs s s') : Env s₀ s' :=
  ⟨hf.mem.trans h.mem, hf.rd.trans h.rd, hf.wr.trans h.wr, fun r hr => by
    have hn : r ≠ .eax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hf.gpr r hn).trans (h.saved r hr)⟩

theorem Env.of_only {s₀ s s' : State} {rs : List XReg} (h : Env s₀ s)
    (hf : Only rs s s') : Env s₀ s' :=
  ⟨hf.mem.trans h.mem, hf.rd.trans h.rd, hf.wr.trans h.wr,
    fun r hr => (congrFun hf.gpr r).trans (h.saved r hr)⟩

theorem Env.setReg {s₀ s : State} (h : Env s₀ s) (d : Reg) (v : BitVec 32)
    (hd : d ∉ calleeSaved) : Env s₀ (s.setReg d v) :=
  ⟨(mem_setReg s d v).trans h.mem, (rd_setReg s d v).trans h.rd,
    (wr_setReg s d v).trans h.wr, fun r hr => by
    rw [gpr_setReg_of_ne s v (show r ≠ d from fun heq => hd (heq ▸ hr))]
    exact h.saved r hr⟩

abbrev H (s₀ : State) : Block := blockAt s₀.mem ((hP s₀).setWidth 64)
abbrev Y (s₀ : State) (i : Nat) : Block :=
  ghashFrom (H s₀) (blockAt s₀.mem ((yP s₀).setWidth 64))
    (blocksAt s₀.mem ((dP s₀).setWidth 64) i)

/-- The accumulator after i blocks and public remaining count/data pointer. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  env : Env s₀ s
  le : i ≤ nBlk s₀
  count : s.gpr .eax = BitVec.ofNat 32 (nBlk s₀ - i)
  data : s.gpr .edx = dP s₀ + BitVec.ofNat 32 (16 * i)
  out : s.gpr .ecx = yP s₀
  rev : s.xmm .xmm0 = VG.Proof.Gcm.X86.revMask
  poly : s.xmm .xmm1 = Impl.Gcm.X86.Pclmul.poly
  hash : x * φ (s.xmm .xmm3) = φ (H s₀)
  acc : s.xmm .xmm2 = Y s₀ i

end VG.Proof.Gcm.X86.Pclmul

namespace VG.Proof.Gcm.X86.Pclmul
open VG VG.X86 VG.X86.RegUpd VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86 (GPre hP yP dP nBlk hR yR)
open VG.Impl.Gcm.X86.Pclmul (argOp at_)

theorem Env.arithFlags {s₀ s : State} (h : Env s₀ s) (v : BitVec 32) (c o : Bool) :
    Env s₀ (arithFlags s v c o) :=
  ⟨(mem_arithFlags s v c o).trans h.mem, (rd_arithFlags s v c o).trans h.rd,
    (wr_arithFlags s v c o).trans h.wr,
    fun r hr => by rw [gpr_arithFlags]; exact h.saved r hr⟩

theorem movArg_ok {s₀ s : State} (hp : GPre s₀) (he : Env s₀ s)
    (i : Nat) (hi : i < 5) (d : Reg) (hd : d ∉ calleeSaved) :
    WP isa (.block [.mov d (.mem (argOp i))]) s fun s' =>
      s'.gpr d = arg s₀ i ∧ Env s₀ s' ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.xmm = s.xmm := by
  refine WP.of_runBlock ⟨s.setReg d (arg s₀ i), ?_, ?_⟩
  · rw [runBlock_cons, movArg_exec hp hi he.sp he.mem he.rd he.wr,
      runStep_some, runBlock_nil]
  · exact ⟨gpr_setReg_self _ _ _, he.setReg d _ hd,
      fun r hr => gpr_setReg_of_ne _ _ hr, rfl⟩

theorem test_ok (s : State) :
    WP isa (.block [.alu .test .eax (.reg .eax)]) s fun s' =>
      s'.zf = some (s.gpr .eax == 0) ∧ Env s s' ∧
      s'.gpr = s.gpr ∧ s'.xmm = s.xmm := by
  refine WP.of_runBlock ⟨arithFlags s (s.gpr .eax) false false, ?_, ?_⟩
  · simp only [runBlock_cons, exec, execAlu, readSrc, Option.bind_some,
      BitVec.and_self, runStep_some, runBlock_nil]
  · exact ⟨rfl, (Env.refl s).arithFlags _ _ _, rfl, rfl⟩

theorem h_read {s : State} (hp : GPre s) :
    InRegions (s.rd ++ s.wr) ((hP s).setWidth 64) 16 := by
  refine ⟨hR s, ?_, Region.contains_self _ _⟩
  simp only [hp.rd, List.mem_append, List.mem_cons, true_or]

theorem y_read {s : State} (hp : GPre s) :
    InRegions (s.rd ++ s.wr) ((yP s).setWidth 64) 16 := by
  refine ⟨yR s, ?_, Region.contains_self _ _⟩
  simp only [hp.wr, List.mem_append, List.mem_cons, or_true, true_or]

theorem Env.trans {s₀ s s' : State} (h : Env s₀ s) (h' : Env s s') : Env s₀ s' :=
  ⟨h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr,
    fun r hr => (h'.saved r hr).trans (h.saved r hr)⟩

theorem prologue_ok (s₀ : State) (hp : GPre s₀) :
    WP isa (.block Impl.Gcm.X86.Pclmul.prologue) s₀ fun s =>
      Inv s₀ 0 s ∧ s.zf = some (decide (nBlk s₀ = 0)) := by
  simp only [Impl.Gcm.X86.Pclmul.prologue, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 Impl.Gcm.X86.Pclmul.revMask s₀ (by decide))
    fun s₁ ⟨rev₁, f₁⟩ => ?_
  have e₁ := (Env.refl s₀).of_setup f₁
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 Impl.Gcm.X86.Pclmul.poly s₁ (by decide))
    fun s₂ ⟨poly₂, f₂⟩ => ?_
  have e₂ := e₁.of_setup f₂
  have rev₂ : s₂.xmm .xmm0 = VG.Proof.Gcm.X86.revMask := by
    rw [f₂.xmm _ (by decide), rev₁]; rfl
  rw [show ([.mov .eax (.mem (argOp 0)), .movdquLoad .xmm7 (at_ .eax 0),
      .xop (.bin .pshufb .xmm7 .xmm0)] : List Instr) =
      ([.mov .eax (.mem (argOp 0))] : List Instr) ++
      [.movdquLoad .xmm7 (at_ .eax 0), .xop (.bin .pshufb .xmm7 .xmm0)] from rfl,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (movArg_ok hp e₂ 0 (by decide) .eax (by decide))
    fun s₃ ⟨ptr₃, e₃, _, x₃⟩ => ?_
  have hread₃ : InRegions (s₃.rd ++ s₃.wr) (s₃.ea (at_ .eax 0)) 16 := by
    simp only [State.ea, at_, ptr₃, BitVec.add_zero, e₃.rd, e₃.wr]
    exact h_read hp
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .eax 0 s₃ (by decide) (by rw [x₃]; exact rev₂) hread₃)
    fun s₄ ⟨hash₄, f₄⟩ => ?_
  have e₄ := e₃.of_only f₄
  rw [WP.block_append_iff]
  refine WP.mono (hInv_ok s₄) fun s₅ ⟨hash₅, f₅⟩ => ?_
  have e₅ := e₄.of_setup f₅
  have rev₅ : s₅.xmm .xmm0 = VG.Proof.Gcm.X86.revMask := by
    rw [f₅.xmm _ (by decide), f₄.xmm _ (by decide), x₃]; exact rev₂
  have poly₅ : s₅.xmm .xmm1 = Impl.Gcm.X86.Pclmul.poly := by
    rw [f₅.xmm _ (by decide), f₄.xmm _ (by decide), x₃]; exact poly₂
  have hash₅' : x * φ (s₅.xmm .xmm3) = φ (H s₀) := by
    rw [hash₅, hash₄, e₃.mem]
    simp only [State.ea, at_, ptr₃, BitVec.add_zero]
  change WP isa (.block (([.mov .ecx (.mem (argOp 1))] : List Instr) ++
    [.movdquLoad .xmm2 (at_ .ecx 0), .xop (.bin .pshufb .xmm2 .xmm0),
      .mov .edx (.mem (argOp 2)), .mov .eax (.mem (argOp 3)), .alu .test .eax (.reg .eax)])) s₅ _
  rw [WP.block_append_iff]
  refine WP.mono (movArg_ok hp e₅ 1 (by decide) .ecx (by decide))
    fun s₆ ⟨ptr₆, e₆, _, x₆⟩ => ?_
  have yread₆ : InRegions (s₆.rd ++ s₆.wr) (s₆.ea (at_ .ecx 0)) 16 := by
    simp only [State.ea, at_, ptr₆, BitVec.add_zero, e₆.rd, e₆.wr]
    exact y_read hp
  change WP isa (.block (([.movdquLoad .xmm2 (at_ .ecx 0),
    .xop (.bin .pshufb .xmm2 .xmm0)] : List Instr) ++
    [.mov .edx (.mem (argOp 2)), .mov .eax (.mem (argOp 3)), .alu .test .eax (.reg .eax)])) s₆ _
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm2 .ecx 0 s₆ (by decide) (by rw [x₆]; exact rev₅) yread₆)
    fun s₇ ⟨acc₇, f₇⟩ => ?_
  have e₇ := e₆.of_only f₇
  change WP isa (.block (([.mov .edx (.mem (argOp 2))] : List Instr) ++
    [.mov .eax (.mem (argOp 3)), .alu .test .eax (.reg .eax)])) s₇ _
  rw [WP.block_append_iff]
  refine WP.mono (movArg_ok hp e₇ 2 (by decide) .edx (by decide))
    fun s₈ ⟨ptr₈, e₈, regs₈, x₈⟩ => ?_
  change WP isa (.block (([.mov .eax (.mem (argOp 3))] : List Instr) ++
    [.alu .test .eax (.reg .eax)])) s₈ _
  rw [WP.block_append_iff]
  refine WP.mono (movArg_ok hp e₈ 3 (by decide) .eax (by decide))
    fun s₉ ⟨count₉, e₉, regs₉, x₉⟩ => ?_
  refine WP.mono (test_ok s₉) fun s ⟨zf, ef, regs, xs⟩ => ?_
  constructor
  · refine ⟨e₉.trans ef, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [regs, count₉, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [regs, regs₉ _ (by decide), ptr₈, Nat.mul_zero, BitVec.add_zero]
    · rw [regs, regs₉ _ (by decide), regs₈ _ (by decide), f₇.gpr, ptr₆]
    · rw [xs, x₉, x₈, f₇.xmm _ (by decide), x₆]; exact rev₅
    · rw [xs, x₉, x₈, f₇.xmm _ (by decide), x₆]; exact poly₅
    · rw [xs, x₉, x₈, f₇.xmm _ (by decide), x₆]; exact hash₅'
    · rw [xs, x₉, x₈, acc₇, e₆.mem]
      simp only [State.ea, at_, ptr₆, BitVec.add_zero,
        Y, Proof.Gcm.ghashFrom_blocksAt_zero]
  · rw [zf, count₉]
    exact congrArg some (by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using Wp.ofNat_beq_zero (arg s₀ 3).isLt)

end VG.Proof.Gcm.X86.Pclmul

namespace VG.Proof.Gcm.X86.Pclmul
open VG VG.X86 VG.X86.RegUpd VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86 (GPre dP nBlk dR)
open VG.Impl.Gcm.X86.Pclmul (at_)

theorem data_read {s₀ s : State} (hp : GPre s₀) {i : Nat} (hi : Inv s₀ i s)
    (hb : i < nBlk s₀) :
    InRegions (s.rd ++ s.wr) (s.ea (at_ .edx 0)) 16 := by
  have hf := hp.fD
  have he : s.ea (at_ .edx 0) = (dP s₀).setWidth 64 + BitVec.ofNat 64 (16 * i) := by
    simp only [State.ea, at_, hi.data, BitVec.add_zero]
    exact addr_eq (by omega)
  rw [he, hi.env.rd, hi.env.wr, hp.rd]
  refine ⟨dR s₀, ?_, Offset.contains_base _ (by omega) (by omega)⟩
  simp only [List.mem_append, List.mem_cons, or_true, true_or]

theorem xor_ok (s : State) :
    WP isa (.block [.xop (.bin .pxor .xmm2 .xmm7)]) s fun s' =>
      s'.xmm .xmm2 = s.xmm .xmm2 ^^^ s.xmm .xmm7 ∧ Only [.xmm2] s s' := by
  refine WP.of_runBlock ⟨s.setXmm .xmm2 (s.xmm .xmm2 ^^^ s.xmm .xmm7), ?_, ?_⟩
  · simp only [runBlock_cons, exec, XOp.exec, XBinOp.eval, runStep_some, runBlock_nil]
  · refine ⟨xmm_setXmm_self _ _ _, gpr_setXmm _ _ _, mem_setXmm _ _ _,
      rd_setXmm _ _ _, wr_setXmm _ _ _, ?_⟩
    intro r hr
    exact xmm_setXmm_of_ne _ _ (by simpa only [List.mem_singleton] using hr)

theorem advance_ok (s : State) :
    WP isa (.block [.alu .add .edx (.imm 16), .alu .sub .eax (.imm 1)]) s fun s' =>
      s'.gpr .eax = s.gpr .eax - 1 ∧ s'.gpr .edx = s.gpr .edx + 16 ∧
      s'.zf = some (s.gpr .eax - 1 == 0) ∧ Env s s' ∧
      s'.gpr .ecx = s.gpr .ecx ∧ s'.xmm = s.xmm := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, Option.bind_some, gpr_setReg, gpr_arithFlags,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, rfl, ?_, True.intro, rfl⟩
  exact (((Env.refl s).arithFlags _ _ _).setReg .edx _ (by decide)).arithFlags _ _ _ |>.setReg .eax _ (by decide)

theorem body_ok {s₀ s : State} (hp : GPre s₀) {i : Nat} (hi : Inv s₀ i s)
    (hb : i < nBlk s₀) :
    WP isa (.block Impl.Gcm.X86.Pclmul.body) s fun s' =>
      Inv s₀ (i + 1) s' ∧ s'.zf = some (decide (nBlk s₀ - (i + 1) = 0)) := by
  simp only [Impl.Gcm.X86.Pclmul.body, List.append_assoc]
  rw [show ([.movdquLoad .xmm7 (at_ .edx 0), .xop (.bin .pshufb .xmm7 .xmm0),
    .xop (.bin .pxor .xmm2 .xmm7)] : List Instr) =
    ([.movdquLoad .xmm7 (at_ .edx 0), .xop (.bin .pshufb .xmm7 .xmm0)] : List Instr) ++
    [.xop (.bin .pxor .xmm2 .xmm7)] from rfl,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .edx 0 s (by decide) hi.rev (data_read hp hi hb))
    fun s₁ ⟨input₁, f₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (xor_ok s₁) fun s₂ ⟨acc₂, f₂⟩ => ?_
  rw [← List.append_assoc, ← List.append_assoc, WP.block_append_iff]
  have poly₂ : s₂.xmm .xmm1 = Impl.Gcm.X86.Pclmul.poly := by
    rw [f₂.xmm _ (by decide), f₁.xmm _ (by decide)]; exact hi.poly
  refine WP.mono (mul_ok s₂ poly₂) fun s₃ ⟨mul₃, f₃⟩ => ?_
  have env₃ := ((hi.env.of_only f₁).of_only f₂).of_only f₃
  have acc₃ : s₃.xmm .xmm2 = Y s₀ (i + 1) := by
    apply φ_inj
    have hin : s₁.xmm .xmm7 = Spec.Gcm.blockAt s₀.mem
        ((dP s₀).setWidth 64 + BitVec.ofNat 64 (16 * i)) := by
      rw [input₁, hi.env.mem]
      refine congrArg (Spec.Gcm.blockAt _) ?_
      simp only [State.ea, at_, hi.data, BitVec.add_zero]
      exact addr_eq (by have hf := hp.fD; omega)
    rw [mul₃, acc₂, hin, f₁.xmm _ (by decide), hi.acc]
    rw [f₂.xmm _ (by decide), f₁.xmm _ (by decide)]
    rw [mul_assoc, mul_left_comm x, hi.hash]
    rw [show Y s₀ (i + 1) = Spec.Gcm.mul (Y s₀ i ^^^ Spec.Gcm.blockAt s₀.mem
      ((dP s₀).setWidth 64 + BitVec.ofNat 64 (16 * i))) (H s₀) from
      Proof.Gcm.ghashFrom_blocksAt_succ _ _ _ _ _, φ_mul]
  refine WP.mono (advance_ok s₃) fun s₄ ⟨count₄, data₄, zf₄, ef₄, out₄, xmm₄⟩ => ?_
  have regs₃ : s₃.gpr = s.gpr := f₃.gpr.trans (f₂.gpr.trans f₁.gpr)
  have bound : nBlk s₀ < 2 ^ 32 := (arg s₀ 3).isLt
  have count : s₃.gpr .eax - 1 = BitVec.ofNat 32 (nBlk s₀ - (i + 1)) := by
    rw [regs₃, hi.count, Wp.ofNat_pred (by omega), Nat.sub_sub]
  constructor
  · refine ⟨env₃.trans ef₄, by omega, count₄.trans count, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [data₄, regs₃, hi.data, BitVec.add_assoc]
      change dP s₀ + (BitVec.ofNat 32 (16 * i) + BitVec.ofNat 32 16) = _
      rw [← BitVec.ofNat_add, show 16 * i + 16 = 16 * (i + 1) by omega]
    · rw [out₄, regs₃]; exact hi.out
    · rw [xmm₄, f₃.xmm _ (by decide), f₂.xmm _ (by decide), f₁.xmm _ (by decide)]; exact hi.rev
    · rw [xmm₄, f₃.xmm _ (by decide)]; exact poly₂
    · rw [xmm₄, f₃.xmm _ (by decide), f₂.xmm _ (by decide), f₁.xmm _ (by decide)]; exact hi.hash
    · rw [xmm₄]; exact acc₃
  · rw [zf₄, count, Wp.ofNat_beq_zero (by omega)]

end VG.Proof.Gcm.X86.Pclmul
