module

public import VerifiedGarbage.Impl.AesXts.X86
public import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
public import VerifiedGarbage.Spec.Xts.Contract
import VerifiedGarbage.Proof.AesCbc.X86.Verified
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.AesCbc.X86.CT
import VerifiedGarbage.Proof.MdStream.X86.Common
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.AesCbc.X86.CT
meta import VerifiedGarbage.Proof.MdStream.X86.Common
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.AesXts.X86.Steps
public import VerifiedGarbage.Proof.AesXts.Batch
import VerifiedGarbage.Proof.AesOcb.X86.Run
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
public import VerifiedGarbage.Proof.AesOcb.X86.Callee
public import VerifiedGarbage.Proof.AesCbc.X86.Body
public import VerifiedGarbage.Proof.AesXts.Spec
import VerifiedGarbage.Proof.CmacAes.X86.UpdateLoop
import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.AesXts.X86.Steps
meta import VerifiedGarbage.Proof.AesXts.Batch
meta import VerifiedGarbage.Proof.AesOcb.X86.Callee
meta import VerifiedGarbage.Impl.AesXts.X86
meta import VerifiedGarbage.Proof.AesCbc.X86.Body
meta import VerifiedGarbage.Proof.AesXts.Spec
meta import VerifiedGarbage.Proof.CmacAes.X86.UpdateLoop
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `AesXts.X86.CT`, which this module and modules that import it used -/

section

/-! ### `AesXts.X86.Body`, which only this module used -/

section

/-!
# XTS-AES on x86: all the blocks in one call

`crypt_wp`: from AES-CBC's loop invariant after no blocks
(`Proof/AesCbc/X86/Body.lean`), `batch` reaches it after all of them
(`batch_wp`), for `xtsMode enc`, for any implementation of the block
functions (`BlocksImpl`). A pass XORs each block's tweak into it, with the
tweak in `xmm0`, multiplying it by `α` after each (`pass_wp`): eight blocks
at a time while eight are left (`oct_wp`, `octs_wp`: their tweaks in `xmm4`,
`OI` among them, and `xmm0` times `α⁸`), then one at a time (`sstep_wp`,
`single_wp`); the invariant `XI` says what `xored` the blocks are, and
that the tweak in memory is still the one the function was given; the
block function is called on all the blocks (`callArgs_wp`, `call_wp`, from
AES-OCB's `BCall`); a second pass XORs the tweaks in again, and the tweak
after the last block is stored (`storeT_wp`, `AesXts.crypt_eq`). Between
the passes the state is `PInv`.

The straight-line pieces with SSE instructions are run to an explicit state
(`xorBlk_run`, `mulX_run`, `mul8_run`, `next_run`, `constsLd_run`): a block in an SSE
register is its 16 bytes, the first least significant (`bx`,
`Proof/AesXts/X86/Steps.lean`).
-/

@[expose] public section

namespace VG.Proof.AesXts.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesXts.X86
open VG.Impl.CmacAes.X86 (argOp at_ setup restore)
open VG.Proof.CmacAes.X86 (wp_arg add0 arg_ofNat ea_at')
open VG.Proof.MdStream.X86 (Upd eval_ne)
open VG.Proof.AesCbc (Mode ciphOf length_blocksAt getElem_blocksAt)
open VG.Proof.AesCbc.X86
open VG.Proof.AesGcm.X86 (w64 runBlock_app_of)
open VG.Proof.AesOcb.X86 (exec_bin exec_movd exec_pshufd)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Proof.AesXts (xored xored_zero xored_getElem xored_step xored_all crypt_eq blocksAt_frame blocksAt_of_out)
open VG.Proof.Cmac (bytesAt_frame)

/-- Between the passes: the blocks are `ys`, and the tweak in memory is the
one the function was given. -/
structure PInv (s₀ : State) (ys : List (List Byte)) (s : State) : Prop where
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) s.mem
  len : ys.length = N s₀
  data : Spec.Cbc.blocksAt s.mem ((Dp s₀).setWidth 64) (N s₀) = ys
  iv : bytesAt s.mem ((Iv s₀).setWidth 64) 16 = iv0 s₀

/-- A pass over the blocks `ys`, after `i` of them: the tweak of the next in
`xmm0`, the number of blocks left in `edi`, and the constants. -/
structure XI (s₀ : State) (ys : List (List Byte)) (i : Nat) (s : State) : Prop where
  esi : s.gpr .esi = D32 s₀ i
  edi : s.gpr .edi = BitVec.ofNat 32 (N s₀ - i)
  ebx : s.gpr .ebx = Iv s₀
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) s.mem
  len : ys.length = N s₀
  data : Spec.Cbc.blocksAt s.mem ((Dp s₀).setWidth 64) (N s₀) = xored (iv0 s₀) ys i
  iv : bytesAt s.mem ((Iv s₀).setWidth 64) 16 = iv0 s₀
  x0 : bx (s.xmm .xmm0) = Spec.Xts.next (iv0 s₀) i
  x6 : s.xmm .xmm6 = onesX
  x7 : s.xmm .xmm7 = cX

theorem length_xored (t : List Byte) (ys : List (List Byte)) (i : Nat) (hi : i ≤ ys.length) :
    (xored t ys i).length = ys.length := by
  simp [xored, AesXts.length_tweaks]; omega

theorem exec_shift (op : XShiftOp) (d : XReg) (n : BitVec 8) (s : State) :
    XOp.exec (.shift op d n) s = s.setXmm d (op.eval (s.xmm d) n) := rfl

/-- The number of blocks left, after one more. -/
theorem left_step {n i : Nat} (hn : n < 2 ^ 32) (hi : i < n) :
    BitVec.ofNat 32 (n - i) - 1 = BitVec.ofNat 32 (n - (i + 1)) ∧
      (BitVec.ofNat 32 (n - i) - 1 == 0) = decide (i + 1 = n) := by
  have e : BitVec.ofNat 32 (n - i) - 1 = BitVec.ofNat 32 (n - (i + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn] : n - i < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega_using [hn] : n - (i + 1) < 2 ^ 32)]
    show (2 ^ 32 - 1 + (n - i)) % 2 ^ 32 = _
    omega_using [hn, hi]
  refine ⟨e, ?_⟩
  rw [e, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega_using [hn] : n - (i + 1) < 2 ^ 32)]
  show n - (i + 1) = 0 ↔ _
  omega_using [hi]

/-- `mulX`: the tweak in `t` times `α`. -/
theorem mulX_run {t : XReg} (h2 : ¬ t = .xmm2) (h6 : ¬ t = .xmm6) (h7 : ¬ t = .xmm7) (s : State)
    (x6 : s.xmm .xmm6 = onesX) (x7 : s.xmm .xmm7 = cX) :
    ∃ s', runBlock isa (mulX t) s = some s' ∧ s'.xmm t = alphaX (s.xmm t) ∧
      (∀ r, ¬ r = t → ¬ r = .xmm2 → s'.xmm r = s.xmm r) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have h2' : ¬ XReg.xmm2 = t := fun h => h2 h.symm
  have h6' : ¬ XReg.xmm6 = t := fun h => h6 h.symm
  have h7' : ¬ XReg.xmm7 = t := fun h => h7 h.symm
  refine ⟨_, by
    simp only [mulX, runBlock_cons, runStep_some, runBlock_nil, exec, exec_bin, exec_shift, exec_pshufd]
    rfl, ?_, fun r h₁ h₂ => ?_, by rfl, by rfl, by rfl, by rfl⟩
  · simp only [xmm_setXmm_self, xmm_setXmm_of_ne _ _ h2, xmm_setXmm_of_ne _ _ h2', reduceCtorEq,
      not_false_eq_true, xmm_setXmm_of_ne, x6, x7]
    exact mulX_val _
  · simp only [xmm_setXmm_of_ne _ _ h₁, xmm_setXmm_of_ne _ _ h₂]

/-- Among eight blocks from block `i`, after `j` of them: the tweak of block
`i` in `xmm0`, and that of the next block in `xmm4`. -/
structure OI (s₀ : State) (ys : List (List Byte)) (i j : Nat) (s : State) : Prop where
  esi : s.gpr .esi = D32 s₀ i
  edi : s.gpr .edi = BitVec.ofNat 32 (N s₀ - i)
  ebx : s.gpr .ebx = Iv s₀
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) s.mem
  len : ys.length = N s₀
  data : Spec.Cbc.blocksAt s.mem ((Dp s₀).setWidth 64) (N s₀) = xored (iv0 s₀) ys (i + j)
  iv : bytesAt s.mem ((Iv s₀).setWidth 64) 16 = iv0 s₀
  x0 : bx (s.xmm .xmm0) = Spec.Xts.next (iv0 s₀) i
  x4 : bx (s.xmm .xmm4) = Spec.Xts.next (iv0 s₀) (i + j)
  x6 : s.xmm .xmm6 = onesX
  x7 : s.xmm .xmm7 = cX

/-- The number of blocks left, after eight more. -/
theorem left_step8 {n i : Nat} (hn : n < 2 ^ 32) (hi : i + 8 ≤ n) :
    BitVec.ofNat 32 (n - i) - 8 = BitVec.ofNat 32 (n - (i + 8)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn] : n - i < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega_using [hn] : n - (i + 8) < 2 ^ 32)]
  show (2 ^ 32 - 8 + (n - i)) % 2 ^ 32 = _
  omega_using [hn, hi]

/-- `mul8`: the tweak in `xmm0` times `α⁸`. -/
theorem mul8_run (s : State) :
    ∃ s', runBlock isa mul8 s = some s' ∧ s'.xmm .xmm0 = Nat.repeat alphaX 8 (s.xmm .xmm0) ∧
      (∀ r, ¬ r = .xmm0 → ¬ r = .xmm3 → s'.xmm r = s.xmm r) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by
    simp only [mul8, runBlock_cons, runStep_some, runBlock_nil, exec, exec_bin, exec_shift, xmm_setXmm_self,
      xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true, eval_movdqa]
    rfl, ?_, fun r h₁ h₂ => ?_, by simp only [gpr_setXmm], by simp only [mem_setXmm], by simp only [rd_setXmm],
    by simp only [wr_setXmm]⟩
  · simp only [xmm_setXmm_self]
    exact mul8_val _
  · simp only [xmm_setXmm_of_ne _ _ h₁, xmm_setXmm_of_ne _ _ h₂]

/-- On to the next eight blocks: `esi`, the number of blocks left, and CF
set if fewer than eight are. -/
theorem next8_run (s : State) :
    ∃ s', runBlock isa [.alu .add .esi (.imm 128), .alu .sub .edi (.imm 8), .alu .cmp .edi (.imm 8)] s = some s' ∧
      s'.gpr .esi = s.gpr .esi + 128 ∧ s'.gpr .edi = s.gpr .edi - 8 ∧
      (∀ r, ¬ r = .esi → ¬ r = .edi → s'.gpr r = s.gpr r) ∧
      s'.cf = some (decide ((s.gpr .edi - 8).toNat < 8)) ∧
      s'.xmm = s.xmm ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
    rfl, ?_, ?_, fun r h₁ h₂ => ?_, ?_, by rfl, by rfl, by rfl, by rfl⟩
  · simp only [gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags, reduceCtorEq, not_false_eq_true]
  · simp only [gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags, reduceCtorEq, not_false_eq_true]
  · simp only [gpr_setReg_of_ne _ _ h₁, gpr_setReg_of_ne _ _ h₂, gpr_arithFlags]
  · simp only [cf_arithFlags, gpr_setReg_self]; rfl

/-- `cmp edi, 8`: CF set if fewer than eight blocks are left. -/
theorem cmp8_run (s : State) :
    ∃ s', runBlock isa [.alu .cmp .edi (.imm 8)] s = some s' ∧
      s'.cf = some (decide ((s.gpr .edi).toNat < 8)) ∧ s'.gpr = s.gpr ∧ s'.xmm = s.xmm ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
    rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl⟩

/-- `test edi, edi`: ZF set if no blocks are left. -/
theorem test_run (s : State) :
    ∃ s', runBlock isa [.alu .test .edi (.reg .edi)] s = some s' ∧
      s'.zf = some (s.gpr .edi &&& s.gpr .edi == 0) ∧ s'.gpr = s.gpr ∧ s'.xmm = s.xmm ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
    rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl⟩

/-- A state that differs in the flags. -/
theorem XI.of_eq {s₀ : State} {ys : List (List Byte)} {i : Nat} {s s' : State} (h : XI s₀ ys i s)
    (hg : s'.gpr = s.gpr) (hx : s'.xmm = s.xmm) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    XI s₀ ys i s' :=
  ⟨by rw [hg, h.esi], by rw [hg, h.edi], by rw [hg, h.ebx], by rw [hg, h.esp], by rw [hrd, h.rd],
    by rw [hwr, h.wr], by rw [hm]; exact h.frame, h.len, by rw [hm, h.data], by rw [hm, h.iv], by rw [hx, h.x0],
    by rw [hx, h.x6], by rw [hx, h.x7]⟩

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- The block at `esi + 16 j`, with `esi` at block `i`, is block `i + j`. -/
theorem UPre.esiA {i j : Nat} (hij : i + j < N s₀) {s : State} (hesi : s.gpr .esi = D32 s₀ i) :
    addr (s.gpr .esi) (16 * j) = blk s₀ (i + j) := by
  rw [← hp.dataA hij, hesi, addr, addr, D32, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]

omit hp in
theorem inBlk {k : Nat} (hk : k < N s₀) {rs : List Region} (h : dataR s₀ ∈ rs) : InRegions rs (blk s₀ k) 16 :=
  covBlk hk h _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

/-- `xorBlk`: the tweak in `t` XORed into block `i + j`. -/
theorem xorBlk_run {t : XReg} (ht : ¬ t = .xmm1) {i j : Nat} (hij : i + j < N s₀) {s : State}
    (hesi : s.gpr .esi = D32 s₀ i) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    ∃ s', runBlock isa (xorBlk t j) s = some s' ∧
      s'.mem = s.mem.writeW (blk s₀ (i + j)) (s.mem.readW (blk s₀ (i + j)) 128 ^^^ s.xmm t) ∧
      (∀ r, ¬ r = .xmm1 → s'.xmm r = s.xmm r) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain a := UPre.esiA hp hij hesi
  obtain rin : InRegions (s.rd ++ s.wr) (blk s₀ (i + j)) 16 := by
    rw [hrd, hwr, hp.rd, hp.wr]; exact inBlk hij (by simp)
  obtain win : InRegions s.wr (blk s₀ (i + j)) 16 := by
    rw [hwr, hp.wr]; exact inBlk hij (by simp)
  refine ⟨_, by
    simp only [xorBlk, runBlock_cons, runStep_some, runBlock_nil, exec, exec_bin, State.load128, State.store128,
      ea_at', gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, a, rin, win, ↓reduceIte, Option.map_some]
    rfl, ?_, fun r h => ?_, by rfl, by rfl, by rfl⟩
  · simp only [xmm_setXmm_self, xmm_setXmm_of_ne _ _ ht]; rfl
  · show ((s.setXmm .xmm1 _).setXmm .xmm1 _).xmm r = _
    rw [xmm_setXmm_of_ne _ _ h, xmm_setXmm_of_ne _ _ h]

omit hp in
/-- On to the next block: `esi` and the number of blocks left. -/
theorem next_run (s : State) :
    ∃ s', runBlock isa [.alu .add .esi (.imm 16), .alu .sub .edi (.imm 1)] s = some s' ∧
      s'.gpr .esi = s.gpr .esi + 16 ∧ s'.gpr .edi = s.gpr .edi - 1 ∧
      (∀ r, ¬ r = .esi → ¬ r = .edi → s'.gpr r = s.gpr r) ∧ s'.zf = some (s.gpr .edi - 1 == 0) ∧
      s'.xmm = s.xmm ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
    rfl, ?_, ?_, fun r h₁ h₂ => ?_, ?_, by rfl, by rfl, by rfl, by rfl⟩
  · simp only [gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags, reduceCtorEq, not_false_eq_true]
  · simp only [gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags, reduceCtorEq, not_false_eq_true]
  · simp only [gpr_setReg_of_ne _ _ h₁, gpr_setReg_of_ne _ _ h₂, gpr_arithFlags]
  · simp only [zf_setReg, zf_arithFlags, gpr_setReg_of_ne, gpr_arithFlags, reduceCtorEq, not_false_eq_true]

omit hp in
theorem UPre.dataBlk {j : Nat} (hj : j < N s₀) {r : Region} (hr : (dataR s₀).Disjoint r) :
    (⟨(Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint r :=
  hr.sub_left (UPre.data_sub hj)

omit hp in
theorem XI.big {ys : List (List Byte)} {i : Nat} {s : State} (h : XI s₀ ys i s) :
    Frame (Big s₀) s₀.mem s.mem :=
  UPre.big_of h.frame

omit hp in
theorem PInv.big {ys : List (List Byte)} {s : State} (h : PInv s₀ ys s) : Frame (Big s₀) s₀.mem s.mem :=
  UPre.big_of h.frame

omit hp in
theorem UPre.n_lt (s₀ : State) : N s₀ < 2 ^ 32 := (arg s₀ 4).isLt

/-- The memory after the tweak of block `k` is XORed into it. -/
theorem xorMem {ys : List (List Byte)} {k : Nat} (hk : k < N s₀) {m m' : Mem} {x : BitVec 128}
    (hf : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) m)
    (hlen : ys.length = N s₀)
    (hd : Spec.Cbc.blocksAt m ((Dp s₀).setWidth 64) (N s₀) = xored (iv0 s₀) ys k)
    (hiv : bytesAt m ((Iv s₀).setWidth 64) 16 = iv0 s₀) (hx : bx x = Spec.Xts.next (iv0 s₀) k)
    (hm : m' = m.writeW (blk s₀ k) (m.readW (blk s₀ k) 128 ^^^ x)) :
    Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) m' ∧
      Spec.Cbc.blocksAt m' ((Dp s₀).setWidth 64) (N s₀) = xored (iv0 s₀) ys (k + 1) ∧
      bytesAt m' ((Iv s₀).setWidth 64) 16 = iv0 s₀ := by
  obtain hy : k < ys.length := by rw [hlen]; exact hk
  obtain blkK : bytesAt m (blk s₀ k) 16 = ys[k] := by
    have := congrArg (·[k]?) hd
    rw [xored_getElem _ hy, List.getElem?_eq_getElem (by rw [length_blocksAt]; exact hk),
      getElem_blocksAt _ _ hk, List.getElem?_eq_getElem hy] at this
    exact Option.some.inj this
  obtain f₁ : Frame [⟨blk s₀ k, 16⟩] m m' := by
    rw [hm]
    exact (Frame.refl _ _).writeW (r := ⟨_, 16⟩) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] m m' :=
    f₁.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl)
  obtain newBlk : bytesAt m' (blk s₀ k) 16 = Spec.Cbc.xor ys[k] (Spec.Xts.next (iv0 s₀) k) := by
    rw [hm, bytesAt_writeW_bx, bx_xor, ← bytesAt_bx, blkK, hx]
  exact ⟨hf.trans (stepFrame hk fStep), by rw [hp.blocksAt_step hk fStep, hd, newBlk, xored_step _ hy],
    by rw [bytesAt_frame f₁ (one (hp.blk_iv hk).symm) (by decide), hiv]⟩

/-- One block of a pass. -/
theorem sstep_wp {ys : List (List Byte)} {i : Nat} (hi : i < N s₀) {s : State} (h : XI s₀ ys i s) :
    WP isa (.block singleBody) s fun s' => XI s₀ ys (i + 1) s' ∧ s'.zf = some (decide (i + 1 = N s₀)) := by
  obtain ⟨u₁, run₁, m₁, x₁, g₁, rd₁, wr₁⟩ :=
    xorBlk_run hp (t := .xmm0) (by decide) (i := i) (j := 0) hi h.esi h.rd h.wr
  rw [Nat.add_zero] at m₁
  obtain ⟨u₂, run₂, t₂, x₂, g₂, m₂, rd₂, wr₂⟩ := mulX_run (t := .xmm0) (by decide) (by decide) (by decide) u₁
    (by rw [x₁ _ (by decide), h.x6]) (by rw [x₁ _ (by decide), h.x7])
  obtain ⟨u₃, run₃, si₃, di₃, g₃, z₃, x₃, m₃, rd₃, wr₃⟩ := next_run u₂
  obtain ⟨l₁, l₂⟩ := left_step (UPre.n_lt s₀) hi
  refine WP.of_runBlock ⟨u₃, runBlock_app_of (runBlock_app_of run₁ run₂) run₃, ?_, ?_⟩
  swap
  · rw [z₃, g₂, g₁, h.edi, l₂]
  obtain mem₃ : u₃.mem = s.mem.writeW (blk s₀ i) (s.mem.readW (blk s₀ i) 128 ^^^ s.xmm .xmm0) := by
    rw [m₃, m₂, m₁]
  obtain ⟨fr, dat, iv⟩ := xorMem hp hi h.frame h.len h.data h.iv h.x0 mem₃
  refine ⟨?_, ?_, ?_, ?_, by rw [rd₃, rd₂, rd₁, h.rd], by rw [wr₃, wr₂, wr₁, h.wr], fr, h.len, dat, iv, ?_, ?_, ?_⟩
  · rw [si₃, g₂, g₁, h.esi, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl,
      Offset.add_add_eq _ (c := 16 * (i + 1)) (by omega_using [])]
  · rw [di₃, g₂, g₁, h.edi, l₁]
  · rw [g₃ _ (by decide) (by decide), g₂, g₁, h.ebx]
  · rw [g₃ _ (by decide) (by decide), g₂, g₁, h.esp]
  · rw [x₃, t₂, bx_alphaX, x₁ _ (by decide), h.x0]; rfl
  · rw [x₃, x₂ _ (by decide) (by decide), x₁ _ (by decide), h.x6]
  · rw [x₃, x₂ _ (by decide) (by decide), x₁ _ (by decide), h.x7]

/-- The blocks, one at a time. -/
theorem single_wp {ys : List (List Byte)} {i₀ : Nat} (hi₀ : i₀ < N s₀) {s : State} (h : XI s₀ ys i₀ s) :
    WP isa (.loop (.block singleBody) .ne) s (XI s₀ ys (N s₀)) := by
  refine WP.loop (M := isa) (body := .block singleBody) (c := .ne) (Q := XI s₀ ys (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ XI s₀ ys j t) ?_ (N s₀ - i₀) s
    ⟨i₀, rfl, hi₀, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (sstep_wp hp hk h) fun s' ⟨h', hz⟩ => ?_
  obtain ev : isa.eval .ne s' = some !decide (k + 1 = N s₀) := by
    show VG.X86.eval .ne s' = _; rw [eval_ne, hz]; rfl
  by_cases hz' : k + 1 = N s₀
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [← hz']
  · right
    refine ⟨by rw [ev]; simp [hz'], N s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hk, hz'], h'⟩

omit hp in
theorem passPro_eq : passPro = .mov .esi (argOp 3) :: .mov .ebx (argOp 2) :: .mov .edi (argOp 4) ::
    (consts ++ ([.movdquLoad .xmm0 (at_ .ebx 0)] : List Instr)) := by
  simp only [passPro, List.append_assoc]; rfl

omit hp in
/-- The constants, and the tweak loaded. -/
theorem constsLd_run {s : State} {Q : Addr} (ha : addr (s.gpr .ebx) 0 = Q) (hin : InRegions (s.rd ++ s.wr) Q 16) :
    ∃ s', runBlock isa (consts ++ ([.movdquLoad .xmm0 (at_ .ebx 0)] : List Instr)) s = some s' ∧
      s'.xmm .xmm0 = s.mem.readW Q 128 ∧ s'.xmm .xmm6 = onesX ∧ s'.xmm .xmm7 = cX ∧
      (∀ r, ¬ r = .eax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [consts, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      exec_bin, exec_shift, exec_pshufd, exec_movd, State.load128, ea_at', gpr_setXmm, mem_setXmm, rd_setXmm,
      wr_setXmm, gpr_setReg_of_ne, mem_setReg, rd_setReg, wr_setReg, reduceCtorEq, not_false_eq_true, ha, hin,
      ↓reduceIte, Option.map_some]
    rfl, ?_, ?_, ?_, fun r h => ?_, by rfl, by rfl, by rfl⟩
  · simp only [xmm_setXmm_self]
  · simp only [xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg, gpr_setReg_self, reduceCtorEq, not_false_eq_true]
    decide
  · simp only [xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg, gpr_setReg_self, reduceCtorEq, not_false_eq_true,
      eval_movdqa]
    decide
  · simp only [gpr_setXmm, gpr_setReg_of_ne _ _ h]

/-- The start of a pass. -/
theorem passPro_wp {ys : List (List Byte)} {s : State} (h : PInv s₀ ys s) :
    WP isa (.block passPro) s (XI s₀ ys 0) := by
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  obtain hargs := hp.args_of h.big
  have hiv := hp.iv_fit
  rw [passPro_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (hargs 3 (by decide)) fun s₁ u₁ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), h.esp])
    (by rw [u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide)) (by rw [u₁.mem]; exact hargs 2 (by decide))
    fun s₂ u₂ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₂.mem, u₁.mem]; exact hargs 4 (by decide)) fun s₃ u₃ => ?_
  obtain b₃ : s₃.gpr .ebx = Iv s₀ := by rw [u₃.other _ (by decide), u₂.gpr]
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, u₂.rd, u₁.rd, h.rd]
  obtain wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]
  obtain ⟨s₄, run₄, x0₄, x6₄, x7₄, g₄, m₄, rd₄, wr₄⟩ := constsLd_run (s := s₃) (Q := (Iv s₀).setWidth 64)
    (by rw [b₃, addr_eq (by omega_using [hiv]), add0])
    (by rw [rd₃, wr₃, hp.rd, hp.wr]
        exact covIv (by simp) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, by rw [rd₄, rd₃], by rw [wr₄, wr₃], by rw [m₄, m₃]; exact h.frame, h.len, ?_, ?_, ?_,
    x6₄, x7₄⟩
  · rw [g₄ _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; simp [D32]
  · rw [g₄ _ (by decide), u₃.gpr, Nat.sub_zero]; exact arg_ofNat s₀ 4
  · rw [g₄ _ (by decide), b₃]
  · rw [g₄ _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.esp]
  · rw [m₄, m₃, h.data, xored_zero]
  · rw [m₄, m₃, h.iv]
  · rw [x0₄, m₃, ← bytesAt_bx, h.iv]; rfl

/-! ## Eight blocks at a time -/

/-- One block of eight. -/
theorem octStep_run {ys : List (List Byte)} {i j : Nat} (hij : i + j < N s₀) {s : State} (h : OI s₀ ys i j s) :
    ∃ s', runBlock isa (octStep j) s = some s' ∧ OI s₀ ys i (j + 1) s' := by
  obtain ⟨u₁, run₁, m₁, x₁, g₁, rd₁, wr₁⟩ := xorBlk_run hp (t := .xmm4) (by decide) hij h.esi h.rd h.wr
  obtain ⟨u₂, run₂, t₂, x₂, g₂, m₂, rd₂, wr₂⟩ := mulX_run (t := .xmm4) (by decide) (by decide) (by decide) u₁
    (by rw [x₁ _ (by decide), h.x6]) (by rw [x₁ _ (by decide), h.x7])
  obtain ⟨fr, dat, iv⟩ := xorMem hp hij h.frame h.len h.data h.iv h.x4 m₁
  exact ⟨u₂, runBlock_app_of run₁ run₂, by rw [g₂, g₁, h.esi], by rw [g₂, g₁, h.edi], by rw [g₂, g₁, h.ebx],
    by rw [g₂, g₁, h.esp], by rw [rd₂, rd₁, h.rd], by rw [wr₂, wr₁, h.wr], by rw [m₂]; exact fr, h.len,
    by rw [m₂]; exact dat, by rw [m₂]; exact iv,
    by rw [x₂ _ (by decide) (by decide), x₁ _ (by decide), h.x0],
    by rw [t₂, bx_alphaX, x₁ _ (by decide), h.x4]; rfl,
    by rw [x₂ _ (by decide) (by decide), x₁ _ (by decide), h.x6],
    by rw [x₂ _ (by decide) (by decide), x₁ _ (by decide), h.x7]⟩

/-- `k` blocks of eight, from block `j` of them. -/
theorem octSteps_run {ys : List (List Byte)} {i : Nat} : ∀ (k j : Nat) {s : State}, i + j + k ≤ N s₀ →
    OI s₀ ys i j s → ∃ s', runBlock isa (octSteps j k) s = some s' ∧ OI s₀ ys i (j + k) s'
  | 0, _, s, _, h => ⟨s, runBlock_nil, h⟩
  | k + 1, j, s, hk, h => by
    obtain ⟨u, run, h'⟩ := octStep_run hp (by omega_using [hk]) h
    obtain ⟨u', run', h''⟩ := octSteps_run k (j + 1) (by omega_using [hk]) h'
    exact ⟨u', runBlock_app_of run run', by rw [show j + (k + 1) = j + 1 + k by omega_arith]; exact h''⟩

/-- Eight blocks. -/
theorem oct_wp {ys : List (List Byte)} {i : Nat} (hi : i + 8 ≤ N s₀) {s : State} (h : XI s₀ ys i s) :
    WP isa (.block octBody) s fun s' => XI s₀ ys (i + 8) s' ∧ s'.cf = some (decide (N s₀ - (i + 8) < 8)) := by
  have hn := UPre.n_lt s₀
  obtain run₁ : runBlock isa [.xop (.bin .movdqa .xmm4 .xmm0)] s = some (s.setXmm .xmm4 (s.xmm .xmm0)) := by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, exec_bin, eval_movdqa]
  obtain h₁ : OI s₀ ys i 0 (s.setXmm .xmm4 (s.xmm .xmm0)) :=
    ⟨h.esi, h.edi, h.ebx, h.esp, h.rd, h.wr, h.frame, h.len, h.data,
      h.iv, by rw [xmm_setXmm_of_ne _ _ (by decide)]; exact h.x0, by rw [xmm_setXmm_self]; exact h.x0,
      by rw [xmm_setXmm_of_ne _ _ (by decide)]; exact h.x6, by rw [xmm_setXmm_of_ne _ _ (by decide)]; exact h.x7⟩
  obtain ⟨u₂, run₂, h₂⟩ := octSteps_run hp 7 0 (by omega_using [hi]) h₁
  obtain ⟨u₃, run₃, m₃, x₃, g₃, rd₃, wr₃⟩ :=
    xorBlk_run hp (t := .xmm4) (by decide) (i := i) (j := 7) (by omega_using [hi]) h₂.esi h₂.rd h₂.wr
  obtain ⟨fr, dat, iv⟩ := xorMem hp (by omega_using [hi]) h₂.frame h₂.len h₂.data h₂.iv h₂.x4 m₃
  obtain ⟨u₄, run₄, t₄, x₄, g₄, m₄, rd₄, wr₄⟩ := mul8_run u₃
  obtain ⟨u₅, run₅, si₅, di₅, g₅, c₅, x₅, m₅, rd₅, wr₅⟩ := next8_run u₄
  obtain l := left_step8 hn hi
  refine WP.of_runBlock ⟨u₅,
    runBlock_app_of (runBlock_app_of (runBlock_app_of (runBlock_app_of run₁ run₂) run₃) run₄) run₅, ?_, ?_⟩
  swap
  · rw [c₅, g₄, g₃, h₂.edi, l, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn])]
  refine ⟨?_, ?_, ?_, ?_, by rw [rd₅, rd₄, rd₃, h₂.rd], by rw [wr₅, wr₄, wr₃, h₂.wr], by rw [m₅, m₄]; exact fr,
    h.len, by rw [m₅, m₄]; exact dat, by rw [m₅, m₄]; exact iv, ?_, ?_, ?_⟩
  · rw [si₅, g₄, g₃, h₂.esi, show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl,
      Offset.add_add_eq _ (c := 16 * (i + 8)) (by omega_using [])]
  · rw [di₅, g₄, g₃, h₂.edi, l]
  · rw [g₅ _ (by decide) (by decide), g₄, g₃, h₂.ebx]
  · rw [g₅ _ (by decide) (by decide), g₄, g₃, h₂.esp]
  · rw [x₅, t₄, bx_iter8, x₃ _ (by decide), h₂.x0]; rfl
  · rw [x₅, x₄ _ (by decide) (by decide), x₃ _ (by decide), h₂.x6]
  · rw [x₅, x₄ _ (by decide) (by decide), x₃ _ (by decide), h₂.x7]

/-- The blocks, eight at a time while eight are left. -/
theorem octs_wp {ys : List (List Byte)} (h8 : 8 ≤ N s₀) {s : State} (h : XI s₀ ys 0 s) :
    WP isa (.loop (.block octBody) .ae) s fun s' => ∃ i, i ≤ N s₀ ∧ N s₀ - i < 8 ∧ XI s₀ ys i s' := by
  refine WP.loop (M := isa) (body := .block octBody) (c := .ae)
    (Q := fun s' => ∃ i, i ≤ N s₀ ∧ N s₀ - i < 8 ∧ XI s₀ ys i s')
    (fun (n : Nat) (t : State) => ∃ i, n = N s₀ - i ∧ i + 8 ≤ N s₀ ∧ XI s₀ ys i t) ?_ (N s₀ - 0) s
    ⟨0, rfl, h8, h⟩
  rintro n s ⟨i, rfl, hi, h⟩
  refine WP.mono (oct_wp hp hi h) fun s' ⟨h', hc⟩ => ?_
  obtain ev : isa.eval .ae s' = some !decide (N s₀ - (i + 8) < 8) := by
    show s'.cf.map (!·) = _; rw [hc]; rfl
  by_cases hlt : N s₀ - (i + 8) < 8
  · left
    exact ⟨by rw [ev]; simp [hlt], i + 8, hi, hlt, h'⟩
  · right
    exact ⟨by rw [ev]; simp [hlt], N s₀ - (i + 8), by omega_using [hi], i + 8, rfl, by omega_using [hlt], h'⟩

omit hp in
/-- `cmp edi, 8`, before the blocks. -/
theorem cmp8_wp {ys : List (List Byte)} {s : State} (h : XI s₀ ys 0 s) :
    WP isa (.block [.alu .cmp .edi (.imm 8)]) s fun s' => XI s₀ ys 0 s' ∧ s'.cf = some (decide (N s₀ < 8)) := by
  have hn := UPre.n_lt s₀
  obtain ⟨s₁, run₁, c₁, g₁, x₁, m₁, rd₁, wr₁⟩ := cmp8_run s
  exact WP.of_runBlock ⟨s₁, run₁, XI.of_eq h g₁ x₁ m₁ rd₁ wr₁, by
    rw [c₁, h.edi, Nat.sub_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]⟩

omit hp in
/-- `test edi, edi`, after the blocks taken eight at a time. -/
theorem test_wp {ys : List (List Byte)} {i : Nat} (hi : i ≤ N s₀) {s : State} (h : XI s₀ ys i s) :
    WP isa (.block [.alu .test .edi (.reg .edi)]) s fun s' => XI s₀ ys i s' ∧ s'.zf = some (decide (i = N s₀)) := by
  have hn := UPre.n_lt s₀
  obtain ⟨s₁, run₁, z₁, g₁, x₁, m₁, rd₁, wr₁⟩ := test_run s
  refine WP.of_runBlock ⟨s₁, run₁, XI.of_eq h g₁ x₁ m₁ rd₁ wr₁, ?_⟩
  rw [z₁, h.edi, BitVec.and_self]
  refine congrArg some ?_
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn])]
  show N s₀ - i = 0 ↔ _
  omega_using [hi]

/-- The blocks eight at a time, if there are eight. -/
theorem octIte_wp {ys : List (List Byte)} {s : State} (h : XI s₀ ys 0 s) (hc : s.cf = some (decide (N s₀ < 8))) :
    WP isa (.ite .b (.block []) (.loop (.block octBody) .ae)) s
      fun s' => ∃ i, i ≤ N s₀ ∧ N s₀ - i < 8 ∧ XI s₀ ys i s' := by
  have ev : isa.eval .b s = some (decide (N s₀ < 8)) := hc
  by_cases h8 : N s₀ < 8
  · exact WP.ite true (by rw [ev]; simp [h8]) (fun _ => WP.block_nil ⟨0, Nat.zero_le _, h8, h⟩)
      (fun h => by cases h)
  · exact WP.ite false (by rw [ev]; simp [h8]) (fun h => by cases h) fun _ => octs_wp hp (by omega_using [h8]) h

/-- The blocks left, one at a time. -/
theorem tailIte_wp {ys : List (List Byte)} {i : Nat} (hi : i ≤ N s₀) {s : State} (h : XI s₀ ys i s)
    (hz : s.zf = some (decide (i = N s₀))) :
    WP isa (.ite .e (.block []) (.loop (.block singleBody) .ne)) s (XI s₀ ys (N s₀)) := by
  have ev : isa.eval .e s = some (decide (i = N s₀)) := hz
  by_cases he : i = N s₀
  · exact WP.ite true (by rw [ev]; simp [he]) (fun _ => WP.block_nil (he ▸ h)) (fun h => by cases h)
  · exact WP.ite false (by rw [ev]; simp [he]) (fun h => by cases h) fun _ =>
      single_wp hp (by omega_using [hi, he]) h

/-- A whole pass. -/
theorem pass_wp {ys : List (List Byte)} {s : State} (h : PInv s₀ ys s) : WP isa pass s (XI s₀ ys (N s₀)) :=
  WP.seq (WP.mono (passPro_wp hp h) fun _ h₁ =>
    WP.seq (WP.mono (cmp8_wp h₁) fun _ ⟨h₂, c₂⟩ =>
      WP.seq (WP.mono (octIte_wp hp h₂ c₂) fun _ ⟨_, hi, _, h₃⟩ =>
        WP.seq (WP.mono (test_wp hi h₃) fun _ ⟨h₄, z₄⟩ => tailIte_wp hp hi h₄ z₄))))

/-- The arguments of the block function on all the blocks. -/
theorem UPre.bcall {s : State} (eax : s.gpr .eax = W s₀) (ecx : s.gpr .ecx = arg s₀ 1)
    (edx : s.gpr .edx = Dp s₀) (ebx : s.gpr .ebx = arg s₀ 4) (ebp : s.gpr .ebp = S s₀)
    (esp : s.gpr .esp = E s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    Proof.AesOcb.X86.BCall s (W s₀) (Dp s₀) (S s₀) (R s₀) (N s₀) := by
  obtain hb : below (s.gpr .esp) 24 = stkR s₀ := by rw [esp]; exact hp.below_eq
  have hdf := hp.data_fit
  refine ⟨eax, by rw [ecx]; exact arg_ofNat s₀ 1, edx, by rw [ebx]; exact arg_ofNat s₀ 4, ebp, hp.rounds,
    by rw [esp]; exact hp.esp24, hp.sch_data, hp.sch_scr.sub_right (Region.sub_prefix (by decide)),
    hp.data_scr.sub_right (Region.sub_prefix (by decide)), by rw [hb]; exact hp.b_sch, by rw [hb]; exact hp.b_data,
    by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide)), hp.sch_fit, hdf,
    by have := hp.scr_fit; omega_using [this], ?_, ?_⟩
  · rw [hrd, hwr, hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨dataR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

omit hp in
theorem callArgs_eq : callArgs = [.mov .eax (argOp 0), .mov .ecx (argOp 1), .mov .edx (argOp 3),
    .mov .ebx (argOp 4), .mov .ebp (argOp 5)] := rfl

/-- After a pass, the arguments of the block function. -/
theorem callArgs_wp {ys : List (List Byte)} {s : State} (h : XI s₀ ys (N s₀) s) :
    WP isa (.block callArgs) s fun s' =>
      Proof.AesOcb.X86.BCall s' (W s₀) (Dp s₀) (S s₀) (R s₀) (N s₀) ∧
      PInv s₀ (xored (iv0 s₀) ys (N s₀)) s' := by
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  obtain hargs := hp.args_of h.big
  rw [callArgs_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (hargs 0 (by decide)) fun s₁ u₁ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), h.esp])
    (by rw [u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide)) (by rw [u₁.mem]; exact hargs 1 (by decide))
    fun s₂ u₂ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₂.mem, u₁.mem]; exact hargs 3 (by decide)) fun s₃ u₃ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₃.mem, u₂.mem, u₁.mem]; exact hargs 4 (by decide)) fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact hargs 5 (by decide)) fun s₅ u₅ => WP.block_nil ?_
  obtain mem₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  obtain wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  obtain esp₅ : s₅.gpr .esp = E s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.esp]
  have hlen : ys.length = N s₀ := h.len
  exact ⟨UPre.bcall hp
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr])
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr])
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr])
    (by rw [u₅.other _ (by decide), u₄.gpr]) u₅.gpr esp₅ rd₅ wr₅,
    esp₅, rd₅, wr₅, by rw [mem₅]; exact h.frame,
    by rw [length_xored _ _ _ (by omega_using [hlen]), hlen], by rw [mem₅, h.data], by rw [mem₅, h.iv]⟩

/-- The call of the block function on all the blocks. -/
theorem call_wp (enc : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {b : Impl.Aes.X86.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (nosp : NoSp b.code) (stack : stackUse b.code = 0)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16))
    {ys : List (List Byte)} {s : State}
    (hc : Proof.AesOcb.X86.BCall s (W s₀) (Dp s₀) (S s₀) (R s₀) (N s₀)) (h : PInv s₀ ys s) :
    WP isa (Impl.AesOcb.X86.blocksFrame ⟨b.name, b.code⟩) s
      (PInv s₀ (ys.map (ciphOf enc (R s₀) (wK s₀)))) := by
  refine WP.mono (Proof.AesOcb.X86.blk_call (fn := ⟨b.name, b.code⟩) ok nosp stack hc) fun s' c => ?_
  obtain hb : below (s.gpr .esp) 24 = stkR s₀ := by rw [h.esp]; exact hp.below_eq
  obtain fr : Frame [dataR s₀, ⟨(S s₀).setWidth 64, 2048⟩, stkR s₀] s.mem s'.mem := by
    have := c.frame; rw [hb] at this; exact this
  obtain fCall : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s'.mem :=
    fr.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨dataR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  obtain dIv : ∀ r ∈ [dataR s₀, ⟨(S s₀).setWidth 64, 2048⟩, stkR s₀], (ivR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.iv_data
    · exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))
    · exact hp.b_iv.symm
  obtain sched : bytesAt s.mem (w64 (W s₀)) (16 * (R s₀ + 1)) = wK s₀ := UPre.sched_bytes hp h.big
  refine ⟨by rw [c.saved .esp (by simp [calleeSaved]), h.esp], by rw [c.rd, h.rd], by rw [c.wr, h.wr],
    h.frame.trans fCall, by simp [h.len], ?_, ?_⟩
  · rw [blocksAt_of_out c.out (fun p => hf _ _ _ p), h.data, sched]
  · rw [bytesAt_frame fr dIv (by decide), h.iv]

omit hp in
theorem storeT_run {s : State} {Q : Addr} (ha : addr (s.gpr .ebx) 0 = Q) (hin : InRegions s.wr Q 16) :
    ∃ s', runBlock isa storeT s = some s' ∧ s'.mem = s.mem.writeW Q (s.xmm .xmm0) ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨_, by
    simp only [storeT, runBlock_cons, runStep_some, runBlock_nil, exec, State.store128, ea_at', ha, hin, ↓reduceIte]
    rfl, by rfl, by rfl, by rfl, by rfl⟩

/-- After the second pass, the tweak stored: XTS of all the blocks
(`AesXts.crypt_eq`). -/
theorem storeT_wp (enc : Bool) {s : State}
    (h : XI s₀ ((xored (iv0 s₀) (blks s₀) (N s₀)).map (ciphOf enc (R s₀) (wK s₀))) (N s₀) s) :
    WP isa (.block storeT) s (LInv (AesXts.xtsMode enc) s₀ (N s₀)) := by
  have hiv := hp.iv_fit
  obtain ⟨s₁, run₁, m₁, g₁, rd₁, wr₁⟩ := storeT_run (s := s) (Q := (Iv s₀).setWidth 64)
    (by rw [h.ebx, addr_eq (by omega_using [hiv]), add0])
    (by rw [h.wr, hp.wr]; exact covIv (by simp) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain fT : Frame [ivR s₀] s.mem s₁.mem := by
    rw [m₁]
    exact (Frame.refl _ _).writeW (r := ⟨_, 16⟩) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain hl : (blks s₀).length = N s₀ := by simp [Spec.Cbc.blocksAt]
  obtain ce := crypt_eq (ciphOf enc (R s₀) (wK s₀)) (iv0 s₀) (blks s₀)
  rw [hl] at ce
  exact { esi := by rw [g₁, h.esi], esp := by rw [g₁, h.esp], rd := by rw [rd₁, h.rd], wr := by rw [wr₁, h.wr]
          frame := h.frame.trans (fT.sub fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact ⟨ivR s₀, by simp, fun _ h => h⟩)
          data := by
            rw [blocksAt_frame fT (fun j hj r hr => by
              simp only [List.mem_singleton] at hr; subst hr
              exact UPre.dataBlk hj hp.iv_data.symm), h.data, xored_all _ h.len, xored_all _ hl, ce, outK,
              AesXts.xtsMode_out, List.take_of_length_le (by omega_using [hl]),
              List.drop_of_length_le (by omega_using [hl]), List.append_nil]
          iv := by
            rw [m₁, bytesAt_writeW_bx, h.x0, chainK, AesXts.xtsMode_chain,
              List.take_of_length_le (by omega_using [hl]), hl] }

omit hp in
/-- Before the first pass. -/
theorem PInv.of_linv {M : Mode} (hM : ∀ R w t, M.chain R w t [] = t) (hO : ∀ R w t, M.out R w t [] = [])
    {s : State} (h : LInv M s₀ 0 s) : PInv s₀ (blks s₀) s :=
  ⟨h.esp, h.rd, h.wr, h.frame, by simp [Spec.Cbc.blocksAt], by rw [h.data]; simp [outK, hO],
    by rw [h.iv]; simp [chainK, hM]⟩

/-- All the blocks. -/
theorem batch_wp (enc : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {b : Impl.Aes.X86.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (nosp : NoSp b.code) (stack : stackUse b.code = 0)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16))
    {s : State} (h : LInv (AesXts.xtsMode enc) s₀ 0 s) :
    WP isa (batch b) s (LInv (AesXts.xtsMode enc) s₀ (N s₀)) :=
  WP.seq (WP.mono (pass_wp hp (PInv.of_linv (fun _ _ _ => rfl) (fun _ _ _ => rfl) h)) fun _ h₂ =>
    WP.seq (WP.mono (callArgs_wp hp h₂) fun _ ⟨c₃, h₃⟩ =>
      WP.seq (WP.mono (call_wp hp enc ok nosp stack hf c₃ h₃) fun _ h₄ =>
        WP.seq (WP.mono (pass_wp hp h₄) fun _ h₅ => storeT_wp hp enc h₅))))

end

/-- The whole function. -/
theorem crypt_wp (enc : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {b : Impl.Aes.X86.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (nosp : NoSp b.code) (stack : stackUse b.code = 0)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16))
    {s₀ : State} (h0 : (modeX86 (AesXts.xtsMode enc)).pre s₀) :
    WP isa (crypt b) s₀ fun s' => abiPreserved s₀ s' ∧ (modeX86 (AesXts.xtsMode enc)).post s₀ s' :=
  ends_wp h0 fun hp _ _ h => batch_wp hp enc ok nosp stack hf h

end VG.Proof.AesXts.X86

end

end

/-!
# XTS-AES on x86: constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`), as AES-CBC's are (`Proof/AesCbc/X86/CT.lean`): the taint
analysis that follows the SSE instructions (`sseTaint`) covers the code
around the call, from `esp`, the stack arguments, and in a pass `esi`, `edi`
and `ebx` (which the correctness proof pins to the public arguments, `XI`),
and the call of the block function on all the blocks, in its frame, is
constant time by its own proof (AES-OCB's `blk_ct`).
-/

@[expose] public section

namespace VG.Proof.AesXts.X86

open VG VG.X86 VG.Impl.AesXts.X86
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.X86
open VG.Proof.MdStream.X86 (eval_ne)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesXts (xored)

/-- A piece of code the taint analysis checks from the registers `rs`, `esp`
and the stack arguments, which agree in two runs, with what each run
reaches. -/
theorem taint_rel {P : State → State → Prop} {c : Prog isa} {F₁ F₂ : State → Prop} (rs : List Reg)
    (ht : ∃ h, (sseTaint.check (argTaint rs (4 + 4 * 6)) c h).isSome = true)
    (ha : ∀ s₁ s₂, P s₁ s₂ → VG.X86.Taint.Agree (argTaint rs (4 + 4 * 6)) s₁ s₂)
    (hw : ∀ s₁ s₂, P s₁ s₂ → WP isa c s₁ F₁ ∧ WP isa c s₂ F₂) :
    RelCT isa P c fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂ := by
  obtain ⟨_, ht⟩ := ht
  exact ((RelCT.taint (A := sseTaint) (P := P) _ ha ht).wp hw).mono (fun _ _ h => h) fun _ _ h => h.2

theorem passPro_taint : ∃ h, (sseTaint.check (argTaint [] (4 + 4 * 6)) (.block passPro) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem singleBody_taint :
    ∃ h, (sseTaint.check (argTaint [.esi, .edi] (4 + 4 * 6)) (.block singleBody) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem callArgs_taint : ∃ h, (sseTaint.check (argTaint [] (4 + 4 * 6)) (.block callArgs) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem storeT_taint : ∃ h, (sseTaint.check (argTaint [.ebx] (4 + 4 * 6)) (.block storeT) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cmp8_taint : ∃ h, (sseTaint.check (argTaint [.esi, .edi] (4 + 4 * 6))
    (.block [.alu .cmp .edi (.imm 8)]) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem test_taint : ∃ h, (sseTaint.check (argTaint [.esi, .edi] (4 + 4 * 6))
    (.block [.alu .test .edi (.reg .edi)]) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem octBody_taint :
    ∃ h, (sseTaint.check (argTaint [.esi, .edi] (4 + 4 * 6)) (.block octBody) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem nil_taint : ∃ h, (sseTaint.check (argTaint [.esi, .edi] (4 + 4 * 6)) (.block []) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem XI.pt {s₀ : State} (hp : UPre s₀) {ys : List (List Byte)} {i : Nat} {s : State}
    (h : XI s₀ ys i s) : Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep h.big hi⟩

theorem PInv.pt {s₀ : State} (hp : UPre s₀) {ys : List (List Byte)} {s : State} (h : PInv s₀ ys s) : Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep h.big hi⟩

section
variable {enc : Bool} {s₀ s₀' : State} (hq : (modeX86 (AesXts.xtsMode enc)).pub s₀ s₀')
include hq

theorem XI.agree (hp : UPre s₀) (hp' : UPre s₀') {ys ys' : List (List Byte)} {i : Nat} {s₁ s₂ : State}
    (h₁ : XI s₀ ys i s₁) (h₂ : XI s₀' ys' i s₂) :
    VG.X86.Taint.Agree (argTaint [.esi, .edi] (4 + 4 * 6)) s₁ s₂ :=
  Pt.agree hq hp hp' (h₁.pt hp) (h₂.pt hp') fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.esi, h₂.esi, pub_D32 hq]
    · rw [h₁.edi, h₂.edi, pub_N hq]

/-- The blocks one at a time, in two runs: the taint analysis checks each
iteration. -/
theorem single_rel (hp : UPre s₀) (hp' : UPre s₀') {i₀ : Nat} (hi₀ : i₀ < N s₀) {ys ys' : List (List Byte)} :
    RelCT isa (fun a b => XI s₀ ys i₀ a ∧ XI s₀' ys' i₀ b) (.loop (.block singleBody) .ne)
      fun a b => XI s₀ ys (N s₀) a ∧ XI s₀' ys' (N s₀') b := by
  have hN' := pub_N hq
  let L (n : Nat) (s₁ s₂ : State) : Prop :=
    ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ XI s₀ ys k s₁ ∧ XI s₀' ys' k s₂
  refine (RelCT.loop (M := isa) L (fun n => ?_) (N s₀ - i₀)).mono
    (fun _ _ h => ⟨i₀, rfl, hi₀, h.1, h.2⟩) fun _ _ h => h
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : L n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k < N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have ct := taint_rel [.esi, .edi] singleBody_taint
    (P := fun a b => N s₀ - k = N s₀ - k ∧ k < N s₀ ∧ XI s₀ ys k a ∧ XI s₀' ys' k b)
    (fun _ _ h => XI.agree hq hp hp' h.2.2.1 h.2.2.2)
    (F₁ := fun (s : State) => XI s₀ ys (k + 1) s ∧ s.zf = some (decide (k + 1 = N s₀)))
    (F₂ := fun (s : State) => XI s₀' ys' (k + 1) s ∧ s.zf = some (decide (k + 1 = N s₀')))
    fun _ _ h => ⟨sstep_wp hp hk h.2.2.1, sstep_wp hp' (by rw [← hN']; exact hk) h.2.2.2⟩
  refine ct.mono (fun _ _ h => h) fun s₁ s₂ ⟨⟨l₁, z₁⟩, ⟨l₂, z₂⟩⟩ => ?_
  have e₁ : isa.eval .ne s₁ = some !decide (k + 1 = N s₀) := by
    show VG.X86.eval .ne s₁ = _; rw [eval_ne, z₁]; rfl
  have e₂ : isa.eval .ne s₂ = some !decide (k + 1 = N s₀) := by
    show VG.X86.eval .ne s₂ = _; rw [eval_ne, z₂, ← hN']; rfl
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : k + 1 = N s₀ := by simpa using hf
    exact ⟨h0 ▸ l₁, by rw [← hN', ← h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : k + 1 ≠ N s₀ := by simpa using ht
    exact ⟨N s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [hk, h0], l₁, l₂⟩

/-- The blocks eight at a time, in two runs: the taint analysis checks each
iteration. -/
theorem octs_rel (hp : UPre s₀) (hp' : UPre s₀') (h8 : 8 ≤ N s₀) {ys ys' : List (List Byte)} :
    RelCT isa (fun a b => XI s₀ ys 0 a ∧ XI s₀' ys' 0 b) (.loop (.block octBody) .ae)
      fun a b => ∃ i, i ≤ N s₀ ∧ N s₀ - i < 8 ∧ XI s₀ ys i a ∧ XI s₀' ys' i b := by
  have hN' := pub_N hq
  let L (n : Nat) (s₁ s₂ : State) : Prop :=
    ∃ k, n = N s₀ - k ∧ k + 8 ≤ N s₀ ∧ XI s₀ ys k s₁ ∧ XI s₀' ys' k s₂
  refine (RelCT.loop (M := isa) L (fun n => ?_) (N s₀ - 0)).mono
    (fun _ _ h => ⟨0, rfl, h8, h.1, h.2⟩) fun _ _ h => h
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : L n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k + 8 ≤ N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have ct := taint_rel [.esi, .edi] octBody_taint
    (P := fun a b => N s₀ - k = N s₀ - k ∧ k + 8 ≤ N s₀ ∧ XI s₀ ys k a ∧ XI s₀' ys' k b)
    (fun _ _ h => XI.agree hq hp hp' h.2.2.1 h.2.2.2)
    (F₁ := fun (s : State) => XI s₀ ys (k + 8) s ∧ s.cf = some (decide (N s₀ - (k + 8) < 8)))
    (F₂ := fun (s : State) => XI s₀' ys' (k + 8) s ∧ s.cf = some (decide (N s₀' - (k + 8) < 8)))
    fun _ _ h => ⟨oct_wp hp hk h.2.2.1, oct_wp hp' (by rw [← hN']; exact hk) h.2.2.2⟩
  refine ct.mono (fun _ _ h => h) fun s₁ s₂ ⟨⟨l₁, c₁⟩, ⟨l₂, c₂⟩⟩ => ?_
  have e₁ : isa.eval .ae s₁ = some !decide (N s₀ - (k + 8) < 8) := by
    show s₁.cf.map (!·) = _; rw [c₁]; rfl
  have e₂ : isa.eval .ae s₂ = some !decide (N s₀ - (k + 8) < 8) := by
    show s₂.cf.map (!·) = _; rw [c₂, ← hN']; rfl
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : N s₀ - (k + 8) < 8 := by simpa using hf
    exact ⟨k + 8, hk, h0, l₁, l₂⟩
  · rw [e₁] at ht
    have h0 : ¬ N s₀ - (k + 8) < 8 := by simpa using ht
    exact ⟨N s₀ - (k + 8), by omega_using [hk], k + 8, rfl, by omega_using [h0], l₁, l₂⟩

/-- A pass over the blocks, in two runs. -/
theorem pass_rel (hp : UPre s₀) (hp' : UPre s₀') {ys ys' : List (List Byte)} :
    RelCT isa (fun a b => PInv s₀ ys a ∧ PInv s₀' ys' b) pass
      fun a b => XI s₀ ys (N s₀) a ∧ XI s₀' ys' (N s₀') b := by
  have hN' := pub_N hq
  -- The start of the pass.
  have a := taint_rel [] passPro_taint (P := fun a b => PInv s₀ ys a ∧ PInv s₀' ys' b)
    (fun _ _ h => Pt.agree hq hp hp' (h.1.pt hp) (h.2.pt hp') fun r hr => by simp at hr)
    (F₁ := XI s₀ ys 0) (F₂ := XI s₀' ys' 0)
    fun _ _ h => ⟨passPro_wp hp h.1, passPro_wp hp' h.2⟩
  -- Are there eight blocks?
  have b := taint_rel [.esi, .edi] cmp8_taint (P := fun a b => XI s₀ ys 0 a ∧ XI s₀' ys' 0 b)
    (fun _ _ h => XI.agree hq hp hp' h.1 h.2)
    (F₁ := fun (s : State) => XI s₀ ys 0 s ∧ s.cf = some (decide (N s₀ < 8)))
    (F₂ := fun (s : State) => XI s₀' ys' 0 s ∧ s.cf = some (decide (N s₀' < 8)))
    fun _ _ h => ⟨cmp8_wp h.1, cmp8_wp h.2⟩
  -- Eight at a time.
  have c : RelCT isa (fun (a b : State) => (XI s₀ ys 0 a ∧ a.cf = some (decide (N s₀ < 8))) ∧
        XI s₀' ys' 0 b ∧ b.cf = some (decide (N s₀' < 8)))
      (.ite .b (.block []) (.loop (.block octBody) .ae))
      fun a b => ∃ i, i ≤ N s₀ ∧ N s₀ - i < 8 ∧ XI s₀ ys i a ∧ XI s₀' ys' i b := by
    refine RelCT.ite (fun s₁ s₂ h => ?_) ?_ ?_
    · show s₁.cf = s₂.cf
      rw [h.1.2, h.2.2, hN']
    · refine (taint_rel [.esi, .edi] nil_taint (fun _ _ h => XI.agree hq hp hp' h.1.1.1 h.1.2.1)
        (F₁ := fun (s : State) => N s₀ < 8 ∧ XI s₀ ys 0 s) (F₂ := XI s₀' ys' 0)
        fun s₁ _ h => ⟨WP.block_nil ⟨by
          have e : s₁.cf = some true := h.2
          rw [h.1.1.2] at e
          simpa using e, h.1.1.1⟩, WP.block_nil h.1.2.1⟩).mono (fun _ _ h => h)
        fun _ _ h => ⟨0, Nat.zero_le _, h.1.1, h.1.2, h.2⟩
    · by_cases h8 : 8 ≤ N s₀
      · exact (octs_rel hq hp hp' h8).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h
      · refine RelCT.of_false fun s₁ _ h => ?_
        have e : s₁.cf = some false := h.2
        rw [h.1.1.2] at e
        have : ¬ N s₀ < 8 := by simpa using e
        omega_using [h8, this]
  -- Are there blocks left?
  have d : RelCT isa (fun (a b : State) => ∃ i, i ≤ N s₀ ∧ N s₀ - i < 8 ∧ XI s₀ ys i a ∧ XI s₀' ys' i b)
      (.block [.alu .test .edi (.reg .edi)])
      fun a b => ∃ i, i ≤ N s₀ ∧ (XI s₀ ys i a ∧ a.zf = some (decide (i = N s₀))) ∧
        XI s₀' ys' i b ∧ b.zf = some (decide (i = N s₀')) :=
    RelCT.exists_ fun i => by
      by_cases hi : i ≤ N s₀
      swap
      · exact RelCT.of_false fun _ _ h => hi h.1
      exact (taint_rel [.esi, .edi] test_taint
        (P := fun a b => i ≤ N s₀ ∧ N s₀ - i < 8 ∧ XI s₀ ys i a ∧ XI s₀' ys' i b)
        (fun _ _ h => XI.agree hq hp hp' h.2.2.1 h.2.2.2)
        (F₁ := fun (s : State) => XI s₀ ys i s ∧ s.zf = some (decide (i = N s₀)))
        (F₂ := fun (s : State) => XI s₀' ys' i s ∧ s.zf = some (decide (i = N s₀')))
        fun _ _ h => ⟨test_wp hi h.2.2.1, test_wp (by rw [← hN']; exact hi) h.2.2.2⟩).mono (fun _ _ h => h)
        fun _ _ h => ⟨i, hi, h.1, h.2⟩
  -- One at a time.
  have e : RelCT isa (fun (a b : State) => ∃ i, i ≤ N s₀ ∧ (XI s₀ ys i a ∧ a.zf = some (decide (i = N s₀))) ∧
        XI s₀' ys' i b ∧ b.zf = some (decide (i = N s₀')))
      (.ite .e (.block []) (.loop (.block singleBody) .ne))
      fun a b => XI s₀ ys (N s₀) a ∧ XI s₀' ys' (N s₀') b := by
    refine RelCT.ite (fun s₁ s₂ ⟨i, _, h₁, h₂⟩ => ?_) ?_ ?_
    · show s₁.zf = s₂.zf
      rw [h₁.2, h₂.2, hN']
    · refine (RelCT.exists_ (P := fun (i : Nat) (s₁ s₂ : State) => (i ≤ N s₀ ∧
          (XI s₀ ys i s₁ ∧ s₁.zf = some (decide (i = N s₀))) ∧ XI s₀' ys' i s₂ ∧ s₂.zf = some (decide (i = N s₀'))) ∧
          isa.eval .e s₁ = some true) fun i => ?_).mono (fun _ _ ⟨⟨i, h⟩, he⟩ => ⟨i, h, he⟩) fun _ _ h => h
      refine (taint_rel [.esi, .edi] nil_taint (fun _ _ h => XI.agree hq hp hp' h.1.2.1.1 h.1.2.2.1)
        (F₁ := XI s₀ ys (N s₀)) (F₂ := XI s₀' ys' (N s₀'))
        fun s₁ _ h => by
          have e : s₁.zf = some true := h.2
          rw [h.1.2.1.2] at e
          have hi : i = N s₀ := by simpa using e
          exact ⟨WP.block_nil (hi ▸ h.1.2.1.1), WP.block_nil (by rw [← hN', ← hi]; exact h.1.2.2.1)⟩).mono
        (fun _ _ h => h) fun _ _ h => h
    · refine (RelCT.exists_ (P := fun (i : Nat) (s₁ s₂ : State) => (i ≤ N s₀ ∧
          (XI s₀ ys i s₁ ∧ s₁.zf = some (decide (i = N s₀))) ∧ XI s₀' ys' i s₂ ∧ s₂.zf = some (decide (i = N s₀'))) ∧
          isa.eval .e s₁ = some false) fun i => ?_).mono (fun _ _ ⟨⟨i, h⟩, he⟩ => ⟨i, h, he⟩) fun _ _ h => h
      by_cases hi : i < N s₀
      · exact (single_rel hq hp hp' hi).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => h
      · refine RelCT.of_false fun s₁ _ h => ?_
        have e : s₁.zf = some false := h.2
        rw [h.1.2.1.2] at e
        have hne : ¬ i = N s₀ := by simpa using e
        have hle := h.1.1
        omega_using [hi, hne, hle]
  exact a.seq (b.seq (c.seq (d.seq e)))

/-- All the blocks, in two runs. -/
theorem batch_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86 f).pre (Proof.Aes.blocksX86 f).pub b.code)
    (nosp : NoSp b.code) (stack : stackUse b.code = 0)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16))
    (hp : UPre s₀) (hp' : UPre s₀') :
    RelCT isa (fun a b => LInv (AesXts.xtsMode enc) s₀ 0 a ∧ LInv (AesXts.xtsMode enc) s₀' 0 b) (batch b)
      fun a b => LInv (AesXts.xtsMode enc) s₀ (N s₀) a ∧ LInv (AesXts.xtsMode enc) s₀' (N s₀') b := by
  -- The first pass.
  have p₁ := (pass_rel hq hp hp' (ys := blks s₀) (ys' := blks s₀')).mono
    (fun a b (h : LInv (AesXts.xtsMode enc) s₀ 0 a ∧ LInv (AesXts.xtsMode enc) s₀' 0 b) =>
      ⟨PInv.of_linv (fun _ _ _ => rfl) (fun _ _ _ => rfl) h.1, PInv.of_linv (fun _ _ _ => rfl) (fun _ _ _ => rfl) h.2⟩)
    fun _ _ h => h
  -- The arguments of the call.
  have c := taint_rel [] callArgs_taint
    (P := fun a b => XI s₀ (blks s₀) (N s₀) a ∧ XI s₀' (blks s₀') (N s₀') b)
    (fun _ _ h => Pt.agree hq hp hp' (h.1.pt hp) (h.2.pt hp') fun r hr => by simp at hr)
    (F₁ := fun (s' : State) => Proof.AesOcb.X86.BCall s' (W s₀) (Dp s₀) (S s₀) (R s₀) (N s₀) ∧
      PInv s₀ (xored (iv0 s₀) (blks s₀) (N s₀)) s')
    (F₂ := fun (s' : State) => Proof.AesOcb.X86.BCall s' (W s₀') (Dp s₀') (S s₀') (R s₀') (N s₀') ∧
      PInv s₀' (xored (iv0 s₀') (blks s₀') (N s₀')) s')
    fun _ _ h => ⟨callArgs_wp hp h.1, callArgs_wp hp' h.2⟩
  -- The call.
  have k := (RelCT.mono (Proof.AesOcb.X86.blk_ct (fn := ⟨b.name, b.code⟩) ok ct
      (I := fun s => Proof.AesOcb.X86.BCall s (W s₀) (Dp s₀) (S s₀) (R s₀) (N s₀) ∧ s.gpr .esp = E s₀)
      fun _ h => h) (P' := fun a b =>
        (Proof.AesOcb.X86.BCall a (W s₀) (Dp s₀) (S s₀) (R s₀) (N s₀) ∧
          PInv s₀ (xored (iv0 s₀) (blks s₀) (N s₀)) a) ∧
        (Proof.AesOcb.X86.BCall b (W s₀') (Dp s₀') (S s₀') (R s₀') (N s₀') ∧
          PInv s₀' (xored (iv0 s₀') (blks s₀') (N s₀')) b))
      (fun _ _ h => ⟨⟨h.1.1, h.1.2.esp⟩, by
        rw [pub_W hq, pub_Dp hq, pub_S hq, pub_R hq, pub_N hq, pub_E hq]; exact ⟨h.2.1, h.2.2.esp⟩⟩)
      fun _ _ _ => trivial).wp
    (F₁ := PInv s₀ ((xored (iv0 s₀) (blks s₀) (N s₀)).map (ciphOf enc (R s₀) (wK s₀))))
    (F₂ := PInv s₀' ((xored (iv0 s₀') (blks s₀') (N s₀')).map (ciphOf enc (R s₀') (wK s₀'))))
    fun _ _ h => ⟨call_wp hp enc ok nosp stack hf h.1.1 h.1.2, call_wp hp' enc ok nosp stack hf h.2.1 h.2.2⟩
  -- The second pass.
  have p₂ := pass_rel hq hp hp'
    (ys := (xored (iv0 s₀) (blks s₀) (N s₀)).map (ciphOf enc (R s₀) (wK s₀)))
    (ys' := (xored (iv0 s₀') (blks s₀') (N s₀')).map (ciphOf enc (R s₀') (wK s₀')))
  -- The tweak stored.
  have t := taint_rel [.ebx] storeT_taint
    (P := fun a b => XI s₀ ((xored (iv0 s₀) (blks s₀) (N s₀)).map (ciphOf enc (R s₀) (wK s₀))) (N s₀) a ∧
      XI s₀' ((xored (iv0 s₀') (blks s₀') (N s₀')).map (ciphOf enc (R s₀') (wK s₀'))) (N s₀') b)
    (fun _ _ h => Pt.agree hq hp hp' (h.1.pt hp) (h.2.pt hp') fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.ebx, h.2.ebx]; exact pub_arg hq (by decide))
    (F₁ := LInv (AesXts.xtsMode enc) s₀ (N s₀)) (F₂ := LInv (AesXts.xtsMode enc) s₀' (N s₀'))
    fun _ _ h => ⟨storeT_wp hp enc h.1, storeT_wp hp' enc h.2⟩
  exact p₁.seq (c.seq ((k.mono (fun _ _ h => h) fun _ _ h => h.2).seq (p₂.seq t)))

end

theorem crypt_ct (enc : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {b : Impl.Aes.X86.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86 f).pre (Proof.Aes.blocksX86 f).pub b.code)
    (nosp : NoSp b.code) (stack : stackUse b.code = 0)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16)) :
    ConstantTime isa (modeX86 (AesXts.xtsMode enc)).pre (modeX86 (AesXts.xtsMode enc)).pub (crypt b) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (ends_rel h₁ h₂ hq (fun hp hp' _ => batch_rel hq ok ct nosp stack hf hp hp')
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesXts.X86

end

end

/-!
# XTS-AES on x86: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), from `crypt_wp` and `crypt_ct`, a state satisfying the
precondition, and the shared contracts of `Spec/Xts/Contract.lean`, with 24
bytes of stack: the call of the block function pushes its five arguments and
the return address.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86

open VG VG.X86 VG.Impl.AesXts.X86
open VG.Proof.AesCbc (ciphOf aesWith_state aesInvWith_state)
open VG.Proof.AesCbc.X86
open VG.Proof.Aes.X86 (BlocksImpl)

theorem encrypt_spSafe (v : BlocksImpl) : (encrypt v.enc).all (fun i => !isa.writesSp i) = true := by
  simp only [encrypt, crypt, batch, pass, Impl.AesOcb.X86.blocksFrame, Code.all, v.encSpSafe]
  decide +kernel

theorem decrypt_spSafe (v : BlocksImpl) : (decrypt v.dec).all (fun i => !isa.writesSp i) = true := by
  simp only [decrypt, crypt, batch, pass, Impl.AesOcb.X86.blocksFrame, Code.all, v.decSpSafe]
  decide +kernel

end VG.Proof.AesXts.X86
