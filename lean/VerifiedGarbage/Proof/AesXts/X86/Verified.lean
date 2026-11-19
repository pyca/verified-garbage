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
tweak in `xmm0`, multiplying it by `α` after each (`pass_wp`, by `sstep_wp`
for one block, whose invariant `XI` says what `xored` the blocks are, and
that the tweak in memory is still the one the function was given); the
block function is called on all the blocks (`callArgs_wp`, `call_wp`, from
AES-OCB's `BCall`); a second pass XORs the tweaks in again, and the tweak
after the last block is stored (`storeT_wp`, `AesXts.crypt_eq`). Between
the passes the state is `PInv`.

The straight-line pieces with SSE instructions are run to an explicit state
(`xorBlk_run`, `mulX_run`, `next_run`, `constsLd_run`): a block in an SSE
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
  obtain hy : i < ys.length := by rw [h.len]; exact hi
  obtain blkI : bytesAt s.mem (blk s₀ i) 16 = ys[i] := by
    have := congrArg (·[i]?) h.data
    rw [xored_getElem _ hy, List.getElem?_eq_getElem (by rw [length_blocksAt]; exact hi),
      getElem_blocksAt _ _ hi, List.getElem?_eq_getElem hy] at this
    exact Option.some.inj this
  obtain mem₃ : u₃.mem = s.mem.writeW (blk s₀ i) (s.mem.readW (blk s₀ i) 128 ^^^ s.xmm .xmm0) := by
    rw [m₃, m₂, m₁]
  obtain f₃ : Frame [⟨blk s₀ i, 16⟩] s.mem u₃.mem := by
    rw [mem₃]
    exact (Frame.refl _ _).writeW (r := ⟨_, 16⟩) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain fStep : Frame [⟨blk s₀ i, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem u₃.mem :=
    f₃.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl)
  obtain newBlk : bytesAt u₃.mem (blk s₀ i) 16 = Spec.Cbc.xor ys[i] (Spec.Xts.next (iv0 s₀) i) := by
    rw [mem₃, bytesAt_writeW_bx, bx_xor, ← bytesAt_bx, blkI, h.x0]
  refine ⟨?_, ?_, ?_, ?_, by rw [rd₃, rd₂, rd₁, h.rd], by rw [wr₃, wr₂, wr₁, h.wr],
    h.frame.trans (stepFrame hi fStep), h.len, ?_, ?_, ?_, ?_, ?_⟩
  · rw [si₃, g₂, g₁, h.esi, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl,
      Offset.add_add_eq _ (c := 16 * (i + 1)) (by omega_using [])]
  · rw [di₃, g₂, g₁, h.edi, l₁]
  · rw [g₃ _ (by decide) (by decide), g₂, g₁, h.ebx]
  · rw [g₃ _ (by decide) (by decide), g₂, g₁, h.esp]
  · rw [hp.blocksAt_step hi fStep, h.data, newBlk, xored_step _ hy]
  · rw [bytesAt_frame f₃ (one (hp.blk_iv hi).symm) (by decide), h.iv]
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

/-- A whole pass. -/
theorem pass_wp {ys : List (List Byte)} (hN : 0 < N s₀) {s : State} (h : PInv s₀ ys s) :
    WP isa pass s (XI s₀ ys (N s₀)) :=
  WP.seq (WP.mono (passPro_wp hp h) fun _ h₁ => single_wp hp hN h₁)

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
    (hN : 0 < N s₀) {s : State} (h : LInv (AesXts.xtsMode enc) s₀ 0 s) :
    WP isa (batch b) s (LInv (AesXts.xtsMode enc) s₀ (N s₀)) :=
  WP.seq (WP.mono (pass_wp hp hN (PInv.of_linv (fun _ _ _ => rfl) (fun _ _ _ => rfl) h)) fun _ h₂ =>
    WP.seq (WP.mono (callArgs_wp hp h₂) fun _ ⟨c₃, h₃⟩ =>
      WP.seq (WP.mono (call_wp hp enc ok nosp stack hf c₃ h₃) fun _ h₄ =>
        WP.seq (WP.mono (pass_wp hp hN h₄) fun _ h₅ => storeT_wp hp enc h₅))))

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
  ends_wp h0 fun hp hN _ h => batch_wp hp enc ok nosp stack hf hN h

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

/-- A pass over the blocks, in two runs. -/
theorem pass_rel (hp : UPre s₀) (hp' : UPre s₀') (hN : 0 < N s₀) {ys ys' : List (List Byte)} :
    RelCT isa (fun a b => PInv s₀ ys a ∧ PInv s₀' ys' b) pass
      fun a b => XI s₀ ys (N s₀) a ∧ XI s₀' ys' (N s₀') b := by
  have a := taint_rel [] passPro_taint (P := fun a b => PInv s₀ ys a ∧ PInv s₀' ys' b)
    (fun _ _ h => Pt.agree hq hp hp' (h.1.pt hp) (h.2.pt hp') fun r hr => by simp at hr)
    (F₁ := XI s₀ ys 0) (F₂ := XI s₀' ys' 0)
    fun _ _ h => ⟨passPro_wp hp h.1, passPro_wp hp' h.2⟩
  exact a.seq (single_rel hq hp hp' hN)

/-- All the blocks, in two runs. -/
theorem batch_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86 f).pre (Proof.Aes.blocksX86 f).pub b.code)
    (nosp : NoSp b.code) (stack : stackUse b.code = 0)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16))
    (hp : UPre s₀) (hp' : UPre s₀') (hN : 0 < N s₀) :
    RelCT isa (fun a b => LInv (AesXts.xtsMode enc) s₀ 0 a ∧ LInv (AesXts.xtsMode enc) s₀' 0 b) (batch b)
      fun a b => LInv (AesXts.xtsMode enc) s₀ (N s₀) a ∧ LInv (AesXts.xtsMode enc) s₀' (N s₀') b := by
  have hN' : 0 < N s₀' := by rw [← pub_N hq]; exact hN
  -- The first pass.
  have p₁ := (pass_rel hq hp hp' hN (ys := blks s₀) (ys' := blks s₀')).mono
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
  have p₂ := pass_rel hq hp hp' hN
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
    (ends_rel h₁ h₂ hq (fun hp hp' hN => batch_rel hq ok ct nosp stack hf hp hp' hN)
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
