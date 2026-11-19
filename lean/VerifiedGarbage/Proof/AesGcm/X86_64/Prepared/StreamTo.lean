module

import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Verified
public import VerifiedGarbage.Proof.AesGcm.ScratchPreparedTo
public import VerifiedGarbage.Proof.Gcm.PreparedContract
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract
public import VerifiedGarbage.Impl.AesGcm.X86_64.StreamTo
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.BlkCall
import Mathlib.Data.List.Dedup
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.CT
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Piece
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.SealFin
public import VerifiedGarbage.Impl.AesGcm.X86_64.Fast
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixNCT
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.CT
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.OnePass
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Lit
meta import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Lit
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixNCT
meta import VerifiedGarbage.Proof.Gcm.X86_64.Cached.OnePass
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.PhaseOne
meta import VerifiedGarbage.Proof.Gcm.X86_64.Cached.PhaseOne
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.SetupFin
meta import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.SetupFin
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CopyLoop
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CopyLoop
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Tab
import VerifiedGarbage.Proof.Framework.Cold
meta import VerifiedGarbage.Proof.Framework.Cold
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixOk
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Copy
import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Finish
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.TailCT
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Tab
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixOk
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Copy
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Finish
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.TailCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-! ### `AesGcm.X86_64.Fast.Verified`, which the modules that import this one used -/

section

/-! ### `AesGcm.X86_64.Split.PrefixSCT`, which only this module used -/

section

/-! ### `AesGcm.X86_64.Split.PrefixS`, which this module and modules that import it used -/

section

/-!
# AES-GCM `seal_split` on x86-64: one to three whole blocks at `src`

Untrusted: everything here is checked by Lean. `prefixF` tells the texts
whose first slice holds one or two whole blocks from the others by
`prefix`'s count of them (`preTest3_ok`, `tst_ok`): those it copies to `dst`
(`copySrc`), encrypts their whole blocks there with a call of
`vg_aes_ctr32` from the counter block, and absorbs them into `Y` at once
with the prepared powers of the key context (`sPath_ok`), then keeps the
data from them on as `prefix` does; the others take `prefix`'s own steps
(`tail_ok`, `call_ok`; `prefixF_ok`). `prefixS`, `prefixN` with `prefixF`,
meets `PreOk` with the number of blocks of `prefixN` (`prefixSOk`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Split

variable {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24}

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

/-- `16 q`, by a shift. -/
theorem shl4_ofNat (q : Nat) : BitVec.ofNat 64 q <<< 4 = BitVec.ofNat 64 (16 * q) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

/-- An address `k` bytes before `p + a`. -/
theorem add_ofInt_back (p : Addr) {a k : Nat} (h : k ≤ a) :
    p + BitVec.ofNat 64 a + BitVec.ofInt 64 (-(k : Int)) = p + BitVec.ofNat 64 (a - k) := by
  rw [BitVec.ofInt_neg, BitVec.ofInt_natCast]; bv_omega

section
variable {Ctx W SP : Addr}

/-- The number of whole blocks at `src` into `rax`, `CF` if fewer than three. -/
theorem preTest3_ok {sl : Nat} (hsl : sl < 2 ^ 64) {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hslot : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 sl) :
    WP isa (.block SealSplit.preTest3) s fun t => t.gpr .rax = BitVec.ofNat 64 (sl / 16) ∧
      t.cf = some (decide (sl / 16 < 3)) ∧ (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain q₁ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain h4 := shr4 sl hsl
  obtain i3 := imm_eq (n := 3) (by decide)
  obtain hq : sl / 16 < 2 ^ 64 := by omega_arith
  unfold SealSplit.preTest3
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r15, q₁, hslot, h4, i3], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, h4]
  · simp only [cf_arithFlags, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, reduceCtorEq, ↓reduceIte, h4,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq, Nat.reducePow, Nat.reduceMod]
  · intro r hr; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr]
  all_goals simp [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags,
    wr_setReg, wr_setFlags]

/-- `ZF` if `rax`, the number `q` of whole blocks, is zero. -/
theorem tst_ok {q : Nat} (hq : q < 2 ^ 64) {s : State} (ax : s.gpr .rax = BitVec.ofNat 64 q) :
    WP isa (.block [.alu .test .rax (.reg .rax)]) s fun t => t.zf = some (decide (q = 0)) ∧
      (∀ r, t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain hz := and_self_beq hq
  apply WP.of_runBlock
  refine ⟨_, by xrun [ax], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [zf_arithFlags, gpr_setFlags, ax, hz]
  · intro r; simp [gpr_arithFlags, gpr_setFlags]
  all_goals simp [mem_arithFlags, mem_setFlags, rd_arithFlags, rd_setFlags, wr_arithFlags, wr_setFlags]

/-- `copySrc`'s arguments: `src`, `dst` and `src_len`. -/
theorem sCopyArgs_ok {D S : Addr} {sl : Nat} {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D) (hsrc : s.mem.readW (W + BitVec.ofNat 64 224) 64 = S)
    (hslot : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 sl) :
    WP isa (.block [.mov .rsi (.mem (at_ .r15 tlO)), .mov .rdi (.mem (at_ .r15 dataO)), .mov .rcx (.mem (at_ .r15 tlenO))])
      s fun t => t.gpr .rsi = S ∧ t.gpr .rdi = D ∧ t.gpr .rcx = BitVec.ofNat 64 sl ∧
        (∀ r, r ≠ .rsi → r ≠ .rdi → r ≠ .rcx → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain q₁ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain q₂ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  obtain q₃ := he.perm.wR (show 224 + 8 ≤ 2560 by decide)
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r15, q₁, q₂, q₃, hslot, hdat, hsrc], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, hsrc]
  · simp [gpr_setReg, hdat]
  · simp [gpr_setReg, hslot]
  · intro r a b c; simp [gpr_setReg, a, b, c]
  all_goals simp [mem_setReg, rd_setReg, wr_setReg]

/-- The arguments of the call of `vg_aes_ctr32`. -/
theorem sCtrArgs_ok {R : Nat} {D : Addr} {sl : Nat} (hsl : sl < 2 ^ 64) {s : State}
    (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s) (hR : RoundsAt s.mem W R)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D)
    (hslot : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 sl) :
    WP isa (.block SealSplit.sCtrArgs) s fun t => t.gpr .rdi = Ctx ∧ t.gpr .rsi = BitVec.ofNat 64 R ∧
      t.gpr .rdx = W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48 ∧ t.gpr .rcx = D ∧
      t.gpr .r8 = BitVec.ofNat 64 (sl / 16) ∧ t.gpr .r9 = W + BitVec.ofNat 64 512 ∧
      t.gpr .rbx = D + BitVec.ofNat 64 (16 * (sl / 16)) ∧
      t.gpr .rbp = BitVec.ofNat 64 (sl / 16) ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain q₁ := he.perm.wR (show 176 + 8 ≤ 2560 by decide)
  obtain q₂ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain q₃ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  obtain h₁ := Gather.shr_ofNat sl 4 hsl
  unfold SealSplit.sCtrArgs
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r13, he.r14, he.r15, q₁, q₂, q₃, hR.1, hdat, hslot, h₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, he.r13]
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, he.r15, hR.1]
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, he.r14, imm_eq]
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, hdat]
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, h₁]
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, he.r15, imm_eq, scrO]
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, hdat, h₁, shl4_ofNat (sl / 16),
      BitVec.add_comm]
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, h₁]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags, gpr_setFlags]
  all_goals simp [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags,
    wr_setReg, wr_setFlags]

end

/-! ## The blocks absorbed at once -/

open VG.Proof.Gcm.X86_64.Pclmul (Only prod zero_ok acc_ok reduce_ok ldrev_ok const_ok)
open VG.Proof.AesGcm.X86_64.Short (IsH1 IsH2 IsH3 ShortFacts pxor712_ok)
open VG.Impl.Gcm.X86_64.Pclmul (revMask poly)

/-- `movdqu x, [b + d]`. -/
theorem ld128_ok (x : XReg) (b : Reg) (d : Nat) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofInt 64 (d : Int)) 16) :
    WP isa (.block [.movdquLoad x (Impl.Gcm.X86_64.Pclmul.at_ b d)]) s fun t =>
      t.xmm x = s.mem.readW (s.gpr b + BitVec.ofInt 64 (d : Int)) 128 ∧ Only [x] s t := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.setXmm, State.load128,
    VG.Proof.Gcm.X86_64.Pclmul.ea_at, hin, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [hr, ite_false]

/-- `movdqu x, [b + d]; pshufb x, xmm0`, for any displacement. -/
theorem ldrevI_ok (x : XReg) (b : Reg) (d : Int) (s : State) (hx : x ≠ .xmm0) (h0 : s.xmm .xmm0 = revMask)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofInt 64 d) 16) :
    WP isa (.block [.movdquLoad x { base := b, disp := d }, .xop (.bin .pshufb x .xmm0)]) s fun s' =>
      s'.xmm x = blockAt s.mem (s.gpr b + BitVec.ofInt 64 d) ∧ Only [x] s s' := by
  obtain e : ∀ t : State, t.ea { base := b, disp := d } = t.gpr b + BitVec.ofInt 64 d := fun _ => rfl
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, State.load128, e, hin, Ne.symm hx, h0, VG.Proof.Gcm.X86_64.Pclmul.rev_eq,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  · rw [VG.Proof.Gcm.X86_64.blockAt_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [hr, ite_false]

/-- `pxor xmm12, xmm12`. -/
theorem clr12_ok (s : State) :
    WP isa (.block [.xop (.bin .pxor .xmm12 .xmm12)]) s fun s' => s'.xmm .xmm12 = 0 ∧ Only [.xmm12] s s' := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, VG.Proof.Gcm.X86_64.Pclmul.eval_pxor, BitVec.xor_self, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [hr, ite_false]

/-- The registers a step writes. -/
abbrev stepRegs : List XReg := [.xmm7, .xmm12, .xmm6, .xmm8, .xmm9, .xmm10, .xmm11]

/-- A step: the block `16 j` bytes before `rbx`, with `xmm12` added, times
the power at `r13 + powOff j`, added to the product, and `xmm12` cleared. -/
theorem sStep_ok (j : Nat) (s : State) (x0 : s.xmm .xmm0 = revMask)
    (hX : InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofInt 64 (-(16 * j : Int))) 16)
    (hP : InRegions (s.rd ++ s.wr) (s.gpr .r13 + BitVec.ofInt 64 ((SealSplit.powOff j : Nat) : Int)) 16) :
    WP isa (.block (SealSplit.sGhStep j)) s fun t =>
      prod t = (prod s).acc (blockAt s.mem (s.gpr .rbx + BitVec.ofInt 64 (-(16 * j : Int))) ^^^ s.xmm .xmm12)
        (s.mem.readW (s.gpr .r13 + BitVec.ofInt 64 ((SealSplit.powOff j : Nat) : Int)) 128) ∧
      t.xmm .xmm12 = 0 ∧ Only stepRegs s t := by
  rw [show SealSplit.sGhStep j = [.movdquLoad .xmm7 { base := .rbx, disp := -(16 * j : Int) },
      .xop (.bin .pshufb .xmm7 .xmm0)] ++ ([.xop (.bin .pxor .xmm7 .xmm12)] ++ ([.xop (.bin .pxor .xmm12 .xmm12)] ++
      ([.movdquLoad .xmm6 (Impl.Gcm.X86_64.Pclmul.at_ .r13 (SealSplit.powOff j))] ++
      Impl.Gcm.X86_64.Pclmul.acc .xmm7 .xmm6))) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (ldrevI_ok .xmm7 .rbx _ s (by decide) x0 hX) fun s₁ ⟨l₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pxor712_ok s₁) fun s₂ ⟨l₂, o₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (clr12_ok s₂) fun s₃ ⟨l₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  obtain O := (o₁.trans o₂).trans o₃
  refine WP.mono (ld128_ok .xmm6 .r13 _ s₃ (by rw [O.rd, O.wr, O.gpr _ (by decide)]; exact hP)) fun s₄ ⟨l₄, o₄⟩ => ?_
  refine WP.mono (acc_ok .xmm7 .xmm6 s₄ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun t ⟨p, o⟩ => ⟨?_, ?_, ((O.trans o₄).trans o).weaken fun r hr => by
      revert hr; cases r <;> decide⟩
  · rw [p, o₄.prod (by decide) (by decide) (by decide), o₃.prod (by decide) (by decide) (by decide),
      o₂.prod (by decide) (by decide) (by decide), o₁.prod (by decide) (by decide) (by decide),
      o₄.xmm _ (by decide), o₃.xmm _ (by decide), l₂, l₁, l₄, O.mem, O.gpr _ (by decide), o₁.xmm _ (by decide)]
  · rw [o.xmm _ (by decide), o₄.xmm _ (by decide), l₃]

section
variable {Ctx St W SP : Addr}

/-- What `sGhK k`'s steps leave: the product of the `k` blocks with their powers. -/
abbrev sProd (Y : Block) (X : List Block) (P : Nat → Block) : VG.Proof.Gcm.X86_64.Pclmul.Prod :=
  match X with
  | [X₀] => VG.Proof.Gcm.X86_64.Pclmul.Prod.zero.acc (X₀ ^^^ Y) (P 1)
  | [X₀, X₁] => (VG.Proof.Gcm.X86_64.Pclmul.Prod.zero.acc (X₀ ^^^ Y) (P 2)).acc X₁ (P 1)
  | [X₀, X₁, X₂] => ((VG.Proof.Gcm.X86_64.Pclmul.Prod.zero.acc (X₀ ^^^ Y) (P 3)).acc X₁ (P 2)).acc X₂ (P 1)
  | _ => VG.Proof.Gcm.X86_64.Pclmul.Prod.zero

/-- The product, reduced, is `GHASH` over the blocks from `Y`, with the
prepared powers. -/
theorem sProd_ghash (hF : ShortFacts) (H Y : Block) {X : List Block} (hX : X.length = 1 ∨ X.length = 2 ∨ X.length = 3) :
    VG.Proof.Gcm.X86_64.Pclmul.reduce (sProd Y X fun j => Spec.Gcm.preparedPower (Spec.Gcm.hpow H j)) =
      ghashFrom H Y X := by
  match X, hX with
  | [X₀], _ => simp only [sProd]; rw [BitVec.xor_comm]; exact hF.pp1 H Y X₀
  | [X₀, X₁], _ => simp only [sProd]; rw [BitVec.xor_comm]; exact hF.pp2 H Y X₀ X₁
  | [X₀, X₁, X₂], _ => simp only [sProd]; rw [BitVec.xor_comm]; exact hF.pp3 H Y X₀ X₁ X₂

/-- `cmp rbp, m`: `CF` if `rbp`, the number of whole blocks, is below `m`. -/
theorem sCmp_ok {q m : Nat} (hq : q < 2 ^ 64) (hm : m < 2 ^ 31) (s : State) (hbp : s.gpr .rbp = BitVec.ofNat 64 q) :
    WP isa (.block [.alu .cmp .rbp (imm m)]) s fun t =>
      t.cf = some (decide (q < m)) ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.xmm = s.xmm := by
  obtain im := imm_eq (n := m) hm
  apply WP.of_runBlock
  refine ⟨_, by xrun [hbp, im], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [cf_arithFlags, ite_true, reduceCtorEq, ↓reduceIte,
      Nat.reducePow, BitVec.toNat_ofNat, Nat.reduceMod, Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt (show m < 2 ^ 64 by omega_arith)]
  · funext r; simp [gpr_arithFlags]
  all_goals simp [mem_arithFlags, rd_arithFlags, wr_arithFlags, xmm_arithFlags]

/-- `cmp rbp, m` and the step for `H'ʲ` if `rbp` is not below `m`. -/
theorem sOpt_ok (j m : Nat) {q : Nat} (hq : q < 2 ^ 64) (hm : m < 2 ^ 31) (s : State)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 q) (x0 : s.xmm .xmm0 = revMask)
    (hX : ¬ q < m → InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofInt 64 (-(16 * j : Int))) 16)
    (hP : InRegions (s.rd ++ s.wr) (s.gpr .r13 + BitVec.ofInt 64 ((SealSplit.powOff j : Nat) : Int)) 16) :
    WP isa (.seq (.block [.alu .cmp .rbp (imm m)]) (.ite .b (.block []) (.block (SealSplit.sGhStep j)))) s fun t =>
      (q < m → prod t = prod s ∧ t.xmm .xmm12 = s.xmm .xmm12) ∧
      (¬ q < m → prod t = (prod s).acc (blockAt s.mem (s.gpr .rbx + BitVec.ofInt 64 (-(16 * j : Int))) ^^^
        s.xmm .xmm12) (s.mem.readW (s.gpr .r13 + BitVec.ofInt 64 ((SealSplit.powOff j : Nat) : Int)) 128) ∧
        t.xmm .xmm12 = 0) ∧ Only stepRegs s t := by
  refine WP.seq (WP.mono (sCmp_ok hq hm s hbp) fun t₁ ⟨cf, g, m₁, rd, wr, x⟩ => ?_)
  obtain o₁ : Only [] s t₁ := ⟨fun r _ => by rw [g], m₁, rd, wr, fun r _ => by rw [x]⟩
  refine WP.ite (decide (q < m)) (by simp only [eval, cf]) (fun hc => ?_) (fun hc => ?_)
  · have hc' := of_decide_eq_true hc
    refine WP.block_nil ⟨fun _ => ⟨by simp only [prod, x], by rw [x]⟩, fun h => absurd hc' h, o₁.weaken nofun⟩
  · have hc' := of_decide_eq_false hc
    refine WP.mono (sStep_ok j t₁ (by rw [x, x0]) (by rw [rd, wr, g]; exact hX hc') (by rw [rd, wr, g]; exact hP))
      fun t ⟨p, z, o⟩ => ⟨fun h => absurd h hc', fun _ => ⟨?_, z⟩, o₁.trans o⟩
    rw [p, show prod t₁ = prod s by simp only [prod, x], g, m₁, x]

/-- `sGhPre`: the constants, `Y` in `xmm12`, the product cleared. -/
theorem sPre_ok {St : Addr} (u : State) (h14 : u.gpr .r14 = St)
    (inY : InRegions (u.rd ++ u.wr) (St + BitVec.ofNat 64 16) 16) :
    WP isa (.block SealSplit.sGhPre) u fun t => t.xmm .xmm0 = revMask ∧ t.xmm .xmm1 = poly ∧
      t.xmm .xmm12 = blockAt u.mem (St + BitVec.ofNat 64 16) ∧ prod t = VG.Proof.Gcm.X86_64.Pclmul.Prod.zero ∧
      Only [.xmm0, .xmm12, .xmm1, .xmm12, .xmm12, .xmm8, .xmm9, .xmm10] u t := by
  simp only [SealSplit.sGhPre, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ u (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  obtain O₂ := o₁.trans o₂
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm12 .r14 16 s₂ (by decide)
    (by rw [o₂.xmm _ (by decide), c₁, VG.Proof.Gcm.X86_64.Pclmul.rev_eq])
    (by rw [O₂.rd, O₂.wr, O₂.gpr _ (by decide), h14, BitVec.ofInt_natCast]; exact inY))
    fun s₃ ⟨l₃, o₃⟩ => ?_
  rw [O₂.gpr _ (by decide), h14, BitVec.ofInt_natCast, O₂.mem] at l₃
  refine WP.mono (zero_ok s₃) fun t ⟨p, o⟩ => ⟨?_, ?_, ?_, p, (O₂.trans o₃).trans o⟩
  · rw [o.xmm _ (by decide), o₃.xmm _ (by decide), o₂.xmm _ (by decide), c₁, VG.Proof.Gcm.X86_64.Pclmul.rev_eq]
  · rw [o.xmm _ (by decide), o₃.xmm _ (by decide), c₂]
  · rw [o.xmm _ (by decide), l₃]

/-- `sGh`: the `q = ⌊sl / 16⌋` blocks (one to three, in `rbp`) before
`rbx = D + 16 q` absorbed into `Y` at `St + 16` at once. -/
theorem sGh_ok {sl : Nat} (hq : 1 ≤ sl / 16 ∧ sl / 16 ≤ 3) {Ctx St D : Addr} (u : State)
    (h13 : u.gpr .r13 = Ctx) (h14 : u.gpr .r14 = St) (hbx : u.gpr .rbx = D + BitVec.ofNat 64 (16 * (sl / 16)))
    (hbp : u.gpr .rbp = BitVec.ofNat 64 (sl / 16))
    (inY : InRegions (u.rd ++ u.wr) (St + BitVec.ofNat 64 16) 16) (outY : InRegions u.wr (St + BitVec.ofNat 64 16) 16)
    (hX : ∀ i < sl / 16, InRegions (u.rd ++ u.wr) (D + BitVec.ofNat 64 (16 * i)) 16)
    (hP : ∀ j, 1 ≤ j → j ≤ 3 → InRegions (u.rd ++ u.wr) (Ctx + BitVec.ofNat 64 (SealSplit.powOff j)) 16) :
    WP isa SealSplit.sGh u fun t =>
      blockAt t.mem (St + BitVec.ofNat 64 16) = VG.Proof.Gcm.X86_64.Pclmul.reduce
        (sProd (blockAt u.mem (St + BitVec.ofNat 64 16)) (blocksAt u.mem D (sl / 16))
          (fun j => u.mem.readW (Ctx + BitVec.ofNat 64 (SealSplit.powOff j)) 128)) ∧
      Frame [⟨St + BitVec.ofNat 64 16, 16⟩] u.mem t.mem ∧
      (∀ r, r ≠ .rax → t.gpr r = u.gpr r) ∧ t.rd = u.rd ∧ t.wr = u.wr := by
  generalize hqd : sl / 16 = q at hq hbx hbp hX ⊢
  -- The block `16 j` bytes before `rbx`, for a step that runs.
  obtain back : ∀ j, j ≤ q → u.gpr .rbx + BitVec.ofInt 64 (-(16 * j : Int)) = D + BitVec.ofNat 64 (16 * (q - j)) :=
    fun j hj => by
      rw [hbx, show (-(16 * j : Int)) = -((16 * j : Nat) : Int) by push_cast; rfl,
        add_ofInt_back D (show 16 * j ≤ 16 * q by omega_arith), Nat.mul_sub]
  obtain pw : ∀ j, u.gpr .r13 + BitVec.ofInt 64 ((SealSplit.powOff j : Nat) : Int) =
      Ctx + BitVec.ofNat 64 (SealSplit.powOff j) := fun j => by rw [h13, BitVec.ofInt_natCast]
  unfold SealSplit.sGh
  refine WP.seq (WP.mono (sPre_ok u h14 inY) fun s₁ ⟨x0, x1, y₁, z₁, o₁⟩ => ?_)
  have g₁ : ∀ r, r ≠ .rax → s₁.gpr r = u.gpr r := o₁.gpr
  -- After both optional steps: the step for `H'` and the reduction.
  obtain fin : ∀ {s₃ : State} (Pr : VG.Proof.Gcm.X86_64.Pclmul.Prod) (Yp : Block), Only (([.xmm0, .xmm12,
      .xmm1, .xmm12, .xmm12, .xmm8, .xmm9, .xmm10] ++ stepRegs) ++ stepRegs) u s₃ → prod s₃ = Pr → s₃.xmm .xmm12 = Yp →
      s₃.xmm .xmm0 = revMask → s₃.xmm .xmm1 = poly →
      WP isa (.block SealSplit.sGhPost) s₃ fun t =>
        blockAt t.mem (St + BitVec.ofNat 64 16) = VG.Proof.Gcm.X86_64.Pclmul.reduce
          (Pr.acc (blockAt u.mem (D + BitVec.ofNat 64 (16 * (q - 1))) ^^^ Yp)
            (u.mem.readW (Ctx + BitVec.ofNat 64 (SealSplit.powOff 1)) 128)) ∧
        Frame [⟨St + BitVec.ofNat 64 16, 16⟩] u.mem t.mem ∧
        (∀ r, r ≠ .rax → t.gpr r = u.gpr r) ∧ t.rd = u.rd ∧ t.wr = u.wr := by
    intro s₃ Pr Yp O hp hy c0 c1
    simp only [SealSplit.sGhPost, List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (sStep_ok 1 s₃ c0 (by rw [O.rd, O.wr, O.gpr _ (by decide), back 1 (by omega_arith)]; exact hX _ (by omega_arith))
      (by rw [O.rd, O.wr, O.gpr _ (by decide), pw]; exact hP 1 (by decide) (by decide))) fun s₄ ⟨p₄, _, o₄⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (reduce_ok .xmm2 s₄ (by decide) (by decide) (by decide) (by decide)
      (by rw [o₄.xmm _ (by decide), c1])) fun s₅ ⟨r₅, o₅⟩ => ?_
    obtain o₄₅ := o₄.trans o₅
    refine WP.mono (Fast.strev_ok .xmm2 .r14 16 s₅ (by decide)
      (by rw [o₄₅.xmm _ (by decide), c0, VG.Proof.Gcm.X86_64.Pclmul.rev_eq])
      (by rw [o₄₅.wr, O.wr, o₄₅.gpr _ (by decide), O.gpr _ (by decide), h14, BitVec.ofInt_natCast]; exact outY))
      fun t ⟨m₈, b₈, g₈, rd₈, wr₈, _⟩ => ?_
    rw [o₄₅.gpr _ (by decide), O.gpr _ (by decide), h14, BitVec.ofInt_natCast] at m₈ b₈
    refine ⟨by rw [b₈, r₅, p₄, hp, hy, O.gpr .rbx (by decide), O.gpr .r13 (by decide), back 1 (by omega_arith), O.mem, pw], ?_,
      fun r a => by rw [g₈, o₄₅.gpr r a, O.gpr r a], by rw [rd₈, o₄₅.rd, O.rd], by rw [wr₈, o₄₅.wr, O.wr]⟩
    rw [m₈, o₄₅.mem, O.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain bp₁ : s₁.gpr .rbp = BitVec.ofNat 64 q := by rw [g₁ _ (by decide), hbp]
  obtain P₁ : ∀ j, 1 ≤ j → j ≤ 3 → InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .r13 + BitVec.ofInt 64 ((SealSplit.powOff j : Nat) : Int)) 16 :=
    fun j a b => by rw [o₁.rd, o₁.wr, g₁ _ (by decide), pw]; exact hP j a b
  refine WP.seq (WP.mono (sOpt_ok 3 3 (q := q) (by omega_arith) (by decide) s₁ bp₁ x0
    (fun h => by rw [o₁.rd, o₁.wr, g₁ _ (by decide), back 3 (by omega_arith)]; exact hX _ (by omega_arith)) (P₁ 3 (by decide) (by decide)))
    fun s₂ ⟨sk₂, tk₂, o₂⟩ => ?_)
  obtain O₂ := o₁.trans o₂
  refine WP.seq (WP.mono (sOpt_ok 2 2 (q := q) (by omega_arith) (by decide) s₂ (by rw [O₂.gpr _ (by decide), hbp])
    (by rw [o₂.xmm _ (by decide), x0])
    (fun h => by rw [O₂.rd, O₂.wr, O₂.gpr _ (by decide), back 2 (by omega_arith)]; exact hX _ (by omega_arith))
    (by rw [O₂.rd, O₂.wr, O₂.gpr _ (by decide), pw]; exact hP 2 (by decide) (by decide)))
    fun s₃ ⟨sk₃, tk₃, o₃⟩ => ?_)
  obtain O₃ := O₂.trans o₃
  obtain c0 : s₃.xmm .xmm0 = revMask := by rw [o₃.xmm _ (by decide), o₂.xmm _ (by decide), x0]
  obtain c1 : s₃.xmm .xmm1 = poly := by rw [o₃.xmm _ (by decide), o₂.xmm _ (by decide), x1]
  have m₁ : s₁.mem = u.mem := o₁.mem
  have m₂ : s₂.mem = u.mem := O₂.mem
  obtain bx₁ : s₁.gpr .rbx = u.gpr .rbx := g₁ _ (by decide)
  obtain bx₂ : s₂.gpr .rbx = u.gpr .rbx := O₂.gpr _ (by decide)
  obtain d₁ : s₁.gpr .r13 = u.gpr .r13 := g₁ _ (by decide)
  obtain d₂ : s₂.gpr .r13 = u.gpr .r13 := O₂.gpr _ (by decide)
  obtain xz : ∀ x : Block, x ^^^ (0 : Block) = x := fun _ => BitVec.xor_zero
  rcases (show q = 1 ∨ q = 2 ∨ q = 3 by omega_arith) with rfl | rfl | rfl
  · obtain ⟨p₂, y₂⟩ := sk₂ (by decide)
    obtain ⟨p₃, y₃⟩ := sk₃ (by decide)
    refine WP.mono (fin _ _ O₃ (p₃.trans (p₂.trans z₁)) (y₃.trans (y₂.trans y₁)) c0 c1) fun t ⟨y, f, g, rd, wr⟩ =>
      ⟨by rw [y]; rfl, f, g, rd, wr⟩
  · obtain ⟨p₂, y₂⟩ := sk₂ (by decide)
    obtain ⟨p₃, y₃⟩ := tk₃ (by decide)
    refine WP.mono (fin _ _ O₃ p₃ y₃ c0 c1) fun t ⟨y, f, g, rd, wr⟩ => ⟨?_, f, g, rd, wr⟩
    rw [y, p₂, z₁, y₂, y₁, m₂, bx₂, d₂, back 2 (by omega_arith), pw, xz]; rfl
  · obtain ⟨p₂, y₂⟩ := tk₂ (by decide)
    obtain ⟨p₃, y₃⟩ := tk₃ (by decide)
    refine WP.mono (fin _ _ O₃ p₃ y₃ c0 c1) fun t ⟨y, f, g, rd, wr⟩ => ⟨?_, f, g, rd, wr⟩
    rw [y, p₂, z₁, y₂, y₁, m₂, bx₂, d₂, m₁, bx₁, d₁, back 2 (by omega_arith), back 3 (by omega_arith), pw, pw,
      xz, xz]; rfl

end

/-- `sProd` reads only the powers `1` to `3`. -/
theorem sProd_congr (Y : Block) (X : List Block) {P Q : Nat → Block} (h : ∀ j, 1 ≤ j → j ≤ 3 → P j = Q j) :
    sProd Y X P = sProd Y X Q := by
  obtain h1 := h 1 (by decide) (by decide)
  obtain h2 := h 2 (by decide) (by decide)
  obtain h3 := h 3 (by decide) (by decide)
  match X with
  | [] => rfl
  | [_] => simp only [sProd, h1]
  | [_, _] => simp only [sProd, h1, h2]
  | [_, _, _] => simp only [sProd, h1, h2, h3]
  | _ :: _ :: _ :: _ :: _ => rfl

/-! ## The path of the texts of one to three whole blocks -/

section
variable (Ctx W SP D S : Addr) (R sl : Nat) (σ : State)

/-- The memory after `copySrc`: `src` copied to `dst`. -/
abbrev sMem : Mem := writeBytes σ.mem D (bytesAt σ.mem S sl)

/-- After `copySrc`'s arguments. -/
structure SA (t : State) : Prop where
  rsi : t.gpr .rsi = S
  rdi : t.gpr .rdi = D
  rcx : t.gpr .rcx = BitVec.ofNat 64 sl
  gpr : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdi → r ≠ .rcx → t.gpr r = σ.gpr r
  mem : t.mem = σ.mem
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr

/-- After `copySrc`. -/
structure SB (t : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP t
  mem : t.mem = sMem D S sl σ
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr

/-- Before the call of `vg_aes_ctr32`. -/
structure SC (t : State) : Prop where
  call : CtrCall t Ctx (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) D (W + BitVec.ofNat 64 512) R (sl / 16)
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP t
  rbx : t.gpr .rbx = D + BitVec.ofNat 64 (16 * (sl / 16))
  rbp : t.gpr .rbp = BitVec.ofNat 64 (sl / 16)
  mem : t.mem = sMem D S sl σ
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr

/-- After the call. -/
structure SD (t : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP t
  rbx : t.gpr .rbx = D + BitVec.ofNat 64 (16 * (sl / 16))
  rbp : t.gpr .rbp = BitVec.ofNat 64 (sl / 16)
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  frame : Frame [⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩, ⟨D, 16 * (sl / 16)⟩,
    ⟨W + BitVec.ofNat 64 512, 2048⟩, below SP 8] (sMem D S sl σ) t.mem
  out : blocksAt t.mem D (sl / 16) = ctr32 (Spec.Gcm.aesWith R (bytesAt (sMem D S sl σ) Ctx (16 * (R + 1))))
    (blockAt (sMem D S sl σ) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48)) (blocksAt (sMem D S sl σ) D (sl / 16))
  ctr : blockAt t.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
    Nat.repeat inc32 (sl / 16) (blockAt (sMem D S sl σ) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48))

/-- After `sGh`. -/
def SE (t : State) : Prop := ∃ u, SD Ctx W SP D S R sl σ u ∧
  blockAt t.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) = VG.Proof.Gcm.X86_64.Pclmul.reduce
    (sProd (blockAt u.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16)) (blocksAt u.mem D (sl / 16))
      (fun j => u.mem.readW (Ctx + BitVec.ofNat 64 (SealSplit.powOff j)) 128)) ∧
  Frame [⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩] u.mem t.mem ∧
  (∀ r, r ≠ .rax → t.gpr r = u.gpr r) ∧ t.rd = u.rd ∧ t.wr = u.wr

end

section
variable {Ctx W SP D S : Addr} {R n sl : Nat} {s : State} (h : PP (CtxMode.preparedN np hpn) Ctx W SP D S R n sl s)
  (hq : 1 ≤ sl / 16 ∧ sl / 16 ≤ 3)
include h

/-- `copySrc`'s arguments. -/
theorem sA_ok {t : State} (g : ∀ r, r ≠ .rax → t.gpr r = s.gpr r) (tm : t.mem = s.mem) (trd : t.rd = s.rd)
    (twr : t.wr = s.wr) :
    WP isa (.block [.mov .rsi (.mem (at_ .r15 tlO)), .mov .rdi (.mem (at_ .r15 dataO)), .mov .rcx (.mem (at_ .r15 tlenO))])
      t (SA D S sl s) := by
  obtain he : Env Ctx (W + BitVec.ofNat 64 16) W SP t := h.env.keep (fun r hr => g r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)) trd twr
  exact WP.mono (sCopyArgs_ok (D := D) (S := S) (sl := sl) he (by rw [tm]; exact h.dat)
    (by rw [tm]; exact h.src) (by rw [tm]; exact h.slen)) fun t₁ ⟨si₁, di₁, cx₁, g₁, m₁, rd₁, wr₁⟩ =>
    ⟨si₁, di₁, cx₁, fun r a b c d => by rw [g₁ r b c d, g r a], m₁.trans tm, rd₁.trans trd, wr₁.trans twr⟩

include hq in
/-- The copy. -/
theorem sB_ok {t₁ : State} (hA : SA D S sl s t₁) : WP isa SealGather.copy t₁ (SB Ctx W SP D S sl s) := by
  have hsl := h.sl_le
  obtain cp : Short.CopyPre t₁ S D sl :=
    ⟨hA.rsi, hA.rdi, hA.rcx, by omega_arith, by rw [hA.rd, hA.wr]; exact h.srcCov,
      by rw [hA.wr]; exact covers_pre h.data.wr hsl, h.sD.sub_right (Region.sub_prefix hsl)⟩
  refine WP.mono (Gather.copy_ok cp) fun t₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ⟨?_, by rw [m₂, hA.mem], rd₂.trans hA.rd,
    wr₂.trans hA.wr⟩
  exact h.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      (rw [g₂ _ (by decide) (by decide) (by decide), hA.gpr _ (by decide) (by decide) (by decide) (by decide)]))
    (rd₂.trans hA.rd) (wr₂.trans hA.wr)

/-- A slot of `W`, kept by the copy. -/
theorem sMem_slot {d : Nat} (hd : d + 8 ≤ 2560) :
    (sMem D S sl s).readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
  (writeBytes_frame' (q := D) s.mem (length_bytesAt _ _ _)).readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((h.data.ok.w.sub_left (Region.sub_prefix h.sl_le)).sub_right (Lay.wSub hd)).symm) (by decide)

/-- The call's arguments. -/
theorem sC_ok {t₂ : State} (hB : SB Ctx W SP D S sl s t₂) :
    WP isa (.block SealSplit.sCtrArgs) t₂ (SC Ctx W SP D S R sl s) := by
  have L := h.lay
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  obtain kp₂ : ∀ d, d + 8 ≤ 2560 → t₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => by rw [hB.mem]; exact sMem_slot h hd
  refine WP.mono (sCtrArgs_ok (R := R) (D := D) (sl := sl) (by omega_arith) hB.env
    ⟨by rw [kp₂ 176 (by decide)]; exact h.rounds.1, h.rounds.2⟩ (by rw [kp₂ 200 (by decide)]; exact h.dat)
    (by rw [kp₂ 192 (by decide)]; exact h.slen)) fun t₃ ⟨di₃, si₃, dx₃, cx₃, r8₃, r9₃, bx₃, bp₃, k₃, m₃, rd₃, wr₃⟩ => ?_
  obtain he₃ : Env Ctx (W + BitVec.ofNat 64 16) W SP t₃ := hB.env.keep k₃ rd₃ wr₃
  have hk := he₃.rsp
  obtain hq16 : 16 * (sl / 16) ≤ n := by omega_arith
  obtain hdq := (h.data.of_eq (rd₃.trans hB.rd) (wr₃.trans hB.wr)).take hq16
  refine ⟨⟨di₃, si₃, dx₃, cx₃, r8₃, r9₃, h.rounds.2, by have := h.data.ok.wrap; omega_arith,
      (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide)),
      hdq.ctx.sub_left (Region.sub_prefix (show 240 ≤ 256 by decide)),
      (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide)),
      (hdq.ok.st.sub_right (Lay.stSub (by decide))).symm,
      L.st_w (a := 48) (n := 16) (d := 512) (k := 2048) (by decide) (.inr ⟨by decide, by decide⟩),
      hdq.ok.w.sub_right (Lay.wSub (by decide)), ?_, ?_, ?_, ?_, ?_, ?_⟩,
    he₃, bx₃, bp₃, m₃.trans hB.mem, rd₃.trans hB.rd, wr₃.trans hB.wr⟩
  · rw [hk]; exact L.kc.sub_right (Region.sub_prefix (by decide))
  · rw [hk]; exact L.stk_st (by decide)
  · rw [hk]; exact hdq.ok.stk
  · rw [hk]; exact L.stk_w (by decide)
  · refine covers_cons ?_ (covers_cons ?_ (covers_cons hdq.ok.rd (covers_left (he₃.perm.wC (by decide)))))
    · exact fun a m' ⟨r, hr, hc'⟩ => by
        simp only [List.mem_singleton] at hr; subst hr
        exact he₃.perm.ctx a m' ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc' ⊢; omega_arith⟩
    · exact covers_left (he₃.perm.stC (by decide))
  · exact covers_cons (he₃.perm.stC (by decide)) (covers_cons hdq.wr (he₃.perm.wC (by decide)))

omit h in
/-- The call. -/
theorem sD_ok (v : Proof.Aes.X86_64.Ctr32Impl) {t₃ : State} (hC : SC Ctx W SP D S R sl s t₃) :
    WP isa (.call v.callee.name v.callee.code) t₃ (SD Ctx W SP D S R sl s) := by
  refine WP.mono (ctr_call v hC.call) fun t₄ G => ?_
  have hk := hC.env.rsp
  have Fk := G.frame
  have ok₄ := G.out
  have ct₄ := G.ctr
  rw [hC.mem, hk] at Fk
  rw [hC.mem] at ok₄ ct₄
  exact ⟨hC.env.of_saved G.saved G.rd G.wr, by rw [G.saved _ (by simp [calleeSaved]), hC.rbx],
    by rw [G.saved _ (by simp [calleeSaved]), hC.rbp], G.rd.trans hC.rd, G.wr.trans hC.wr, Fk, ok₄, ct₄⟩

include hq in
/-- `sGh`. -/
theorem sE_ok {t₄ : State} (hD : SD Ctx W SP D S R sl s t₄) : WP isa SealSplit.sGh t₄ (SE Ctx W SP D S R sl s) := by
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  obtain inP : ∀ j, 1 ≤ j → j ≤ 3 → InRegions (t₄.rd ++ t₄.wr) (Ctx + BitVec.ofNat 64 (SealSplit.powOff j)) 16 :=
    fun j h₁ h₂ => by
      rw [hD.rd, hD.wr]
      refine Short.in_of_covers16 h.ext.cov ?_ (show 1024 < 2 ^ 64 by decide)
      show SealSplit.powOff j + 16 ≤ 1024
      unfold SealSplit.powOff; omega_arith
  exact WP.mono (sGh_ok (Ctx := Ctx) (St := W + BitVec.ofNat 64 16) (D := D) hq t₄
    hD.env.r13 hD.env.r14 hD.rbx hD.rbp (hD.env.perm.stR (by decide)) (hD.env.perm.stW (by decide))
    (fun i hi => by rw [hD.rd, hD.wr]; exact Short.in_of_covers16 h.data.ok.rd (by omega_arith) hn) inP)
    fun t₅ P => ⟨t₄, hD, P⟩

include hq in
/-- `rest`, after `sGh`: what `prefix` leaves. -/
theorem sF_ok (hF : ShortFacts) {t₅ : State} (hE : SE Ctx W SP D S R sl s t₅) :
    WP isa (.block SealSplit.rest) t₅ (PPost Ctx W SP D S R n sl s) := by
  obtain ⟨t₄, hD, y₅, f₅, g₅, rd₅, wr₅⟩ := hE
  have L := h.lay
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  have hw := h.data.ok.wrap
  obtain s64 : sl < 64 := by omega_arith
  obtain q16 : 16 * (sl / 16) ≤ sl := Nat.mul_div_le sl 16
  -- What the copy wrote: the whole blocks, then the bytes left.
  obtain hsplit : bytesAt s.mem S sl = bytesAt s.mem S (16 * (sl / 16)) ++
      bytesAt s.mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16) := by
    rw [← bytesAt_add, show 16 * (sl / 16) + sl % 16 = sl by omega_arith]
  obtain hm₂ : sMem D S sl s = writeBytes (writeBytes s.mem D (bytesAt s.mem S (16 * (sl / 16))))
      (D + BitVec.ofNat 64 (16 * (sl / 16))) (bytesAt s.mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16)) := by
    have := writeBytes_append s.mem D (bytesAt s.mem S (16 * (sl / 16)))
      (bytesAt s.mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16)) (by rw [length_bytesAt, length_bytesAt]; omega_arith)
    rw [length_bytesAt] at this
    rw [sMem, hsplit, this]
  obtain FC : Frame [⟨D, sl⟩] s.mem (sMem D S sl s) := writeBytes_frame' _ (length_bytesAt _ _ _)
  obtain F1 : Frame [⟨D, 16 * (sl / 16)⟩] s.mem (writeBytes s.mem D (bytesAt s.mem S (16 * (sl / 16)))) :=
    writeBytes_frame' _ (length_bytesAt _ _ _)
  obtain F2 : Frame [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩]
      (writeBytes s.mem D (bytesAt s.mem S (16 * (sl / 16)))) (sMem D S sl s) := by
    rw [hm₂]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  obtain dBT : (⟨D, 16 * (sl / 16)⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩ := by
    simpa using Offset.disjoint D (d := 0) (n := 16 * (sl / 16)) (e := 16 * (sl / 16))
      (k := sl % 16) (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  obtain one : ∀ {X Y : Region}, X.Disjoint Y → ∀ r ∈ [Y], X.Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  obtain bl₂ : blocksAt (sMem D S sl s) D (sl / 16) = blocksAt s.mem S (sl / 16) := by
    rw [blocksAt_frame F2 (one dBT) (by omega_arith), Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq]
    have := bytesAt_writeBytes_self s.mem D (bytesAt s.mem S (16 * (sl / 16))) (by rw [length_bytesAt]; omega_arith)
    rw [length_bytesAt] at this
    rw [this]
  obtain tl₂ : bytesAt (sMem D S sl s) (D + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16) =
      bytesAt s.mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16) := by
    have := bytesAt_writeBytes_self (writeBytes s.mem D (bytesAt s.mem S (16 * (sl / 16))))
      (D + BitVec.ofNat 64 (16 * (sl / 16))) (bytesAt s.mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16))
      (by rw [length_bytesAt]; omega_arith)
    rw [length_bytesAt] at this
    rw [hm₂, this]
  have Fk := hD.frame
  have ok₄ := hD.out
  have ct₄ := hD.ctr
  -- The call's writes, among what `prefix` may write.
  obtain Fc : Frame (callWr W D (sl / 16) ++ [below SP 56]) (sMem D S sl s) t₄.mem := Fk.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨D, sl / 16 * 16⟩, by simp, Region.sub_prefix (by omega_arith)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 448, 2112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨below SP 56, by simp, below_sub (by decide) (by decide)⟩
  obtain he₅ : Env Ctx (W + BitVec.ofNat 64 16) W SP t₅ := hD.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₅ _ (by decide)) rd₅ wr₅
  -- Regions apart.
  obtain subT : Region.Sub ⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩ ⟨D, n⟩ := Offset.sub_base D (by omega_arith)
  obtain subQ : Region.Sub ⟨D, 16 * (sl / 16)⟩ ⟨D, n⟩ := Region.sub_prefix (by omega_arith)
  obtain cbY : (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint
      ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩ :=
    Offset.disjoint _ (.inr (by decide)) (by have := L.sw; omega_arith) (by have := L.sw; omega_arith)
  obtain qY : (⟨D, 16 * (sl / 16)⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩ :=
    (h.data.ok.st.sub_left subQ).sub_right (Lay.stSub (by decide))
  obtain tY : (⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩ : Region).Disjoint
      ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩ :=
    (h.data.ok.st.sub_left subT).sub_right (Lay.stSub (by decide))
  -- The context, kept.
  obtain hdC : ∀ r ∈ callWr W D (sl / 16) ++ [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩, below SP 56],
      (⟨Ctx, (CtxMode.preparedN np hpn).len⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | rfl | rfl
    · exact h.ext.cs.sub_right (Lay.stSub (by decide))
    · exact h.ext.cs.sub_right (Lay.stSub (by decide))
    · exact h.ext.cd.sub_right (Region.sub_prefix (by omega_arith))
    · exact h.ext.cw.sub_right (Lay.wSub (by decide))
    · exact h.ext.cd.sub_right subT
    · exact h.kM.symm
  obtain toL : ∀ {rs : List Region}, (∀ r ∈ rs, r ∈ callWr W D (sl / 16) ++
      [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩, below SP 56]) → ∀ r ∈ rs, ∃ r' ∈ callWr W D (sl / 16) ++
      [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩, below SP 56], Region.Sub r r' :=
    fun hm r hr => ⟨r, hm r hr, fun _ h => h⟩
  obtain FL₂ : Frame (callWr W D (sl / 16) ++ [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩, below SP 56])
      s.mem (sMem D S sl s) := (F1.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨D, sl / 16 * 16⟩, by simp, Region.sub_prefix (by omega_arith)⟩).trans
      (F2.sub (toL fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp))
  obtain FL₄ : Frame (callWr W D (sl / 16) ++ [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩, below SP 56])
      s.mem t₄.mem := FL₂.trans (Fc.sub fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
        · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  obtain Pw : Gcm.X86_64.Stitch.PowersN np t₄.mem Ctx := (CtxMode.preparedN np hpn).frame FL₄ hdC h.ext.w h.ext.ok
  obtain hH : ctxH t₄.mem Ctx = ctxH s.mem Ctx := by
    simp only [ctxH_eq]
    exact blockAt_frame FL₄ fun r hr => (hdC r hr).sub_left (Offset.sub_base Ctx (show 240 + 16 ≤ 1024 by decide))
  obtain hP : ∀ j, 1 ≤ j → j ≤ 3 → t₄.mem.readW (Ctx + BitVec.ofNat 64 (SealSplit.powOff j)) 128 =
      Spec.Gcm.preparedPower (Spec.Gcm.hpow (ctxH s.mem Ctx) j) := fun j h₁ h₂ => by
    rw [← hH]
    obtain rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 := by omega_arith
    · exact (Pw 0 (by omega_arith)).2
    · exact (Pw 0 (by omega_arith)).1
    · exact (Pw 1 (by omega_arith)).2
  -- What the steps keep.
  obtain cb₂ : blockAt (sMem D S sl s) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
      blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) :=
    blockAt_frame FC (one ((h.data.ok.st.sub_left (Region.sub_prefix hsl)).sub_right (Lay.stSub (by decide))).symm)
  obtain cb₅ : blockAt t₅.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
      blockAt t₄.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) := blockAt_frame f₅ (one cbY)
  obtain bl₅ : blocksAt t₅.mem D (sl / 16) = blocksAt t₄.mem D (sl / 16) := blocksAt_frame f₅ (one qY) (by omega_arith)
  obtain y₄ : blockAt t₄.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) =
      blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) := by
    rw [blockAt_frame Fk fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact cbY.symm
      · exact qY.symm
      · exact L.st_w (a := 16) (n := 16) (d := 512) (k := 2048) (by decide) (.inr ⟨by decide, by decide⟩)
      · exact (L.stk_st (a := 16) (n := 16) (by decide)).symm]
    exact blockAt_frame FC (one ((h.data.ok.st.sub_left (Region.sub_prefix hsl)).sub_right (Lay.stSub (by decide))).symm)
  obtain hc : Spec.Gcm.aesWith R (bytesAt (sMem D S sl s) Ctx (16 * (R + 1))) = ctxCiph s.mem Ctx R :=
    ciph_frame FC (one (h.data.ctx.sub_right (Region.sub_prefix hsl))) h.rounds.2
  refine rest_ok h he₅ (rd₅.trans hD.rd) (wr₅.trans hD.wr) ((FL₄.trans (f₅.sub (toL fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp)))) ?_ ?_ ?_ ?_
  · show blocksAt t₅.mem D (sl / 16) = _
    rw [bl₅, ok₄, hc, cb₂, bl₂]
  · show blockAt t₅.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = _
    rw [cb₅, ct₄, cb₂]
  · show blockAt t₅.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) =
      ghashFrom (ctxH s.mem Ctx) (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16)) _
    rw [y₅, sProd_congr _ _ hP, y₄, sProd_ghash hF _ _ (by rw [Proof.Gcm.length_blocksAt]; omega_arith), bl₅]
  · rw [bytesAt_frame f₅ (one tY) (by omega_arith), bytesAt_frame Fk (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (h.data.ok.st.sub_left subT).sub_right (Lay.stSub (by decide))
      · exact dBT.symm
      · exact (h.data.ok.w.sub_left subT).sub_right (Lay.wSub (by decide))
      · exact (h.data.ok.stk.sub_right subT).symm) (by omega_arith), tl₂]

include hq in
/-- The texts of one to three whole blocks, from a state that `prefix` could start from but
for `rax` and the flags: the slice copied to `dst`, its whole blocks
encrypted there by a call of `vg_aes_ctr32` and absorbed at once. -/
theorem sPath_ok (hF : ShortFacts) (v : Proof.Aes.X86_64.Ctr32Impl) {t : State}
    (g : ∀ r, r ≠ .rax → t.gpr r = s.gpr r) (tm : t.mem = s.mem) (trd : t.rd = s.rd) (twr : t.wr = s.wr) :
    WP isa (.seq SealSplit.copySrc (.seq (.block SealSplit.sCtrArgs) (.seq (.call v.callee.name v.callee.code)
      (.seq SealSplit.sGh (.block SealSplit.rest))))) t (PPost Ctx W SP D S R n sl s) := by
  unfold SealSplit.copySrc
  exact WP.seq (WP.seq (WP.mono (sA_ok h g tm trd twr) fun _ hA => WP.mono (sB_ok h hq hA) fun _ hB =>
    WP.seq (WP.mono (sC_ok h hB) fun _ hC => WP.seq (WP.mono (sD_ok v hC) fun _ hD =>
      WP.seq (WP.mono (sE_ok h hq hD) fun _ hE => sF_ok h hq hF hE)))))

/-- `prefixF`: by `prefix`'s own steps for no whole block and for four or
more, by the path above for one to three. -/
theorem prefixF_ok (hF : ShortFacts) (v : Proof.Aes.X86_64.Ctr32Impl) (T : BlkToFn (CtxMode.preparedN np hpn)) :
    WP isa (SealSplit.prefixF ⟨v.callee.name, v.callee.code⟩ T.fn) s (PPost Ctx W SP D S R n sl s) := by
  have hn := h.data.ok.lt
  have hsl := h.sl_le
  have he := h.env
  unfold SealSplit.prefixF
  refine WP.seq (WP.mono (preTest3_ok (sl := sl) (by omega_arith) he h.slen) fun s₁ ⟨ax₁, cf₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  obtain he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) rd₁ wr₁
  refine WP.iteCold_iff.mpr (WP.ite (decide (sl / 16 < 3)) (by simp only [eval, cf₁]) (fun h4 => ?_) (fun _ => ?_))
  · have h4' : sl / 16 < 3 := of_decide_eq_true h4
    refine WP.seq (WP.mono (tst_ok (q := sl / 16) (by omega_arith) ax₁) fun s₂ ⟨zf₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
    obtain he₂ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := he₁.keep (fun r _ => g₂ r) rd₂ wr₂
    refine WP.ite (decide (sl / 16 = 0)) (by simp only [eval, zf₂]) (fun h0 => ?_) (fun h0 => ?_)
    · have h0' : sl / 16 = 0 := of_decide_eq_true h0
      refine tail_ok h ⟨he₂, rd₂.trans rd₁, wr₂.trans wr₁, by rw [m₂, m₁]; exact Frame.refl _ _, ?_, ?_, ?_⟩
      · rw [h0']; rfl
      · rw [h0', m₂, m₁]; rfl
      · rw [h0', m₂, m₁]; rfl
    · have h0' : sl / 16 ≠ 0 := of_decide_eq_false h0
      exact sPath_ok h ⟨by omega_arith, by omega_arith⟩ hF v (fun r hr => (g₂ r).trans (g₁ r hr)) (m₂.trans m₁)
        (rd₂.trans rd₁) (wr₂.trans wr₁)
  · exact WP.seq (WP.mono (call_ok h T he₁ ax₁ m₁ rd₁ wr₁) fun _ H => tail_ok h H)

end

/-- `prefixS` meets `PreOk` with `prefixN`'s number of blocks: by the path
above for the texts of one to three whole blocks (`prefixF_ok`), by `prefixN`'s
steps for the others. -/
theorem prefixSOk (hF : ShortFacts) (v : Proof.Aes.X86_64.Ctr32Impl) {ctr : Fn}
    (hc : ctr = ⟨v.callee.name, v.callee.code⟩) {c : Prog isa} (hE : EncNOk np hpn c)
    (T : BlkToFn (CtxMode.preparedN np hpn)) :
    PreOk (CtxMode.preparedN np hpn) (SealSplit.prefixS ctr T.fn c)
    fun n sl => if 1 ≤ sl / 256 ∧ sl / 256 < n / 256 then 16 * (n / 256) else sl / 16 := by
  intro Ctx W SP D S R n sl s h
  subst hc
  unfold SealSplit.prefixS
  refine WP.seq (WP.mono (nTest_ok (n := n) (sl := sl) h.data.ok.lt h.sl_le h.env h.slen h.len)
    fun t ⟨cf, g, tm, trd, twr⟩ => ?_)
  refine WP.ite (decide (1 ≤ sl / 256 ∧ sl / 256 < n / 256)) (by simp only [eval, cf]) (fun hc => ?_) (fun hc => ?_)
  · have hc' := of_decide_eq_true hc
    simp only [hc', and_self, ↓reduceIte]
    exact nPath_ok h hE hc' g tm trd twr
  · have he : Env Ctx (W + BitVec.ofNat 64 16) W SP t := h.env.keep (fun r hr => g r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) trd twr
    obtain hc' := of_decide_eq_false hc
    simp only [hc', ↓reduceIte]
    exact WP.mono (prefixF_ok (h.of_eq he tm trd twr) hF v T) fun _ P => (P.toG (h.of_eq he tm trd twr)).of_eq tm trd twr

end VG.Proof.AesGcm.X86_64.Split

end

end

/-!
# AES-GCM `seal_split` on x86-64: `prefixS` in constant time

Untrusted: everything here is checked by Lean. Two runs from states with the
same public values take the same branches of `nTest`, `preTest3` and the
test of `rax` (on the lengths); on the path for one to three whole blocks,
each piece is checked by the taint analysis from the registers that hold the
same values in both (`W`, then the copy's arguments, then the key context,
the state and `W`, then the data and the number of blocks that `rbx` and
`rbp` keep across the call, as `SA`–`SE` give them), and the call of
`vg_aes_ctr32` by its contract; the others are `prefix`'s pieces
(`callPart_rel`, `tail_rel`) and `prefixN`'s (`prefixFRel`, `prefixSRel`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.Split

variable {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24}

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn step)

theorem preTest3_check :
    ∃ hc, (taint.check (Taint.ofRegs [.r15]) (.block SealSplit.preTest3) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem tst_check :
    ∃ hc, (taint.check (Taint.ofRegs [.rax]) (.block [.alu .test .rax (.reg .rax)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem sCopyArgs_check : ∃ hc, (taint.check (Taint.ofRegs [.r15])
    (.block [.mov .rsi (.mem (at_ .r15 tlO)), .mov .rdi (.mem (at_ .r15 dataO)), .mov .rcx (.mem (at_ .r15 tlenO))])
    hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem sCtrArgs_check :
    ∃ hc, (taint.check (Taint.ofRegs [.r13, .r14, .r15]) (.block SealSplit.sCtrArgs) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem sGh_check :
    ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r13, .r14]) SealSplit.sGh hc).isSome = true :=
  ⟨_, by unfold SealSplit.sGh SealSplit.sGhPre SealSplit.sGhPost SealSplit.sGhStep; taint_decide⟩

section
variable {Ctx W SP D S : Addr} {R n sl : Nat} {σ σ' : State}
  (h : PP (CtxMode.preparedN np hpn) Ctx W SP D S R n sl σ) (h' : PP (CtxMode.preparedN np hpn) Ctx W SP D S R n sl σ')
include h h'

/-- What the path for one to three whole blocks starts from. -/
abbrev STs (σ t : State) : Prop :=
  (∀ r, r ≠ .rax → t.gpr r = σ.gpr r) ∧ t.mem = σ.mem ∧ t.rd = σ.rd ∧ t.wr = σ.wr

/-- After `preTest3`. -/
abbrev ST3 (sl : Nat) (σ t : State) : Prop :=
  t.gpr .rax = BitVec.ofNat 64 (sl / 16) ∧ t.cf = some (decide (sl / 16 < 3)) ∧ STs σ t

/-- After its test of `rax`. -/
abbrev STz (sl : Nat) (σ t : State) : Prop :=
  t.gpr .rax = BitVec.ofNat 64 (sl / 16) ∧ t.zf = some (decide (sl / 16 = 0)) ∧ STs σ t

/-- The path for one to three whole blocks, in two runs. -/
theorem sPath_rel (hF : Short.ShortFacts) (v : Proof.Aes.X86_64.Ctr32Impl) (hq : 1 ≤ sl / 16 ∧ sl / 16 ≤ 3) {P : State → State → Prop}
    (hP : ∀ a b, P a b → STs σ a ∧ STs σ' b) :
    RelCT isa P (.seq SealSplit.copySrc (.seq (.block SealSplit.sCtrArgs) (.seq (.call v.callee.name v.callee.code)
      (.seq SealSplit.sGh (.block SealSplit.rest))))) fun _ _ => True := by
  unfold SealSplit.copySrc
  refine RelCT.seq (RelCT.seq (step [.r15] sCopyArgs_check (F₁ := STs σ) (F₂ := STs σ')
    (G₁ := SA D S sl σ) (G₂ := SA D S sl σ')
    (fun _ _ g r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨⟨g₁, -⟩, ⟨g₂, -⟩⟩ := hP _ _ g
      rw [g₁ _ (by decide), g₂ _ (by decide), h.env.r15, h'.env.r15])
    hP (fun _ ⟨g, m, rd, wr⟩ => sA_ok h g m rd wr) (fun _ ⟨g, m, rd, wr⟩ => sA_ok h' g m rd wr))
    (step [.rsi, .rdi, .rcx] Gather.copy_check (F₁ := SA D S sl σ) (F₂ := SA D S sl σ')
      (G₁ := SB Ctx W SP D S sl σ) (G₂ := SB Ctx W SP D S sl σ')
      (fun _ _ g r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [g.1.rsi, g.2.rsi]
        · rw [g.1.rdi, g.2.rdi]
        · rw [g.1.rcx, g.2.rcx])
      (fun _ _ g => g) (fun _ g => sB_ok h hq g) (fun _ g => sB_ok h' hq g))) ?_
  refine RelCT.seq (step [.r13, .r14, .r15] sCtrArgs_check (F₁ := SB Ctx W SP D S sl σ) (F₂ := SB Ctx W SP D S sl σ')
    (G₁ := SC Ctx W SP D S R sl σ) (G₂ := SC Ctx W SP D S R sl σ')
    (fun _ _ g r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [g.1.env.r13, g.2.env.r13]
      · rw [g.1.env.r14, g.2.env.r14]
      · rw [g.1.env.r15, g.2.env.r15])
    (fun _ _ g => g) (fun _ g => sC_ok h g) (fun _ g => sC_ok h' g)) ?_
  refine RelCT.seq (rel_wp (ctr_rel v (P := fun s₁ s₂ => SC Ctx W SP D S R sl σ s₁ ∧ SC Ctx W SP D S R sl σ' s₂)
      fun s₁ s₂ g => ⟨_, _, _, _, _, _, g.1.call, g.2.call, by rw [g.1.env.rsp, g.2.env.rsp]⟩)
    (fun _ _ g => g) (fun _ g => sD_ok v g) (fun _ g => sD_ok v g)) ?_
  refine RelCT.seq (step [.rbx, .rbp, .r13, .r14] sGh_check
    (F₁ := SD Ctx W SP D S R sl σ) (F₂ := SD Ctx W SP D S R sl σ')
    (G₁ := SE Ctx W SP D S R sl σ) (G₂ := SE Ctx W SP D S R sl σ')
    (fun _ _ g r hr => by
      obtain ⟨-, g₁, g₂⟩ := g
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [g₁.rbx, g₂.rbx]
      · rw [g₁.rbp, g₂.rbp]
      · rw [g₁.env.r13, g₂.env.r13]
      · rw [g₁.env.r14, g₂.env.r14])
    (fun _ _ g => g.2) (fun _ g => sE_ok h hq g) (fun _ g => sE_ok h' hq g)) ?_
  exact (step [.r15] rest_check (F₁ := SE Ctx W SP D S R sl σ) (F₂ := SE Ctx W SP D S R sl σ')
    (G₁ := fun _ => True) (G₂ := fun _ => True)
    (fun _ _ g r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨⟨u, hu, -, -, gu, -⟩, ⟨u', hu', -, -, gu', -⟩⟩ := g
      rw [gu _ (by decide), gu' _ (by decide), hu.env.r15, hu'.env.r15])
    (fun _ _ g => g) (fun _ g => WP.mono (sF_ok h hq hF g) fun _ _ => trivial)
    (fun _ g => WP.mono (sF_ok h' hq hF g) fun _ _ => trivial)).mono
    (fun _ _ g => g) fun _ _ _ => trivial

end

/-- `prefixF` in two runs. -/
theorem prefixFRel (hF : Short.ShortFacts) (v : Proof.Aes.X86_64.Ctr32Impl)
    (T : BlkToFn (CtxMode.preparedN np hpn)) :
    PreRel (CtxMode.preparedN np hpn) (SealSplit.prefixF ⟨v.callee.name, v.callee.code⟩ T.fn) := by
  intro Ctx W SP D S R n sl σ σ' h h'
  unfold SealSplit.prefixF SealSplit.preTail
  have hsl : ∀ {σ : State}, PP (CtxMode.preparedN np hpn) Ctx W SP D S R n sl σ → sl < 2 ^ 64 := fun h => by
    have := h.sl_le; have := h.data.ok.lt; omega_arith
  have he : ∀ {σ t : State}, PP (CtxMode.preparedN np hpn) Ctx W SP D S R n sl σ → STs σ t →
      Env Ctx (W + BitVec.ofNat 64 16) W SP t := fun h g => h.env.keep (fun r hr => g.1 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide))
    g.2.2.1 g.2.2.2
  have pre4 : ∀ {σ : State}, PP (CtxMode.preparedN np hpn) Ctx W SP D S R n sl σ →
      WP isa (.block SealSplit.preTest3) σ (ST3 sl σ) := fun h =>
    WP.mono (preTest3_ok (hsl h) h.env h.slen) fun _ ⟨ax, cf, g, m, rd, wr⟩ => ⟨ax, cf, g, m, rd, wr⟩
  refine RelCT.seq (step [.r15] preTest3_check (F₁ := (· = σ)) (F₂ := (· = σ'))
    (G₁ := ST3 sl σ) (G₂ := ST3 sl σ')
    (fun _ _ g r hr => by
      obtain ⟨rfl, rfl⟩ := g; simp only [List.mem_singleton] at hr; subst hr; rw [h.env.r15, h'.env.r15])
    (fun _ _ g => g) (fun _ hs => by rw [hs]; exact pre4 h) (fun _ hs => by rw [hs]; exact pre4 h')) ?_
  refine RelCT.iteCold (RelCT.ite (fun _ _ g => by simp only [eval, g.1.2.1, g.2.2.1]) ?_ ?_)
  · refine StreamTo.RelCT.of_imp (sl / 16 < 3) (fun _ _ g => by
      have e := g.2; simp only [eval, g.1.1.2.1] at e; simpa using e) fun h4 => ?_
    have tz : ∀ {σ t : State}, ST3 sl σ t → WP isa (.block [.alu .test .rax (.reg .rax)]) t (STz sl σ) :=
      fun ⟨ax, _, g, m, rd, wr⟩ => WP.mono (tst_ok (q := sl / 16) (by omega_using [h4]) ax) fun _ ⟨zf, g', m', rd', wr'⟩ =>
        ⟨by rw [g' .rax]; exact ax, zf, fun r hr => (g' r).trans (g r hr), m'.trans m, rd'.trans rd, wr'.trans wr⟩
    refine RelCT.seq (step [.rax] tst_check (F₁ := ST3 sl σ) (F₂ := ST3 sl σ')
      (G₁ := STz sl σ) (G₂ := STz sl σ')
      (fun _ _ g r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [g.1.1.1, g.1.2.1])
      (fun _ _ g => g.1) (fun _ g => tz g) (fun _ g => tz g)) ?_
    refine RelCT.ite (fun _ _ g => by simp only [eval, g.1.2.1, g.2.2.1]) ?_ ?_
    · refine StreamTo.RelCT.of_imp (sl / 16 = 0) (fun _ _ g => by
        have e := g.2; simp only [eval, g.1.1.2.1] at e; simpa using e) fun h0 => ?_
      exact (tail_rel h h').mono (fun _ _ g =>
        ⟨mid2_zero ⟨he h g.1.1.2.2, g.1.1.1, g.1.1.2.1, g.1.1.2.2.2⟩ h0,
          mid2_zero ⟨he h' g.1.2.2.2, g.1.2.1, g.1.2.2.1, g.1.2.2.2.2⟩ h0⟩) fun _ _ g => g
    · refine StreamTo.RelCT.of_imp (sl / 16 ≠ 0) (fun _ _ g => by
        have e := g.2; simp only [eval, g.1.1.2.1] at e; simpa using e) fun h0 => ?_
      exact sPath_rel h h' hF v ⟨by omega_using [h0], by omega_using [h4]⟩ fun _ _ g => ⟨g.1.1.2.2, g.1.2.2.2⟩
  · exact RelCT.seq ((callPart_rel h h' T).mono (fun _ _ g =>
      ⟨⟨he h g.1.1.2.2, g.1.1.1, g.1.1.2.2.2⟩, ⟨he h' g.1.2.2.2, g.1.2.1, g.1.2.2.2.2⟩⟩) fun _ _ g => g)
      (tail_rel h h')

/-- `prefixS` in two runs. -/
theorem prefixSRel (hF : Short.ShortFacts) (v : Proof.Aes.X86_64.Ctr32Impl) {ctr : Fn} (hc : ctr = ⟨v.callee.name, v.callee.code⟩)
    {c : Prog isa} (hE : EncNOk np hpn c)
    (hct : ∃ hc, (taint.check (Taint.ofRegs encNRegs) c hc).isSome = true) (T : BlkToFn (CtxMode.preparedN np hpn)) :
    PreRel (CtxMode.preparedN np hpn) (SealSplit.prefixS ctr T.fn c) := by
  intro Ctx W SP D S R n sl σ σ' h h'
  subst hc
  unfold SealSplit.prefixS
  refine RelCT.seq (step [.r15] nTest_check (F₁ := (· = σ)) (F₂ := (· = σ'))
    (G₁ := NT n sl σ) (G₂ := NT n sl σ')
    (fun _ _ g r hr => by
      obtain ⟨rfl, rfl⟩ := g; simp only [List.mem_singleton] at hr; subst hr; rw [h.env.r15, h'.env.r15])
    (fun _ _ g => g) (fun _ hs => by rw [hs]; exact nTest_ok h.data.ok.lt h.sl_le h.env h.slen h.len)
    (fun _ hs => by rw [hs]; exact nTest_ok h'.data.ok.lt h'.sl_le h'.env h'.slen h'.len)) ?_
  refine RelCT.ite (fun _ _ g => by simp only [eval, g.1.1, g.2.1]) ?_ ?_
  · refine StreamTo.RelCT.of_imp (1 ≤ sl / 256 ∧ sl / 256 < n / 256) (fun _ _ g => by
      have e := g.2; simp only [eval, g.1.1.1] at e; simpa using e) fun hC => ?_
    exact nPath_rel h h' hE hct hC fun _ _ g => g.1
  · refine rel_each fun t t' g => ?_
    obtain ⟨⟨⟨-, g₁, m₁, rd₁, wr₁⟩, ⟨-, g₂, m₂, rd₂, wr₂⟩⟩, -⟩ := g
    have he : ∀ {σ t : State} {M : CtxMode} {R : Nat}, PP M Ctx W SP D S R n sl σ →
        (∀ r, r ≠ .rax → r ≠ .rcx → t.gpr r = σ.gpr r) → t.rd = σ.rd → t.wr = σ.wr →
        Env Ctx (W + BitVec.ofNat 64 16) W SP t := fun h g rd wr => h.env.keep (fun r hr => g r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide))
      rd wr
    exact prefixFRel hF v T (h.of_eq (he h g₁ rd₁ wr₁) m₁ rd₁ wr₁) (h'.of_eq (he h' g₂ rd₂ wr₂) m₂ rd₂ wr₂)

/-! ## What every instruction of `prefixS` does not do -/

/-- The path for one to three whole blocks, but for the call. -/
theorem sParts_mx : (SealSplit.copySrc.allInstrs (fun i => !loadsMxcsr i) &&
    (Code.block SealSplit.sCtrArgs : Prog isa).allInstrs (fun i => !loadsMxcsr i) &&
    SealSplit.sGh.allInstrs (fun i => !loadsMxcsr i) &&
    (Code.block SealSplit.rest : Prog isa).allInstrs (fun i => !loadsMxcsr i)) = true := by
  decide +kernel
theorem sParts_spSafe : (SealSplit.copySrc.all (fun i => !X86_64.isa.writesSp i) &&
    (Code.block SealSplit.sCtrArgs : Prog isa).all (fun i => !X86_64.isa.writesSp i) &&
    SealSplit.sGh.all (fun i => !X86_64.isa.writesSp i) &&
    (Code.block SealSplit.rest : Prog isa).all (fun i => !X86_64.isa.writesSp i)) = true := by
  decide +kernel
theorem sParts_xdepth : SealSplit.copySrc.x86_64Depth = 0 ∧ SealSplit.sGh.x86_64Depth = 0 := by
  decide +kernel

theorem prefixS_mx {ctr fTo : Fn} {c : Prog isa} (hc : ctr.code.allInstrs (fun i => !loadsMxcsr i) = true)
    (h : (SealSplit.prefixN fTo c).allInstrs (fun i => !loadsMxcsr i) = true) :
    (SealSplit.prefixS ctr fTo c).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := sParts_mx
  simp only [SealSplit.prefixS, SealSplit.prefixN, SealSplit.prefixF, Code.iteCold, SealSplit.prefix, SealSplit.preTail,
    Code.allInstrs, Bool.and_eq_true] at e h hc ⊢
  simp only [e, h, hc, and_self, and_true, true_and]
  decide

theorem prefixS_spSafe {ctr fTo : Fn} {c : Prog isa} (hc : ctr.code.all (fun i => !X86_64.isa.writesSp i) = true)
    (h : (SealSplit.prefixN fTo c).all (fun i => !X86_64.isa.writesSp i) = true) :
    (SealSplit.prefixS ctr fTo c).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := sParts_spSafe
  simp only [SealSplit.prefixS, SealSplit.prefixN, SealSplit.prefixF, Code.iteCold, SealSplit.prefix, SealSplit.preTail,
    Code.all, Bool.and_eq_true] at e h hc ⊢
  simp only [e, h, hc, and_self, and_true, true_and]
  decide

theorem prefixS_xdepth {ctr fTo : Fn} {c : Prog isa} (hc : ctr.code.x86_64Depth = 0) {d : Nat} (hd : 8 ≤ d)
    (h : (SealSplit.prefixN fTo c).x86_64Depth ≤ d) : (SealSplit.prefixS ctr fTo c).x86_64Depth ≤ d := by
  have e := sParts_xdepth
  simp only [SealSplit.prefixS, SealSplit.prefixN, SealSplit.prefixF, Code.iteCold, SealSplit.prefix, SealSplit.preTail,
    Code.x86_64Depth, hc, e.1, e.2] at h ⊢
  simp only [Nat.max_le] at h ⊢; omega

end VG.Proof.AesGcm.X86_64.Split

end

end

/-! ### `AesGcm.X86_64.Split.OnePassZ`, which only this module used -/

section

/-!
# AES-GCM `seal_split` on x86-64: the one-pass loops

Untrusted: everything here is checked by Lean. What `prefixN` needs of its
loop (`EncNOk`, the taint check from `encNRegs`, and that no instruction
loads `MXCSR` or writes `rsp` and nothing is pushed), for the loop on
512-bit registers (`StitchZHTo.encN`, from its literal) and for that on
256-bit ones (`StitchR.encN`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64

theorem encNR_ok {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24} (hS : Gcm.X86_64.StitchR.SetupFin np hpn) :
    EncNOk np hpn Impl.Gcm.X86_64.StitchR.encN :=
  fun hp hm hn => Gcm.X86_64.StitchR.encN_ok hS hp hm hn

theorem encNZ_ok (h1 : Gcm.X86_64.StitchZHTo.PhaseOne) : EncNOk 24 (by decide) Impl.Gcm.X86_64.StitchZHTo.encN :=
  fun hp hm hn => Gcm.X86_64.StitchZHTo.encN_ok h1 hp hm hn

theorem encNZ_check :
    ∃ hc, (taint.check (Taint.ofRegs encNRegs) Impl.Gcm.X86_64.StitchZHTo.encN hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem encNZ_mx : Impl.Gcm.X86_64.StitchZHTo.encN.allInstrs (fun i => !loadsMxcsr i) = true := by
  lit_decide
theorem encNZ_spSafe : Impl.Gcm.X86_64.StitchZHTo.encN.all (fun i => !X86_64.isa.writesSp i) = true :=
  Code.all_of_spTest (by lit_decide)
theorem encNZ_xdepth : Impl.Gcm.X86_64.StitchZHTo.encN.x86_64Depth = 0 := by decide +kernel

end VG.Proof.AesGcm.X86_64.Split

end

end

/-!
# AES-GCM `seal_split` on x86-64 with a prepared key context: `Verified`

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_split_prepared`
takes the path for TLS records (`Fast.sel`) before `splitMid` if the
implementations have `seal`'s short path (`splitMidR`), which needs the CPU
features of the loops on 512-bit registers; it meets the shared contract of
`Spec/Gcm/Prepared.lean` as `Split.sealSplitP_framed` does
(`sealSplitPrepared_framed`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Split

variable {np : Nat} {hpn : 8 ≤ np ∧ np ≤ 24}

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts)
open VG.Proof.AesGcm.X86_64.Fast (fastCond_mx fastCond_spSafe fastCond_xdepth fastAad_mx fastAad_spSafe
  fastAad_xdepth)

/-- The one-pass loop named `n`. -/
def _root_.VG.Proof.AesGcm.X86_64.OnePassName.code : OnePassName → Prog isa
  | .r => Impl.Gcm.X86_64.StitchR.encN
  | .z => Impl.Gcm.X86_64.StitchZHTo.encN

theorem _root_.VG.Proof.AesGcm.X86_64.OnePassName.ok (hF : ShortFacts) :
    ∀ n : OnePassName, (n = .z → np = 24) → EncNOk np hpn n.code
  | .r, _ => encNR_ok (hF.setupFin np hpn)
  | .z, h => by obtain rfl := h rfl; exact encNZ_ok hF.phaseOneZ

theorem _root_.VG.Proof.AesGcm.X86_64.OnePassName.check :
    ∀ n : OnePassName, ∃ hc, (taint.check (Taint.ofRegs encNRegs) n.code hc).isSome = true
  | .r => encN_check
  | .z => encNZ_check

theorem _root_.VG.Proof.AesGcm.X86_64.OnePassName.mx :
    ∀ n : OnePassName, n.code.allInstrs (fun i => !loadsMxcsr i) = true
  | .r => encNR_mx
  | .z => encNZ_mx

theorem _root_.VG.Proof.AesGcm.X86_64.OnePassName.spSafe :
    ∀ n : OnePassName, n.code.all (fun i => !X86_64.isa.writesSp i) = true
  | .r => encNR_spSafe
  | .z => encNZ_spSafe

theorem _root_.VG.Proof.AesGcm.X86_64.OnePassName.xdepth : ∀ n : OnePassName, n.code.x86_64Depth = 0
  | .r => encNR_xdepth
  | .z => encNZ_xdepth

/-- The whole blocks of the path for TLS records: in one pass if `v` takes
them so (`SealSplit.prefixN`, with its loop; on 256-bit registers, one to
three whole blocks without it, `SealSplit.prefixS`), and otherwise by `fTo`
(`SealSplit.prefix`). -/
def _root_.VG.Proof.AesGcm.X86_64.GcmImpl.splitPre (v : GcmImpl) (fTo : Fn) : Prog isa :=
  match v.onePass with
  | some .r => SealSplit.prefixS ⟨v.ctr.callee.name, v.ctr.callee.code⟩ fTo OnePassName.r.code
  | some .z => SealSplit.prefixN fTo OnePassName.z.code
  | none => SealSplit.prefix fTo

/-- `seal_split`'s code after the entry for the implementations `v` and a
prepared key context: the path for TLS records first, from 256 bytes if `v`
has `seal`'s short path, which is faster for less, and otherwise at every
length (`any`). -/
def _root_.VG.Proof.AesGcm.X86_64.GcmImpl.splitMidR (v : GcmImpl) (c : Callees) (fTo : Fn) : Prog isa :=
  if v.short then Fast.sel c (v.splitPre fTo) Short.finKs v.splitFin (v.splitMid c fTo)
  else Fast.sel c (v.splitPre fTo) Short.finKsA v.splitFin (v.splitMid c fTo) true

theorem fastTail_mx : (Fast.tail Short.finKs : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel
theorem fastTail_spSafe : (Fast.tail Short.finKs : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel
theorem fastTail_xdepth : (Fast.tail Short.finKs : Prog isa).x86_64Depth = 0 := by decide +kernel
theorem fastTailA_mx : (Fast.tail Short.finKsA : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel
theorem fastTailA_spSafe : (Fast.tail Short.finKsA : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel
theorem fastTailA_xdepth : (Fast.tail Short.finKsA : Prog isa).x86_64Depth = 0 := by decide +kernel

section
variable (v : GcmImpl) (B : BlkFn (CtxMode.preparedN np hpn)) (T : BlkToFn (CtxMode.preparedN np hpn))

theorem tail_mx :
    ((.seq (SealSplit.«prefix» T.fn) (SealSplit.body (v.withBlk B) v.splitFin) : Prog isa)).allInstrs
      (fun i => !loadsMxcsr i) = true :=
  ((Bool.and_eq_true _ _).mp (run_mx v B T)).2

theorem tail_spSafe :
    ((.seq (SealSplit.«prefix» T.fn) (SealSplit.body (v.withBlk B) v.splitFin) : Prog isa)).all
      (fun i => !X86_64.isa.writesSp i) = true :=
  ((Bool.and_eq_true _ _).mp (run_spSafe v B T)).2

theorem tail_xdepth :
    ((.seq (SealSplit.«prefix» T.fn) (SealSplit.body (v.withBlk B) v.splitFin) : Prog isa)).x86_64Depth ≤ 56 :=
  (Nat.max_le.mp (run_xdepth v B T)).2

omit B in
theorem splitPre_mx (tp : (SealSplit.prefix T.fn).allInstrs (fun i => !loadsMxcsr i) = true) :
    (v.splitPre T.fn).allInstrs (fun i => !loadsMxcsr i) = true := by
  unfold GcmImpl.splitPre; split
  exacts [prefixS_mx v.ctr.mxcsr (prefixN_mx (OnePassName.mx _) tp), prefixN_mx (OnePassName.mx _) tp, tp]

omit B in
theorem splitPre_spSafe (tp : (SealSplit.prefix T.fn).all (fun i => !X86_64.isa.writesSp i) = true) :
    (v.splitPre T.fn).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold GcmImpl.splitPre; split
  exacts [prefixS_spSafe v.ctr.spSafe (prefixN_spSafe (OnePassName.spSafe _) tp),
    prefixN_spSafe (OnePassName.spSafe _) tp, tp]

omit B in
theorem splitPre_xdepth (tp : (SealSplit.prefix T.fn).x86_64Depth ≤ 56) : (v.splitPre T.fn).x86_64Depth ≤ 56 := by
  unfold GcmImpl.splitPre; split
  exacts [prefixS_xdepth v.ctr.noStack (by decide) (prefixN_xdepth (OnePassName.xdepth _) tp),
    prefixN_xdepth (OnePassName.xdepth _) tp, tp]

theorem splitMidR_mx : (v.splitMidR (v.withBlk B) T.fn).allInstrs (fun i => !loadsMxcsr i) = true := by
  unfold GcmImpl.splitMidR; split
  · obtain ⟨tp, tb⟩ := (Bool.and_eq_true _ _).mp (tail_mx v B T)
    replace tp := splitPre_mx v T tp
    have o := splitMid_mx v B T
    simp only [Fast.sel, Fast.run, Code.allInstrs] at tp tb o ⊢
    rw [fastCond_mx, fastAad_mx, o, tp, tb, fastTail_mx]; rfl
  · obtain ⟨tp, tb⟩ := (Bool.and_eq_true _ _).mp (tail_mx v B T)
    replace tp := splitPre_mx v T tp
    have o := splitMid_mx v B T
    simp only [Fast.sel, Fast.run, Code.allInstrs] at tp tb o ⊢
    rw [fastCond_mx, fastAad_mx, o, tp, tb, fastTailA_mx]; rfl

theorem splitMidR_spSafe : (v.splitMidR (v.withBlk B) T.fn).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold GcmImpl.splitMidR; split
  · obtain ⟨tp, tb⟩ := (Bool.and_eq_true _ _).mp (tail_spSafe v B T)
    replace tp := splitPre_spSafe v T tp
    have o := splitMid_spSafe v B T
    simp only [Fast.sel, Fast.run, Code.all] at tp tb o ⊢
    rw [fastCond_spSafe, fastAad_spSafe, o, tp, tb, fastTail_spSafe]; rfl
  · obtain ⟨tp, tb⟩ := (Bool.and_eq_true _ _).mp (tail_spSafe v B T)
    replace tp := splitPre_spSafe v T tp
    have o := splitMid_spSafe v B T
    simp only [Fast.sel, Fast.run, Code.all] at tp tb o ⊢
    rw [fastCond_spSafe, fastAad_spSafe, o, tp, tb, fastTailA_spSafe]; rfl

theorem splitMidR_xdepth : (v.splitMidR (v.withBlk B) T.fn).x86_64Depth ≤ 56 := by
  unfold GcmImpl.splitMidR; split
  · have t := tail_xdepth v B T
    have tp := splitPre_xdepth v T (Nat.max_le.mp t).1
    have o := splitMid_xdepth v B T
    simp only [Fast.sel, Fast.run, Code.x86_64Depth, fastCond_xdepth, fastAad_xdepth, fastTail_xdepth,
      Nat.max_le] at t tp o ⊢
    omega_using [tp, o, t]
  · have t := tail_xdepth v B T
    have tp := splitPre_xdepth v T (Nat.max_le.mp t).1
    have o := splitMid_xdepth v B T
    simp only [Fast.sel, Fast.run, Code.x86_64Depth, fastCond_xdepth, fastAad_xdepth, fastTailA_xdepth,
      Nat.max_le] at t tp o ⊢
    omega_using [tp, o, t]

theorem splitMidR_ok (hF : ShortFacts) (hz : ∀ n, v.onePass = some n → n = .z → np = 24) : MidOk (CtxMode.preparedN np hpn) (v.splitMidR (v.withBlk B) T.fn) := by
  unfold GcmImpl.splitMidR GcmImpl.splitPre; split <;> split
  · exact Fast.sel_ok hF v B (prefixSOk hF v.ctr rfl (OnePassName.ok hF .r nofun) T) Short.finKs_ksOk
      (splitFin_ok v hF) (splitMid_ok v B T hF)
  · exact Fast.sel_ok hF v B (prefixNOk (OnePassName.ok hF _ (hz _ ‹_›)) T) Short.finKs_ksOk (splitFin_ok v hF)
      (splitMid_ok v B T hF)
  · exact Fast.sel_ok hF v B (prefixOk T) Short.finKs_ksOk (splitFin_ok v hF) (splitMid_ok v B T hF)
  · exact Fast.sel_ok hF v B (prefixSOk hF v.ctr rfl (OnePassName.ok hF .r nofun) T) Short.finKsA_ksOk
      (splitFin_ok v hF) (splitMid_ok v B T hF)
  · exact Fast.sel_ok hF v B (prefixNOk (OnePassName.ok hF _ (hz _ ‹_›)) T) Short.finKsA_ksOk (splitFin_ok v hF)
      (splitMid_ok v B T hF)
  · exact Fast.sel_ok hF v B (prefixOk T) Short.finKsA_ksOk (splitFin_ok v hF) (splitMid_ok v B T hF)

theorem splitMidR_rel (hF : ShortFacts) (hz : ∀ n, v.onePass = some n → n = .z → np = 24) : MidRel (CtxMode.preparedN np hpn) (v.splitMidR (v.withBlk B) T.fn) := by
  have hq : ∀ n sl : Nat, sl ≤ n → 16 * (sl / 16) ≤ n := fun _ _ h => by omega_using [h]
  have nq : ∀ n sl : Nat, sl ≤ n →
      16 * (if 1 ≤ sl / 256 ∧ sl / 256 < n / 256 then 16 * (n / 256) else sl / 16) ≤ n :=
    fun n sl h => by split <;> omega_arith
  unfold GcmImpl.splitMidR GcmImpl.splitPre; split <;> split
  · exact @Fast.sel_rel _ _ false v B _ _ (prefixSOk hF v.ctr rfl (OnePassName.ok hF .r nofun) T)
      (prefixSRel hF v.ctr rfl (OnePassName.ok hF .r nofun) (OnePassName.check _) T) nq hF _ Short.finKs_ksOk
      Short.finKs_rel _ (splitFin_rel v hF) _ (splitMid_rel v B T hF)
  · exact @Fast.sel_rel _ _ false v B _ _ (prefixNOk (OnePassName.ok hF _ (hz _ ‹_›)) T)
      (prefixNRel (OnePassName.ok hF _ (hz _ ‹_›)) (OnePassName.check _) T) nq hF _ Short.finKs_ksOk Short.finKs_rel _
      (splitFin_rel v hF) _ (splitMid_rel v B T hF)
  · exact @Fast.sel_rel _ _ false v B _ _ (prefixOk T) (prefixRel T) hq hF _ Short.finKs_ksOk Short.finKs_rel _
      (splitFin_rel v hF) _ (splitMid_rel v B T hF)
  · exact @Fast.sel_rel _ _ true v B _ _ (prefixSOk hF v.ctr rfl (OnePassName.ok hF .r nofun) T)
      (prefixSRel hF v.ctr rfl (OnePassName.ok hF .r nofun) (OnePassName.check _) T) nq hF _ Short.finKsA_ksOk
      Short.finKsA_rel _ (splitFin_rel v hF) _ (splitMid_rel v B T hF)
  · exact @Fast.sel_rel _ _ true v B _ _ (prefixNOk (OnePassName.ok hF _ (hz _ ‹_›)) T)
      (prefixNRel (OnePassName.ok hF _ (hz _ ‹_›)) (OnePassName.check _) T) nq hF _ Short.finKsA_ksOk Short.finKsA_rel _
      (splitFin_rel v hF) _ (splitMid_rel v B T hF)
  · exact @Fast.sel_rel _ _ true v B _ _ (prefixOk T) (prefixRel T) hq hF _ Short.finKsA_ksOk Short.finKsA_rel _
      (splitFin_rel v hF) _ (splitMid_rel v B T hF)

theorem sealSplitR_mx :
    (SealSplit.«seal» (v.splitMidR (v.withBlk B) T.fn)).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [SealSplit.«seal», Code.allInstrs]
  rw [splitMidR_mx v B T]; rfl

theorem sealSplitR_spSafe :
    (SealSplit.«seal» (v.splitMidR (v.withBlk B) T.fn)).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [SealSplit.«seal», Code.all]
  rw [splitMidR_spSafe v B T]; rfl

theorem sealSplitR_xdepth : (SealSplit.«seal» (v.splitMidR (v.withBlk B) T.fn)).x86_64Depth ≤ 56 := by
  have := splitMidR_xdepth v B T
  simp only [SealSplit.«seal», Code.x86_64Depth, tagOut, Nat.max_le]
  omega_using [this]

theorem sealSplitR_correct (hF : ShortFacts) (hz : ∀ n, v.onePass = some n → n = .z → np = 24) (s : State)
    (hs : (Proof.AesGcm.sealSplitX86_64M (CtxMode.preparedN np hpn)).pre s) :
    ∃ t s', Exec isa (SealSplit.«seal» (v.splitMidR (v.withBlk B) T.fn)) s t s' ∧ abiPreserved s s' ∧
      (Proof.AesGcm.sealSplitX86_64M (CtxMode.preparedN np hpn)).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := sealSplitM_wp (splitMidR_ok v B T hF hz) hs
  exact ⟨t, s', he, abiPreserved_of_exec (sealSplitR_mx v B T) he hg, hp⟩

end

section
variable (v : GcmImpl) (B : BlkFn CtxMode.prepared) (T : BlkToFn CtxMode.prepared)

theorem sealSplitPrepared_core (hF : ShortFacts) :
    Verified X86_64.target (SealSplit.«seal» (v.splitMidR (v.withBlk B) T.fn))
      (Proof.AesGcm.sealSplitPreparedScratchContract X86_64.abi 56) :=
  Verified.of_correct (k := Proof.AesGcm.sealSplitX86_64M CtxMode.prepared) (sealSplitR_correct v B T hF (fun _ _ _ => rfl))
    (sealSplitM_ct (splitMidR_ok v B T hF (fun _ _ _ => rfl)) (splitMidR_rel v B T hF (fun _ _ _ => rfl)))
    splitPrepared_implies

/-- `vg_aes_gcm_seal_split_prepared`, in its frame. -/
theorem sealSplitPrepared_framed (hF : ShortFacts) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2616 5 (SealSplit.«seal» (v.splitMidR (v.withBlk B) T.fn)))
      (Proof.Gcm.sealSplitPreparedContract X86_64.abi 2672) :=
  X86_64.Verified.stackArgScratch (hpostOut := Proof.AesGcm.sealSplitPrecomputedPostOut_local _) (sig := Proof.Gcm.sealSplitPreparedSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Proof.Gcm.sealSplitPreparedPre X86_64.abi.ptrBits)
    (post := Proof.Gcm.sealSplitPost X86_64.abi.ptrBits) (wa := true) (stack := 56)
    (bytes := 2616) (sealSplitPrepared_core v B T hF) (by decide) (by decide) (by decide)
    (sealSplitR_spSafe v B T) (sealSplitR_xdepth v B T) (Proof.AesGcm.sealSplitPreparedPre_local _)
    (Proof.AesGcm.sealSplitPrecomputedPost_local _) splitFrameSatPrepared_pre

end

end VG.Proof.AesGcm.X86_64.Split

end

end

/-! # Prepared-context StreamTo contracts -/

@[expose] public section

set_option linter.unusedSimpArgs false
namespace VG.Proof.AesGcm.X86_64.StreamTo
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm (arg args rounds)
open VG.Impl.AesGcm.X86_64.StreamTo

theorem streamToPrepared_implies : (Proof.AesGcm.streamEncryptToX86_64M CtxMode.prepared).Implies
    (Proof.AesGcm.streamEncryptToPreparedScratchContract X86_64.abi 2624) := by
  exact { pre := by sig_implies_pre [Proof.AesGcm.streamEncryptToPreparedScratchContract,
      Proof.AesGcm.streamEncryptToPreparedScratchSig, Proof.AesGcm.streamEncryptToPrecomputedScratchSig, Proof.Gcm.streamEncryptToPreparedPre,
      Proof.Gcm.streamEncryptToPost, Proof.AesGcm.streamEncryptToX86_64M,
      Proof.AesGcm.streamToPreM, Proof.AesGcm.streamToPost, Proof.AesGcm.streamToPub, X86_64.abi,
      Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stkS, Proof.AesGcm.ret, Proof.AesGcm.rounds,
      X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs, CtxMode.prepared, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr]
          post := by sig_implies_post [Proof.AesGcm.streamEncryptToPreparedScratchContract,
      Proof.AesGcm.streamEncryptToPreparedScratchSig, Proof.AesGcm.streamEncryptToPrecomputedScratchSig, Proof.Gcm.streamEncryptToPreparedPre,
      Proof.Gcm.streamEncryptToPost, Proof.AesGcm.streamEncryptToX86_64M,
      Proof.AesGcm.streamToPreM, Proof.AesGcm.streamToPost, Proof.AesGcm.streamToPub, X86_64.abi,
      Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stkS, Proof.AesGcm.ret, Proof.AesGcm.rounds,
      X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs, CtxMode.prepared, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr]
          pub := by sig_implies_pub [Proof.AesGcm.streamEncryptToPreparedScratchContract,
      Proof.AesGcm.streamEncryptToPreparedScratchSig, Proof.AesGcm.streamEncryptToPrecomputedScratchSig, Proof.Gcm.streamEncryptToPreparedPre,
      Proof.Gcm.streamEncryptToPost, Proof.AesGcm.streamEncryptToX86_64M,
      Proof.AesGcm.streamToPreM, Proof.AesGcm.streamToPost, Proof.AesGcm.streamToPub, X86_64.abi,
      Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stkS, Proof.AesGcm.ret, Proof.AesGcm.rounds,
      X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs, CtxMode.prepared, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr]
          sat := ⟨streamToSatP, by
            sig_pre [Proof.AesGcm.streamEncryptToPreparedScratchContract,
              Proof.AesGcm.streamEncryptToPreparedScratchSig, Proof.AesGcm.streamEncryptToPrecomputedScratchSig, Proof.Gcm.streamEncryptToPreparedPre,
              X86_64.abi, X86_64.argRegs, streamToSatP, streamToSat]
            sig_and_intros
            all_goals first
              | rfl
              | decide
              | exact preparedPowersRepr_of_zero fun _ _ => rfl
              | exact Region.disjoint_of_sep (by decide)⟩ }

theorem streamEncryptToPrepared_core (T : BlkToFn CtxMode.prepared) (E : EncFn CtxMode.prepared) :
    Verified X86_64.target (encrypt T.fn E.fn)
      (Proof.AesGcm.streamEncryptToPreparedScratchContract X86_64.abi 2624) :=
  Verified.of_correct (k := Proof.AesGcm.streamEncryptToX86_64M CtxMode.prepared) (encrypt_correct T E)
    (encrypt_ct T E) streamToPrepared_implies

theorem streamToFrameSatPrepared_pre : ∃ s, (Proof.Gcm.streamEncryptToPreparedContract X86_64.abi 4856).pre s := by
  refine ⟨streamToFrameSatP, ?_⟩
  sig_pre [Proof.Gcm.streamEncryptToPreparedContract, Proof.Gcm.streamEncryptToPreparedSig, Proof.Gcm.streamEncryptToPrecomputedSig,
    Proof.Gcm.streamEncryptToPreparedPre, Proof.Gcm.streamEncryptToPost, X86_64.abi, X86_64.argRegs,
    streamToFrameSatP, streamToFrameSat, streamToSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact preparedPowersRepr_of_zero fun _ _ => rfl

theorem streamEncryptToPrepared_framed (T : BlkToFn CtxMode.prepared) (E : EncFn CtxMode.prepared) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 2232 3 (encrypt T.fn E.fn))
      (Proof.Gcm.streamEncryptToPreparedContract X86_64.abi 4856) :=
  X86_64.Verified.stackArgScratchPre (hpostOut := Proof.AesGcm.streamEncryptToPrecomputedPostOut_local _ _ (fun _ _ _ _ _ _ _ _ _ _ h => h.2.1)) (sig := Proof.Gcm.streamEncryptToPreparedSig) (nm := "scratch")
    (e := .u64) (n := 274) (pre := Proof.Gcm.streamEncryptToPreparedPre X86_64.abi.ptrBits)
    (post := Proof.Gcm.streamEncryptToPost X86_64.abi.ptrBits) (wa := true) (stack := 2624)
    (bytes := 2232) (streamEncryptToPrepared_core T E) (by decide) (by decide) (by decide)
    (encrypt_spAll T E) (encrypt_xdepth T E) (Proof.AesGcm.streamEncryptToPreparedPre_local _)
    (Proof.AesGcm.streamEncryptToPrecomputedPost_local _) streamToFrameSatPrepared_pre

end VG.Proof.AesGcm.X86_64.StreamTo
