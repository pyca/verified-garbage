module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixN
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Tab
public import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.AesGcm.X86_64.Split.PrefixOk
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Copy
import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Finish
import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Aad
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# AES-GCM `seal_split` on x86-64: one to three whole blocks at `src`

Untrusted: everything here is checked by Lean. `prefixS` takes the texts whose
first slice holds one to three whole blocks (`sTest_ok`): it copies the
slice to `dst` (`copySrc`), encrypts its whole blocks there with a call of
`vg_aes_ctr32` from the counter block (`sCall_ok`), and absorbs them into
`Y` at once with the prepared powers of the key context (`sGhK_ok`), then
keeps the data from them on as `prefix` does; it meets `PreOk` with the
number of blocks of `prefixN` (`prefixSOk`).
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

/-- `a - 1 < 3` unsigned: `1 ≤ a ≤ 3`. -/
theorem pred_lt_three {a : Nat} (ha : a < 2 ^ 64) :
    (BitVec.ofNat 64 a - 1#64).toNat < 3 ↔ 1 ≤ a ∧ a ≤ 3 := by
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  omega

section
variable {Ctx W SP : Addr}

/-- `CF` if `src` holds one to three whole blocks. -/
theorem sTest_ok {sl : Nat} (hsl : sl < 2 ^ 64) {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hslot : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 sl) :
    WP isa (.block SealSplit.sTest) s fun t => t.cf = some (decide (1 ≤ sl / 16 ∧ sl / 16 ≤ 3)) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have q₁ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have h₁ := Gather.shr_ofNat sl 4 hsl
  have i1 := imm_eq (n := 1) (by decide)
  have i3 := imm_eq (n := 3) (by decide)
  unfold SealSplit.sTest
  apply WP.of_runBlock
  refine ⟨_, by xrun [he.r15, q₁, hslot, h₁, i1, i3], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [cf_arithFlags, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true, reduceCtorEq, ↓reduceIte,
      Nat.reducePow, BitVec.toNat_ofNat, Nat.reduceMod, pred_lt_three (show sl / 16 < 2 ^ 64 by omega)]
  · intro r ha; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, ha]
  all_goals simp [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags,
    wr_setReg, wr_setFlags]

/-- `copySrc`'s arguments: `src`, `dst` and `src_len`. -/
theorem sCopyArgs_ok {D S : Addr} {sl : Nat} {s : State} (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hdat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D) (hsrc : s.mem.readW (W + BitVec.ofNat 64 224) 64 = S)
    (hslot : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 sl) :
    WP isa (.block [.mov .rsi (.mem (at_ .r15 tlO)), .mov .rdi (.mem (at_ .r15 dataO)), .mov .rcx (.mem (at_ .r15 tlenO))])
      s fun t => t.gpr .rsi = S ∧ t.gpr .rdi = D ∧ t.gpr .rcx = BitVec.ofNat 64 sl ∧
        (∀ r, r ≠ .rsi → r ≠ .rdi → r ≠ .rcx → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have q₁ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have q₃ := he.perm.wR (show 224 + 8 ≤ 2560 by decide)
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
      t.gpr .r8 = BitVec.ofNat 64 (sl / 16) ∧ t.gpr .r9 = W + BitVec.ofNat 64 512 ∧ t.gpr .rbx = D ∧
      t.gpr .rbp = BitVec.ofNat 64 (sl / 16) ∧
      (∀ r ∈ [Reg.r13, .r14, .r15, .rsp], t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have q₁ := he.perm.wR (show 176 + 8 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have q₃ := he.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have h₁ := Gather.shr_ofNat sl 4 hsl
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
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, hdat]
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

/-- A step after the first: block `i` at `rbx`, times the power at `r13 + powOff (k - i)`. -/
theorem sStep_ok (k i : Nat) (hi : i ≠ 0) (s : State) (x0 : s.xmm .xmm0 = revMask)
    (hX : InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofInt 64 ((16 * i : Nat) : Int)) 16)
    (hP : InRegions (s.rd ++ s.wr) (s.gpr .r13 + BitVec.ofInt 64 ((SealSplit.powOff (k - i) : Nat) : Int)) 16) :
    WP isa (.block (SealSplit.sGhStep k i)) s fun t =>
      prod t = (prod s).acc (blockAt s.mem (s.gpr .rbx + BitVec.ofInt 64 ((16 * i : Nat) : Int)))
        (s.mem.readW (s.gpr .r13 + BitVec.ofInt 64 ((SealSplit.powOff (k - i) : Nat) : Int)) 128) ∧
      Only [.xmm7, .xmm6, .xmm8, .xmm9, .xmm10, .xmm11] s t := by
  simp only [SealSplit.sGhStep, hi, ↓reduceIte, List.nil_append, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .rbx (16 * i) s (by decide) x0 hX) fun s₁ ⟨l₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ld128_ok .xmm6 .r13 _ s₁ (by rw [o₁.rd, o₁.wr, o₁.gpr _ (by decide)]; exact hP)) fun s₂ ⟨l₂, o₂⟩ => ?_
  refine WP.mono (acc_ok .xmm7 .xmm6 s₂ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun t ⟨p, o⟩ => ⟨?_, ((o₁.trans o₂).trans o).weaken fun r hr => by
      revert hr; cases r <;> decide⟩
  rw [p, o₂.prod (by decide) (by decide) (by decide), o₁.prod (by decide) (by decide) (by decide),
    o₂.xmm _ (by decide), l₁, l₂, o₁.mem, o₁.gpr _ (by decide)]

/-- The first step: block 0 at `rbx`, `Y` (in `xmm12`) added, times the power
at `r13 + powOff k`. -/
theorem sStep0_ok (k : Nat) (s : State) (x0 : s.xmm .xmm0 = revMask)
    (hX : InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofInt 64 ((16 * 0 : Nat) : Int)) 16)
    (hP : InRegions (s.rd ++ s.wr) (s.gpr .r13 + BitVec.ofInt 64 ((SealSplit.powOff (k - 0) : Nat) : Int)) 16) :
    WP isa (.block (SealSplit.sGhStep k 0)) s fun t =>
      prod t = (prod s).acc (blockAt s.mem (s.gpr .rbx + BitVec.ofInt 64 ((16 * 0 : Nat) : Int)) ^^^ s.xmm .xmm12)
        (s.mem.readW (s.gpr .r13 + BitVec.ofInt 64 ((SealSplit.powOff (k - 0) : Nat) : Int)) 128) ∧
      Only [.xmm7, .xmm7, .xmm6, .xmm8, .xmm9, .xmm10, .xmm11] s t := by
  simp only [SealSplit.sGhStep, ↓reduceIte, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .rbx (16 * 0) s (by decide) x0 hX) fun s₁ ⟨l₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pxor712_ok s₁) fun s₂ ⟨l₂, o₂⟩ => ?_
  rw [WP.block_append_iff]
  have hP₂ : InRegions (s₂.rd ++ s₂.wr)
      (s₂.gpr .r13 + BitVec.ofInt 64 ((SealSplit.powOff (k - 0) : Nat) : Int)) 16 := by
    rw [o₂.rd, o₂.wr, o₂.gpr _ (by decide), o₁.rd, o₁.wr, o₁.gpr _ (by decide)]; exact hP
  refine WP.mono (ld128_ok .xmm6 .r13 _ s₂ hP₂) fun s₃ ⟨l₃, o₃⟩ => ?_
  refine WP.mono (acc_ok .xmm7 .xmm6 s₃ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun t ⟨p, o⟩ => ⟨?_, (((o₁.trans o₂).trans o₃).trans o).weaken fun r hr => by
      revert hr; cases r <;> decide⟩
  rw [p, o₃.prod (by decide) (by decide) (by decide), o₂.prod (by decide) (by decide) (by decide),
    o₁.prod (by decide) (by decide) (by decide), o₃.xmm _ (by decide), l₂, l₁, l₃, o₂.mem, o₁.mem,
    o₂.gpr _ (by decide), o₁.gpr _ (by decide), o₁.xmm _ (by decide)]

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

/-- The steps of `sGhK k`, from a cleared product: `sProd` of the `k` blocks at
`rbx` and the powers at `r13`. -/
theorem sSteps_ok {k : Nat} (hk : k = 1 ∨ k = 2 ∨ k = 3) {D : Addr} (u : State) (x0 : u.xmm .xmm0 = revMask)
    (hbx : u.gpr .rbx = D) (hz : prod u = VG.Proof.Gcm.X86_64.Pclmul.Prod.zero)
    (hX : ∀ i < k, InRegions (u.rd ++ u.wr) (D + BitVec.ofNat 64 (16 * i)) 16)
    (hP : ∀ j, 1 ≤ j → j ≤ 3 → InRegions (u.rd ++ u.wr) (u.gpr .r13 + BitVec.ofNat 64 (SealSplit.powOff j)) 16) :
    WP isa (.block ((List.range k).flatMap (SealSplit.sGhStep k))) u fun t =>
      prod t = sProd (u.xmm .xmm12) (blocksAt u.mem D k)
        (fun j => u.mem.readW (u.gpr .r13 + BitVec.ofNat 64 (SealSplit.powOff j)) 128) ∧
      Only [.xmm7, .xmm7, .xmm6, .xmm8, .xmm9, .xmm10, .xmm11] u t := by
  have eX : ∀ i, u.gpr .rbx + BitVec.ofInt 64 ((16 * i : Nat) : Int) = D + BitVec.ofNat 64 (16 * i) := fun i => by
    rw [hbx, BitVec.ofInt_natCast]
  have eP : ∀ j, u.gpr .r13 + BitVec.ofInt 64 ((SealSplit.powOff j : Nat) : Int) =
      u.gpr .r13 + BitVec.ofNat 64 (SealSplit.powOff j) := fun j => by rw [BitVec.ofInt_natCast]
  have W : ∀ {a b : List XReg}, (∀ r ∈ a, r ∈ [.xmm7, .xmm7, .xmm6, .xmm8, .xmm9, .xmm10, .xmm11]) →
      (∀ r ∈ b, r ∈ [.xmm7, .xmm7, .xmm6, .xmm8, .xmm9, .xmm10, .xmm11]) →
      ∀ r ∈ a ++ b, r ∈ [XReg.xmm7, .xmm7, .xmm6, .xmm8, .xmm9, .xmm10, .xmm11] := fun ha hb r hr => by
    rcases List.mem_append.mp hr with h | h; exacts [ha r h, hb r h]
  have S6 : ∀ r ∈ [XReg.xmm7, .xmm6, .xmm8, .xmm9, .xmm10, .xmm11],
      r ∈ [XReg.xmm7, .xmm7, .xmm6, .xmm8, .xmm9, .xmm10, .xmm11] := by decide
  have S7 : ∀ r ∈ [XReg.xmm7, .xmm7, .xmm6, .xmm8, .xmm9, .xmm10, .xmm11],
      r ∈ [XReg.xmm7, .xmm7, .xmm6, .xmm8, .xmm9, .xmm10, .xmm11] := fun _ h => h
  rcases hk with rfl | rfl | rfl
  · show WP isa (.block (SealSplit.sGhStep 1 0 ++ [])) u _
    rw [List.append_nil]
    refine WP.mono (sStep0_ok 1 u x0 (by rw [eX]; exact hX 0 (by decide)) (by rw [eP]; exact hP 1 (by decide) (by decide)))
      fun t ⟨p, o⟩ => ⟨?_, o⟩
    rw [p, hz, eX, eP]; rfl
  · show WP isa (.block (SealSplit.sGhStep 2 0 ++ (SealSplit.sGhStep 2 1 ++ []))) u _
    rw [List.append_nil, WP.block_append_iff]
    refine WP.mono (sStep0_ok 2 u x0 (by rw [eX]; exact hX 0 (by decide)) (by rw [eP]; exact hP 2 (by decide) (by decide)))
      fun t₁ ⟨p₁, o₁⟩ => ?_
    have c₁ : t₁.gpr .rbx = u.gpr .rbx := o₁.gpr _ (by decide)
    have d₁ : t₁.gpr .r13 = u.gpr .r13 := o₁.gpr _ (by decide)
    refine WP.mono (sStep_ok 2 1 (by decide) t₁ (by rw [o₁.xmm _ (by decide), x0])
      (by rw [o₁.rd, o₁.wr, c₁, eX]; exact hX 1 (by decide)) (by rw [o₁.rd, o₁.wr, d₁, eP]; exact hP 1 (by decide) (by decide)))
      fun t ⟨p, o⟩ => ⟨?_, (o₁.trans o).weaken (W S7 S6)⟩
    rw [p, p₁, hz, c₁, d₁, o₁.mem, eX, eX, eP, eP]; rfl
  · show WP isa (.block (SealSplit.sGhStep 3 0 ++ (SealSplit.sGhStep 3 1 ++ (SealSplit.sGhStep 3 2 ++ [])))) u _
    rw [List.append_nil, WP.block_append_iff]
    refine WP.mono (sStep0_ok 3 u x0 (by rw [eX]; exact hX 0 (by decide)) (by rw [eP]; exact hP 3 (by decide) (by decide)))
      fun t₁ ⟨p₁, o₁⟩ => ?_
    have c₁ : t₁.gpr .rbx = u.gpr .rbx := o₁.gpr _ (by decide)
    have d₁ : t₁.gpr .r13 = u.gpr .r13 := o₁.gpr _ (by decide)
    rw [WP.block_append_iff]
    refine WP.mono (sStep_ok 3 1 (by decide) t₁ (by rw [o₁.xmm _ (by decide), x0])
      (by rw [o₁.rd, o₁.wr, c₁, eX]; exact hX 1 (by decide)) (by rw [o₁.rd, o₁.wr, d₁, eP]; exact hP 2 (by decide) (by decide)))
      fun t₂ ⟨p₂, o₂⟩ => ?_
    have O := o₁.trans o₂
    have c₂ : t₂.gpr .rbx = u.gpr .rbx := O.gpr _ (by decide)
    have d₂ : t₂.gpr .r13 = u.gpr .r13 := O.gpr _ (by decide)
    refine WP.mono (sStep_ok 3 2 (by decide) t₂ (by rw [O.xmm _ (by decide), x0])
      (by rw [O.rd, O.wr, c₂, eX]; exact hX 2 (by decide)) (by rw [O.rd, O.wr, d₂, eP]; exact hP 1 (by decide) (by decide)))
      fun t ⟨p, o⟩ => ⟨?_, (O.trans o).weaken (W (W S7 S6) S6)⟩
    rw [p, p₂, p₁, hz, c₂, d₂, c₁, d₁, O.mem, o₁.mem, eX, eX, eX, eP, eP, eP]; rfl

/-- `sGhK k`: the `k` blocks at `rbx` absorbed into `Y` at `St + 16` with
the powers of the context, reduced once. -/
theorem sGhK_ok {k : Nat} (hk : k = 1 ∨ k = 2 ∨ k = 3) {Ctx St D : Addr} (u : State) (h13 : u.gpr .r13 = Ctx)
    (h14 : u.gpr .r14 = St) (hbx : u.gpr .rbx = D)
    (inY : InRegions (u.rd ++ u.wr) (St + BitVec.ofNat 64 16) 16) (outY : InRegions u.wr (St + BitVec.ofNat 64 16) 16)
    (hX : ∀ i < k, InRegions (u.rd ++ u.wr) (D + BitVec.ofNat 64 (16 * i)) 16)
    (hP : ∀ j, 1 ≤ j → j ≤ 3 → InRegions (u.rd ++ u.wr) (Ctx + BitVec.ofNat 64 (SealSplit.powOff j)) 16) :
    WP isa (.block (SealSplit.sGhK k)) u fun t =>
      blockAt t.mem (St + BitVec.ofNat 64 16) = VG.Proof.Gcm.X86_64.Pclmul.reduce
        (sProd (blockAt u.mem (St + BitVec.ofNat 64 16)) (blocksAt u.mem D k)
          (fun j => u.mem.readW (Ctx + BitVec.ofNat 64 (SealSplit.powOff j)) 128)) ∧
      Frame [⟨St + BitVec.ofNat 64 16, 16⟩] u.mem t.mem ∧
      (∀ r, r ≠ .rax → t.gpr r = u.gpr r) ∧ t.rd = u.rd ∧ t.wr = u.wr := by
  simp only [SealSplit.sGhK, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ u (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₃ ⟨c₂, o₂⟩ => ?_
  have O₂ := o₁.trans o₂
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm12 .r14 16 s₃ (by decide)
    (by rw [o₂.xmm _ (by decide), c₁, VG.Proof.Gcm.X86_64.Pclmul.rev_eq])
    (by rw [O₂.rd, O₂.wr, O₂.gpr _ (by decide), h14, BitVec.ofInt_natCast]; exact inY))
    fun s₄ ⟨l₄, o₄⟩ => ?_
  rw [O₂.gpr _ (by decide), h14, BitVec.ofInt_natCast, O₂.mem] at l₄
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s₄) fun s₅ ⟨p₅, o₅⟩ => ?_
  have o₄₅ := O₂.trans (o₄.trans o₅)
  have rd₅ : s₅.rd = u.rd := o₄₅.rd
  have wr₅ : s₅.wr = u.wr := o₄₅.wr
  have mm₅ : s₅.mem = u.mem := o₄₅.mem
  have d₅ : s₅.gpr .r13 = Ctx := by rw [o₄₅.gpr _ (by decide), h13]
  rw [WP.block_append_iff]
  refine WP.mono (sSteps_ok hk (D := D) s₅ (by rw [(o₄.trans o₅).xmm _ (by decide), o₂.xmm _ (by decide), c₁])
    (by rw [o₄₅.gpr _ (by decide), hbx]) p₅
    (fun i hi => by rw [rd₅, wr₅]; exact hX i hi) (fun j h₁ h₂ => by rw [rd₅, wr₅, d₅]; exact hP j h₁ h₂))
    fun s₆ ⟨p₆, o₆⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok .xmm2 s₆ (by decide) (by decide) (by decide) (by decide)
    (by rw [o₆.xmm _ (by decide), (o₄.trans o₅).xmm _ (by decide), c₂])) fun s₇ ⟨r₇, o₇⟩ => ?_
  have o₆₇ := o₆.trans o₇
  refine WP.mono (Fast.strev_ok .xmm2 .r14 16 s₇ (by decide)
    (by rw [o₆₇.xmm _ (by decide), (o₄.trans o₅).xmm _ (by decide), o₂.xmm _ (by decide), c₁,
      VG.Proof.Gcm.X86_64.Pclmul.rev_eq])
    (by rw [o₆₇.wr, wr₅, o₆₇.gpr _ (by decide), o₄₅.gpr _ (by decide), h14, BitVec.ofInt_natCast]; exact outY))
    fun t ⟨m₈, b₈, g₈, rd₈, wr₈, _⟩ => ?_
  rw [o₆₇.gpr _ (by decide), o₄₅.gpr _ (by decide), h14, BitVec.ofInt_natCast] at m₈ b₈
  have y12 : s₅.xmm .xmm12 = blockAt u.mem (St + BitVec.ofNat 64 16) := by
    rw [o₅.xmm _ (by decide), l₄]
  refine ⟨by rw [b₈, r₇, p₆, y12, mm₅, d₅], ?_, fun r a => by rw [g₈, o₆₇.gpr r a, o₄₅.gpr r a],
    by rw [rd₈, o₆₇.rd, rd₅], by rw [wr₈, o₆₇.wr, wr₅]⟩
  rw [m₈, o₆₇.mem, mm₅]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-- `cmp rbp, m`: `CF` if `rbp`, the number of whole blocks, is below `m`. -/
theorem sCmp_ok {q m : Nat} (hq : q < 2 ^ 64) (hm : m < 2 ^ 31) (s : State) (hbp : s.gpr .rbp = BitVec.ofNat 64 q) :
    WP isa (.block [.alu .cmp .rbp (imm m)]) s fun t =>
      t.cf = some (decide (q < m)) ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have im := imm_eq (n := m) hm
  apply WP.of_runBlock
  refine ⟨_, by xrun [hbp, im], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [cf_arithFlags, ite_true, reduceCtorEq, ↓reduceIte,
      Nat.reducePow, BitVec.toNat_ofNat, Nat.reduceMod, Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt (show m < 2 ^ 64 by omega)]
  · funext r; simp [gpr_arithFlags]
  all_goals simp [mem_arithFlags, rd_arithFlags, wr_arithFlags]

/-- `sGh`: the `⌊sl / 16⌋` blocks at `rbx` (one to three, in `rbp`) absorbed
into `Y` at `St + 16` at once. -/
theorem sGh_ok {sl : Nat} (hq : 1 ≤ sl / 16 ∧ sl / 16 ≤ 3) {Ctx St D : Addr} (u : State)
    (h13 : u.gpr .r13 = Ctx) (h14 : u.gpr .r14 = St) (hbx : u.gpr .rbx = D)
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
  unfold SealSplit.sGh
  have K : ∀ {k : Nat} {t₁ : State}, t₁.gpr = u.gpr → t₁.mem = u.mem → t₁.rd = u.rd → t₁.wr = u.wr →
      k = sl / 16 → (k = 1 ∨ k = 2 ∨ k = 3) →
      WP isa (.block (SealSplit.sGhK k)) t₁ fun t =>
        blockAt t.mem (St + BitVec.ofNat 64 16) = VG.Proof.Gcm.X86_64.Pclmul.reduce
          (sProd (blockAt u.mem (St + BitVec.ofNat 64 16)) (blocksAt u.mem D (sl / 16))
            (fun j => u.mem.readW (Ctx + BitVec.ofNat 64 (SealSplit.powOff j)) 128)) ∧
        Frame [⟨St + BitVec.ofNat 64 16, 16⟩] u.mem t.mem ∧
        (∀ r, r ≠ .rax → t.gpr r = u.gpr r) ∧ t.rd = u.rd ∧ t.wr = u.wr := fun g₁ m₁ rd₁ wr₁ hk k3 => by
    subst hk
    refine WP.mono (sGhK_ok (Ctx := Ctx) (St := St) (D := D) k3 _ (by rw [g₁, h13]) (by rw [g₁, h14])
      (by rw [g₁, hbx]) (by rw [rd₁, wr₁]; exact inY) (by rw [wr₁]; exact outY)
      (fun i hi => by rw [rd₁, wr₁]; exact hX i hi) (fun j a b => by rw [rd₁, wr₁]; exact hP j a b))
      fun t ⟨y, f, g, rd, wr⟩ => ?_
    rw [m₁] at y f
    exact ⟨y, f, fun r a => by rw [g r a, g₁], rd.trans rd₁, wr.trans wr₁⟩
  refine WP.seq (WP.mono (sCmp_ok (q := sl / 16) (m := 2) (by omega) (by decide) u hbp)
    fun t₁ ⟨cf₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  refine WP.ite (decide (sl / 16 < 2)) (by simp only [eval, cf₁]) (fun hc => ?_) (fun hc => ?_)
  · exact K g₁ m₁ rd₁ wr₁ (by have := of_decide_eq_true hc; omega) (.inl rfl)
  · have hc' := of_decide_eq_false hc
    refine WP.seq (WP.mono (sCmp_ok (q := sl / 16) (m := 3) (by omega) (by decide) t₁ (by rw [g₁, hbp]))
      fun t₂ ⟨cf₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
    refine WP.ite (decide (sl / 16 < 3)) (by simp only [eval, cf₂]) (fun hc => ?_) (fun hc => ?_)
    · exact K (k := 2) (g₂.trans g₁) (m₂.trans m₁) (rd₂.trans rd₁) (wr₂.trans wr₁)
        (by have := of_decide_eq_true hc; omega) (.inr (.inl rfl))
    · exact K (k := 3) (g₂.trans g₁) (m₂.trans m₁) (rd₂.trans rd₁) (wr₂.trans wr₁)
        (by have := of_decide_eq_false hc; omega) (.inr (.inr rfl))

end

/-- `sProd` reads only the powers `1` to `3`. -/
theorem sProd_congr (Y : Block) (X : List Block) {P Q : Nat → Block} (h : ∀ j, 1 ≤ j → j ≤ 3 → P j = Q j) :
    sProd Y X P = sProd Y X Q := by
  have h1 := h 1 (by decide) (by decide)
  have h2 := h 2 (by decide) (by decide)
  have h3 := h 3 (by decide) (by decide)
  match X with
  | [] => rfl
  | [_] => simp only [sProd, h1]
  | [_, _] => simp only [sProd, h1, h2]
  | [_, _, _] => simp only [sProd, h1, h2, h3]
  | _ :: _ :: _ :: _ :: _ => rfl

/-! ## The path of the texts `sTest` takes -/

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
  rbx : t.gpr .rbx = D
  rbp : t.gpr .rbp = BitVec.ofNat 64 (sl / 16)
  mem : t.mem = sMem D S sl σ
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr

/-- After the call. -/
structure SD (t : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP t
  rbx : t.gpr .rbx = D
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
  have he : Env Ctx (W + BitVec.ofNat 64 16) W SP t := h.env.keep (fun r hr => g r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)) trd twr
  exact WP.mono (sCopyArgs_ok (D := D) (S := S) (sl := sl) he (by rw [tm]; exact h.dat)
    (by rw [tm]; exact h.src) (by rw [tm]; exact h.slen)) fun t₁ ⟨si₁, di₁, cx₁, g₁, m₁, rd₁, wr₁⟩ =>
    ⟨si₁, di₁, cx₁, fun r a b c d => by rw [g₁ r b c d, g r a], m₁.trans tm, rd₁.trans trd, wr₁.trans twr⟩

include hq in
/-- The copy. -/
theorem sB_ok {t₁ : State} (hA : SA D S sl s t₁) : WP isa SealGather.copy t₁ (SB Ctx W SP D S sl s) := by
  have hsl := h.sl_le
  have cp : Short.CopyPre t₁ S D sl :=
    ⟨hA.rsi, hA.rdi, hA.rcx, by omega, by rw [hA.rd, hA.wr]; exact h.srcCov,
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
  have kp₂ : ∀ d, d + 8 ≤ 2560 → t₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => by rw [hB.mem]; exact sMem_slot h hd
  refine WP.mono (sCtrArgs_ok (R := R) (D := D) (sl := sl) (by omega) hB.env
    ⟨by rw [kp₂ 176 (by decide)]; exact h.rounds.1, h.rounds.2⟩ (by rw [kp₂ 200 (by decide)]; exact h.dat)
    (by rw [kp₂ 192 (by decide)]; exact h.slen)) fun t₃ ⟨di₃, si₃, dx₃, cx₃, r8₃, r9₃, bx₃, bp₃, k₃, m₃, rd₃, wr₃⟩ => ?_
  have he₃ : Env Ctx (W + BitVec.ofNat 64 16) W SP t₃ := hB.env.keep k₃ rd₃ wr₃
  have hk := he₃.rsp
  have hq16 : 16 * (sl / 16) ≤ n := by omega
  have hdq := (h.data.of_eq (rd₃.trans hB.rd) (wr₃.trans hB.wr)).take hq16
  refine ⟨⟨di₃, si₃, dx₃, cx₃, r8₃, r9₃, h.rounds.2, by have := h.data.ok.wrap; omega,
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
        exact he₃.perm.ctx a m' ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc' ⊢; omega⟩
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
  have inP : ∀ j, 1 ≤ j → j ≤ 3 → InRegions (t₄.rd ++ t₄.wr) (Ctx + BitVec.ofNat 64 (SealSplit.powOff j)) 16 :=
    fun j h₁ h₂ => by
      rw [hD.rd, hD.wr]
      refine Short.in_of_covers16 h.ext.cov ?_ (show 1024 < 2 ^ 64 by decide)
      show SealSplit.powOff j + 16 ≤ 1024
      unfold SealSplit.powOff; omega
  exact WP.mono (sGh_ok (Ctx := Ctx) (St := W + BitVec.ofNat 64 16) (D := D) hq t₄
    hD.env.r13 hD.env.r14 hD.rbx hD.rbp (hD.env.perm.stR (by decide)) (hD.env.perm.stW (by decide))
    (fun i hi => by rw [hD.rd, hD.wr]; exact Short.in_of_covers16 h.data.ok.rd (by omega) hn) inP)
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
  have s64 : sl < 64 := by omega
  have q16 : 16 * (sl / 16) ≤ sl := Nat.mul_div_le sl 16
  -- What the copy wrote: the whole blocks, then the bytes left.
  have hsplit : bytesAt s.mem S sl = bytesAt s.mem S (16 * (sl / 16)) ++
      bytesAt s.mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16) := by
    rw [← bytesAt_add, show 16 * (sl / 16) + sl % 16 = sl by omega]
  have hm₂ : sMem D S sl s = writeBytes (writeBytes s.mem D (bytesAt s.mem S (16 * (sl / 16))))
      (D + BitVec.ofNat 64 (16 * (sl / 16))) (bytesAt s.mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16)) := by
    have := writeBytes_append s.mem D (bytesAt s.mem S (16 * (sl / 16)))
      (bytesAt s.mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16)) (by rw [length_bytesAt, length_bytesAt]; omega)
    rw [length_bytesAt] at this
    rw [sMem, hsplit, this]
  have FC : Frame [⟨D, sl⟩] s.mem (sMem D S sl s) := writeBytes_frame' _ (length_bytesAt _ _ _)
  have F1 : Frame [⟨D, 16 * (sl / 16)⟩] s.mem (writeBytes s.mem D (bytesAt s.mem S (16 * (sl / 16)))) :=
    writeBytes_frame' _ (length_bytesAt _ _ _)
  have F2 : Frame [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩]
      (writeBytes s.mem D (bytesAt s.mem S (16 * (sl / 16)))) (sMem D S sl s) := by
    rw [hm₂]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  have dBT : (⟨D, 16 * (sl / 16)⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩ := by
    simpa using Offset.disjoint D (d := 0) (n := 16 * (sl / 16)) (e := 16 * (sl / 16))
      (k := sl % 16) (.inl (by omega)) (by omega) (by omega)
  have one : ∀ {X Y : Region}, X.Disjoint Y → ∀ r ∈ [Y], X.Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  have bl₂ : blocksAt (sMem D S sl s) D (sl / 16) = blocksAt s.mem S (sl / 16) := by
    rw [blocksAt_frame F2 (one dBT) (by omega), Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq]
    have := bytesAt_writeBytes_self s.mem D (bytesAt s.mem S (16 * (sl / 16))) (by rw [length_bytesAt]; omega)
    rw [length_bytesAt] at this
    rw [this]
  have tl₂ : bytesAt (sMem D S sl s) (D + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16) =
      bytesAt s.mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16) := by
    have := bytesAt_writeBytes_self (writeBytes s.mem D (bytesAt s.mem S (16 * (sl / 16))))
      (D + BitVec.ofNat 64 (16 * (sl / 16))) (bytesAt s.mem (S + BitVec.ofNat 64 (16 * (sl / 16))) (sl % 16))
      (by rw [length_bytesAt]; omega)
    rw [length_bytesAt] at this
    rw [hm₂, this]
  have Fk := hD.frame
  have ok₄ := hD.out
  have ct₄ := hD.ctr
  -- The call's writes, among what `prefix` may write.
  have Fc : Frame (callWr W D (sl / 16) ++ [below SP 56]) (sMem D S sl s) t₄.mem := Fk.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨D, sl / 16 * 16⟩, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 448, 2112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨below SP 56, by simp, below_sub (by decide) (by decide)⟩
  have he₅ : Env Ctx (W + BitVec.ofNat 64 16) W SP t₅ := hD.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₅ _ (by decide)) rd₅ wr₅
  -- Regions apart.
  have subT : Region.Sub ⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩ ⟨D, n⟩ := Offset.sub_base D (by omega)
  have subQ : Region.Sub ⟨D, 16 * (sl / 16)⟩ ⟨D, n⟩ := Region.sub_prefix (by omega)
  have cbY : (⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint
      ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩ :=
    Offset.disjoint _ (.inr (by decide)) (by have := L.sw; omega_arith) (by have := L.sw; omega_arith)
  have qY : (⟨D, 16 * (sl / 16)⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩ :=
    (h.data.ok.st.sub_left subQ).sub_right (Lay.stSub (by decide))
  have tY : (⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩ : Region).Disjoint
      ⟨W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16, 16⟩ :=
    (h.data.ok.st.sub_left subT).sub_right (Lay.stSub (by decide))
  -- The context, kept.
  have hdC : ∀ r ∈ callWr W D (sl / 16) ++ [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩, below SP 56],
      (⟨Ctx, (CtxMode.preparedN np hpn).len⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | rfl | rfl
    · exact h.ext.cs.sub_right (Lay.stSub (by decide))
    · exact h.ext.cs.sub_right (Lay.stSub (by decide))
    · exact h.ext.cd.sub_right (Region.sub_prefix (by omega))
    · exact h.ext.cw.sub_right (Lay.wSub (by decide))
    · exact h.ext.cd.sub_right subT
    · exact h.kM.symm
  have toL : ∀ {rs : List Region}, (∀ r ∈ rs, r ∈ callWr W D (sl / 16) ++
      [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩, below SP 56]) → ∀ r ∈ rs, ∃ r' ∈ callWr W D (sl / 16) ++
      [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩, below SP 56], Region.Sub r r' :=
    fun hm r hr => ⟨r, hm r hr, fun _ h => h⟩
  have FL₂ : Frame (callWr W D (sl / 16) ++ [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩, below SP 56])
      s.mem (sMem D S sl s) := (F1.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨D, sl / 16 * 16⟩, by simp, Region.sub_prefix (by omega)⟩).trans
      (F2.sub (toL fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp))
  have FL₄ : Frame (callWr W D (sl / 16) ++ [⟨D + BitVec.ofNat 64 (16 * (sl / 16)), sl % 16⟩, below SP 56])
      s.mem t₄.mem := FL₂.trans (Fc.sub fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
        · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  have Pw : Gcm.X86_64.Stitch.PowersN np t₄.mem Ctx := (CtxMode.preparedN np hpn).frame FL₄ hdC h.ext.w h.ext.ok
  have hH : ctxH t₄.mem Ctx = ctxH s.mem Ctx := by
    simp only [ctxH_eq]
    exact blockAt_frame FL₄ fun r hr => (hdC r hr).sub_left (Offset.sub_base Ctx (show 240 + 16 ≤ 1024 by decide))
  have hP : ∀ j, 1 ≤ j → j ≤ 3 → t₄.mem.readW (Ctx + BitVec.ofNat 64 (SealSplit.powOff j)) 128 =
      Spec.Gcm.preparedPower (Spec.Gcm.hpow (ctxH s.mem Ctx) j) := fun j h₁ h₂ => by
    rw [← hH]
    obtain rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 := by omega
    · exact (Pw 0 (by omega)).2
    · exact (Pw 0 (by omega)).1
    · exact (Pw 1 (by omega)).2
  -- What the steps keep.
  have cb₂ : blockAt (sMem D S sl s) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
      blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) :=
    blockAt_frame FC (one ((h.data.ok.st.sub_left (Region.sub_prefix hsl)).sub_right (Lay.stSub (by decide))).symm)
  have cb₅ : blockAt t₅.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) =
      blockAt t₄.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) := blockAt_frame f₅ (one cbY)
  have bl₅ : blocksAt t₅.mem D (sl / 16) = blocksAt t₄.mem D (sl / 16) := blocksAt_frame f₅ (one qY) (by omega)
  have y₄ : blockAt t₄.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) =
      blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) := by
    rw [blockAt_frame Fk fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact cbY.symm
      · exact qY.symm
      · exact L.st_w (a := 16) (n := 16) (d := 512) (k := 2048) (by decide) (.inr ⟨by decide, by decide⟩)
      · exact (L.stk_st (a := 16) (n := 16) (by decide)).symm]
    exact blockAt_frame FC (one ((h.data.ok.st.sub_left (Region.sub_prefix hsl)).sub_right (Lay.stSub (by decide))).symm)
  have hc : Spec.Gcm.aesWith R (bytesAt (sMem D S sl s) Ctx (16 * (R + 1))) = ctxCiph s.mem Ctx R :=
    ciph_frame FC (one (h.data.ctx.sub_right (Region.sub_prefix hsl))) h.rounds.2
  refine rest_ok h he₅ (rd₅.trans hD.rd) (wr₅.trans hD.wr) ((FL₄.trans (f₅.sub (toL fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp)))) ?_ ?_ ?_ ?_
  · show blocksAt t₅.mem D (sl / 16) = _
    rw [bl₅, ok₄, hc, cb₂, bl₂]
  · show blockAt t₅.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48) = _
    rw [cb₅, ct₄, cb₂]
  · show blockAt t₅.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16) =
      ghashFrom (ctxH s.mem Ctx) (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 16)) _
    rw [y₅, sProd_congr _ _ hP, y₄, sProd_ghash hF _ _ (by rw [Proof.Gcm.length_blocksAt]; omega), bl₅]
  · rw [bytesAt_frame f₅ (one tY) (by omega), bytesAt_frame Fk (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (h.data.ok.st.sub_left subT).sub_right (Lay.stSub (by decide))
      · exact dBT.symm
      · exact (h.data.ok.w.sub_left subT).sub_right (Lay.wSub (by decide))
      · exact (h.data.ok.stk.sub_right subT).symm) (by omega), tl₂]

include hq in
/-- The texts `sTest` takes, from a state that `prefix` could start from but
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

end

/-- `prefixS` meets `PreOk` with `prefixN`'s number of blocks: by the path
above for the texts `sTest` takes, by `prefixN` for the others. -/
theorem prefixSOk (hF : ShortFacts) (v : Proof.Aes.X86_64.Ctr32Impl) {ctr : Fn}
    (hc : ctr = ⟨v.callee.name, v.callee.code⟩) {c : Prog isa} (hE : EncNOk np hpn c)
    (T : BlkToFn (CtxMode.preparedN np hpn)) :
    PreOk (CtxMode.preparedN np hpn) (SealSplit.prefixS ctr T.fn c)
    fun n sl => if 1 ≤ sl / 256 ∧ sl / 256 < n / 256 then 16 * (n / 256) else sl / 16 := by
  intro Ctx W SP D S R n sl s h
  subst hc
  unfold SealSplit.prefixS
  refine WP.seq (WP.mono (sTest_ok (sl := sl) (by have := h.sl_le; have := h.data.ok.lt; omega) h.env h.slen)
    fun t ⟨cf, g, tm, trd, twr⟩ => ?_)
  refine WP.ite (decide (1 ≤ sl / 16 ∧ sl / 16 ≤ 3)) (by simp only [eval, cf]) (fun hs => ?_) (fun hs => ?_)
  · have hs' := of_decide_eq_true hs
    have : ¬ (1 ≤ sl / 256 ∧ sl / 256 < n / 256) := by omega
    simp only [this, ↓reduceIte]
    exact WP.mono (sPath_ok h hs' hF v g tm trd twr) fun _ Q => Q.toG h
  · have he : Env Ctx (W + BitVec.ofNat 64 16) W SP t := h.env.keep (fun r hr => g r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)) trd twr
    exact WP.mono (prefixNOk hE T (h.of_eq he tm trd twr)) fun _ P => P.of_eq tm trd twr

end VG.Proof.AesGcm.X86_64.Split
