module

public import VerifiedGarbage.Proof.Gcm.PrecomputedContract
public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.AesGcm.X86_64.Frame
import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksVerifiedP
public import VerifiedGarbage.Proof.AesGcm.ScratchP
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Call
import VerifiedGarbage.Proof.AesGcm.X86_64.OpenCT
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamCryptCT
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.AesGcm.X86_64.SealCT
import VerifiedGarbage.Proof.AesGcm.X86_64.InitCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.AesGcm.X86_64.InitCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.AesGcm.X86_64.Init
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksContract
public import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.AesGcm.X86_64.Ghash1
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Init
meta import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksContract
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Ghash1
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `AesGcm.X86_64.InitPCT`, which only this module used -/

section

/-! ### `AesGcm.X86_64.InitP`, which only this module used -/

section

/-!
# AES-GCM on x86-64: `vg_aes_gcm_init_precomputed`

Untrusted: everything here is checked by Lean. `init`'s code (`initWith_wp`),
then the hash subkey `H` copied to `ctx + 256` (`powStart_ok`), which is
`H¹` (`hpow_one`), and `H²`–`H⁴⁸` after it, each `vg_ghash` from a zero
block over the one before it: `(0 ⊕ Hᵏ) • H = Hᵏ⁺¹` (`powStep_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt hpow mul ghashFrom)

/-- A fold whose steps keep the first component, keeps it. -/
theorem foldl_fst_keep {β : Type} (F : β × β → Nat → β × β) (P : Nat → Prop)
    (hF : ∀ zv i, P i → (F zv i).1 = zv.1) : ∀ (l : List Nat) (zv : β × β), (∀ i ∈ l, P i) → (l.foldl F zv).1 = zv.1
  | [], _, _ => rfl
  | i :: l, zv, h => by
    rw [List.foldl_cons, foldl_fst_keep F P hF l _ fun j hj => h j (List.mem_cons_of_mem _ hj),
      hF zv i (h i (List.mem_cons_self ..))]

/-- `1 • y = y`: only the first bit of `1` is set, so the product is `y`. -/
theorem mul_one_left (y : Block) : mul Spec.Gcm.one y = y := by
  unfold mul
  rw [List.range_succ_eq_map, List.foldl_cons,
    foldl_fst_keep _ (fun i => Spec.Gcm.one.getMsbD i = false) (fun zv i h => by simp only [h]; rfl) _ _
      fun i hi => ?_]
  · have h0 : Spec.Gcm.one.getMsbD 0 = true := by decide
    simp only [h0, ↓reduceIte]
    exact BitVec.zero_xor
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have : ∀ j < 127, Spec.Gcm.one.getMsbD (j + 1) = false := by decide
    exact this j (List.mem_range.mp hj)

/-- Unfolded by rewriting: as a definitional check, the kernel would evaluate
`mul` on the literal `one` rather than unfold `Nat.repeat` once (a minute). -/
theorem hpow_one (h : Block) : hpow h 1 = h := by
  rw [hpow, Nat.repeat, Nat.repeat]; exact mul_one_left h

/-- The regions of `vg_aes_gcm_init_precomputed`: the key context of 1024
bytes at `Ctx`, the working space at `W`, the return address at `SP` and the
stack below it. -/
structure IPLay (Ctx W SP : Addr) : Prop where
  cw : Ctx.toNat + 1024 ≤ 2 ^ 64
  ww : W.toNat + 2560 ≤ 2 ^ 64
  cs : (⟨Ctx, 1024⟩ : Region).Disjoint ⟨W, 2560⟩
  kc : (below SP 8).Disjoint ⟨Ctx, 1024⟩
  ks : (below SP 8).Disjoint ⟨W, 2560⟩
  rc : (⟨SP, 8⟩ : Region).Disjoint ⟨Ctx, 1024⟩
  rs : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 2560⟩

theorem IPLay.of {s : State} (hp : Proof.AesGcm.initPreL 1024 s) :
    IPLay (s.gpr .rdx) (s.gpr .rcx) (s.gpr .rsp) ∧ Covers [⟨s.gpr .rdx, 1024⟩] s.wr ∧
      Covers [⟨s.gpr .rcx, 2560⟩] s.wr := by
  simp only [Proof.AesGcm.initPreL, Proof.AesGcm.ret, Proof.AesGcm.stk] at hp
  obtain ⟨-, hwr, -, -, d_cs, r_c, r_s, -, k_c, k_s, wc, ws, -⟩ := hp
  exact ⟨⟨wc, ws, d_cs, k_c, k_s, r_c, r_s⟩, by rw [hwr]; exact covers_of_mem (List.mem_cons_self ..),
    by rw [hwr]; exact covers_of_mem (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩

/-- What the powers leave, after `j` of them from `m₅`: `Hᵏ⁺¹` at
`Ctx + 256 + 16 k` for `k ≤ j`, and `rbp` past them. -/
structure PowInv (Ctx W SP : Addr) (rd wr : List Region) (m₅ : Mem) (j : Nat) (t : State) : Prop where
  r13 : t.gpr .r13 = Ctx
  r15 : t.gpr .r15 = W
  rbp : t.gpr .rbp = Ctx + BitVec.ofNat 64 (272 + 16 * j)
  rsp : t.gpr .rsp = SP
  rd : t.rd = rd
  wr : t.wr = wr
  frame : Frame [⟨Ctx + BitVec.ofNat 64 256, 768⟩, ⟨W + BitVec.ofNat 64 512, 256⟩, below SP 8] m₅ t.mem
  pows : ∀ k ≤ j, blockAt t.mem (Ctx + BitVec.ofNat 64 (256 + 16 * k)) =
    hpow (blockAt m₅ (Ctx + BitVec.ofNat 64 240)) (k + 1)

section
variable {Ctx W SP : Addr} (L : IPLay Ctx W SP)
include L

/-- `H` copied to `Ctx + 256`, and `rbp` past it. -/
theorem powStart_ok {t : State} (pC : Covers [⟨Ctx, 1024⟩] t.wr) (h13 : t.gpr .r13 = Ctx)
    (h15 : t.gpr .r15 = W) (hsp : t.gpr .rsp = SP) :
    WP isa (.block (([.mov .rax (.mem (at_ .r13 240)), .store (at_ .r13 256) .rax,
      .mov .rax (.mem (at_ .r13 248)), .store (at_ .r13 264) .rax] : List Instr) ++ ptr .rbp .r13 272)) t
      (PowInv Ctx W SP t.rd t.wr t.mem 0) := by
  obtain r₁ := in_left (rd := t.rd) (in_off pC (show 240 + 8 ≤ 1024 by decide) (by decide))
  obtain r₂ := in_left (rd := t.rd) (in_off pC (show 248 + 8 ≤ 1024 by decide) (by decide))
  obtain w₁ := in_off pC (show 256 + 8 ≤ 1024 by decide) (by decide)
  obtain w₂ := in_off pC (show 264 + 8 ≤ 1024 by decide) (by decide)
  obtain sep : Mem.Sep (Ctx + BitVec.ofNat 64 248) (64 / 8) (Ctx + BitVec.ofNat 64 256) (64 / 8) :=
    Offset.sep _ (.inl (by decide)) (by have := L.cw; omega_arith) (by have := L.cw; omega_arith)
  obtain ⟨t', run, hm, h13', h15', hbp, hsp', hrd, hwr⟩ : ∃ t', runBlock isa
      (([.mov .rax (.mem (at_ .r13 240)), .store (at_ .r13 256) .rax,
        .mov .rax (.mem (at_ .r13 248)), .store (at_ .r13 264) .rax] : List Instr) ++ ptr .rbp .r13 272) t = some t' ∧
      t'.mem = (t.mem.writeW (Ctx + BitVec.ofNat 64 256) (t.mem.readW (Ctx + BitVec.ofNat 64 240) 64)).writeW
        (Ctx + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (t.mem.readW (Ctx + BitVec.ofNat 64 248) 64) ∧
      t'.gpr .r13 = Ctx ∧ t'.gpr .r15 = W ∧ t'.gpr .rbp = Ctx + BitVec.ofNat 64 272 ∧ t'.gpr .rsp = SP ∧
      t'.rd = t.rd ∧ t'.wr = t.wr := by
    rw [add_ofNat_assoc]
    refine ⟨_, by xrun [h13, r₁, r₂, w₁, w₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [mem_setReg, mem_arithFlags, Mem.readW_writeW_sep sep (by decide)]
    · simp [gpr_setReg, gpr_arithFlags, h13]
    · simp [gpr_setReg, gpr_arithFlags, h15]
    · simp [gpr_setReg, gpr_arithFlags, h13, imm_eq]
    · simp [gpr_setReg, gpr_arithFlags, hsp]
    all_goals simp [rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags]
  refine WP.of_runBlock ⟨t', run, h13', h15', by rw [hbp], hsp', hrd, hwr, ?_, fun k hk => ?_⟩
  · rw [hm]
    exact (Cmac.frame_store2 _ _ _).sub fun r hr => ⟨_, List.mem_cons_self .., by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩
  · have hk0 : k = 0 := by omega_arith
    subst hk0
    show blockAt t'.mem (Ctx + BitVec.ofNat 64 256) = hpow _ 1
    obtain e : Ctx + BitVec.ofNat 64 248 = Ctx + BitVec.ofNat 64 240 + BitVec.ofNat 64 8 :=
      (add_ofNat_assoc Ctx 240 8).symm
    rw [hpow_one, blockAt, blockAt, hm, Cmac.bytesAt_store2, Cmac.le8_readW, Cmac.le8_readW, e,
      ← Cmac.bytesAt_split]
end

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : IPLay Ctx W SP)
include L

omit L in
theorem pow_zf (Ctx : Addr) {k : Nat} (hk : k ≤ 47) :
    ((Ctx + BitVec.ofNat 64 (272 + 16 * k)) - (Ctx + BitVec.ofNat 64 1024) == 0) = decide (k = 47) := by
  by_cases h : k = 47
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    obtain e2 := congrArg (· + (Ctx + BitVec.ofNat 64 1024)) e
    simp only [BitVec.sub_add_cancel] at e2
    obtain e3 : BitVec.ofNat 64 (272 + 16 * k) = BitVec.ofNat 64 1024 :=
      (BitVec.add_right_inj Ctx).mp (by simpa using e2)
    have := congrArg BitVec.toNat e3
    simp at this; omega_arith

omit L in
/-- The loop's test: `rbp` against the end of the table, `r13 + 1024`. -/
theorem powEnd_run {k : Nat} (hk : k ≤ 47) {t : State} (h13 : t.gpr .r13 = Ctx)
    (hbp : t.gpr .rbp = Ctx + BitVec.ofNat 64 (272 + 16 * k)) :
    ∃ t', runBlock isa (ptr .rax .r13 1024 ++ ([.alu .cmp .rbp (.reg .rax)] : List Instr)) t = some t' ∧
      (∀ r, r ≠ .rax → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      isa.eval .ne t' = some (decide (k ≠ 47)) := by
  refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr; simp [gpr_setReg, gpr_arithFlags, hr]
  all_goals try simp [mem_arithFlags, mem_setReg, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags]
  show Option.map (!·) (some _) = _
  simp only [gpr_setReg, gpr_arithFlags, ite_true, h13, hbp, imm_eq (show 1024 < 2 ^ 31 by decide),
    Option.map_some, reduceCtorEq, ite_false]
  rw [pow_zf Ctx hk]

omit L in
theorem powEnd_ok {rd wr : List Region} {m₅ : Mem} {k : Nat} (hk : k ≤ 47) {t : State}
    (h : PowInv Ctx W SP rd wr m₅ k t) :
    WP isa (.block (ptr .rax .r13 1024 ++ ([.alu .cmp .rbp (.reg .rax)] : List Instr))) t fun t' =>
      PowInv Ctx W SP rd wr m₅ k t' ∧ isa.eval .ne t' = some (decide (k ≠ 47)) := by
  obtain ⟨t', run, hg, hm, hrd, hwr, he⟩ := powEnd_run hk h.r13 h.rbp
  refine WP.of_runBlock ⟨t', run, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, he⟩
  · rw [hg _ (by decide)]; exact h.r13
  · rw [hg _ (by decide)]; exact h.r15
  · rw [hg _ (by decide)]; exact h.rbp
  · rw [hg _ (by decide)]; exact h.rsp
  · rw [hrd]; exact h.rd
  · rw [hwr]; exact h.wr
  · rw [hm]; exact h.frame
  · intro j hj; rw [hm]; exact h.pows j hj

end

/-- What the key context holds, outside a frame that leaves its first 256 bytes. -/
theorem keyRepr_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {key : List Byte}
    (hl : key.length = 16 ∨ key.length = 24 ∨ key.length = 32) (hd : ∀ r ∈ rs, (⟨p, 256⟩ : Region).Disjoint r)
    (h : Spec.Gcm.KeyRepr m p key) : Spec.Gcm.KeyRepr m' p key := by
  obtain hR : 16 * (Spec.Aes.rounds (key.length / 4) + 1) ≤ 240 := by
    rcases hl with h | h | h <;> rw [h] <;> decide
  refine ⟨?_, ?_⟩
  · rw [bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by omega_arith))) (by omega_arith)]
    exact h.1
  · have e : blockAt m' (p + BitVec.ofNat 64 240) = blockAt m (p + BitVec.ofNat 64 240) :=
      blockAt_frame hf fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by decide))
    exact e.trans h.2

end VG.Proof.AesGcm.X86_64

end

end

/-!
# AES-GCM on x86-64: `vg_aes_gcm_init_precomputed` is constant time

Untrusted: everything here is checked by Lean. `init`'s code is
(`initWith_rel`); then both runs copy the hash subkey and call `vg_ghash` 47
times with the same arguments, which depend only on the pointers
(`PowRegs`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64

/-- One run of the powers, after `j` of them: the registers and the
permissions. -/
def PowRegs (Ctx W SP : Addr) (rd wr : List Region) (j : Nat) (t : State) : Prop :=
  t.gpr .r13 = Ctx ∧ t.gpr .r15 = W ∧ t.gpr .rbp = Ctx + BitVec.ofNat 64 (272 + 16 * j) ∧
    t.gpr .rsp = SP ∧ t.rd = rd ∧ t.wr = wr

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : IPLay Ctx W SP) {rd₁ wr₁ rd₂ wr₂ : List Region}
  (pC₁ : Covers [⟨Ctx, 1024⟩] wr₁) (pW₁ : Covers [⟨W, 2560⟩] wr₁)
  (pC₂ : Covers [⟨Ctx, 1024⟩] wr₂) (pW₂ : Covers [⟨W, 2560⟩] wr₂)
include L pC₁ pW₁ pC₂ pW₂

omit L pC₁ pW₁ pC₂ pW₂ in
theorem powNext_ok {Y : Addr} {j : Nat} {t : State} (hY : Y = Ctx + BitVec.ofNat 64 (272 + 16 * j))
    {rd wr : List Region} (h13 : t.gpr .r13 = Ctx) (h15 : t.gpr .r15 = W) (hbp : t.gpr .rbp = Y)
    (hsp : t.gpr .rsp = SP) (hrd : t.rd = rd) (hwr : t.wr = wr) :
    WP isa (.block [.alu .add .rbp (imm 16)]) t (PowRegs Ctx W SP rd wr (j + 1)) := by
  refine WP.of_runBlock ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, h13]
  · simp [gpr_setReg, gpr_arithFlags, h15]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, hbp, hY, imm_eq (show 16 < 2 ^ 31 by decide),
      add_ofNat_assoc]
    congr 2
  · simp [gpr_setReg, gpr_arithFlags, hsp]
  · simp [rd_setReg, rd_arithFlags, hrd]
  · simp [wr_setReg, wr_arithFlags, hwr]

omit L pC₁ pW₁ pC₂ pW₂ in
theorem powEndRegs_ok {rd wr : List Region} {k : Nat} (hk : k ≤ 47) {t : State}
    (h : PowRegs Ctx W SP rd wr k t) :
    WP isa (.block (ptr .rax .r13 1024 ++ ([.alu .cmp .rbp (.reg .rax)] : List Instr))) t fun t' =>
      PowRegs Ctx W SP rd wr k t' ∧ isa.eval .ne t' = some (decide (k ≠ 47)) := by
  obtain ⟨h13, h15, hbp, hsp, hrd, hwr⟩ := h
  obtain ⟨t', run, hg, -, hrd', hwr', he⟩ := powEnd_run hk h13 hbp
  exact WP.of_runBlock ⟨t', run, ⟨by rw [hg _ (by decide)]; exact h13, by rw [hg _ (by decide)]; exact h15,
    by rw [hg _ (by decide)]; exact hbp, by rw [hg _ (by decide)]; exact hsp, hrd'.trans hrd,
    hwr'.trans hwr⟩, he⟩

end

end VG.Proof.AesGcm.X86_64

end

end

/-!
# AES-GCM on x86-64, for a key context of either kind

Untrusted: everything here is checked by Lean. `seal`, `open`,
`stream_encrypt` and `stream_decrypt` calling the whole-blocks functions `B`
for a key context of kind `M` (`GcmImpl.withBlk`): their code loads no
`mxcsr`, keeps `rsp` and uses 24 bytes of stack, as for
`vg_aes_gcm_init`'s (`Verified.lean`, `Frame.lean`), and so they preserve
what the ABI says (`sealM_correct`, …).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)

variable (v : GcmImpl) {M : CtxMode} (B : BlkFn M)

theorem sealM_mx : («seal» (v.withBlk B)).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.allInstrs, GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem sealM_spSafe : («seal» (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.all, GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem sealM_xdepth : («seal» (v.withBlk B)).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, oneUndo, tagLenOk, recv, cmp, tagOut, copyTag, copyLoop, xorLoop, xorLoopG, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega_using [e]

theorem sealM_correct (s : State) (hs : (Proof.AesGcm.sealX86_64M M).pre s) :
    ∃ t s', Exec isa («seal» (v.withBlk B)) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := sealM_wp v B hs
  exact ⟨t, s', he, abiPreserved_of_exec (sealM_mx v B) he hg, hp⟩

theorem openM_mx : («open» (v.withBlk B)).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.allInstrs, GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem openM_spSafe : («open» (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, ↓reduceIte, Bool.false_eq_true, oneUndo, Code.all, GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem openM_xdepth : («open» (v.withBlk B)).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneBlocks, oneTag, oneCrypt, oneCryptG, oneCryptBlk, oneUndo, tagLenOk, recv, cmp, tagOut, copyTag, copyLoop, xorLoop, xorLoopG, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega_using [d]

theorem openM_correct (s : State) (hs : (Proof.AesGcm.openX86_64M M).pre s) :
    ∃ t s', Exec isa («open» (v.withBlk B)) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := openM_wp v B hs
  exact ⟨t, s', he, abiPreserved_of_exec (openM_mx v B) he hg, hp⟩

theorem streamEncryptM_mx : (streamEncrypt (v.withBlk B)).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, ↓reduceIte, Bool.false_eq_true, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, oneCryptG, oneCryptBlk, Code.allInstrs, GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamEncryptM_spSafe : (streamEncrypt (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, ↓reduceIte, Bool.false_eq_true, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, oneCryptG, oneCryptBlk, Code.all, GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamEncryptM_xdepth : (streamEncrypt (v.withBlk B)).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, oneAad, copyLoop, xorLoop, xorLoopG, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega_using [e]

theorem streamEncryptM_correct (s : State) (hs : (Proof.AesGcm.streamEncryptX86_64M M).pre s) :
    ∃ t s', Exec isa (streamEncrypt (v.withBlk B)) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.streamEncryptX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamEncryptM_wp v B hs
  exact ⟨t, s', he, abiPreserved_of_exec (streamEncryptM_mx v B) he hg, hp⟩

theorem streamDecryptM_mx : (streamDecrypt (v.withBlk B)).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, ↓reduceIte, Bool.false_eq_true, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, oneCryptG, oneCryptBlk, Code.allInstrs, GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamDecryptM_spSafe : (streamDecrypt (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, ↓reduceIte, Bool.false_eq_true, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, oneCryptG, oneCryptBlk, Code.all, GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamDecryptM_xdepth : (streamDecrypt (v.withBlk B)).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, j0hash, j0, firstFlush, streamText, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, oneAad, copyLoop, xorLoop, xorLoopG, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega_using [d]

theorem streamDecryptM_correct (s : State) (hs : (Proof.AesGcm.streamDecryptX86_64M M).pre s) :
    ∃ t s', Exec isa (streamDecrypt (v.withBlk B)) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.streamDecryptX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamDecryptM_wp v B hs
  exact ⟨t, s', he, abiPreserved_of_exec (streamDecryptM_mx v B) he hg, hp⟩

omit v B in
/-- Memory of zeros on a key context's 1024 bytes holds the powers of its
hash subkey. -/
theorem powersRepr_of_zero {m : Mem} {p : Addr} (h : ∀ i < 128 * 8, m (p + BitVec.ofNat 64 i) = 0) :
    Spec.Gcm.PowersRepr m p :=
  Proof.AesGcm.powersRepr_congr (m₁ := fun _ => 0) h (powersRepr_zero p)

/-- A state satisfying `vg_aes_gcm_seal_precomputed`'s precondition:
`sealSat`, with a key context of 1024 bytes. -/
def sealSatP : State :=
  { sealSat with rd := [⟨0x1000, 1024⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x8008, 32⟩] }

/-- `vg_aes_gcm_seal_precomputed`'s contract, for any code that does what
it says. -/
theorem sealPCode_verified {c : Prog isa}
    (hc : ∀ s, (Proof.AesGcm.sealX86_64M CtxMode.powers).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.sealX86_64.post s s')
    (hct : ConstantTime isa (Proof.AesGcm.sealX86_64M CtxMode.powers).pre Proof.AesGcm.sealX86_64.pub c) :
    Verified X86_64.target c (Proof.AesGcm.sealPrecomputedScratchContract X86_64.abi 24) :=
  Verified.of_correct hc hct
    { pre := by
        sig_implies_pre [Proof.AesGcm.sealPrecomputedScratchContract, Proof.AesGcm.sealPrecomputedScratchSig,
          Proof.Gcm.sealPrecomputedPre, Proof.AesGcm.sealRoundsPost, Proof.AesGcm.sealX86_64M, Proof.AesGcm.sealX86_64,
          Proof.AesGcm.sealPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, CtxMode.powers, X86_64.abi,
          Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      post := by
        sig_implies_post [Proof.AesGcm.sealPrecomputedScratchContract, Proof.AesGcm.sealPrecomputedScratchSig,
          Proof.Gcm.sealPrecomputedPre, Proof.AesGcm.sealRoundsPost, Proof.AesGcm.sealX86_64M, Proof.AesGcm.sealX86_64,
          Proof.AesGcm.sealPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, CtxMode.powers, X86_64.abi,
          Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      pub := by
        sig_implies_pub [Proof.AesGcm.sealPrecomputedScratchContract, Proof.AesGcm.sealPrecomputedScratchSig,
          Proof.Gcm.sealPrecomputedPre, Proof.AesGcm.sealRoundsPost, Proof.AesGcm.sealX86_64M, Proof.AesGcm.sealX86_64,
          Proof.AesGcm.sealPre, Proof.AesGcm.oneLay, Proof.AesGcm.onePub, CtxMode.powers, X86_64.abi,
          Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      sat := ⟨sealSatP, by
        sig_pre [Proof.AesGcm.sealPrecomputedScratchContract, Proof.AesGcm.sealPrecomputedScratchSig,
          Proof.Gcm.sealPrecomputedPre, X86_64.abi, X86_64.argRegs, sealSatP, sealSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | (refine powersRepr_of_zero fun i hi => ?_
             split
             · next h => exfalso; bv_omega
             · rfl)⟩ }

theorem sealP_verified :
    Verified X86_64.target («seal» (v.withBlk v.blkP)) (Proof.AesGcm.sealPrecomputedScratchContract X86_64.abi 24) :=
  sealPCode_verified (sealM_correct v v.blkP) (sealM_ct v v.blkP)

/-- A state satisfying `vg_aes_gcm_open_precomputed`'s precondition:
`openSat`, with a key context of 1024 bytes. -/
def openSatP : State :=
  { openSat with rd := [⟨0x1000, 1024⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0, 0⟩, ⟨0x8008, 40⟩] }

/-- `vg_aes_gcm_open_precomputed`'s contract, for any code that does what
it says. -/
theorem openPCode_verified {c : Prog isa}
    (hc : ∀ s, (Proof.AesGcm.openX86_64M CtxMode.powers).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.openX86_64.post s s')
    (hct : ConstantTime isa (Proof.AesGcm.openX86_64M CtxMode.powers).pre Proof.AesGcm.openX86_64.pub c) :
    Verified X86_64.target c (Proof.AesGcm.openPrecomputedScratchContract X86_64.abi 24) :=
  Verified.of_correct hc hct
    { pre := by sig_implies_pre [Proof.AesGcm.openPrecomputedScratchContract, Proof.AesGcm.openPrecomputedScratchSig,
          Proof.Gcm.openPrecomputedPre, Proof.AesGcm.openRoundsPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64M,
          Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay,
          Proof.AesGcm.onePub, CtxMode.powers, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      post := by sig_implies_post [Proof.AesGcm.openPrecomputedScratchContract, Proof.AesGcm.openPrecomputedScratchSig,
          Proof.Gcm.openPrecomputedPre, Proof.AesGcm.openRoundsPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64M,
          Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay,
          Proof.AesGcm.onePub, CtxMode.powers, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesGcm.openPrecomputedScratchContract, Proof.AesGcm.openPrecomputedScratchSig,
          Proof.Gcm.openPrecomputedPre, Proof.AesGcm.openRoundsPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64M,
          Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay,
          Proof.AesGcm.onePub, CtxMode.powers, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs] at h
        sig_split h
        sig_reduce [Proof.AesGcm.openPrecomputedScratchContract, Proof.AesGcm.openPrecomputedScratchSig,
          Proof.Gcm.openPrecomputedPre, Proof.AesGcm.openRoundsPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64M,
          Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay,
          Proof.AesGcm.onePub, CtxMode.powers, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
        sig_simp [Proof.AesGcm.openPrecomputedScratchContract, Proof.AesGcm.openPrecomputedScratchSig,
          Proof.Gcm.openPrecomputedPre, Proof.AesGcm.openRoundsPost, Spec.Gcm.openLeak, Proof.AesGcm.openX86_64M,
          Proof.AesGcm.openX86_64, Proof.AesGcm.openLeak, Proof.AesGcm.openPre, Proof.AesGcm.oneLay,
          Proof.AesGcm.onePub, CtxMode.powers, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := ⟨openSatP, by
        sig_pre [Proof.AesGcm.openPrecomputedScratchContract, Proof.AesGcm.openPrecomputedScratchSig,
          Proof.Gcm.openPrecomputedPre, X86_64.abi, X86_64.argRegs, openSatP, openSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact powersRepr_of_zero fun _ _ => rfl⟩ }

theorem openP_verified :
    Verified X86_64.target («open» (v.withBlk v.blkP)) (Proof.AesGcm.openPrecomputedScratchContract X86_64.abi 24) :=
  openPCode_verified (openM_correct v v.blkP) (openM_ct v v.blkP)

/-- A state satisfying the preconditions of `vg_aes_gcm_stream_encrypt_precomputed`
and `_decrypt_precomputed`: `crSat`, with a key context of 1024 bytes. -/
def crSatP : State := { crSat with rd := [⟨0x1000, 1024⟩, ⟨0x8008, 16⟩] }

theorem streamEncryptP_verified :
    Verified X86_64.target (streamEncrypt (v.withBlk v.blkP))
      (Proof.AesGcm.streamEncryptPrecomputedScratchContract X86_64.abi 24) :=
  Verified.of_correct (streamEncryptM_correct v v.blkP) (streamEncryptM_ct v v.blkP)
    { pre := by sig_implies_pre [Proof.AesGcm.streamEncryptPrecomputedScratchContract, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Proof.Gcm.streamTextPrecomputedPre, Proof.AesGcm.streamEncryptRoundsPost, Proof.AesGcm.streamEncryptX86_64M,
          Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.powers,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      post := by sig_implies_post [Proof.AesGcm.streamEncryptPrecomputedScratchContract, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Proof.Gcm.streamTextPrecomputedPre, Proof.AesGcm.streamEncryptRoundsPost, Proof.AesGcm.streamEncryptX86_64M,
          Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.powers,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      pub := by sig_implies_pub [Proof.AesGcm.streamEncryptPrecomputedScratchContract, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Proof.Gcm.streamTextPrecomputedPre, Proof.AesGcm.streamEncryptRoundsPost, Proof.AesGcm.streamEncryptX86_64M,
          Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.powers,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      sat := ⟨crSatP, by
        sig_pre [Proof.AesGcm.streamEncryptPrecomputedScratchContract, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Proof.Gcm.streamTextPrecomputedPre, X86_64.abi, X86_64.argRegs, crSatP, crSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact powersRepr_of_zero fun _ _ => rfl⟩ }

theorem streamDecryptP_verified :
    Verified X86_64.target (streamDecrypt (v.withBlk v.blkP))
      (Proof.AesGcm.streamDecryptPrecomputedScratchContract X86_64.abi 24) :=
  Verified.of_correct (streamDecryptM_correct v v.blkP) (streamDecryptM_ct v v.blkP)
    { pre := by sig_implies_pre [Proof.AesGcm.streamDecryptPrecomputedScratchContract, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Proof.Gcm.streamTextPrecomputedPre, Proof.AesGcm.streamDecryptRoundsPost, Proof.AesGcm.streamDecryptX86_64M,
          Proof.AesGcm.streamDecryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.powers,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      post := by sig_implies_post [Proof.AesGcm.streamDecryptPrecomputedScratchContract, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Proof.Gcm.streamTextPrecomputedPre, Proof.AesGcm.streamDecryptRoundsPost, Proof.AesGcm.streamDecryptX86_64M,
          Proof.AesGcm.streamDecryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.powers,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      pub := by sig_implies_pub [Proof.AesGcm.streamDecryptPrecomputedScratchContract, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Proof.Gcm.streamTextPrecomputedPre, Proof.AesGcm.streamDecryptRoundsPost, Proof.AesGcm.streamDecryptX86_64M,
          Proof.AesGcm.streamDecryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.powers,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      sat := ⟨crSatP, by
        sig_pre [Proof.AesGcm.streamDecryptPrecomputedScratchContract, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Proof.Gcm.streamTextPrecomputedPre, X86_64.abi, X86_64.argRegs, crSatP, crSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact powersRepr_of_zero fun _ _ => rfl⟩ }

/-! ### With their working space on the stack -/

/-- A state satisfying `vg_aes_gcm_seal_precomputed`'s precondition, without
the working space. -/
def sealFrameSatP : State := { sealFrameSat with rd := [⟨0x1000, 1024⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x8008, 24⟩] }

theorem sealFrameSatP_pre : ∃ s, (Proof.AesGcm.sealPrecomputedRoundsContract X86_64.abi 2624).pre s := by
  refine ⟨sealFrameSatP, ?_⟩
  sig_pre [Proof.AesGcm.sealPrecomputedRoundsContract, Proof.Gcm.sealPrecomputedSig, Proof.Gcm.sealPrecomputedPre,
    Proof.AesGcm.sealRoundsPost, X86_64.abi, X86_64.argRegs, sealFrameSatP, sealFrameSat, sealSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine powersRepr_of_zero fun i hi => ?_
       split
       · next h => exfalso; bv_omega
       · rfl)

/-- `vg_aes_gcm_seal_precomputed` in its frame, for any code that meets the
contract within it. -/
theorem sealPCode_framed {c : Prog isa}
    (hv : Verified X86_64.target c (Proof.AesGcm.sealPrecomputedScratchContract X86_64.abi 24))
    (hsp : c.all (fun i => !X86_64.isa.writesSp i) = true) (hxd : c.x86_64Depth ≤ 24) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 c)
      (Proof.AesGcm.sealPrecomputedRoundsContract X86_64.abi 2624) :=
  X86_64.Verified.stackArgScratch (hpostOut := Proof.AesGcm.sealPrecomputedPostOut_local _) (sig := Proof.Gcm.sealPrecomputedSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Proof.Gcm.sealPrecomputedPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.sealRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2600) hv (by decide) (by decide) (by decide)
    hsp hxd (Proof.AesGcm.sealPrecomputedPre_local _)
    (Proof.AesGcm.sealPrecomputedPost_local _) sealFrameSatP_pre

theorem sealP_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 3 («seal» (v.withBlk v.blkP)))
      (Proof.AesGcm.sealPrecomputedRoundsContract X86_64.abi 2624) :=
  sealPCode_framed (sealP_verified v) (sealM_spSafe v v.blkP) (sealM_xdepth v v.blkP)

/-- A state satisfying `vg_aes_gcm_open_precomputed`'s precondition, without
the working space. -/
def openFrameSatP : State :=
  { openFrameSat with rd := [⟨0x1000, 1024⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0, 0⟩, ⟨0x8008, 32⟩] }

theorem openFrameSatP_pre : ∃ s, (Proof.AesGcm.openPrecomputedRoundsContract X86_64.abi 2632).pre s := by
  refine ⟨openFrameSatP, ?_⟩
  sig_pre [Proof.AesGcm.openPrecomputedRoundsContract, Proof.Gcm.openPrecomputedSig, Proof.Gcm.openPrecomputedPre,
    Proof.AesGcm.openRoundsPost, Spec.Gcm.openLeak, X86_64.abi, X86_64.argRegs, openFrameSatP, openFrameSat, openSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact powersRepr_of_zero fun _ _ => rfl

/-- `vg_aes_gcm_open_precomputed` in its frame, for any code that meets the
contract within it. -/
theorem openPCode_framed {c : Prog isa}
    (hv : Verified X86_64.target c (Proof.AesGcm.openPrecomputedScratchContract X86_64.abi 24))
    (hsp : c.all (fun i => !X86_64.isa.writesSp i) = true) (hxd : c.x86_64Depth ≤ 24) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 c)
      (Proof.AesGcm.openPrecomputedRoundsContract X86_64.abi 2632) :=
  X86_64.Verified.stackArgScratch (hpostOut := Proof.AesGcm.openPrecomputedPostOut_local _) (sig := Proof.Gcm.openPrecomputedSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Proof.Gcm.openPrecomputedPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.openRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (leak := some (Spec.Gcm.openLeak X86_64.abi.ptrBits)) (bytes := 2608) hv
    (by decide) (by decide) (by decide) hsp hxd
    (Proof.AesGcm.openPrecomputedPre_local _) (Proof.AesGcm.openPrecomputedPost_local _) openFrameSatP_pre
    (hleak := Proof.AesGcm.openPrecomputedLeak_local _)

theorem openP_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 («open» (v.withBlk v.blkP)))
      (Proof.AesGcm.openPrecomputedRoundsContract X86_64.abi 2632) :=
  openPCode_framed (openP_verified v) (openM_spSafe v v.blkP) (openM_xdepth v v.blkP)

/-- A state satisfying the preconditions of `vg_aes_gcm_stream_encrypt_precomputed`
and `_decrypt_precomputed`, without the working space. -/
def crFrameSatP : State := { crFrameSat with rd := [⟨0x1000, 1024⟩, ⟨0x8008, 8⟩] }

theorem streamEncryptFrameSatP_pre : ∃ s, (Proof.AesGcm.streamEncryptPrecomputedRoundsContract X86_64.abi 2608).pre s := by
  refine ⟨crFrameSatP, ?_⟩
  sig_pre [Proof.AesGcm.streamEncryptPrecomputedRoundsContract, Proof.Gcm.streamCryptPrecomputedSig,
    Proof.Gcm.streamTextPrecomputedPre, Proof.AesGcm.streamEncryptRoundsPost, X86_64.abi, X86_64.argRegs, crFrameSatP, crFrameSat,
    crSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact powersRepr_of_zero fun _ _ => rfl

theorem streamEncryptP_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamEncrypt (v.withBlk v.blkP)))
      (Proof.AesGcm.streamEncryptPrecomputedRoundsContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratch (hpostOut := Proof.AesGcm.streamEncryptPrecomputedPostOut_local _) (sig := Proof.Gcm.streamCryptPrecomputedSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Proof.Gcm.streamTextPrecomputedPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.streamEncryptRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) (streamEncryptP_verified v) (by decide) (by decide) (by decide)
    (streamEncryptM_spSafe v v.blkP) (streamEncryptM_xdepth v v.blkP) (Proof.AesGcm.streamTextPrecomputedPre_local _)
    (Proof.AesGcm.streamEncryptPrecomputedPost_local _) streamEncryptFrameSatP_pre

theorem streamDecryptFrameSatP_pre : ∃ s, (Proof.AesGcm.streamDecryptPrecomputedRoundsContract X86_64.abi 2608).pre s := by
  refine ⟨crFrameSatP, ?_⟩
  sig_pre [Proof.AesGcm.streamDecryptPrecomputedRoundsContract, Proof.Gcm.streamCryptPrecomputedSig,
    Proof.Gcm.streamTextPrecomputedPre, Proof.AesGcm.streamDecryptRoundsPost, X86_64.abi, X86_64.argRegs, crFrameSatP, crFrameSat,
    crSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact powersRepr_of_zero fun _ _ => rfl

theorem streamDecryptP_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamDecrypt (v.withBlk v.blkP)))
      (Proof.AesGcm.streamDecryptPrecomputedRoundsContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratch (hpostOut := Proof.AesGcm.streamDecryptPrecomputedPostOut_local _) (sig := Proof.Gcm.streamCryptPrecomputedSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Proof.Gcm.streamTextPrecomputedPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.streamDecryptRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) (streamDecryptP_verified v) (by decide) (by decide) (by decide)
    (streamDecryptM_spSafe v v.blkP) (streamDecryptM_xdepth v v.blkP) (Proof.AesGcm.streamTextPrecomputedPre_local _)
    (Proof.AesGcm.streamDecryptPrecomputedPost_local _) streamDecryptFrameSatP_pre

/-! ### `vg_aes_gcm_init_precomputed` -/

omit B in
theorem initP_mx : (initPrecomputed v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  have hs : (powLoop v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
    simp only [powLoop, powStep, Code.allInstrs, GcmImpl.callees, v.gh.mxcsr, Bool.true_and, Bool.and_true]
    decide +kernel
  simp only [initPrecomputed, initWith, Code.allInstrs]
  rw [hs]
  simp only [GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

omit B in
theorem initP_spSafe : (initPrecomputed v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  have hs : (powLoop v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
    simp only [powLoop, powStep, Code.all, GcmImpl.callees, v.gh.spSafe, Bool.true_and, Bool.and_true]
    decide +kernel
  simp only [initPrecomputed, initWith, Code.all]
  rw [hs]
  simp only [GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, Bool.true_and, Bool.and_true]
  decide +kernel

omit B in
theorem initP_xdepth : (initPrecomputed v.callees).x86_64Depth ≤ 8 := by
  have hs : (powLoop v.callees).x86_64Depth ≤ 8 := by
    simp only [powLoop, powStep, Code.x86_64Depth, GcmImpl.callees, v.gh.noStack, Nat.max_le]
    decide +kernel
  simp only [initPrecomputed, initWith, Code.x86_64Depth, Nat.max_le]
  refine ⟨?_, ?_, ?_, ?_, ?_, hs, ?_⟩
  all_goals first | decide +kernel | (simp only [GcmImpl.callees, v.ctr.noStack, v.key.noStack]; decide +kernel)

omit B in
/-- A state satisfying `vg_aes_gcm_init_precomputed`'s precondition: `initSat`,
with a key context of 1024 bytes. -/
def initSatP : State := { initSat with wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2560⟩] }

omit B in
/-- A state satisfying `vg_aes_gcm_init_precomputed`'s precondition, without
the working space. -/
def initFrameSatP : State := { initSat with wr := [⟨0x2000, 1024⟩] }

theorem initFrameSatP_pre : ∃ s, (Proof.Gcm.initPrecomputedContract X86_64.abi 2576).pre s := by
  implies_sat [Proof.Gcm.initPrecomputedContract, Proof.Gcm.initPrecomputedSig, Spec.Gcm.initPre,
    Proof.Gcm.initPrecomputedPost, X86_64.abi, X86_64.argRegs] [initFrameSatP, initSat] using initFrameSatP

end VG.Proof.AesGcm.X86_64
