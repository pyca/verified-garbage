module

public import VerifiedGarbage.Proof.AesCfb.Spec
public import VerifiedGarbage.Impl.AesCfb.X86_64
public import VerifiedGarbage.Proof.AesCbc.X86_64.Group
import VerifiedGarbage.Proof.AesCbc.X86_64.Block
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.AesCfb.Spec
meta import VerifiedGarbage.Impl.AesCfb.X86_64
meta import VerifiedGarbage.Proof.AesCbc.X86_64.Group
meta import VerifiedGarbage.Proof.AesCbc.X86_64.Block
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract

-- separate module: the CFB128 group, which only `Verified.lean` uses, out of the one-block proofs.

/-!
# AES-CFB128 on x86-64: decryption four blocks at a time

`decGroup_ok`: one run of `decGroup` takes the loop invariant AES-CBC's
proofs share (`Proof/AesCbc/X86_64/Loop.lean`) from `k` blocks to `k + 4`
(`GroupOk`), for `cfbMode false`, for any implementation of the block
functions (`BlocksImpl`): the inputs of the block cipher, `Cⱼ₋₁` (the
chaining value for the first, the data block before for the others), are
copied to the slots of `gR` (`decA4_wp`) and enciphered there in place by one
call, the last `Cⱼ` becomes the chaining value, and each slot is XORed into
its data block. `decGroup_ct`: it is constant time (`GroupCt`).
-/

@[expose] public section

namespace VG.Proof.AesCfb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCfb.X86_64
open VG.Impl.AesCbc.X86_64 (copy gOff xorAt advance4 at_)
open VG.Proof.AesCbc
open VG.Proof.AesCbc.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)

/-- Closes the disjointness goals between the regions of a group. -/
macro "cfb_gd" : tactic => `(tactic| first
  | with_reducible exact UPre.dBB ‹_› ‹_› (by omega) (by omega) (by omega)
  | with_reducible exact UPre.dBT ‹_› ‹_› (by omega) (by omega)
  | with_reducible exact (UPre.dBT ‹_› ‹_› (by omega) (by omega)).symm
  | with_reducible exact UPre.dTT (by omega) (by omega) (by omega)
  | with_reducible exact UPre.dBI ‹_› ‹_› (by omega)
  | with_reducible exact (UPre.dBI ‹_› ‹_› (by omega)).symm
  | with_reducible exact UPre.dTI ‹_› (by omega)
  | with_reducible exact (UPre.dTI ‹_› (by omega)).symm
  | with_reducible exact UPre.dBG ‹_› ‹_› (by omega)
  | with_reducible exact UPre.dBS ‹_› ‹_› (by omega)
  | with_reducible exact UPre.dBK ‹_› ‹_› (by omega)
  | with_reducible exact UPre.dIG ‹_›
  | with_reducible exact UPre.dIS ‹_›
  | with_reducible exact UPre.dIK ‹_›)

/-- The slots as the call addresses them. -/
theorem slot_add (s₀ : State) (j : Nat) :
    S s₀ + BitVec.ofNat 64 2112 + BitVec.ofNat 64 (16 * j) = sl s₀ j := by
  rw [Offset.add_add]; rfl

/-- The arguments of the block function for the four slots. -/
theorem callArgs4_ok (s : State) :
    ∃ s', runBlock isa callArgs4 s = some s' ∧
      s'.gpr .rdi = s.gpr .rbx ∧ s'.gpr .rsi = s.gpr .rbp ∧
      s'.gpr .rdx = s.gpr .r15 + BitVec.ofNat 64 2112 ∧
      s'.gpr .rcx = 4 ∧ s'.gpr .r8 = s.gpr .r15 ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e : BitVec.signExtend 64 (BitVec.ofNat 32 gOff) = BitVec.ofNat 64 2112 := by decide
  refine ⟨_, by
    simp only [callArgs4, runBlock_cons, runStep_some, exec, execAlu, readSrc, Option.map_some,
      Option.bind_some, e]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, State.setReg32]

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-! ## The pieces of the group -/

/-- The chaining value copied to slot 0. -/
theorem UPre.ivSave_ok {t : State} (r12 : t.gpr .r12 = Iv s₀) (r15 : t.gpr .r15 = S s₀)
    (rd : t.rd = s₀.rd) (wr : t.wr = s₀.wr) :
    ∃ t', runBlock isa (copy .r15 gOff .r12 0) t = some t' ∧ (∀ r, r ≠ .rax → t'.gpr r = t.gpr r) ∧
      t'.mem = copyMem t.mem (sl s₀ 0) (Iv s₀) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hR : t.rd ++ t.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd, wr, hp.rd, hp.wr]; rfl
  have hW : t.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr, hp.wr]
  exact copy_ok t (dst := .r15) (src := .r12) (d := gOff) (e := 0)
    (by rw [r15]; rfl) (by rw [r15]; exact sl8 s₀ 0) (by rw [r12]; simp) (by rw [r12])
    (by rw [hR]; exact in_rw (by simp) cIv0) (by rw [hR]; exact in_rw (by simp) cIv8)
    (by rw [hW]; exact in_rw (by simp) (cSl s₀ (by decide)))
    (by rw [hW]; exact in_rw (by simp) (cSl8 s₀ (by decide)))
    (by decide) (by decide)

variable {k : Nat} (hk : k + 4 ≤ N s₀)
include hk

/-- Data block `j` copied to slot `j + 1`. -/
theorem UPre.cfbSave_ok {j : Nat} (hj : j < 3) {t : State} (r13 : t.gpr .r13 = blk s₀ k)
    (r15 : t.gpr .r15 = S s₀) (rd : t.rd = s₀.rd) (wr : t.wr = s₀.wr) :
    ∃ t', runBlock isa (saveAt j) t = some t' ∧ (∀ r, r ≠ .rax → t'.gpr r = t.gpr r) ∧
      t'.mem = copyMem t.mem (sl s₀ (j + 1)) (blk s₀ (k + j)) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hR : t.rd ++ t.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd, wr, hp.rd, hp.wr]; rfl
  have hW : t.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr, hp.wr]
  exact copy_ok t (dst := .r15) (src := .r13) (d := gOff + 16 * (j + 1)) (e := 16 * j)
    (by rw [r15]) (by rw [r15, sl8]) (by rw [r13, UPre.blk_add]) (by rw [r13, UPre.blk_add8])
    (by rw [hR]; exact in_rw (by simp) (hp.cBlk0 (k := k + j) (by omega)))
    (by rw [hR]; exact in_rw (by simp) (hp.cBlk8 (k := k + j) (by omega)))
    (by rw [hW]; exact in_rw (by simp) (cSl s₀ (by omega)))
    (by rw [hW]; exact in_rw (by simp) (cSl8 s₀ (by omega)))
    (by decide) (by decide)

/-- Data block 3 copied to the chaining value. -/
theorem UPre.ivLast_ok {t : State} (r12 : t.gpr .r12 = Iv s₀) (r13 : t.gpr .r13 = blk s₀ k)
    (rd : t.rd = s₀.rd) (wr : t.wr = s₀.wr) :
    ∃ t', runBlock isa (copy .r12 0 .r13 (16 * 3)) t = some t' ∧ (∀ r, r ≠ .rax → t'.gpr r = t.gpr r) ∧
      t'.mem = copyMem t.mem (Iv s₀) (blk s₀ (k + 3)) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hR : t.rd ++ t.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd, wr, hp.rd, hp.wr]; rfl
  have hW : t.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr, hp.wr]
  exact copy_ok t (dst := .r12) (src := .r13) (d := 0) (e := 16 * 3)
    (by rw [r12]; simp) (by rw [r12]) (by rw [r13, UPre.blk_add]) (by rw [r13, UPre.blk_add8])
    (by rw [hR]; exact in_rw (by simp) (hp.cBlk0 (k := k + 3) (by omega)))
    (by rw [hR]; exact in_rw (by simp) (hp.cBlk8 (k := k + 3) (by omega)))
    (by rw [hW]; exact in_rw (by simp) cIv0) (by rw [hW]; exact in_rw (by simp) cIv8)
    (by decide) (by decide)

/-- Slot `j` XORed into data block `j`. -/
theorem UPre.cfbFix_ok {j : Nat} (hj : j < 4) {t : State} (r13 : t.gpr .r13 = blk s₀ k)
    (r15 : t.gpr .r15 = S s₀) (rd : t.rd = s₀.rd) (wr : t.wr = s₀.wr) :
    ∃ t', runBlock isa (fixAt j) t = some t' ∧ (∀ r, r ≠ .rax → t'.gpr r = t.gpr r) ∧
      t'.mem = xorMem t.mem (blk s₀ (k + j)) (sl s₀ j) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hR : t.rd ++ t.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [rd, wr, hp.rd, hp.wr]; rfl
  have hW : t.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [wr, hp.wr]
  exact xorAt_ok t (dst := .r13) (src := .r15) (d := 16 * j) (e := gOff + 16 * j)
    (by rw [r13, UPre.blk_add]) (by rw [r13, UPre.blk_add8]) (by rw [r15]) (by rw [r15, sl8])
    (by rw [hR]; exact in_rw (by simp) (hp.cBlk0 (k := k + j) (by omega)))
    (by rw [hR]; exact in_rw (by simp) (hp.cBlk8 (k := k + j) (by omega)))
    (by rw [hR]; exact in_rw (by simp) (cSl s₀ hj)) (by rw [hR]; exact in_rw (by simp) (cSl8 s₀ hj))
    (by rw [hW]; exact in_rw (by simp) (hp.cBlk0 (k := k + j) (by omega)))
    (by rw [hW]; exact in_rw (by simp) (hp.cBlk8 (k := k + j) (by omega)))
    (by decide) (by decide)

end

/-! ## Before the call -/

/-- What the code before the call leaves. -/
structure DecA4 (s₀ : State) (k : Nat) (s t : State) : Prop where
  pre : CallPre4 t (W s₀) (S s₀ + BitVec.ofNat 64 2112) (S s₀) (R s₀)
  saved : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [gR s₀] s.mem t.mem
  slot0 : bytesAt t.mem (sl s₀ 0) 16 = bytesAt s.mem (Iv s₀) 16
  slot : ∀ j < 3, bytesAt t.mem (sl s₀ (j + 1)) 16 = bytesAt s.mem (blk s₀ (k + j)) 16

theorem decA4_wp {M : Mode} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k + 4 ≤ N s₀)
    {s : State} (h : LInv M s₀ k s) :
    WP isa (.block (decSave ++ callArgs4)) s (DecA4 s₀ k s) := by
  obtain ⟨t₁, run₁, g₁, m₁, rd₁, wr₁⟩ := UPre.ivSave_ok hp h.r12 h.r15 h.rd h.wr
  obtain ⟨t₂, run₂, g₂, m₂, rd₂, wr₂⟩ := UPre.cfbSave_ok hp hk (j := 0) (by decide)
    (by rw [g₁ _ (by decide), h.r13]) (by rw [g₁ _ (by decide), h.r15]) (by rw [rd₁, h.rd]) (by rw [wr₁, h.wr])
  obtain ⟨t₃, run₃, g₃, m₃, rd₃, wr₃⟩ := UPre.cfbSave_ok hp hk (j := 1) (by decide)
    (by rw [g₂ _ (by decide), g₁ _ (by decide), h.r13]) (by rw [g₂ _ (by decide), g₁ _ (by decide), h.r15])
    (by rw [rd₂, rd₁, h.rd]) (by rw [wr₂, wr₁, h.wr])
  obtain ⟨t₄, run₄, g₄, m₄, rd₄, wr₄⟩ := UPre.cfbSave_ok hp hk (j := 2) (by decide)
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), h.r13])
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), h.r15])
    (by rw [rd₃, rd₂, rd₁, h.rd]) (by rw [wr₃, wr₂, wr₁, h.wr])
  obtain ⟨t₅, run₅, rdi₅, rsi₅, rdx₅, rcx₅, r8₅, cs₅, mem₅, rd₅, wr₅⟩ := callArgs4_ok t₄
  have g (r : Reg) (hr : r ≠ .rax) : t₄.gpr r = s.gpr r := by
    rw [g₄ r hr, g₃ r hr, g₂ r hr, g₁ r hr]
  have rd₄' : t₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, rd₁]
  have wr₄' : t₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, wr₁]
  show WP isa (.block (copy .r15 gOff .r12 0 ++ saveAt 0 ++ saveAt 1 ++ saveAt 2 ++ callArgs4)) s _
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.of_runBlock ⟨t₁, run₁, WP.of_runBlock ⟨t₂, run₂, WP.of_runBlock ⟨t₃, run₃,
    WP.of_runBlock ⟨t₄, run₄, WP.of_runBlock ⟨t₅, run₅, ?_⟩⟩⟩⟩⟩
  have keep (r : Reg) (hr : r ∈ calleeSaved) : t₅.gpr r = s.gpr r := by
    rw [cs₅ r hr, g r (calleeSaved_ne_rax hr)]
  refine ⟨hp.callPre4G (by rw [rdi₅, g _ (by decide), h.rbx]) (by rw [rsi₅, g _ (by decide), h.rbp])
    (by rw [rdx₅, g _ (by decide), h.r15]) rcx₅ (by rw [r8₅, g _ (by decide), h.r15])
    (by rw [keep .rsp (by simp [calleeSaved]), h.rsp]) (by rw [rd₅, rd₄', h.rd]) (by rw [wr₅, wr₄', h.wr]),
    keep, by rw [rd₅, rd₄'], by rw [wr₅, wr₄'], ?_, ?_, fun j hj => ?_⟩
  · rw [mem₅, m₄, m₃, m₂, m₁]
    exact (copyMem_frameG _ (j := 0) (by decide) _).trans ((copyMem_frameG _ (j := 1) (by decide) _).trans
      ((copyMem_frameG _ (j := 2) (by decide) _).trans (copyMem_frameG _ (j := 3) (by decide) _)))
  · rw [mem₅, m₄, copyMem_other, m₃, copyMem_other, m₂, copyMem_other, m₁, copyMem_bytes] <;> cfb_gd
  · rw [mem₅]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · rw [m₄, copyMem_other, m₃, copyMem_other, m₂, copyMem_bytes, m₁, copyMem_other] <;> cfb_gd
    · rw [m₄, copyMem_other, m₃, copyMem_bytes, m₂, copyMem_other, m₁, copyMem_other] <;> cfb_gd
    · rw [m₄, copyMem_bytes, m₃, copyMem_other, m₂, copyMem_other, m₁, copyMem_other] <;> cfb_gd

/-! ## The group -/

theorem decGroup_ok (v : BlocksImpl) : GroupOk (cfbMode false) (decGroup v.enc) := by
  intro s₀ hp k hk s h
  have len : (blks s₀).length = N s₀ := by simp [Spec.Cbc.blocksAt]
  refine WP.seq (WP.mono (decA4_wp hp hk h) fun t₅ a => ?_)
  have rsp₅ : t₅.gpr .rsp = s₀.gpr .rsp := by rw [a.saved .rsp (by simp [calleeSaved]), h.rsp]
  refine WP.seq (WP.mono (blk_call4 v.encOk v.encNosp v.encDepth a.pre) fun t₆ c => ?_)
  have g₆ (r : Reg) (hr : r ∈ calleeSaved) : t₆.gpr r = s.gpr r := by rw [c.saved r hr, a.saved r hr]
  have rd₆ : t₆.rd = s₀.rd := by rw [c.rd, a.rd, h.rd]
  have wr₆ : t₆.wr = s₀.wr := by rw [c.wr, a.wr, h.wr]
  have r12₆ : t₆.gpr .r12 = Iv s₀ := by rw [g₆ _ (by simp [calleeSaved]), h.r12]
  have r13₆ : t₆.gpr .r13 = blk s₀ k := by rw [g₆ _ (by simp [calleeSaved]), h.r13]
  have r15₆ : t₆.gpr .r15 = S s₀ := by rw [g₆ _ (by simp [calleeSaved]), h.r15]
  obtain ⟨t₇, run₇, g₇, m₇, rd₇, wr₇⟩ := UPre.ivLast_ok hp hk r12₆ r13₆ rd₆ wr₆
  obtain ⟨t₈, run₈, g₈, m₈, rd₈, wr₈⟩ := UPre.cfbFix_ok hp hk (j := 0) (by decide)
    (by rw [g₇ _ (by decide), r13₆]) (by rw [g₇ _ (by decide), r15₆]) (by rw [rd₇, rd₆]) (by rw [wr₇, wr₆])
  obtain ⟨t₉, run₉, g₉, m₉, rd₉, wr₉⟩ := UPre.cfbFix_ok hp hk (j := 1) (by decide)
    (by rw [g₈ _ (by decide), g₇ _ (by decide), r13₆]) (by rw [g₈ _ (by decide), g₇ _ (by decide), r15₆])
    (by rw [rd₈, rd₇, rd₆]) (by rw [wr₈, wr₇, wr₆])
  obtain ⟨t₁₀, run₁₀, g₁₀, m₁₀, rd₁₀, wr₁₀⟩ := UPre.cfbFix_ok hp hk (j := 2) (by decide)
    (by rw [g₉ _ (by decide), g₈ _ (by decide), g₇ _ (by decide), r13₆])
    (by rw [g₉ _ (by decide), g₈ _ (by decide), g₇ _ (by decide), r15₆])
    (by rw [rd₉, rd₈, rd₇, rd₆]) (by rw [wr₉, wr₈, wr₇, wr₆])
  have g₁₀' (r : Reg) (hr : r ≠ .rax) : t₁₀.gpr r = t₆.gpr r := by
    rw [g₁₀ r hr, g₉ r hr, g₈ r hr, g₇ r hr]
  obtain ⟨t₁₁, run₁₁, g₁₁, m₁₁, rd₁₁, wr₁₁⟩ := UPre.cfbFix_ok hp hk (j := 3) (by decide)
    (by rw [g₁₀' _ (by decide), r13₆]) (by rw [g₁₀' _ (by decide), r15₆])
    (by rw [rd₁₀, rd₉, rd₈, rd₇, rd₆]) (by rw [wr₁₀, wr₉, wr₈, wr₇, wr₆])
  obtain ⟨t₁₂, run₁₂, r13₁₂, r14₁₂, cf₁₂, keep₁₂, m₁₂, rd₁₂, wr₁₂⟩ := advance4_regs (s := t₁₁) hk
    (by rw [g₁₁ _ (by decide), g₁₀' _ (by decide), r13₆])
    (by rw [g₁₁ _ (by decide), g₁₀' _ (by decide), g₆ _ (by simp [calleeSaved]), h.r14])
  show WP isa (.block (copy .r12 0 .r13 (16 * 3) ++ fixAt 0 ++ fixAt 1 ++ fixAt 2 ++ fixAt 3 ++ advance4)) t₆ _
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  refine WP.of_runBlock ⟨t₇, run₇, WP.of_runBlock ⟨t₈, run₈, WP.of_runBlock ⟨t₉, run₉,
    WP.of_runBlock ⟨t₁₀, run₁₀, WP.of_runBlock ⟨t₁₁, run₁₁, WP.of_runBlock ⟨t₁₂, run₁₂, ?_⟩⟩⟩⟩⟩⟩
  have g (r : Reg) (hr : r ∈ calleeSaved) (h13 : r ≠ .r13) (h14 : r ≠ .r14) : t₁₂.gpr r = s.gpr r := by
    rw [keep₁₂ r h13 h14, g₁₁ r (calleeSaved_ne_rax hr), g₁₀' r (calleeSaved_ne_rax hr), g₆ r hr]
  -- Memory.
  have cframe := c.frame
  rw [rsp₅] at cframe
  have fAll : Frame [⟨blk s₀ k, 64⟩, ivR s₀, ⟨S s₀, 2064⟩, gR s₀, stkR s₀] s.mem t₁₂.mem := by
    rw [m₁₂, m₁₁, m₁₀, m₉, m₈, m₇]
    refine (a.frame.sub ?_).trans ((cframe.sub ?_).trans (((copyMem_frame _ _ _).sub ?_).trans
      (((xorMem_frameB _ (by decide) _).sub ?_).trans (((xorMem_frameB _ (by decide) _).sub ?_).trans
        (((xorMem_frameB _ (by decide) _).sub ?_).trans ((xorMem_frameB _ (by decide) _).sub ?_))))))
    all_goals intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    · subst hr; exact ⟨gR s₀, by simp, fun _ h => h⟩
    · rcases hr with rfl | rfl | rfl
      · exact ⟨gR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    all_goals subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have big₄ : Frame (Big s₀) s₀.mem t₅.mem :=
    (UPre.big_of h.frame).trans (UPre.bigStep (a.frame.sub (all_cons ⟨gR s₀, by simp, fun _ h => h⟩ all_nil)))
  have hb (j : Nat) (hj : j < 4) :
      bytesAt s.mem (blk s₀ (k + j)) 16 = (blks s₀)[k + j]'(by rw [len]; omega) := h.blockAt (by omega) (by omega)
  have chain : bytesAt s.mem (Iv s₀) 16 = Spec.Cbc.next (iv0 s₀) ((blks s₀).take k) := by
    rw [h.iv]; simp only [chainK, cfbMode_chain, cts, Bool.false_eq_true, ite_false]
  -- The enciphered slots after the call, and the data blocks it left.
  have e (j : Nat) (hj : j < 4) : bytesAt t₆.mem (sl s₀ j) 16 =
      Spec.Cbc.aesWith (R s₀) (wK s₀) (bytesAt t₅.mem (sl s₀ j) 16) := by
    have := c.out j hj
    rw [slot_add] at this
    rw [this, ← aesWith_state, UPre.sched_bytes hp big₄]
  have dB (j : Nat) (hj : j < 4) :
      bytesAt t₆.mem (blk s₀ (k + j)) 16 = (blks s₀)[k + j]'(by rw [len]; omega) := by
    rw [bytesAt_frame cframe (all_cons (hp.dBG hk hj) (all_cons (hp.dBS hk hj) (all_cons (hp.dBK hk hj) all_nil)))
      (by decide), bytesAt_frame a.frame (all_cons (hp.dBG hk hj) all_nil) (by decide), hb j hj]
  -- The blocks and the chaining value after the group.
  have o0 : bytesAt t₁₂.mem (blk s₀ (k + 0)) 16 = Spec.Cbc.xor ((blks s₀)[k + 0]'(by rw [len]; omega))
      (Spec.Cbc.aesWith (R s₀) (wK s₀) (Spec.Cbc.next (iv0 s₀) ((blks s₀).take k))) := by
    rw [m₁₂, m₁₁, xorMem_other, m₁₀, xorMem_other, m₉, xorMem_other, m₈, xorMem_bytes, m₇, copyMem_other,
      copyMem_other, dB 0 (by decide), e 0 (by decide), a.slot0, chain] <;> cfb_gd
  have o (j : Nat) (hj : j < 3) : bytesAt t₁₂.mem (blk s₀ (k + (j + 1))) 16 =
      Spec.Cbc.xor ((blks s₀)[k + (j + 1)]'(by rw [len]; omega))
        (Spec.Cbc.aesWith (R s₀) (wK s₀) ((blks s₀)[k + j]'(by rw [len]; omega))) := by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · rw [m₁₂, m₁₁, xorMem_other, m₁₀, xorMem_other, m₉, xorMem_bytes, m₈, xorMem_other, xorMem_other, m₇,
        copyMem_other, copyMem_other, dB 1 (by decide), e 1 (by decide), a.slot 0 (by decide), hb 0 (by decide)]
        <;> cfb_gd
    · rw [m₁₂, m₁₁, xorMem_other, m₁₀, xorMem_bytes, m₉, xorMem_other, xorMem_other, m₈, xorMem_other,
        xorMem_other, m₇, copyMem_other, copyMem_other, dB 2 (by decide), e 2 (by decide), a.slot 1 (by decide),
        hb 1 (by decide)] <;> cfb_gd
    · rw [m₁₂, m₁₁, xorMem_bytes, m₁₀, xorMem_other, xorMem_other, m₉, xorMem_other, xorMem_other, m₈,
        xorMem_other, xorMem_other, m₇, copyMem_other, copyMem_other, dB 3 (by decide), e 3 (by decide),
        a.slot 2 (by decide), hb 2 (by decide)] <;> cfb_gd
  have ivF : bytesAt t₁₂.mem (Iv s₀) 16 = (blks s₀)[k + 3]'(by rw [len]; omega) := by
    rw [m₁₂, m₁₁, xorMem_other, m₁₀, xorMem_other, m₉, xorMem_other, m₈, xorMem_other, m₇, copyMem_bytes,
      dB 3 (by decide)] <;> cfb_gd
  -- The mode.
  have take4 : (blks s₀).take (k + 4) = (blks s₀).take k ++ [(blks s₀)[k + 0]'(by rw [len]; omega)] ++
      [(blks s₀)[k + 1]'(by rw [len]; omega)] ++ [(blks s₀)[k + 2]'(by rw [len]; omega)] ++
      [(blks s₀)[k + 3]'(by rw [len]; omega)] := by
    have t₀ : (blks s₀).take (k + 1) = (blks s₀).take k ++ [(blks s₀)[k + 0]'(by rw [len]; omega)] :=
      take_succ_blks s₀ (by omega)
    have t₁ : (blks s₀).take (k + 2) = (blks s₀).take (k + 1) ++ [(blks s₀)[k + 1]'(by rw [len]; omega)] :=
      take_succ_blks s₀ (by omega)
    have t₂ : (blks s₀).take (k + 3) = (blks s₀).take (k + 2) ++ [(blks s₀)[k + 2]'(by rw [len]; omega)] :=
      take_succ_blks s₀ (by omega)
    have t₃ : (blks s₀).take (k + 4) = (blks s₀).take (k + 3) ++ [(blks s₀)[k + 3]'(by rw [len]; omega)] :=
      take_succ_blks s₀ (by omega)
    rw [t₃, t₂, t₁, t₀]
  have hl : (outK (cfbMode false) s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega
  refine ⟨⟨?_, ?_, ?_, r13₁₂, r14₁₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, cf₁₂⟩
  · rw [g .rbx (by simp [calleeSaved]) (by decide) (by decide), h.rbx]
  · rw [g .rbp (by simp [calleeSaved]) (by decide) (by decide), h.rbp]
  · rw [g .r12 (by simp [calleeSaved]) (by decide) (by decide), h.r12]
  · rw [g .r15 (by simp [calleeSaved]) (by decide) (by decide), h.r15]
  · rw [g .rsp (by simp [calleeSaved]) (by decide) (by decide), h.rsp]
  · rw [rd₁₂, rd₁₁, rd₁₀, rd₉, rd₈, rd₇, rd₆]
  · rw [wr₁₂, wr₁₁, wr₁₀, wr₉, wr₈, wr₇, wr₆]
  · exact h.frame.trans (stepFrame4 hk fAll)
  · rw [hp.blocksAt_step4 hk fAll h.data hl, o0, o 0 (by decide), o 1 (by decide), o 2 (by decide)]
    simp only [outK, cfbMode_out, cfb, Bool.false_eq_true, ite_false]
    rw [take4, decrypt_snoc, decrypt_snoc, decrypt_snoc, decrypt_snoc, next_snoc, next_snoc, next_snoc]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · rw [ivF]
    simp only [chainK, cfbMode_chain, cts, Bool.false_eq_true, ite_false, take4, next_snoc]

/-! ## Constant time -/

theorem decGroupPre_taint : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
    (.block (decSave ++ callArgs4)) h).isSome = true := ⟨_, by taint_decide⟩

theorem decGroupPost_taint : ∃ h, (taint.check (Taint.ofRegs [.r12, .r13, .r14, .r15])
    (.block (decFix ++ advance4)) h).isSome = true := ⟨_, by taint_decide⟩

theorem decGroup_ct (v : BlocksImpl) : GroupCt (cfbMode false) (decGroup v.enc) :=
  fun hp hp' hq k => group_ct (D := fun s₀ _ => S s₀ + BitVec.ofNat 64 2112)
    (fun hq _ => by rw [pub_S hq]) v.encOk v.encCt v.encNosp v.encDepth
    decGroupPre_taint decGroupPost_taint
    (@fun _ hp _ hk _ h => WP.mono (decA4_wp hp hk h) fun _ a => Mid4.of h a.pre a.saved) hp hp' hq k

end VG.Proof.AesCfb.X86_64
