module

import VerifiedGarbage.Proof.AesCcm.X86_64.CryptCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.AesCcm.X86_64.CryptCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.AesCcm.X86_64.Callee
public import VerifiedGarbage.Proof.AesCcm.X86_64.Args
public import VerifiedGarbage.Proof.CmacAes.X86_64.Variant
import VerifiedGarbage.Proof.AesCcm.X86_64.Seal
public import VerifiedGarbage.Impl.AesCcm.X86_64
public import VerifiedGarbage.Proof.AesCcm.X86_64.Env
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Ccm
import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.AesGcm.X86_64.Mask
import VerifiedGarbage.Proof.AesCcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
public import VerifiedGarbage.Proof.AesCcm.X86_64.Crypt
import VerifiedGarbage.Proof.AesCcm.X86_64.Ctrs
import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.AesCcm.X86_64.Callee
meta import VerifiedGarbage.Proof.AesCcm.X86_64.Args
meta import VerifiedGarbage.Proof.CmacAes.X86_64.Variant
meta import VerifiedGarbage.Proof.AesCcm.X86_64.Seal
meta import VerifiedGarbage.Impl.AesCcm.X86_64
meta import VerifiedGarbage.Proof.AesCcm.X86_64.Env
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Spec.Ccm
meta import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Mask
meta import VerifiedGarbage.Proof.AesCcm.X86_64.Run
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
meta import VerifiedGarbage.Proof.AesCcm.X86_64.Crypt
meta import VerifiedGarbage.Proof.AesCcm.X86_64.Ctrs
meta import VerifiedGarbage.Proof.AesCcm.Mac
meta import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86_64.Narrow
import VerifiedGarbage.Proof.AesCcm.X86_64.Tag
import VerifiedGarbage.Proof.AesCcm.X86_64.Mac
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Narrow
meta import VerifiedGarbage.Proof.AesCcm.X86_64.Tag
meta import VerifiedGarbage.Proof.AesCcm.X86_64.Mac
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.AesCcm.X86_64.CTBase
public import VerifiedGarbage.Proof.AesCcm.X86_64.Aad
public import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Call
meta import VerifiedGarbage.Proof.AesCcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesCcm.X86_64.Aad
meta import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Call

/-! ### `AesCcm.X86_64.SealCT`, which only this module used -/

section

/-! ### `AesCcm.X86_64.MacCT`, which only this module used -/

section

/-!
# AES-CCM on x86-64: the MAC is constant time

Untrusted: everything here is checked by Lean. The code between the calls
of `vg_cmac_aes_update` passes the taint analysis from the public slots and
registers (`rel_taintC`); each call has the same arguments in both runs, by
correctness (`upd_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr copyLoop minLen)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)
open VG.Proof.CmacAes.Stream.X86_64 (UArgs upd_rel)
open VG.Proof.AesGcm.X86_64 (LoopPre copyLoop_ok)
open VG.Proof.AesCcm (hdrLen headLen adataBlocks)
open VG.WriteBytes

/-! ## `updBlock` -/

/-- The arguments of `updBlock`'s call. -/
theorem updArgsBlk_ok {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hRo : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (.block (updArgs y ++ ptr .rcx .r15 bO ++ ([.mov32 .r8 (imm 1)] : List Instr))) s fun s₁ =>
      UArgs s₁ K (W + BitVec.ofNat 64 y) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 384) R 1 ∧
      s₁.gpr .rsp = SP := by
  have h15 := E.r15
  have h13 := E.r13
  have r₁ := E.perm.wR (show 232 + 8 ≤ 2560 by decide)
  have hy' : y < 2 ^ 31 := by omega_arith
  obtain ⟨s₁, run₁, hm₁, hdi, hsi, hdx, hcx, hr8, hr9, hg₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      (updArgs y ++ ptr .rcx .r15 bO ++ [.mov32 .r8 (imm 1)]) s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .rdi = K ∧ s₁.gpr .rsi = BitVec.ofNat 64 R ∧ s₁.gpr .rdx = W + BitVec.ofNat 64 y ∧
      s₁.gpr .rcx = W + BitVec.ofNat 64 32 ∧ s₁.gpr .r8 = BitVec.ofNat 64 1 ∧
      s₁.gpr .r9 = W + BitVec.ofNat 64 384 ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp], s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [updArgs, h15, r₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [gpr_setReg, h13]
    · simp [gpr_setReg, hRo]
    · simp [gpr_setReg, h15, imm_eq hy']
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg]
    · simp [gpr_setReg, h15]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]
    all_goals rfl
  have E₁ : Env K W SP s₁ := E.keep hg₁ hrd₁ hwr₁
  have hq := srcW (s := s₁) L E₁.perm (t := 32) (k := 16 * 1) (by decide)
  have hqy : (⟨W + BitVec.ofNat 64 32, 16 * 1⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 y, 16⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  exact WP.of_runBlock ⟨s₁, run₁, uargs L E₁ hR (by omega_arith) hq hqy (by decide) hdi hsi hdx hcx hr8 hr9, E₁.rsp⟩

theorem updArgs_check {y : Nat} (hy : y = 0 ∨ y = 96) :
    ∃ hc, (taint.check (ccmT []) (.block (updArgs y ++ ptr .rcx .r15 bO ++ ([.mov32 .r8 (imm 1)] : List Instr))) hc).isSome = true := by
  rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- `updBlock y` in two runs. -/
theorem updBlock_rel (v : UpdateImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → Both K W SP R N A D nl al n tl [] s₁ s₂) :
    RelCT isa P (updBlock v.callee y) fun _ _ => True := by
  have a := (rel_taintC [] hDW hn hP (c := .block (updArgs y ++ ptr .rcx .r15 bO ++ [.mov32 .r8 (imm 1)]))
    (updArgs_check hy)).wp
    (F₁ := fun (s₁ : State) => UArgs s₁ K (W + BitVec.ofNat 64 y) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 384) R 1 ∧
      s₁.gpr .rsp = SP)
    (F₂ := fun (s₁ : State) => UArgs s₁ K (W + BitVec.ofNat 64 y) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 384) R 1 ∧
      s₁.gpr .rsp = SP)
    fun s₁ s₂ (h : P s₁ s₂) => ⟨updArgsBlk_ok L (hP _ _ h).e₁ hR (hP _ _ h).sl₁.rounds hy,
      updArgsBlk_ok L (hP _ _ h).e₂ hR (hP _ _ h).sl₂.rounds hy⟩
  exact RelCT.seq a (upd_rel v fun s₁ s₂ h => ⟨_, _, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2, h.2.2.2]⟩)

/-! ## `b0` -/

/-- A run whose `W + 48` holds `Ctr₀` for some nonce of `nl` bytes. -/
def C0 (W : Addr) (nl : Nat) (s : State) : Prop :=
  ∃ nonce : List Byte, nonce.length = nl ∧ bytesAt s.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0

theorem b0Pre_check {y : Nat} (hy : y = 0 ∨ y = 96) :
    ∃ hc, (taint.check (ccmT []) (.seq (.block [.mov .rax (.mem (at_ .r15 tlO)), .alu .sub .rax (imm 2),
        .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .mov32 .rcx (imm 14),
        .alu .sub .rcx (.mem (at_ .r15 nlenO)), .alu .add .rax (.reg .rcx), .mov .rcx (.mem (at_ .r15 alenO)),
        .alu .test .rcx (.reg .rcx)])
      (.seq (.ite .e (.block []) (.block [.alu .add .rax (imm 64)]))
      (.block (([.mov .rcx (.mem (at_ .r15 c0O)), .mov .rdx (.mem (at_ .r15 (c0O + 8))),
        .mov .rsi (.mem (at_ .r15 lenO)), .store (at_ .r15 bO) .rcx, .store8 (at_ .r15 bO) .rax, .bswap .rsi,
        .alu .or .rsi (.reg .rdx), .store (at_ .r15 (bO + 8)) .rsi] : List Instr) ++ zero16 y)))) hc).isSome = true := by
  rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- `b0 y` in two runs. -/
theorem b0_rel (v : UpdateImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hal : al < 2 ^ 64)
    (hn' : n < 256 ^ (15 - nl)) {y : Nat} (hy : y = 0 ∨ y = 96) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → Both K W SP R N A D nl al n tl [] s₁ s₂ ∧ C0 W nl s₁ ∧ C0 W nl s₂) :
    RelCT isa P (b0 v.callee y) fun _ _ => True := by
  have hy16 : y + 16 ≤ 112 := by omega_arith
  have pre : ∀ s, Both K W SP R N A D nl al n tl [] s s → C0 W nl s → WP isa _ s fun s' =>
      Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨W + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 y, 16⟩] s.mem s'.mem := fun s hb ⟨nonce, hl, hc⟩ =>
    WP.mono (b0Pre_ok L hb.e₁ hb.sl₁ hl h7 h13 ht4 ht16 hte hal hn' hc hy) fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  have hB : ∀ s₁ s₂, P s₁ s₂ → ∀ s, (s = s₁ ∨ s = s₂) → Both K W SP R N A D nl al n tl [] s s ∧ C0 W nl s :=
    fun s₁ s₂ h s hs => by
      obtain ⟨b, c₁, c₂⟩ := hP _ _ h
      rcases hs with rfl | rfl
      · exact ⟨⟨b.e₁, b.e₁, b.sl₁, b.sl₁, b.wr₁, b.wr₁, fun _ h => nomatch h⟩, c₁⟩
      · exact ⟨⟨b.e₂, b.e₂, b.sl₂, b.sl₂, b.wr₂, b.wr₂, fun _ h => nomatch h⟩, c₂⟩
  have a := (rel_taintC [] hDW hn (fun s₁ s₂ h => (hP s₁ s₂ h).1) (b0Pre_check hy)).wpDep
    (F := fun (s s' : State) => Both K W SP R N A D nl al n tl [] s s ∧ Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨W + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 y, 16⟩] s.mem s'.mem)
    fun s₁ s₂ (h : P s₁ s₂) => ⟨WP.mono (pre s₁ (hB _ _ h s₁ (.inl rfl)).1 (hB _ _ h s₁ (.inl rfl)).2) fun _ q =>
        ⟨(hB _ _ h s₁ (.inl rfl)).1, q⟩,
      WP.mono (pre s₂ (hB _ _ h s₂ (.inr rfl)).1 (hB _ _ h s₂ (.inr rfl)).2) fun _ q =>
        ⟨(hB _ _ h s₂ (.inr rfl)).1, q⟩⟩
  refine rel_assoc3 (RelCT.seq a (updBlock_rel v L hR hDW hn hy (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    fun s₁' s₂' h => ?_))
  obtain ⟨-, σ₁, σ₂, hσ, ⟨b₁, E₁, -, w₁, f₁⟩, ⟨b₂, E₂, -, w₂, f₂⟩⟩ := h
  have hm : ∀ r ∈ [(⟨W + BitVec.ofNat 64 32, 16⟩ : Region), ⟨W + BitVec.ofNat 64 y, 16⟩],
      ∃ r' ∈ mutR W SP D n, Region.Sub r r' := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
    · exact ⟨wA W, by simp, Offset.sub_base W hy16⟩
  exact ⟨E₁, E₂, slots_mut L hDW (f₁.sub hm) b₁.sl₁, slots_mut L hDW (f₂.sub hm) b₂.sl₁, w₁.trans b₁.wr₁,
    w₂.trans b₂.wr₁, fun _ h => nomatch h⟩

/-! ## `absorbPad` -/

theorem absorbW1_ok {s : State} {len : Nat} (hbp : s.gpr .rbp = BitVec.ofNat 64 len) (hl : len < 2 ^ 64) :
    WP isa (.block [.mov .r8 (.reg .rbp), .shift .shr .r8 4, .alu .test .r8 (.reg .r8)]) s fun s₁ =>
      s₁.mem = s.mem ∧ s₁.gpr .r8 = BitVec.ofNat 64 (len / 16) ∧ (∀ r, r ≠ .r8 → s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  refine WP.of_runBlock ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [gpr_setReg, hbp, shr4 len hl]
  · intro r a; simp [gpr_setReg, gpr_setFlags, a]
  all_goals rfl

theorem absorbWArgs_ok {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hRo : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} (hP : Buf K W SP s P len)
    (h12 : s.gpr .r12 = P) (h8 : s.gpr .r8 = BitVec.ofNat 64 (len / 16)) :
    WP isa (.block (updArgs y ++ ([.mov .rcx (.reg .r12)] : List Instr))) s fun s₂ =>
      UArgs s₂ K (W + BitVec.ofNat 64 y) P (W + BitVec.ofNat 64 384) R (len / 16) ∧ s₂.gpr .rsp = SP := by
  have hl := hP.lt
  have h15 := E.r15
  have h13 := E.r13
  have r₁ := E.perm.wR (show 232 + 8 ≤ 2560 by decide)
  have hy' : y < 2 ^ 31 := by omega_arith
  obtain ⟨s₂, run₂, hdi, hsi, hdx, hcx, hr8₂, hr9, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      (updArgs y ++ [.mov .rcx (.reg .r12)]) s = some s₂ ∧
      s₂.gpr .rdi = K ∧ s₂.gpr .rsi = BitVec.ofNat 64 R ∧ s₂.gpr .rdx = W + BitVec.ofNat 64 y ∧
      s₂.gpr .rcx = P ∧ s₂.gpr .r8 = BitVec.ofNat 64 (len / 16) ∧ s₂.gpr .r9 = W + BitVec.ofNat 64 384 ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp], s₂.gpr r = s.gpr r) ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by crun [updArgs, h15, r₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h13]
    · simp [gpr_setReg, hRo]
    · simp [gpr_setReg, h15, imm_eq hy']
    · simp [gpr_setReg, h12]
    · simp [gpr_setReg, h8]
    · simp [gpr_setReg, h15]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]
    all_goals rfl
  have E₂ : Env K W SP s₂ := E.keep hg₂ hrd₂ hwr₂
  have hb : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
  have hq := srcBuf ((hP.take hb).of_eq (s' := s₂) hrd₂ hwr₂)
  have hqy : (⟨P, 16 * (len / 16)⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 y, 16⟩ :=
    (hP.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by omega_arith))
  exact WP.of_runBlock ⟨s₂, run₂, uargs L E₂ hR (by omega_arith) hq hqy (by omega_arith) hdi hsi hdx hcx hr8₂ hr9, E₂.rsp⟩

theorem absorbT1_ok {s : State} {len : Nat} (hbp : s.gpr .rbp = BitVec.ofNat 64 len) (hl : len < 2 ^ 64) :
    WP isa (.block [.mov .rcx (.reg .rbp), .alu .and .rcx (imm 15), .alu .test .rcx (.reg .rcx)]) s fun s₁ =>
      s₁.mem = s.mem ∧ s₁.gpr .rcx = BitVec.ofNat 64 (len % 16) ∧ (∀ r, r ≠ .rcx → s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.zf = some (decide (len % 16 = 0)) := by
  refine WP.of_runBlock ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [gpr_setReg, hbp, and15', toNat_ofNat_of_lt hl]
  · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
  · rfl
  · rfl
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, hbp, and15', toNat_ofNat_of_lt hl,
      and_self_beq (show len % 16 < 2 ^ 64 by omega_arith)]

theorem absorbT2_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {P : Addr} {len : Nat}
    (hP : Buf K W SP s P len) (h12 : s.gpr .r12 = P) (hbp : s.gpr .rbp = BitVec.ofNat 64 len)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 (len % 16)) (h0 : len % 16 ≠ 0) :
    WP isa (.seq (.block (zero16 bO ++ ([.mov .rsi (.reg .rbp), .alu .sub .rsi (.reg .rcx), .alu .add .rsi (.reg .r12)] : List Instr) ++
        ptr .rdi .r15 bO)) copyLoop) s fun s' =>
      Env K W SP s' ∧ Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hl := hP.lt
  have h15 := E.r15
  have w₁ := E.perm.wW (show 32 + 8 ≤ 2560 by decide)
  have w₂ := E.perm.wW (show 40 + 8 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hm₂, hsi, hdi, hcx₂, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      (zero16 bO ++ [.mov .rsi (.reg .rbp), .alu .sub .rsi (.reg .rcx), .alu .add .rsi (.reg .r12)] ++
        ptr .rdi .r15 bO) s = some s₂ ∧
      s₂.mem = (s.mem.writeW (W + BitVec.ofNat 64 32) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 40)
        (0 : BitVec 64) ∧
      s₂.gpr .rsi = P + BitVec.ofNat 64 (16 * (len / 16)) ∧ s₂.gpr .rdi = W + BitVec.ofNat 64 32 ∧
      s₂.gpr .rcx = BitVec.ofNat 64 (len % 16) ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdi → s₂.gpr r = s.gpr r) ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    refine ⟨_, by crun [zero16, h15, w₁, w₂, add_ofNat_assoc], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags]; rfl
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbp, h12, hcx]
      rw [ofNat_sub (by omega_arith) hl, BitVec.add_comm, show len - len % 16 = 16 * (len / 16) by omega_arith]
    · simp [gpr_setReg, h15]
    · simp [gpr_setReg, hcx]
    · intro r a b c; simp [gpr_setReg, gpr_arithFlags, a, b, c]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have E₂ : Env K W SP s₂ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hrd₂ hwr₂
  have hT := (hP.slice (a := 16 * (len / 16)) (k := len % 16) (by omega_arith)).of_eq (s' := s₂) hrd₂ hwr₂
  have lp : LoopPre s₂ (P + BitVec.ofNat 64 (16 * (len / 16))) (W + BitVec.ofNat 64 32) (len % 16) :=
    ⟨hsi, hdi, hcx₂, by omega_arith, by omega_arith, hT.rd, E₂.perm.wC (by omega_arith), hT.w.sub_right (Lay.wSub (by omega_arith))⟩
  refine WP.mono (copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, hg₃, hrd₃, hwr₃⟩ => ⟨E₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide)) hrd₃ hwr₃, ?_,
    by rw [hrd₃, hrd₂], by rw [hwr₃, hwr₂]⟩
  have fZ : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s.mem s₂.mem := by
    rw [hm₂]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (0 : BitVec 64)
      (Offset.contains W (d := 32) (n := 8) (e := 32) (k := 16) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) (0 : BitVec 64)
      (Offset.contains W (d := 40) (n := 8) (e := 32) (k := 16) (by decide) (by decide) (by decide))
  refine fZ.trans ?_
  rw [hm₃]
  exact writeBytes_frame _ _ _ (by
    rw [length_bytesAt]
    exact Offset.contains W (d := 32) (n := len % 16) (e := 32) (k := 16) (by decide) (by omega_arith) (by decide))

/-- What a run of `absorbPad` needs: the `len` bytes at `P` in `r12`, `rbp`. -/
structure AbsPre (K W SP : Addr) (P : Addr) (len : Nat) (s : State) : Prop where
  buf : Buf K W SP s P len
  r12 : s.gpr .r12 = P
  rbp : s.gpr .rbp = BitVec.ofNat 64 len

theorem absW1_check : ∃ hc, ((taint.check (ccmT [.r12, .rbp])
    (.block [.mov .r8 (.reg .rbp), .shift .shr .r8 4, .alu .test .r8 (.reg .r8)]) hc).map (·.flags)) = some true :=
  ⟨_, by taint_decide⟩

theorem absWArgs_check {y : Nat} (hy : y = 0 ∨ y = 96) :
    ∃ hc, (taint.check (ccmT [.r12, .r8]) (.block (updArgs y ++ ([.mov .rcx (.reg .r12)] : List Instr))) hc).isSome = true := by
  rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- The whole blocks, in two runs. -/
theorem absorbWhole_rel (v : UpdateImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} {Q : State → State → Prop}
    (hQ : ∀ s₁ s₂, Q s₁ s₂ → One K W SP R N A D nl al n tl s₁ ∧ One K W SP R N A D nl al n tl s₂ ∧
      AbsPre K W SP P len s₁ ∧ AbsPre K W SP P len s₂) :
    RelCT isa Q (.seq (.block [.mov .r8 (.reg .rbp), .shift .shr .r8 4, .alu .test .r8 (.reg .r8)])
      (.ite .e (.block []) (.seq (.block (updArgs y ++ ([.mov .rcx (.reg .r12)] : List Instr))) (callUpdate v.callee))))
      fun _ _ => True := by
  have r₁ := (rel_flagsC [.r12, .rbp] hDW hn (fun s₁ s₂ (h : Q s₁ s₂) => by
    obtain ⟨o₁, o₂, a₁, a₂⟩ := hQ _ _ h
    exact Both.of o₁ o₂ (agree_of (l := [(.r12, P), (.rbp, BitVec.ofNat 64 len)])
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl
                      · exact a₁.r12
                      · exact a₁.rbp)
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl
                      · exact a₂.r12
                      · exact a₂.rbp))) absW1_check).wpDep
    (F := fun (σ s' : State) => One K W SP R N A D nl al n tl σ ∧ AbsPre K W SP P len σ ∧
      (s'.mem = σ.mem ∧ s'.gpr .r8 = BitVec.ofNat 64 (len / 16) ∧ (∀ r, r ≠ .r8 → s'.gpr r = σ.gpr r) ∧
        s'.rd = σ.rd ∧ s'.wr = σ.wr))
    fun s₁ s₂ (h : Q s₁ s₂) => by
      obtain ⟨o₁, o₂, a₁, a₂⟩ := hQ _ _ h
      exact ⟨WP.mono (absorbW1_ok a₁.rbp a₁.buf.lt) fun _ q => ⟨o₁, a₁, q⟩,
        WP.mono (absorbW1_ok a₂.rbp a₂.buf.lt) fun _ q => ⟨o₂, a₂, q⟩⟩
  -- After the first block, in each run.
  have after : ∀ σ s', One K W SP R N A D nl al n tl σ → AbsPre K W SP P len σ →
      (s'.mem = σ.mem ∧ s'.gpr .r8 = BitVec.ofNat 64 (len / 16) ∧ (∀ r, r ≠ .r8 → s'.gpr r = σ.gpr r) ∧
        s'.rd = σ.rd ∧ s'.wr = σ.wr) →
      One K W SP R N A D nl al n tl s' ∧ AbsPre K W SP P len s' ∧ s'.gpr .r8 = BitVec.ofNat 64 (len / 16) :=
    fun σ s' o a ⟨hm, h8, hg, hrd, hwr⟩ =>
      ⟨⟨o.env.keep (fun r hr => hg r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
          hrd hwr, hm ▸ o.sl, hwr.trans o.wr⟩,
        ⟨a.buf.of_eq hrd hwr, by rw [hg _ (by decide), a.r12], by rw [hg _ (by decide), a.rbp]⟩, h8⟩
  refine RelCT.seq r₁ (RelCT.ite (fun s₁ s₂ h => eval_e_eq h.1.2) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  have hA : ∀ s₁ s₂, ((s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf) ∧ ∃ σ₁ σ₂, Q σ₁ σ₂ ∧
      (One K W SP R N A D nl al n tl σ₁ ∧ AbsPre K W SP P len σ₁ ∧ (s₁.mem = σ₁.mem ∧
        s₁.gpr .r8 = BitVec.ofNat 64 (len / 16) ∧ (∀ r, r ≠ .r8 → s₁.gpr r = σ₁.gpr r) ∧ s₁.rd = σ₁.rd ∧
        s₁.wr = σ₁.wr)) ∧
      (One K W SP R N A D nl al n tl σ₂ ∧ AbsPre K W SP P len σ₂ ∧ (s₂.mem = σ₂.mem ∧
        s₂.gpr .r8 = BitVec.ofNat 64 (len / 16) ∧ (∀ r, r ≠ .r8 → s₂.gpr r = σ₂.gpr r) ∧ s₂.rd = σ₂.rd ∧
        s₂.wr = σ₂.wr))) ∧ isa.eval .e s₁ = some false →
      (One K W SP R N A D nl al n tl s₁ ∧ AbsPre K W SP P len s₁ ∧ s₁.gpr .r8 = BitVec.ofNat 64 (len / 16)) ∧
      (One K W SP R N A D nl al n tl s₂ ∧ AbsPre K W SP P len s₂ ∧ s₂.gpr .r8 = BitVec.ofNat 64 (len / 16)) :=
    fun s₁ s₂ ⟨⟨_, σ₁, σ₂, _, ⟨o₁, a₁, q₁⟩, ⟨o₂, a₂, q₂⟩⟩, _⟩ => ⟨after σ₁ s₁ o₁ a₁ q₁, after σ₂ s₂ o₂ a₂ q₂⟩
  have r₂ := (rel_taintC [.r12, .r8] hDW hn (fun s₁ s₂ h => by
    obtain ⟨⟨o₁, a₁, h₁⟩, ⟨o₂, a₂, h₂⟩⟩ := hA s₁ s₂ h
    exact Both.of o₁ o₂ (agree_of (l := [(.r12, P), (.r8, BitVec.ofNat 64 (len / 16))])
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl
                      · exact a₁.r12
                      · exact h₁)
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl
                      · exact a₂.r12
                      · exact h₂))) (absWArgs_check hy)).wp
    (F₁ := fun (s : State) => UArgs s K (W + BitVec.ofNat 64 y) P (W + BitVec.ofNat 64 384) R (len / 16) ∧
      s.gpr .rsp = SP)
    (F₂ := fun (s : State) => UArgs s K (W + BitVec.ofNat 64 y) P (W + BitVec.ofNat 64 384) R (len / 16) ∧
      s.gpr .rsp = SP)
    fun s₁ s₂ h => by
      obtain ⟨⟨o₁, a₁, h₁⟩, ⟨o₂, a₂, h₂⟩⟩ := hA s₁ s₂ h
      exact ⟨absorbWArgs_ok L o₁.env hR o₁.sl.rounds hy a₁.buf a₁.r12 h₁,
        absorbWArgs_ok L o₂.env hR o₂.sl.rounds hy a₂.buf a₂.r12 h₂⟩
  exact RelCT.seq r₂ (upd_rel v fun s₁ s₂ h => ⟨_, _, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2, h.2.2.2]⟩)

theorem absT1_check : ∃ hc, ((taint.check (ccmT [.r12, .rbp])
    (.block [.mov .rcx (.reg .rbp), .alu .and .rcx (imm 15), .alu .test .rcx (.reg .rcx)]) hc).map (·.flags)) =
      some true := ⟨_, by taint_decide⟩

theorem absT2_check : ∃ hc, (taint.check (ccmT [.rcx, .r12, .rbp])
    (.seq (.block (zero16 bO ++ ([.mov .rsi (.reg .rbp), .alu .sub .rsi (.reg .rcx), .alu .add .rsi (.reg .r12)] : List Instr) ++
      ptr .rdi .r15 bO)) copyLoop) hc).isSome = true := ⟨_, by taint_decide⟩

/-- The last bytes, in two runs. -/
theorem absorbTail_rel (v : UpdateImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} {Q : State → State → Prop}
    (hQ : ∀ s₁ s₂, Q s₁ s₂ → One K W SP R N A D nl al n tl s₁ ∧ One K W SP R N A D nl al n tl s₂ ∧
      AbsPre K W SP P len s₁ ∧ AbsPre K W SP P len s₂) :
    RelCT isa Q (.seq (.block [.mov .rcx (.reg .rbp), .alu .and .rcx (imm 15), .alu .test .rcx (.reg .rcx)])
        (.ite .e (.block [])
          (.seq (.block (zero16 bO ++ ([.mov .rsi (.reg .rbp), .alu .sub .rsi (.reg .rcx), .alu .add .rsi (.reg .r12)] : List Instr) ++
              ptr .rdi .r15 bO))
            (.seq copyLoop (updBlock v.callee y)))))
      fun _ _ => True := by
  have r₁ := (rel_flagsC [.r12, .rbp] hDW hn (fun s₁ s₂ (h : Q s₁ s₂) => by
    obtain ⟨o₁, o₂, a₁, a₂⟩ := hQ _ _ h
    exact Both.of o₁ o₂ (agree_of (l := [(.r12, P), (.rbp, BitVec.ofNat 64 len)])
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl
                      · exact a₁.r12
                      · exact a₁.rbp)
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl
                      · exact a₂.r12
                      · exact a₂.rbp))) absT1_check).wpDep
    (F := fun (σ s' : State) => One K W SP R N A D nl al n tl σ ∧ AbsPre K W SP P len σ ∧
      (s'.mem = σ.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 (len % 16) ∧ (∀ r, r ≠ .rcx → s'.gpr r = σ.gpr r) ∧
        s'.rd = σ.rd ∧ s'.wr = σ.wr ∧ s'.zf = some (decide (len % 16 = 0))))
    fun s₁ s₂ (h : Q s₁ s₂) => by
      obtain ⟨o₁, o₂, a₁, a₂⟩ := hQ _ _ h
      exact ⟨WP.mono (absorbT1_ok a₁.rbp a₁.buf.lt) fun _ q => ⟨o₁, a₁, q⟩,
        WP.mono (absorbT1_ok a₂.rbp a₂.buf.lt) fun _ q => ⟨o₂, a₂, q⟩⟩
  have after : ∀ σ s', One K W SP R N A D nl al n tl σ → AbsPre K W SP P len σ →
      (s'.mem = σ.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 (len % 16) ∧ (∀ r, r ≠ .rcx → s'.gpr r = σ.gpr r) ∧
        s'.rd = σ.rd ∧ s'.wr = σ.wr ∧ s'.zf = some (decide (len % 16 = 0))) →
      One K W SP R N A D nl al n tl s' ∧ AbsPre K W SP P len s' ∧ s'.gpr .rcx = BitVec.ofNat 64 (len % 16) :=
    fun σ s' o a ⟨hm, hc, hg, hrd, hwr, _⟩ =>
      ⟨⟨o.env.keep (fun r hr => hg r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
          hrd hwr, hm ▸ o.sl, hwr.trans o.wr⟩,
        ⟨a.buf.of_eq hrd hwr, by rw [hg _ (by decide), a.r12], by rw [hg _ (by decide), a.rbp]⟩, hc⟩
  refine RelCT.seq r₁ (RelCT.ite (fun s₁ s₂ h => eval_e_eq h.1.2) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  have hA : ∀ s₁ s₂, ((s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf) ∧ ∃ σ₁ σ₂, Q σ₁ σ₂ ∧
      (One K W SP R N A D nl al n tl σ₁ ∧ AbsPre K W SP P len σ₁ ∧ (s₁.mem = σ₁.mem ∧
        s₁.gpr .rcx = BitVec.ofNat 64 (len % 16) ∧ (∀ r, r ≠ .rcx → s₁.gpr r = σ₁.gpr r) ∧ s₁.rd = σ₁.rd ∧
        s₁.wr = σ₁.wr ∧ s₁.zf = some (decide (len % 16 = 0)))) ∧
      (One K W SP R N A D nl al n tl σ₂ ∧ AbsPre K W SP P len σ₂ ∧ (s₂.mem = σ₂.mem ∧
        s₂.gpr .rcx = BitVec.ofNat 64 (len % 16) ∧ (∀ r, r ≠ .rcx → s₂.gpr r = σ₂.gpr r) ∧ s₂.rd = σ₂.rd ∧
        s₂.wr = σ₂.wr ∧ s₂.zf = some (decide (len % 16 = 0))))) ∧ isa.eval .e s₁ = some false →
      (One K W SP R N A D nl al n tl s₁ ∧ AbsPre K W SP P len s₁ ∧ s₁.gpr .rcx = BitVec.ofNat 64 (len % 16)) ∧
      (One K W SP R N A D nl al n tl s₂ ∧ AbsPre K W SP P len s₂ ∧ s₂.gpr .rcx = BitVec.ofNat 64 (len % 16)) ∧
      len % 16 ≠ 0 :=
    fun s₁ s₂ ⟨⟨_, σ₁, σ₂, _, ⟨o₁, a₁, q₁⟩, ⟨o₂, a₂, q₂⟩⟩, he⟩ => by
      refine ⟨after σ₁ s₁ o₁ a₁ q₁, after σ₂ s₂ o₂ a₂ q₂, fun h0 => ?_⟩
      rw [show isa.eval .e s₁ = s₁.zf from rfl, q₁.2.2.2.2.2, h0] at he; cases he
  have r₂ := (rel_taintC [.rcx, .r12, .rbp] hDW hn (fun s₁ s₂ h => by
    obtain ⟨⟨o₁, a₁, h₁⟩, ⟨o₂, a₂, h₂⟩, -⟩ := hA s₁ s₂ h
    exact Both.of o₁ o₂ (agree_of (l := [(.rcx, BitVec.ofNat 64 (len % 16)), (.r12, P), (.rbp, BitVec.ofNat 64 len)])
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl | rfl
                      · exact h₁
                      · exact a₁.r12
                      · exact a₁.rbp)
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl | rfl
                      · exact h₂
                      · exact a₂.r12
                      · exact a₂.rbp))) absT2_check).wpDep
    (F := fun (σ s' : State) => One K W SP R N A D nl al n tl σ ∧
      (Env K W SP s' ∧ Frame [⟨W + BitVec.ofNat 64 32, 16⟩] σ.mem s'.mem ∧ s'.rd = σ.rd ∧ s'.wr = σ.wr))
    fun s₁ s₂ h => by
      obtain ⟨⟨o₁, a₁, h₁⟩, ⟨o₂, a₂, h₂⟩, h0⟩ := hA s₁ s₂ h
      exact ⟨WP.mono (absorbT2_ok o₁.env a₁.buf a₁.r12 a₁.rbp h₁ h0) fun _ q => ⟨o₁, q⟩,
        WP.mono (absorbT2_ok o₂.env a₂.buf a₂.r12 a₂.rbp h₂ h0) fun _ q => ⟨o₂, q⟩⟩
  have hm : ∀ r ∈ [(⟨W + BitVec.ofNat 64 32, 16⟩ : Region)], ∃ r' ∈ mutR W SP D n, Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
  refine rel_assoc (RelCT.seq r₂ (updBlock_rel v L hR hDW hn hy (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    fun s₁ s₂ h => ?_))
  obtain ⟨-, σ₁, σ₂, -, ⟨o₁, E₁, f₁, -, w₁⟩, ⟨o₂, E₂, f₂, -, w₂⟩⟩ := h
  exact ⟨E₁, E₂, slots_mut L hDW (f₁.sub hm) o₁.sl, slots_mut L hDW (f₂.sub hm) o₂.sl, w₁.trans o₁.wr,
    w₂.trans o₂.wr, fun _ h => nomatch h⟩

/-- What the pieces of the MAC write, within what the pieces may write. -/
theorem macR_mut [fp : Footprint] (W SP D : Addr) (n : Nat) {y : Nat} (hy : y + 16 ≤ 112) :
    ∀ r ∈ macR W SP y, ∃ r' ∈ mutR W SP D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨wA W, by simp, Offset.sub_base W hy⟩
  · exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
  · exact ⟨wC W, by simp, scratch_sub_tail W⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- After a piece of the MAC, the public facts of a run. -/
theorem One.macR [fp : Footprint] {K W SP : Addr} {R : Nat} {N A D : Addr} {nl al n tl : Nat} (L : Lay K W SP)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) {y : Nat} (hy : y + 16 ≤ 112) {s s' : State}
    (o : One K W SP R N A D nl al n tl s) (E : Env K W SP s') (hf : Frame (macR W SP y) s.mem s'.mem)
    (hwr : s'.wr = s.wr) : One K W SP R N A D nl al n tl s' :=
  ⟨E, slots_mut L hDW (hf.sub (macR_mut W SP D n hy)) o.sl, hwr.trans o.wr⟩

/-- `absorbPad y` in two runs. -/
theorem absorbPad_rel (v : UpdateImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {len : Nat} {Q : State → State → Prop}
    (hQ : ∀ s₁ s₂, Q s₁ s₂ → One K W SP R N A D nl al n tl s₁ ∧ One K W SP R N A D nl al n tl s₂ ∧
      AbsPre K W SP P len s₁ ∧ AbsPre K W SP P len s₂) :
    RelCT isa Q (absorbPad v.callee y) fun _ _ => True := by
  have hy16 : y + 16 ≤ 112 := by omega_arith
  have r₁ := (absorbWhole_rel v L hR hDW hn hy hQ).wpDep
    (F := fun (σ s' : State) => One K W SP R N A D nl al n tl σ ∧ AbsPre K W SP P len σ ∧
      ∃ Y, @Absorbed _ K W SP σ y P len Y s')
    fun s₁ s₂ h => by
      obtain ⟨o₁, o₂, a₁, a₂⟩ := hQ _ _ h
      exact ⟨WP.mono (absorbWhole_ok v L o₁.env hR o₁.sl.rounds hy a₁.buf a₁.r12 a₁.rbp) fun _ q => ⟨o₁, a₁, _, q⟩,
        WP.mono (absorbWhole_ok v L o₂.env hR o₂.sl.rounds hy a₂.buf a₂.r12 a₂.rbp) fun _ q => ⟨o₂, a₂, _, q⟩⟩
  refine rel_assoc (RelCT.seq r₁ (absorbTail_rel v L hR hDW hn hy (N := N) (A := A) (nl := nl) (al := al)
    (tl := tl) (P := P) (len := len) fun s₁ s₂ h => ?_))
  obtain ⟨-, σ₁, σ₂, -, ⟨o₁, a₁, _, A₁⟩, ⟨o₂, a₂, _, A₂⟩⟩ := h
  exact ⟨o₁.macR L hDW hy16 A₁.env A₁.frame A₁.wr, o₂.macR L hDW hy16 A₂.env A₂.frame A₂.wr,
    ⟨a₁.buf.of_eq A₁.rd A₁.wr, A₁.r12, A₁.rbp⟩, ⟨a₂.buf.of_eq A₂.rd A₂.wr, A₂.r12, A₂.rbp⟩⟩

/-! ## `aad` -/

theorem aadHeadPre_check : ∃ hc, (taint.check (ccmT [.r12, .rbp]) (.seq header (.seq minLen
    (.seq (.block [.mov .rsi (.reg .r12), .mov .rdi (.reg .r15), .alu .add .rdi (.reg .rbx), .alu .add .rdi (imm bO),
      .alu .add .r12 (.reg .rcx), .alu .sub .rbp (.reg .rcx)]) copyLoop))) hc).isSome = true := ⟨_, by taint_decide⟩

/-- The first block of the associated data, in two runs. -/
theorem aadHead_rel (v : UpdateImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : Addr} {a : Nat} (ha0 : 0 < a) {Q : State → State → Prop}
    (hQ : ∀ s₁ s₂, Q s₁ s₂ → One K W SP R N A D nl al n tl s₁ ∧ One K W SP R N A D nl al n tl s₂ ∧
      AbsPre K W SP P a s₁ ∧ AbsPre K W SP P a s₂) :
    RelCT isa Q (aadHead v.callee y) fun _ _ => True := by
  have r₁ := (rel_taintC [.r12, .rbp] hDW hn (fun s₁ s₂ (h : Q s₁ s₂) => by
    obtain ⟨o₁, o₂, a₁, a₂⟩ := hQ _ _ h
    exact Both.of o₁ o₂ (agree_of (l := [(.r12, P), (.rbp, BitVec.ofNat 64 a)])
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl
                      · exact a₁.r12
                      · exact a₁.rbp)
      (fun p hp => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl
                      · exact a₂.r12
                      · exact a₂.rbp))) aadHeadPre_check).wpDep
    (F := fun (σ s' : State) => One K W SP R N A D nl al n tl σ ∧
      (Env K W SP s' ∧ s'.rd = σ.rd ∧ s'.wr = σ.wr ∧ Frame [⟨W + BitVec.ofNat 64 32, 16⟩] σ.mem s'.mem))
    fun s₁ s₂ h => by
      obtain ⟨o₁, o₂, a₁, a₂⟩ := hQ _ _ h
      exact ⟨WP.mono (aadHeadPre_ok o₁.env a₁.buf ha0 a₁.r12 a₁.rbp) fun _ q => ⟨o₁, q.1, q.2.1, q.2.2.1, q.2.2.2.1⟩,
        WP.mono (aadHeadPre_ok o₂.env a₂.buf ha0 a₂.r12 a₂.rbp) fun _ q => ⟨o₂, q.1, q.2.1, q.2.2.1, q.2.2.2.1⟩⟩
  have hm : ∀ r ∈ [(⟨W + BitVec.ofNat 64 32, 16⟩ : Region)], ∃ r' ∈ mutR W SP D n, Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
  refine rel_assoc4 (RelCT.seq r₁ (updBlock_rel v L hR hDW hn hy (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    fun s₁ s₂ h => ?_))
  obtain ⟨-, σ₁, σ₂, -, ⟨o₁, E₁, -, w₁, f₁⟩, ⟨o₂, E₂, -, w₂, f₂⟩⟩ := h
  exact ⟨E₁, E₂, slots_mut L hDW (f₁.sub hm) o₁.sl, slots_mut L hDW (f₂.sub hm) o₂.sl, w₁.trans o₁.wr,
    w₂.trans o₂.wr, fun _ h => nomatch h⟩

theorem aadBlk_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (S : Slots W R N A D nl al n tl s.mem) (ha : al < 2 ^ 64) :
    WP isa (.block [.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO)), .alu .test .rbp (.reg .rbp)])
      s fun s₁ => s₁.mem = s.mem ∧ s₁.gpr .r12 = A ∧ s₁.gpr .rbp = BitVec.ofNat 64 al ∧
        s₁.zf = some (decide (al = 0)) ∧ (∀ r ∈ [Reg.r13, .r15, .rsp], s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧
        s₁.wr = s.wr := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 176 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 184 + 8 ≤ 2560 by decide)
  have hAp := S.aad
  have hal := S.alen
  refine WP.of_runBlock ⟨_, by crun [h15, r₁, r₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [gpr_setReg, gpr_arithFlags, hAp]
  · simp [gpr_setReg, gpr_arithFlags, hal]
  · simp only [zf_arithFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, hal, and_self_beq ha]
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  all_goals rfl

theorem aadBlk_check : ∃ hc, ((taint.check (ccmT [])
    (.block [.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO)), .alu .test .rbp (.reg .rbp)])
    hc).map (·.flags)) = some true := ⟨_, by taint_decide⟩

/-- The associated data, in two runs. -/
theorem aad_rel (v : UpdateImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    {y : Nat} (hy : y = 0 ∨ y = 96) {Q : State → State → Prop}
    (hQ : ∀ s₁ s₂, Q s₁ s₂ → One K W SP R N A D nl al n tl s₁ ∧ One K W SP R N A D nl al n tl s₂ ∧
      Buf K W SP s₁ A al ∧ Buf K W SP s₂ A al) :
    RelCT isa Q (aad v.callee y) fun _ _ => True := by
  have hy16 : y + 16 ≤ 112 := by omega_arith
  have r₁ := (rel_flagsC [] hDW hn (fun s₁ s₂ (h : Q s₁ s₂) => by
    obtain ⟨o₁, o₂, -, -⟩ := hQ _ _ h; exact Both.of o₁ o₂ fun _ h => nomatch h) aadBlk_check).wpDep
    (F := fun (σ s' : State) => One K W SP R N A D nl al n tl σ ∧ Buf K W SP σ A al ∧
      (s'.mem = σ.mem ∧ s'.gpr .r12 = A ∧ s'.gpr .rbp = BitVec.ofNat 64 al ∧
        s'.zf = some (decide (al = 0)) ∧ (∀ r ∈ [Reg.r13, .r15, .rsp], s'.gpr r = σ.gpr r) ∧ s'.rd = σ.rd ∧
        s'.wr = σ.wr))
    fun s₁ s₂ h => by
      obtain ⟨o₁, o₂, b₁, b₂⟩ := hQ _ _ h
      exact ⟨WP.mono (aadBlk_ok o₁.env o₁.sl b₁.lt) fun _ q => ⟨o₁, b₁, q⟩,
        WP.mono (aadBlk_ok o₂.env o₂.sl b₂.lt) fun _ q => ⟨o₂, b₂, q⟩⟩
  refine RelCT.seq r₁ (RelCT.ite (fun s₁ s₂ h => eval_e_eq h.1.2) (RelCT.block_nil fun _ _ _ => trivial) ?_)
  -- The associated data is not empty.
  have hA : ∀ s₁ s₂, ((s₁.cf = s₂.cf ∧ s₁.zf = s₂.zf) ∧ ∃ σ₁ σ₂, Q σ₁ σ₂ ∧
      (One K W SP R N A D nl al n tl σ₁ ∧ Buf K W SP σ₁ A al ∧ (s₁.mem = σ₁.mem ∧ s₁.gpr .r12 = A ∧
        s₁.gpr .rbp = BitVec.ofNat 64 al ∧ s₁.zf = some (decide (al = 0)) ∧
        (∀ r ∈ [Reg.r13, .r15, .rsp], s₁.gpr r = σ₁.gpr r) ∧ s₁.rd = σ₁.rd ∧ s₁.wr = σ₁.wr)) ∧
      (One K W SP R N A D nl al n tl σ₂ ∧ Buf K W SP σ₂ A al ∧ (s₂.mem = σ₂.mem ∧ s₂.gpr .r12 = A ∧
        s₂.gpr .rbp = BitVec.ofNat 64 al ∧ s₂.zf = some (decide (al = 0)) ∧
        (∀ r ∈ [Reg.r13, .r15, .rsp], s₂.gpr r = σ₂.gpr r) ∧ s₂.rd = σ₂.rd ∧ s₂.wr = σ₂.wr))) ∧
      isa.eval .e s₁ = some false →
      (One K W SP R N A D nl al n tl s₁ ∧ AbsPre K W SP A al s₁) ∧
      (One K W SP R N A D nl al n tl s₂ ∧ AbsPre K W SP A al s₂) ∧ 0 < al :=
    fun s₁ s₂ ⟨⟨_, σ₁, σ₂, _, ⟨o₁, b₁, m₁, h₁, p₁, z₁, g₁, rd₁, wr₁⟩, ⟨o₂, b₂, m₂, h₂, p₂, _, g₂, rd₂, wr₂⟩⟩, he⟩ => by
      refine ⟨⟨⟨o₁.env.keep g₁ rd₁ wr₁, m₁ ▸ o₁.sl, wr₁.trans o₁.wr⟩, ⟨b₁.of_eq rd₁ wr₁, h₁, p₁⟩⟩,
        ⟨⟨o₂.env.keep g₂ rd₂ wr₂, m₂ ▸ o₂.sl, wr₂.trans o₂.wr⟩, ⟨b₂.of_eq rd₂ wr₂, h₂, p₂⟩⟩, ?_⟩
      rcases Nat.eq_zero_or_pos al with h0 | h0
      · rw [show isa.eval .e s₁ = s₁.zf from rfl, z₁, h0] at he; cases he
      · exact h0
  rcases Nat.eq_zero_or_pos al with h0 | h0
  · exact RelCT.of_false fun s₁ s₂ h => by have := (hA s₁ s₂ h).2.2; omega_arith
  have hl : headLen al ≤ al := by unfold headLen; have := Proof.AesCcm.hdrLen_le al; omega_arith
  have r₂ := (aadHead_rel v L hR hDW hn hy h0 (P := A) (A := A) (N := N) (nl := nl) (tl := tl)
    fun s₁ s₂ h => by obtain ⟨⟨o₁, a₁⟩, ⟨o₂, a₂⟩, -⟩ := hA s₁ s₂ h; exact ⟨o₁, o₂, a₁, a₂⟩).wpDep
    (F := fun (σ s' : State) => One K W SP R N A D nl al n tl σ ∧ AbsPre K W SP A al σ ∧
      ∃ Y, @Absorbed _ K W SP σ y (A + BitVec.ofNat 64 (headLen al)) (al - headLen al) Y s')
    fun s₁ s₂ h => by
      obtain ⟨⟨o₁, a₁⟩, ⟨o₂, a₂⟩, -⟩ := hA s₁ s₂ h
      exact ⟨WP.mono (aadHead_ok v L o₁.env hR o₁.sl.rounds hy a₁.buf h0 a₁.r12 a₁.rbp) fun _ q => ⟨o₁, a₁, _, q⟩,
        WP.mono (aadHead_ok v L o₂.env hR o₂.sl.rounds hy a₂.buf h0 a₂.r12 a₂.rbp) fun _ q => ⟨o₂, a₂, _, q⟩⟩
  refine RelCT.seq r₂ (absorbPad_rel v L hR hDW hn hy (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    (P := A + BitVec.ofNat 64 (headLen al)) (len := al - headLen al)
    fun s₁ s₂ h => ?_)
  obtain ⟨-, σ₁, σ₂, -, ⟨o₁, a₁, _, A₁⟩, ⟨o₂, a₂, _, A₂⟩⟩ := h
  exact ⟨o₁.macR L hDW hy16 A₁.env A₁.frame A₁.wr, o₂.macR L hDW hy16 A₂.env A₂.frame A₂.wr,
    ⟨(a₁.buf.drop hl).of_eq A₁.rd A₁.wr, A₁.r12, A₁.rbp⟩, ⟨(a₂.buf.drop hl).of_eq A₂.rd A₂.wr, A₂.r12, A₂.rbp⟩⟩

/-! ## `mac` and `tag` -/

theorem macBlk_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (S : Slots W R N A D nl al n tl s.mem) :
    WP isa (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))]) s fun s₃ =>
      s₃.mem = s.mem ∧ s₃.gpr .r12 = D ∧ s₃.gpr .rbp = BitVec.ofNat 64 n ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → s₃.gpr r = s.gpr r) ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have hd := S.data
  have hl := S.len
  refine WP.of_runBlock ⟨_, by crun [h15, r₁, r₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [gpr_setReg, hd]
  · simp [gpr_setReg, hl]
  · intro r a b; simp [gpr_setReg, a, b]
  all_goals rfl

theorem macBlk_check : ∃ hc, (taint.check (ccmT [])
    (.block [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO))]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- The MAC, in two runs. -/
theorem mac_rel (v : UpdateImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hal : al < 2 ^ 64)
    (hn' : n < 256 ^ (15 - nl)) {y : Nat} (hy : y = 0 ∨ y = 96) {Q : State → State → Prop}
    (hQ : ∀ s₁ s₂, Q s₁ s₂ → (One K W SP R N A D nl al n tl s₁ ∧ C0 W nl s₁ ∧ Buf K W SP s₁ A al ∧
      Buf K W SP s₁ D n) ∧ (One K W SP R N A D nl al n tl s₂ ∧ C0 W nl s₂ ∧ Buf K W SP s₂ A al ∧ Buf K W SP s₂ D n)) :
    RelCT isa Q (mac v.callee y) fun _ _ => True := by
  have hy16 : y + 16 ≤ 112 := by omega_arith
  have r₁ := (b0_rel v L hR hDW hn h7 h13 ht4 ht16 hte hal hn' hy (P := Q) fun s₁ s₂ h => by
    obtain ⟨⟨o₁, c₁, -⟩, ⟨o₂, c₂, -⟩⟩ := hQ _ _ h
    exact ⟨Both.of o₁ o₂ (fun _ h => nomatch h), c₁, c₂⟩).wpDep
    (F := fun (σ s' : State) => One K W SP R N A D nl al n tl σ ∧ Buf K W SP σ A al ∧ Buf K W SP σ D n ∧
      (Env K W SP s' ∧ Frame (macR W SP y) σ.mem s'.mem ∧ s'.rd = σ.rd ∧ s'.wr = σ.wr))
    fun s₁ s₂ h => by
      obtain ⟨⟨o₁, ⟨_, l₁, c₁⟩, a₁, d₁⟩, ⟨o₂, ⟨_, l₂, c₂⟩, a₂, d₂⟩⟩ := hQ _ _ h
      exact ⟨WP.mono (b0_ok v L o₁.env o₁.sl hR l₁ h7 h13 ht4 ht16 hte hal hn' c₁ hy) fun _ q =>
          ⟨o₁, a₁, d₁, q.1, q.2.1, q.2.2.2.1, q.2.2.2.2⟩,
        WP.mono (b0_ok v L o₂.env o₂.sl hR l₂ h7 h13 ht4 ht16 hte hal hn' c₂ hy) fun _ q =>
          ⟨o₂, a₂, d₂, q.1, q.2.1, q.2.2.2.1, q.2.2.2.2⟩⟩
  have hB : ∀ s₁ s₂, (True ∧ ∃ σ₁ σ₂, Q σ₁ σ₂ ∧
      (One K W SP R N A D nl al n tl σ₁ ∧ Buf K W SP σ₁ A al ∧ Buf K W SP σ₁ D n ∧
        (Env K W SP s₁ ∧ Frame (macR W SP y) σ₁.mem s₁.mem ∧ s₁.rd = σ₁.rd ∧ s₁.wr = σ₁.wr)) ∧
      (One K W SP R N A D nl al n tl σ₂ ∧ Buf K W SP σ₂ A al ∧ Buf K W SP σ₂ D n ∧
        (Env K W SP s₂ ∧ Frame (macR W SP y) σ₂.mem s₂.mem ∧ s₂.rd = σ₂.rd ∧ s₂.wr = σ₂.wr))) →
      (One K W SP R N A D nl al n tl s₁ ∧ Buf K W SP s₁ A al ∧ Buf K W SP s₁ D n) ∧
      (One K W SP R N A D nl al n tl s₂ ∧ Buf K W SP s₂ A al ∧ Buf K W SP s₂ D n) :=
    fun s₁ s₂ ⟨_, σ₁, σ₂, _, ⟨o₁, a₁, d₁, E₁, f₁, rd₁, wr₁⟩, ⟨o₂, a₂, d₂, E₂, f₂, rd₂, wr₂⟩⟩ =>
      ⟨⟨o₁.macR L hDW hy16 E₁ f₁ wr₁, a₁.of_eq rd₁ wr₁, d₁.of_eq rd₁ wr₁⟩,
        ⟨o₂.macR L hDW hy16 E₂ f₂ wr₂, a₂.of_eq rd₂ wr₂, d₂.of_eq rd₂ wr₂⟩⟩
  have r₂ := (aad_rel v L hR hDW hn hy (A := A) (N := N) (nl := nl) (tl := tl) fun s₁ s₂ h => by
    obtain ⟨⟨o₁, a₁, -⟩, ⟨o₂, a₂, -⟩⟩ := hB s₁ s₂ h; exact ⟨o₁, o₂, a₁, a₂⟩).wpDep
    (F := fun (σ s' : State) => One K W SP R N A D nl al n tl σ ∧ Buf K W SP σ D n ∧
      ∃ Y, @MacStep _ K W SP σ y Y s')
    fun s₁ s₂ h => by
      obtain ⟨⟨o₁, a₁, d₁⟩, ⟨o₂, a₂, d₂⟩⟩ := hB s₁ s₂ h
      exact ⟨WP.mono (aad_ok v L o₁.env o₁.sl hR hy a₁) fun _ q => ⟨o₁, d₁, _, q⟩,
        WP.mono (aad_ok v L o₂.env o₂.sl hR hy a₂) fun _ q => ⟨o₂, d₂, _, q⟩⟩
  have hC : ∀ (PP : State → State → Prop) s₁ s₂, (True ∧ ∃ σ₁ σ₂, PP σ₁ σ₂ ∧
      (One K W SP R N A D nl al n tl σ₁ ∧ Buf K W SP σ₁ D n ∧ ∃ Y, @MacStep _ K W SP σ₁ y Y s₁) ∧
      (One K W SP R N A D nl al n tl σ₂ ∧ Buf K W SP σ₂ D n ∧ ∃ Y, @MacStep _ K W SP σ₂ y Y s₂)) →
      (One K W SP R N A D nl al n tl s₁ ∧ Buf K W SP s₁ D n) ∧ (One K W SP R N A D nl al n tl s₂ ∧ Buf K W SP s₂ D n) :=
    fun _ s₁ s₂ ⟨_, σ₁, σ₂, _, ⟨o₁, d₁, _, M₁⟩, ⟨o₂, d₂, _, M₂⟩⟩ =>
      ⟨⟨o₁.macR L hDW hy16 M₁.env M₁.frame M₁.wr, d₁.of_eq M₁.rd M₁.wr⟩,
        ⟨o₂.macR L hDW hy16 M₂.env M₂.frame M₂.wr, d₂.of_eq M₂.rd M₂.wr⟩⟩
  refine RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq ((rel_taintC (K := K) (SP := SP) (R := R) (N := N) (A := A)
      (nl := nl) (al := al) (tl := tl) [] hDW hn ?hb macBlk_check).wpDep
    (F := fun (σ s' : State) => One K W SP R N A D nl al n tl σ ∧ Buf K W SP σ D n ∧
      (s'.mem = σ.mem ∧ s'.gpr .r12 = D ∧ s'.gpr .rbp = BitVec.ofNat 64 n ∧
        (∀ r, r ≠ .r12 → r ≠ .rbp → s'.gpr r = σ.gpr r) ∧ s'.rd = σ.rd ∧ s'.wr = σ.wr)) ?hw)
    (absorbPad_rel v L hR hDW hn hy (N := N) (A := A) (nl := nl) (al := al) (tl := tl) (P := D) (len := n) ?hq)))
  case hb =>
    intro s₁ s₂ h
    obtain ⟨⟨o₁, -⟩, ⟨o₂, -⟩⟩ := hC _ s₁ s₂ h; exact Both.of o₁ o₂ fun _ h => nomatch h
  case hw =>
    intro s₁ s₂ h
    obtain ⟨⟨o₁, d₁⟩, ⟨o₂, d₂⟩⟩ := hC _ s₁ s₂ h
    exact ⟨WP.mono (macBlk_ok o₁.env o₁.sl) fun _ q => ⟨o₁, d₁, q⟩,
      WP.mono (macBlk_ok o₂.env o₂.sl) fun _ q => ⟨o₂, d₂, q⟩⟩
  intro s₁ s₂ h
  obtain ⟨_, σ₁, σ₂, _, ⟨o₁, d₁, m₁, h12₁, hbp₁, g₁, rd₁, wr₁⟩, ⟨o₂, d₂, m₂, h12₂, hbp₂, g₂, rd₂, wr₂⟩⟩ := h
  have keep : ∀ {σ s' : State}, One K W SP R N A D nl al n tl σ → s'.mem = σ.mem →
      (∀ r, r ≠ .r12 → r ≠ .rbp → s'.gpr r = σ.gpr r) → s'.rd = σ.rd → s'.wr = σ.wr →
      One K W SP R N A D nl al n tl s' := fun o m g rd wr =>
    ⟨o.env.keep (fun r hr => g r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
      rd wr, m ▸ o.sl, wr.trans o.wr⟩
  exact ⟨keep o₁ m₁ g₁ rd₁ wr₁, keep o₂ m₂ g₂ rd₂ wr₂, ⟨d₁.of_eq rd₁ wr₁, h12₁, hbp₁⟩, ⟨d₂.of_eq rd₂ wr₂, h12₂, hbp₂⟩⟩

theorem tagArgs_check {y : Nat} (hy : y = 0 ∨ y = 96) : ∃ hc, (taint.check (ccmT [])
    (.block (([.mov .rsi (.mem (at_ .r15 roundsO)), .mov32 .rax (imm 0)] : List Instr) ++ ctrAt ++ ([.mov .rdi (.reg .r13)] : List Instr) ++
      ptr .rdx .r15 c1O ++ ptr .rcx .r15 y ++ ([.mov32 .r8 (imm 1)] : List Instr) ++ ptr .r9 .r15 scrO)) hc).isSome = true := by
  rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- The tag, in two runs. -/
theorem tag_rel (v : Ctr32Impl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hn : n ≤ 2 ^ 64)
    (h7 : 7 ≤ nl) (h13 : nl ≤ 13) {y : Nat} (hy : y = 0 ∨ y = 96) {Q : State → State → Prop}
    (hQ : ∀ s₁ s₂, Q s₁ s₂ → (One K W SP R N A D nl al n tl s₁ ∧ C0 W nl s₁) ∧
      (One K W SP R N A D nl al n tl s₂ ∧ C0 W nl s₂)) :
    RelCT isa Q (tag v.callee y) fun _ _ => True := by
  have a := (rel_taintC [] hDW hn (fun s₁ s₂ h => by
    obtain ⟨⟨o₁, -⟩, ⟨o₂, -⟩⟩ := hQ _ _ h; exact Both.of o₁ o₂ fun _ h => nomatch h) (tagArgs_check hy)).wp
    (F₁ := fun (s : State) => CtrCall s K (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 y) (W + BitVec.ofNat 64 384) R 1 ∧
      s.gpr .rsp = SP)
    (F₂ := fun (s : State) => CtrCall s K (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 y) (W + BitVec.ofNat 64 384) R 1 ∧
      s.gpr .rsp = SP)
    fun s₁ s₂ h => by
      obtain ⟨⟨o₁, _, l₁, c₁⟩, ⟨o₂, _, l₂, c₂⟩⟩ := hQ _ _ h
      exact ⟨WP.mono (tagArgs_ok L o₁.env hR o₁.sl.rounds (by omega_arith) (by omega_arith) c₁ hy) fun _ q => ⟨q.2.1, q.1.rsp⟩,
        WP.mono (tagArgs_ok L o₂.env hR o₂.sl.rounds (by omega_arith) (by omega_arith) c₂ hy) fun _ q => ⟨q.2.1, q.1.rsp⟩⟩
  exact RelCT.seq a (ctr_rel v fun s₁ s₂ h => ⟨_, _, _, _, _, _, h.2.1.1, h.2.2.1, by rw [h.2.1.2, h.2.2.2]⟩)

end VG.Proof.AesCcm.X86_64

end

end

/-!
# AES-CCM on x86-64: `vg_aes_ccm_seal` is constant time

Untrusted: everything here is checked by Lean. Between the pieces, each run
has the public arguments, some `Ctr₀`, its buffers and the address of `tag`
on the stack (`Mid`), which every piece keeps (`ctrs_mid`, `mac_mid`,
`tag_mid`, `ctr_mid`); the pieces are related from it (`mac_rel`, `tag_rel`,
`crypt_rel`), and the entry, which loads `W` from the stack first, by the
taint analysis from the public arguments (`entry_rel`).

The taint analysis knows `W` as the second writable region, as it is for
`open`; `seal` may write `tag` too, before `W`, but its pieces before the copy
of the tag do not, and run the same from its states with `tag` only readable
(`rel_narrow`). The copy of the tag and the exit are related by the taint
analysis from the registers that correctness says agree (`sealTail_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr copyLoop copyTag)
open VG.Proof.AesGcm.X86_64 (LoopPre copyLoop_ok)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

/-- Code the taint analysis checks from the registers `rs`, public. -/
theorem rel_taintR {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s₁ s₂ h => Taint.agree_ofRegs (hag _ _ h)) hc

/-- Runs related from each pair of states. -/
theorem rel_of_pt {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, P σ₁ σ₂ → RelCT isa (fun t₁ t₂ => t₁ = σ₁ ∧ t₂ = σ₂) c Q) : RelCT isa P c Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

/-- The address of `tag`, `T`, at `SP + 24`, apart from what the pieces
write. -/
structure ArgT (W SP D : Addr) (n : Nat) (T : Addr) (s : State) : Prop where
  val : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T
  rd : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8
  w : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨W, 2560⟩
  d : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨D, n⟩

theorem ArgT.mut {W SP D T : Addr} {n : Nat} {s s' : State} (h : ArgT W SP D n T s)
    (hf : Frame (mutR W SP D n) s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : ArgT W SP D n T s' :=
  ⟨by rw [argT_kept (hf.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩) h.w h.d, h.val],
    by rw [hrd, hwr]; exact h.rd, h.w, h.d⟩

/-- A run between the pieces: the public arguments, some `Ctr₀` at `W + 48`,
the associated data and the data in its regions, and the address of the
tag. -/
def Mid (K W SP : Addr) (R : Nat) (N A D : Addr) (nl al n tl : Nat) (T : Addr) (s : State) : Prop :=
  One K W SP R N A D nl al n tl s ∧ C0 W nl s ∧ Buf K W SP s A al ∧ Buf K W SP s D n ∧ ArgT W SP D n T s

theorem ctrs_mid {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr} {nl al n tl : Nat} {s : State}
    (o : One K W SP R N A D nl al n tl s) (hN : Buf K W SP s N nl) (hA : Buf K W SP s A al)
    (hD : Buf K W SP s D n) (hT : ArgT W SP D n T s) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) :
    WP isa ctrs s (Mid K W SP R N A D nl al n tl T) :=
  WP.mono (ctrs_ok o.env o.sl hN h7 h13) fun _ ⟨E, f, c, rd, wr⟩ =>
    have f' : Frame (mutR W SP D n) s.mem _ := (f.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩).sub
      (wR_mut W SP D n)
    ⟨⟨E, slots_mut L hD.w f' o.sl, wr.trans o.wr⟩, ⟨_, length_bytesAt _ _ _, c⟩, hA.of_eq rd wr, hD.of_eq rd wr,
      hT.mut f' rd wr⟩

theorem mac_mid (v : UpdateImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16)
    (hte : tl % 2 = 0) (hn' : n < 256 ^ (15 - nl)) {y : Nat} (hy : y = 0 ∨ y = 96) {s : State}
    (h : Mid K W SP R N A D nl al n tl T s) : WP isa (mac v.callee y) s (Mid K W SP R N A D nl al n tl T) := by
  obtain ⟨o, ⟨nonce, hl, c⟩, hA, hD, hT⟩ := h
  refine WP.mono (mac_ok v L o.env o.sl hR hl h7 h13 ht4 ht16 hte hn' c hy hA hD) fun s' M => ?_
  refine ⟨o.macR L hD.w (by omega_using [hy]) M.env M.frame M.wr, ⟨nonce, hl, ?_⟩, hA.of_eq M.rd M.wr, hD.of_eq M.rd M.wr,
    hT.mut (M.frame.sub (macR_mut W SP D n (by omega_using [hy]))) M.rd M.wr⟩
  rw [bytesAt_frame M.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rcases hy with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm) (by decide), c]

theorem tag_mid (v : Ctr32Impl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) {y : Nat} (hy : y = 0 ∨ y = 96) {s : State}
    (h : Mid K W SP R N A D nl al n tl T s) : WP isa (tag v.callee y) s (Mid K W SP R N A D nl al n tl T) := by
  obtain ⟨o, ⟨nonce, hl, c⟩, hA, hD, hT⟩ := h
  refine WP.mono (tag_ok v L o.env hR o.sl.rounds (by omega_using [h7, hl]) (by omega_using [h13, hl]) c hy) fun s' ⟨E, _, rd, wr, f, _⟩ => ?_
  have f' : Frame (mutR W SP D n) s.mem s'.mem := f.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
    · exact ⟨wA W, by simp, Offset.sub_base W (by omega_using [hy])⟩
    · exact ⟨wC W, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  refine ⟨⟨E, slots_mut L hD.w f' o.sl, wr.trans o.wr⟩, ⟨nonce, hl, ?_⟩, hA.of_eq rd wr,
    hD.of_eq rd wr, hT.mut f' rd wr⟩
  rw [bytesAt_frame f (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · rcases hy with rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm) (by decide), c]

/-- The context of counter mode, from a run between the pieces. -/
theorem Mid.ctx {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (hn' : n < 256 ^ (15 - nl))
    (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩) {s : State} (h : Mid K W SP R N A D nl al n tl T s) :
    ∃ nonce, CtrCtx K W SP s R nonce D n := by
  obtain ⟨o, ⟨nonce, hl, c⟩, -, hD, -⟩ := h
  exact ⟨nonce, L, hR, o.sl.rounds, by omega_using [h7, hl], by omega_using [h13, hl], by rw [hl]; exact hn', c, hD,
    by rw [o.wr]; exact covers_of_mem List.mem_cons_self, hdk⟩

theorem ctr_mid (v : Ctr32Impl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr} {nl al n tl : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (hn' : n < 256 ^ (15 - nl))
    (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩) {s : State} (h : Mid K W SP R N A D nl al n tl T s) :
    WP isa (ctr v.callee) s (Mid K W SP R N A D nl al n tl T) := by
  obtain ⟨nonce, C⟩ := h.ctx L hR h7 h13 hn' hdk
  obtain ⟨o, ⟨nonce', hl, c⟩, hA, hD, hT⟩ := h
  refine WP.mono (ctr_ok v C o.env o.sl) fun s' ⟨E, rd, wr, f, _⟩ => ?_
  refine ⟨⟨E, slots_mut L hD.w (f.sub (ctrR_mut W SP D n)) o.sl, wr.trans o.wr⟩, ⟨nonce', hl, ?_⟩,
    hA.of_eq rd wr, hD.of_eq rd wr, hT.mut (f.sub (ctrR_mut W SP D n)) rd wr⟩
  rw [bytesAt_frame f (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
    · exact (hD.w.sub_right (Lay.wSub (by decide))).symm) (by decide), c]

/-- A run after the entry: the public arguments, its buffers and the address
of the tag. -/
def Pre₀ (K W SP : Addr) (R : Nat) (N A D : Addr) (nl al n tl : Nat) (T : Addr) (s : State) : Prop :=
  One K W SP R N A D nl al n tl s ∧ Buf K W SP s N nl ∧ Buf K W SP s A al ∧ Buf K W SP s D n ∧
    ArgT W SP D n T s

theorem ctrs_check : ∃ hc, (taint.check (ccmT []) ctrs hc).isSome = true := ⟨_, by taint_decide⟩

/-- `seal` after its entry, up to the copy of the tag, in two runs. -/
theorem sealFront_rel (v : UpdateImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr}
    {nl al n tl : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hn : n ≤ 2 ^ 64) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0)
    (hal : al < 2 ^ 64) (hn' : n < 256 ^ (15 - nl)) (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩)
    {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → Pre₀ K W SP R N A D nl al n tl T s₁ ∧ Pre₀ K W SP R N A D nl al n tl T s₂) :
    RelCT isa P (sealFront v.callee v.ctr.callee) fun s₁ s₂ =>
      True ∧ Mid K W SP R N A D nl al n tl T s₁ ∧ Mid K W SP R N A D nl al n tl T s₂ := by
  have r₁ := (rel_taintC [] hDW hn (fun s₁ s₂ h => by
      obtain ⟨⟨o₁, -⟩, ⟨o₂, -⟩⟩ := hP _ _ h; exact Both.of o₁ o₂ fun _ h => nomatch h) ctrs_check).wp
    (F₁ := Mid K W SP R N A D nl al n tl T) (F₂ := Mid K W SP R N A D nl al n tl T) fun s₁ s₂ h => by
      obtain ⟨⟨o₁, n₁, a₁, d₁, t₁⟩, ⟨o₂, n₂, a₂, d₂, t₂⟩⟩ := hP _ _ h
      exact ⟨ctrs_mid L o₁ n₁ a₁ d₁ t₁ h7 h13, ctrs_mid L o₂ n₂ a₂ d₂ t₂ h7 h13⟩
  have r₂ := (mac_rel v L hR hDW hn h7 h13 ht4 ht16 hte hal hn' (y := 0) (.inl rfl)
    (Q := fun s₁ s₂ => True ∧ Mid K W SP R N A D nl al n tl T s₁ ∧ Mid K W SP R N A D nl al n tl T s₂)
    fun _ _ h => ⟨⟨h.2.1.1, h.2.1.2.1, h.2.1.2.2.1, h.2.1.2.2.2.1⟩,
      ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩⟩).wp
    (F₁ := Mid K W SP R N A D nl al n tl T) (F₂ := Mid K W SP R N A D nl al n tl T)
    fun _ _ h => ⟨mac_mid v L hR h7 h13 ht4 ht16 hte hn' (.inl rfl) h.2.1,
      mac_mid v L hR h7 h13 ht4 ht16 hte hn' (.inl rfl) h.2.2⟩
  have r₃ := (tag_rel v.ctr L hR hDW hn h7 h13 (y := 0) (.inl rfl)
    (Q := fun s₁ s₂ => True ∧ Mid K W SP R N A D nl al n tl T s₁ ∧ Mid K W SP R N A D nl al n tl T s₂)
    fun _ _ h => ⟨⟨h.2.1.1, h.2.1.2.1⟩, ⟨h.2.2.1, h.2.2.2.1⟩⟩).wp
    (F₁ := Mid K W SP R N A D nl al n tl T) (F₂ := Mid K W SP R N A D nl al n tl T)
    fun _ _ h => ⟨tag_mid v.ctr L hR h7 h13 (.inl rfl) h.2.1, tag_mid v.ctr L hR h7 h13 (.inl rfl) h.2.2⟩
  have r₄ := (rel_of_pt (c := ctr v.ctr.callee)
    (P := fun s₁ s₂ => True ∧ Mid K W SP R N A D nl al n tl T s₁ ∧ Mid K W SP R N A D nl al n tl T s₂)
    fun σ₁ σ₂ h => by
      obtain ⟨_, C₁⟩ := h.2.1.ctx L hR h7 h13 hn' hdk
      obtain ⟨_, C₂⟩ := h.2.2.ctx L hR h7 h13 hn' hdk
      exact crypt_rel v.ctr C₁ C₂ h.2.1.1 h.2.2.1).wp
    (F₁ := Mid K W SP R N A D nl al n tl T) (F₂ := Mid K W SP R N A D nl al n tl T)
    fun _ _ h => ⟨ctr_mid v.ctr L hR h7 h13 hn' hdk h.2.1, ctr_mid v.ctr L hR h7 h13 hn' hdk h.2.2⟩
  exact RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ (r₄.mono (fun _ _ h => h) fun _ _ h => ⟨trivial, h.2⟩)))

/-- `seal` after its entry, up to the copy of the tag, in one run. -/
theorem sealFront_mid (v : UpdateImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr}
    {nl al n tl : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl)
    (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hn' : n < 256 ^ (15 - nl)) (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩)
    {s : State} (h : Pre₀ K W SP R N A D nl al n tl T s) :
    WP isa (sealFront v.callee v.ctr.callee) s (Mid K W SP R N A D nl al n tl T) := by
  obtain ⟨o, hN, hA, hD, hT⟩ := h
  exact WP.seq (WP.mono (ctrs_mid L o hN hA hD hT h7 h13) fun _ h₁ =>
    WP.seq (WP.mono (mac_mid v L hR h7 h13 ht4 ht16 hte hn' (.inl rfl) h₁) fun _ h₂ =>
    WP.seq (WP.mono (tag_mid v.ctr L hR h7 h13 (.inl rfl) h₂) fun _ h₃ => ctr_mid v.ctr L hR h7 h13 hn' hdk h₃)))

/-! ## Moving the tag to the regions read only -/

/-- `s` with the tag `⟨T, tl⟩` read only, and the data and `W` its writable
regions. -/
abbrev narrowT (D : Addr) (n : Nat) (T : Addr) (tl : Nat) (W : Addr) (s : State) : State :=
  s.withRegions (s.rd ++ [⟨T, tl⟩]) [⟨D, n⟩, ⟨W, 2560⟩]

theorem covers_narrowT (rd : List Region) (d t w : Region) :
    Covers (rd ++ [d, t, w]) ((rd ++ [t]) ++ [d, w]) :=
  Covers.of_mem fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp [h]

/-! ## The copy of the tag and the exit -/

/-- What the copy of the tag needs of a run: `r15` and `rsp` hold `W` and
`SP`, the tag length is in its slot, and the address of the tag `T` on the
stack, all where the run may read them. -/
def SealOut (W SP T : Addr) (tl : Nat) (s : State) : Prop :=
  s.gpr .r15 = W ∧ s.gpr .rsp = SP ∧ s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 tl ∧
    InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 208) 8 ∧ s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T ∧
    InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8

theorem Mid.sealOut {K W SP : Addr} {R : Nat} {N A D T : Addr} {nl al n tl : Nat} {σ s : State}
    (h : Mid K W SP R N A D nl al n tl T σ) (hg : σ.gpr = s.gpr) (hm : σ.mem = s.mem)
    (hc : Covers (σ.rd ++ σ.wr) (s.rd ++ s.wr)) : SealOut W SP T tl s := by
  obtain ⟨o, -, -, -, hT⟩ := h
  refine ⟨by rw [← hg]; exact o.env.r15, by rw [← hg]; exact o.env.rsp, by rw [← hm]; exact o.sl.tl,
    hc _ _ (o.env.perm.wR (show 208 + 8 ≤ 2560 by decide)), by rw [← hm]; exact hT.val, hc _ _ hT.rd⟩

/-- The arguments of the copy of the tag. -/
theorem tagOutArgs_ok {W SP T : Addr} {tl : Nat} {s : State} (h : SealOut W SP T tl s) :
    WP isa (.block [.mov .rdi (.mem (at_ .rsp 24)), .mov .rsi (.reg .r15), .mov .rcx (.mem (at_ .r15 tlO))]) s
      fun s' => s'.gpr .rdi = T ∧ s'.gpr .rsi = W ∧ s'.gpr .rcx = BitVec.ofNat 64 tl ∧ s'.gpr .r15 = W := by
  obtain ⟨h15, hsp, htl, r₁, hT, r₂⟩ := h
  refine WP.of_runBlock ⟨_, by crun [h15, hsp, r₁, r₂], ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, hsp, hT]
  · simp [gpr_setReg, h15]
  · simp [gpr_setReg, htl]
  · simp [gpr_setReg, h15]

theorem tagOutArgs_check : ∃ hc, (taint.check (Taint.ofRegs [.r15, .rsp])
    (.block [.mov .rdi (.mem (at_ .rsp 24)), .mov .rsi (.reg .r15), .mov .rcx (.mem (at_ .r15 tlO))]) hc).isSome =
      true := ⟨_, by taint_decide⟩

theorem tagCopy_check : ∃ hc, (taint.check (Taint.ofRegs [.rdi, .rsi, .rcx, .r15])
    (.seq copyTag (.block restore)) hc).isSome = true := ⟨_, by taint_decide⟩

/-- `(a; b); c`, related as `a; (b; c)`. -/
theorem rel_assoc' {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq e₁ c₁ => cases e₁ with | seq a₁ b₁ =>
  cases e₂ with | seq e₂ c₂ => cases e₂ with | seq a₂ b₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
  simp only [List.append_assoc] at ht ⊢
  exact ⟨ht, hq⟩

/-- The copy of the tag and the exit, in two runs with the same `W`, `SP`,
tag length and tag. -/
theorem sealTail_rel {W SP T : Addr} {tl : Nat} {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → SealOut W SP T tl s₁ ∧ SealOut W SP T tl s₂) :
    RelCT isa P (.seq tagOut (.block restore)) fun _ _ => True := by
  have a := (rel_taintR (P := P) [.r15, .rsp] (fun s₁ s₂ h r hr => by
      obtain ⟨⟨a₁, b₁, -⟩, ⟨a₂, b₂, -⟩⟩ := hP _ _ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]) tagOutArgs_check).wp
    (F₁ := fun (s : State) => s.gpr .rdi = T ∧ s.gpr .rsi = W ∧ s.gpr .rcx = BitVec.ofNat 64 tl ∧ s.gpr .r15 = W)
    (F₂ := fun (s : State) => s.gpr .rdi = T ∧ s.gpr .rsi = W ∧ s.gpr .rcx = BitVec.ofNat 64 tl ∧ s.gpr .r15 = W)
    fun _ _ h => ⟨tagOutArgs_ok (hP _ _ h).1, tagOutArgs_ok (hP _ _ h).2⟩
  have b := rel_taintR (P := fun s₁ s₂ => True ∧
      (s₁.gpr .rdi = T ∧ s₁.gpr .rsi = W ∧ s₁.gpr .rcx = BitVec.ofNat 64 tl ∧ s₁.gpr .r15 = W) ∧
      (s₂.gpr .rdi = T ∧ s₂.gpr .rsi = W ∧ s₂.gpr .rcx = BitVec.ofNat 64 tl ∧ s₂.gpr .r15 = W))
    (c := .seq copyTag (.block restore)) [.rdi, .rsi, .rcx, .r15] (fun _ _ h r hr => by
      obtain ⟨-, ⟨a₁, b₁, c₁, d₁⟩, ⟨a₂, b₂, c₂, d₂⟩⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [c₁, c₂]
      · rw [d₁, d₂]) tagCopy_check
  exact rel_assoc' (RelCT.seq a b)

/-! ## The entry -/

theorem loadW_ok {s : State} (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 40) 8) :
    WP isa (.block [.mov .rax (.mem (at_ .rsp 40))]) s fun s' =>
      s'.gpr .rax = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 40) 64 ∧ ∀ r, r ≠ .rax → s'.gpr r = s.gpr r := by
  refine WP.of_runBlock ⟨_, by crun [hr], ?_, ?_⟩
  · simp only [gpr_setReg, ite_true]
  · intro r a; simp only [gpr_setReg, a, ite_false]

theorem entryW_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem (at_ .rsp 40))]) hc).isSome =
    true := ⟨_, by taint_decide⟩

theorem entryRest_check :
    ∃ hc, (taint.check (Taint.ofRegs [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) (.block entry.tail) hc).isSome =
      true := ⟨_, by taint_decide⟩

/-- The entry, in two runs with the same arguments in registers and the same
`W`. -/
theorem entry_rel {s₀ s₀' : State} {F₁ F₂ : State → Prop}
    (hag : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r)
    (hw : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 40) 64 = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 40) 64)
    (hr₁ : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsp + BitVec.ofNat 64 40) 8)
    (hr₂ : InRegions (s₀'.rd ++ s₀'.wr) (s₀'.gpr .rsp + BitVec.ofNat 64 40) 8)
    (hE₁ : WP isa (.block entry) s₀ F₁) (hE₂ : WP isa (.block entry) s₀' F₂) :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block entry) fun s₁ s₂ => True ∧ F₁ s₁ ∧ F₂ s₂ := by
  have l := (rel_taintR (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') [.rsp] (fun _ _ h r hr => by
      obtain ⟨rfl, rfl⟩ := h; simp only [List.mem_singleton] at hr; subst hr; exact hag _ (by simp))
      entryW_check).wp
    (F₁ := fun (s' : State) => s'.gpr .rax = s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 40) 64 ∧
      ∀ r, r ≠ .rax → s'.gpr r = s₀.gpr r)
    (F₂ := fun (s' : State) => s'.gpr .rax = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 40) 64 ∧
      ∀ r, r ≠ .rax → s'.gpr r = s₀'.gpr r)
    fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨loadW_ok hr₁, loadW_ok hr₂⟩
  have e : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block entry) fun _ _ => True :=
    RelCT.block_append (M := isa) (l₁ := [.mov .rax (.mem (at_ .rsp 40))]) (l₂ := entry.tail) (RelCT.seq l
      (rel_taintR (P := fun (s₁ s₂ : State) => True ∧
          (s₁.gpr .rax = s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 40) 64 ∧ ∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r) ∧
          (s₂.gpr .rax = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 40) 64 ∧ ∀ r, r ≠ .rax → s₂.gpr r = s₀'.gpr r))
        (.rax :: [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) (fun _ _ h r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · rw [h.2.1.1, h.2.2.1, hw]
        · have hx : r ≠ .rax := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
          rw [h.2.1.2 r hx, h.2.2.2 r hx, hag r hr]) entryRest_check))
  exact e.wp fun _ _ h => by rw [h.1, h.2]; exact ⟨hE₁, hE₂⟩

/-- What the entry leaves, for the arguments: the environment, the slots, the
same permissions, and the address of the tag still at `SP + 24`. -/
theorem entry_post {s : State} {K W SP N A D T : Addr} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D R nl al n tl) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa (.block entry) s fun s₁ => Env K W SP s₁ ∧ Slots W R N A D nl al n tl s₁.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr ∧ ArgT W SP D n T s₁ := by
  obtain ⟨s₁, run₁, E₁, S₁, _, f₁, rd₁, wr₁⟩ :=
    entry_ok Ar.perm hsp Ar.args Ar.argsW hD hn hW htl hdi hsi hdx hcx hr8 hr9
  have hTr : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8 := by
    have h := in_off (d := 16) (n := 8) Ar.args (by decide) (by decide)
    rw [add_ofNat_assoc] at h
    exact h
  refine WP.of_runBlock ⟨s₁, run₁, E₁, S₁, rd₁, wr₁, ⟨?_, by rw [rd₁, wr₁]; exact hTr, Ar.argsW, Ar.argsD⟩⟩
  rw [f₁.readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact argT_disj (n := n) Ar.argsW Ar.argsD _ List.mem_cons_self) (by decide), hT]

theorem argW_in {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat} (Ar : Args s K W SP N A D R nl al n tl)
    (hsp : s.gpr .rsp = SP) : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 40) 8 := by
  have h := in_off (d := 32) (n := 8) Ar.args (by decide) (by decide)
  rw [add_ofNat_assoc] at h
  rw [hsp]; exact h

theorem pub_regs {s₀ s₀' : State} (hq : onePub s₀ s₀') :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, -⟩ := hq
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [q1, q2, q3, q4, q5, q6, q7]

/-- What the entry of `seal` leaves: with the tag read only, a run after the
entry. -/
def SealIn (K W SP : Addr) (R : Nat) (N A D : Addr) (nl al n tl : Nat) (T : Addr) (s : State) : Prop :=
  s.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 2560⟩] ∧ Pre₀ K W SP R N A D nl al n tl T (narrowT D n T tl W s)

theorem sealIn_of {s s₁ : State} {K W SP N A D T : Addr} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D R nl al n tl) (hwr : s.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 2560⟩])
    (h : Env K W SP s₁ ∧ Slots W R N A D nl al n tl s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ ArgT W SP D n T s₁) :
    SealIn K W SP R N A D nl al n tl T s₁ := by
  obtain ⟨E, S, rd, wr, hT⟩ := h
  have hwr₁ : s₁.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 2560⟩] := by rw [wr]; exact hwr
  have hc : Covers (s₁.rd ++ s₁.wr) ((narrowT D n T tl W s₁).rd ++ (narrowT D n T tl W s₁).wr) := by
    rw [hwr₁]; exact covers_narrowT _ _ _ _
  have hb : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → Buf K W SP (narrowT D n T tl W s₁) P len := fun hP =>
    { hP.of_eq rd wr with rd := (hP.of_eq rd wr).rd.trans hc }
  exact ⟨hwr₁, ⟨⟨E.r13, E.r15, E.rsp, E.perm.k.trans hc, Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; simp⟩, S, rfl⟩, hb Ar.nonce, hb Ar.aad, hb Ar.data,
    ⟨hT.val, hc _ _ hT.rd, hT.w, hT.d⟩⟩

theorem entry_seal {s : State} (hp : sealX86_64.pre s) :
    WP isa (.block entry) s (SealIn (s.gpr .rdi) (arg s 4) (s.gpr .rsp) (s.gpr .rsi).toNat (s.gpr .rdx) (s.gpr .r8)
      (arg s 0) (s.gpr .rcx).toNat (s.gpr .r9).toNat (arg s 1).toNat (arg s 3).toNat (arg s 2)) :=
  WP.mono (entry_post (args_of_seal hp).1.1 rfl rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl rfl
      (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm)
    fun _ h => sealIn_of (args_of_seal hp).1.1 hp.2.1 h

/-- The second run, with the first's public arguments. -/
theorem entry_seal_pub {s₀ s₀' : State} (hp' : sealX86_64.pre s₀') (hq : onePub s₀ s₀') :
    WP isa (.block entry) s₀' (SealIn (s₀.gpr .rdi) (arg s₀ 4) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx)
      (s₀.gpr .r8) (arg s₀ 0) (s₀.gpr .rcx).toNat (s₀.gpr .r9).toNat (arg s₀ 1).toNat (arg s₀ 3).toNat
      (arg s₀ 2)) := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, qa⟩ := hq
  rw [qa 0 (by decide), qa 1 (by decide), qa 2 (by decide), qa 3 (by decide), qa 4 (by decide), q1, q2, q3, q4,
    q5, q6, q7]
  exact entry_seal hp'

/-- `vg_aes_ccm_seal`, in two runs with the same public arguments. -/
theorem seal_rel (v : UpdateImpl) {s₀ s₀' : State} (hp : sealX86_64.pre s₀) (hp' : sealX86_64.pre s₀')
    (hq : sealX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («seal» v.callee v.ctr.callee) fun _ _ => True := by
  have Ar := (args_of_seal hp).1.1
  have L := Ar.lay
  refine RelCT.seq (entry_rel (pub_regs hq) (hq.2.2.2.2.2.2.2 4 (by decide)) (argW_in Ar rfl)
    (argW_in (args_of_seal hp').1.1 rfl) (entry_seal hp) (entry_seal_pub hp' hq)) ?_
  have hn := Nat.le_of_lt Ar.data.lt
  have front := rel_narrow (c := sealFront v.callee v.ctr.callee)
    (P := fun s₁ s₂ => True ∧
      SealIn (s₀.gpr .rdi) (arg s₀ 4) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx) (s₀.gpr .r8) (arg s₀ 0)
        (s₀.gpr .rcx).toNat (s₀.gpr .r9).toNat (arg s₀ 1).toNat (arg s₀ 3).toNat (arg s₀ 2) s₁ ∧
      SealIn (s₀.gpr .rdi) (arg s₀ 4) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx) (s₀.gpr .r8) (arg s₀ 0)
        (s₀.gpr .rcx).toNat (s₀.gpr .r9).toNat (arg s₀ 1).toNat (arg s₀ 3).toNat (arg s₀ 2) s₂)
    [⟨arg s₀ 2, (arg s₀ 3).toNat⟩]
    [⟨arg s₀ 0, (arg s₀ 1).toNat⟩, ⟨arg s₀ 4, 2560⟩]
    (sealFront_rel v L Ar.rounds Ar.data.w hn Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.aad.lt Ar.hn Ar.dk
      fun _ _ h => by obtain ⟨_, _, hp, rfl, rfl⟩ := h; exact ⟨hp.2.1.2, hp.2.2.2⟩)
    fun s₁ s₂ h => by
      have hc : ∀ {s : State}, s.wr = [⟨arg s₀ 0, (arg s₀ 1).toNat⟩, ⟨arg s₀ 2, (arg s₀ 3).toNat⟩, ⟨arg s₀ 4, 2560⟩] →
          Covers ([⟨arg s₀ 2, (arg s₀ 3).toNat⟩] ++ [⟨arg s₀ 0, (arg s₀ 1).toNat⟩, ⟨arg s₀ 4, 2560⟩]) s.wr ∧
          Covers [⟨arg s₀ 0, (arg s₀ 1).toNat⟩, ⟨arg s₀ 4, 2560⟩] s.wr := fun hw => by
        rw [hw]
        refine ⟨Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_⟩ <;>
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢ <;>
          rcases hr with h | h | h <;> simp [h]
      obtain ⟨_, ⟨hw₁, p₁⟩, ⟨hw₂, p₂⟩⟩ := h
      obtain ⟨t₁, u₁, e₁, -⟩ := sealFront_mid v L Ar.rounds Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.hn Ar.dk p₁
      obtain ⟨t₂, u₂, e₂, -⟩ := sealFront_mid v L Ar.rounds Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.hn Ar.dk p₂
      exact ⟨⟨(hc hw₁).1, (hc hw₁).2, t₁, u₁, e₁⟩, ⟨(hc hw₂).1, (hc hw₂).2, t₂, u₂, e₂⟩⟩
  exact RelCT.seq front (sealTail_rel fun _ _ h => by
    obtain ⟨_, _, ⟨-, m₁, m₂⟩, ⟨g₁, h₁, c₁⟩, ⟨g₂, h₂, c₂⟩⟩ := h
    exact ⟨m₁.sealOut g₁ h₁ c₁, m₂.sealOut g₂ h₂ c₂⟩)

theorem seal_ct (v : UpdateImpl) : ConstantTime isa sealX86_64.pre sealX86_64.pub («seal» v.callee v.ctr.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (seal_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesCcm.X86_64

end

end

/-! ### `AesCcm.X86_64.Open`, which this module and modules that import it used -/

section

/-! ### `AesCcm.X86_64.Mask`, which only this module used -/

section

/-!
# AES-CCM on x86-64: masking the data (`mask`)

Untrusted: everything here is checked by Lean. `mask` ANDs every byte of the
data with `0 − ok`, for `ok` 1 or 0: the data stays if the tags were equal,
and is zeroed if not (`mask_ok`): its first block loads the data, its
length and the mask, and `maskTail` (`Proof/AesGcm/X86_64/Mask.lean`) masks
the data.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

variable [fp : Footprint]

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Proof.AesGcm.X86_64 (in_of_covers succ_ofNat MInv maskTail_wp ofNat_shr4)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)

omit fp in
theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, length_bytesAt]

omit fp in
/-- Every byte of the data ANDed with `0 − ok`. -/
theorem mask_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {R : Nat} {N A D : Addr} {nl al n tl : Nat}
    (S : Slots W R N A D nl al n tl s.mem) (hD : Buf K W SP s D n) (hDw : Covers [⟨D, n⟩] s.wr) {c : Bool}
    (hok : s.mem.readW (W + BitVec.ofNat 64 224) 64 = if c then 1 else 0) :
    WP isa mask s fun s' => Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = writeBytes s.mem D (if c then bytesAt s.mem D n else zeros n) := by
  have h15 := E.r15
  obtain r₁ := E.perm.wR (show 192 + 8 ≤ 2560 by decide)
  obtain r₂ := E.perm.wR (show 200 + 8 ≤ 2560 by decide)
  obtain r₃ := E.perm.wR (show 224 + 8 ≤ 2560 by decide)
  have hn := hD.lt
  have hd := S.data
  have hl := S.len
  obtain ⟨s₁, run₁, m₁, h12₁, hbp₁, h11₁, r10₁, rcx₁, zf₁, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .r12 (.mem (at_ .r15 dataO)), .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .r11 (imm 0),
        .alu .sub .r11 (.mem (at_ .r15 okO)), .mov32 .r10 (imm 0), .mov .rcx (.reg .rbp),
        .shift .shr .rcx 4, .alu .test .rcx (.reg .rcx)] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧
      s₁.gpr .r11 = 0 - (if c then 1 else 0) ∧ s₁.gpr .r10 = BitVec.ofNat 64 0 ∧
      s₁.gpr .rcx = BitVec.ofNat 64 (n / 16) ∧ s₁.zf = some (decide (n / 16 = 0)) ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp], s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [h15, r₁, r₂, r₃, execShift], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hd]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hl]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hok]; rfl
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, hl, ofNat_shr4 hn]
    · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false,
        reduceCtorEq, hl, ofNat_shr4 hn, and_self_beq (show n / 16 < 2 ^ 64 by omega_using [hn])]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  obtain E₁ : Env K W SP s₁ := E.keep g₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.mono (maskTail_wp hn (by rw [rd₁, wr₁]; exact hD.rd) (by rw [wr₁]; exact hDw) h12₁ h11₁ hbp₁ r10₁ rcx₁
    zf₁) fun t ht => ?_
  refine ⟨E₁.keep (fun r hr => ht.keep r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    ht.rd ht.wr, by rw [ht.rd, rd₁], by rw [ht.wr, wr₁], ?_⟩
  rw [ht.mem, m₁]
  rfl

end VG.Proof.AesCcm.X86_64

end

end


/-!
# AES-CCM on x86-64: `vg_aes_ccm_open`

Untrusted: everything here is checked by Lean. `open` is `entry`, `Ctr₀`,
counter mode over the data (which decrypts it), the encrypted MAC of the
plaintext at `W + 96`, then the comparison of its first `t` bytes with the
received tag at `T`, whose address is on the stack, the mask of the data and
`restore` (`openTail_ok`, `open_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

variable [fp : Footprint]

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm ptr recv cmp)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

omit fp in
/-- The tag length loaded into `rbx`, and the address of the received tag
`T` into `rsi`. -/
theorem loadTag_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {R : Nat} {N A D : Addr}
    {nl al n tl : Nat} (S : Slots W R N A D nl al n tl s.mem) {T : Addr}
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T) (hTr : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8) :
    ∃ s₁, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .rbx = BitVec.ofNat 64 tl ∧ s₁.gpr .rsi = T ∧
      (∀ r, r ≠ .rbx → r ≠ .rsi → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have h15 := E.r15
  have hsp := E.rsp
  obtain rt := E.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have htl := S.tl
  refine ⟨_, by crun [h15, hsp, rt, hTr], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [gpr_setReg, htl]
  · simp [gpr_setReg, hsp, hT]
  · intro r a b; simp [gpr_setReg, a, b]
  all_goals rfl

omit fp in
/-- The comparison of the encrypted MAC at `W + 96` with the received tag at
`T`, and `ok` stored at `W + 224`. -/
theorem openCmp_ok {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {R : Nat} {N A D : Addr}
    {nl al n tl : Nat} (S : Slots W R N A D nl al n tl s.mem) (ht1 : 1 ≤ tl) (ht16 : tl ≤ 16) {T : Addr}
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T) (hTr : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8)
    (hTc : Covers [⟨T, tl⟩] (s.rd ++ s.wr)) (hTW : (⟨T, tl⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))]) (.seq recv (.seq (cmp uO)
      (.block [.store (at_ .r15 okO) .rax])))) s fun s₄ =>
      Env K W SP s₄ ∧ s₄.rd = s.rd ∧ s₄.wr = s.wr ∧
      Frame [⟨W + BitVec.ofNat 64 224, 8⟩, ⟨W + BitVec.ofNat 64 240, 32⟩] s.mem s₄.mem ∧
      s₄.mem.readW (W + BitVec.ofNat 64 224) 64 =
        if bytesAt s.mem (W + BitVec.ofNat 64 96) tl = bytesAt s.mem T tl then 1 else 0 := by
  obtain ⟨s₁, run₁, hm₁, hbx₁, hsi₁, hg₁, hrd₁, hwr₁⟩ := loadTag_ok E S hT hTr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain E₁ : Env K W SP s₁ := E.keep (fun r hr => hg₁ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    hrd₁ hwr₁
  refine WP.seq (WP.mono (recv_ok E₁ hbx₁ ht1 ht16 hsi₁ (by rw [hrd₁, hwr₁]; exact hTc)
      (hTW.sub_right (Lay.wSub (by decide)))) fun s₂ ⟨E₂, hR₂, f₂, hbx₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (cmp_ok L (o := 96) (by decide) E₂ (by rw [hbx₂, hbx₁]) ht1 ht16 (length_bytesAt _ _ _) hR₂)
    fun s₃ ⟨E₃, hax₃, f₃, rd₃, wr₃⟩ => ?_)
  -- `ok` in `W + 224`.
  have h15₃ := E₃.r15
  obtain wo := E₃.perm.wW (show 224 + 8 ≤ 2560 by decide)
  obtain ⟨s₄, run₄, hm₄, hg₄, hrd₄, hwr₄⟩ : ∃ s₄, runBlock isa [.store (at_ .r15 okO) .rax] s₃ = some s₄ ∧
      s₄.mem = s₃.mem.writeW (W + BitVec.ofNat 64 224) (s₃.gpr .rax) ∧ s₄.gpr = s₃.gpr ∧ s₄.rd = s₃.rd ∧
      s₄.wr = s₃.wr := by
    refine ⟨_, by crun [h15₃, wo], ?_, ?_, ?_, ?_⟩ <;> rfl
  obtain E₄ : Env K W SP s₄ := E₃.keep (fun r _ => by rw [hg₄]) hrd₄ hwr₄
  obtain f₄ : Frame [⟨W + BitVec.ofNat 64 224, 8⟩] s₃.mem s₄.mem := by
    rw [hm₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain f₀₄w : Frame [⟨W + BitVec.ofNat 64 224, 8⟩, ⟨W + BitVec.ofNat 64 240, 32⟩] s.mem s₄.mem := by
    rw [← hm₁]
    refine ((f₂.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_)).trans (f₄.sub fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨⟨W + BitVec.ofNat 64 240, 32⟩, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 240, 32⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  obtain rd₀₄ : s₄.rd = s.rd := by rw [hrd₄, rd₃, rd₂, hrd₁]
  obtain wr₀₄ : s₄.wr = s.wr := by rw [hwr₄, wr₃, wr₂, hwr₁]
  obtain hV : bytesAt s₂.mem (W + BitVec.ofNat 64 96) tl = bytesAt s.mem (W + BitVec.ofNat 64 96) tl := by
    rw [bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide))
      (by omega_arith), hm₁]
  rw [hV, hm₁] at hax₃
  refine WP.of_runBlock ⟨s₄, run₄, E₄, rd₀₄, wr₀₄, f₀₄w, ?_⟩
  rw [hm₄, Mem.readW_writeW_self64, hax₃]

/-- From the encrypted MAC at `W + 96` on: the comparison, the mask and the
restore. -/
theorem openTail_ok {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {R : Nat} {N A D : Addr}
    {nl al n tl : Nat} (S : Slots W R N A D nl al n tl s.mem) (hD : Buf K W SP s D n) (hDw : Covers [⟨D, n⟩] s.wr)
    (ht1 : 1 ≤ tl) (ht16 : tl ≤ 16) {g : Reg → BitVec 64} (sv : Saved s.mem W g) {T : Addr}
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T) (hTr : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8)
    (hTc : Covers [⟨T, tl⟩] (s.rd ++ s.wr)) (hTW : (⟨T, tl⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))]) (.seq recv (.seq (cmp uO)
      (.seq (.block [.store (at_ .r15 okO) .rax]) (.seq mask (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++
        restore))))))) s fun s' =>
      (∀ p ∈ saved, s'.gpr p.1 = g p.1) ∧ s'.gpr .rsp = SP ∧
      s'.gpr .rax = (if bytesAt s.mem (W + BitVec.ofNat 64 96) tl = bytesAt s.mem T tl then 1 else 0) ∧
      bytesAt s'.mem D n =
        (if bytesAt s.mem (W + BitVec.ofNat 64 96) tl = bytesAt s.mem T tl then bytesAt s.mem D n else zeros n) ∧
      Frame [⟨W + BitVec.ofNat 64 224, 8⟩, ⟨W + BitVec.ofNat 64 240, 32⟩, ⟨D, n⟩] s.mem s'.mem := by
  refine seq_assoc4 (WP.seq (WP.mono (openCmp_ok L E S ht1 ht16 hT hTr hTc hTW)
    fun s₄ ⟨E₄, rd₀₄, wr₀₄, f₀₄w, hok'⟩ => ?_))
  obtain f₀₄ : Frame (mutR W SP D n) s.mem s₄.mem := f₀₄w.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨wK W, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨wC W, by simp, Offset.sub W (by decide) (by have := tailBytes_le; have := tailBytes_ge; have := scratchBytes_le; omega)⟩
  obtain S₄ := slots_mut L hD.w f₀₄ S
  obtain ⟨c, hc⟩ : ∃ c, c = decide (bytesAt s.mem (W + BitVec.ofNat 64 96) tl = bytesAt s.mem T tl) := ⟨_, rfl⟩
  obtain hok : s₄.mem.readW (W + BitVec.ofNat 64 224) 64 = if c then 1 else 0 := by
    rw [hok', hc]; simp only [decide_eq_true_eq]
  refine WP.seq (WP.mono (mask_ok E₄ S₄ (hD.of_eq rd₀₄ wr₀₄) (by rw [wr₀₄]; exact hDw) hok)
    fun s₅ ⟨E₅, rd₅, wr₅, hm₅⟩ => ?_)
  -- `ok` in `rax`, and the registers back.
  obtain f₅ : Frame [⟨D, n⟩] s₄.mem s₅.mem := by
    rw [hm₅]; exact writeBytes_frame' _ (length_mask _ _ _ _)
  obtain hok₅ : s₅.mem.readW (W + BitVec.ofNat 64 224) 64 = if c then 1 else 0 := by
    rw [f₅.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hD.w.sub_right (Lay.wSub (by decide))).symm)
      (by decide), hok]
  have h15₅ := E₅.r15
  obtain ro := E₅.perm.wR (show 224 + 8 ≤ 2560 by decide)
  obtain ⟨s₆, run₆, hm₆, hax₆, hg₆, hrd₆, hwr₆⟩ : ∃ s₆, runBlock isa [.mov .rax (.mem (at_ .r15 okO))] s₅ = some s₆ ∧
      s₆.mem = s₅.mem ∧ s₆.gpr .rax = (if c then 1 else 0) ∧ (∀ r, r ≠ .rax → s₆.gpr r = s₅.gpr r) ∧
      s₆.rd = s₅.rd ∧ s₆.wr = s₅.wr := by
    refine ⟨_, by crun [h15₅, ro], ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, ite_true, hok₅]
    · intro r h; simp only [gpr_setReg, h, ite_false]
    all_goals rfl
  obtain E₆ : Env K W SP s₆ := E₅.keep (fun r hr => hg₆ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) hrd₆ hwr₆
  obtain f₀₆ : Frame (mutR W SP D n) s.mem s₆.mem := by
    rw [hm₆]; exact f₀₄.trans (f₅.sub fun r hr => ⟨r, by simp at hr ⊢; simp [hr], fun _ h => h⟩)
  obtain ⟨s₇, run₇, hg₇, hm₇, hsp₇, hax₇⟩ := restore_ok E₆ (saved_mut L hD.w f₀₆ sv)
  refine WP.of_runBlock ⟨s₇, by rw [runBlock_append, run₆, Option.bind_some, run₇], hg₇,
    by rw [hsp₇, E₆.rsp], ?_, ?_, ?_⟩
  · rw [hax₇, hax₆, hc]; simp only [decide_eq_true_eq]
  · have hx : (if c then bytesAt s₄.mem D n else zeros n).length = n := length_mask _ _ _ _
    obtain e := bytesAt_writeBytes_at s₄.mem D (o := 0) (n := n) (if c then bytesAt s₄.mem D n else zeros n)
      (by rw [hx]; omega_arith) hD.lt
    rw [BitVec.add_zero, List.take_zero, List.nil_append, Nat.zero_add,
      List.drop_eq_nil_of_le (by rw [length_bytesAt, hx]), List.append_nil] at e
    obtain hd₄ : bytesAt s₄.mem D n = bytesAt s.mem D n := bytesAt_frame f₀₄w (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact hD.w.sub_right (Lay.wSub (by decide))) (by have := hD.lt; omega_arith)
    rw [hm₇, hm₆, hm₅, e, hc, hd₄]
    simp only [decide_eq_true_eq]
  · rw [hm₇, hm₆]
    exact (f₀₄w.sub fun r hr => ⟨r, by simp at hr ⊢; rcases hr with rfl | rfl <;> simp, fun _ h => h⟩).trans
      (f₅.sub fun r hr => ⟨r, by simp at hr ⊢; simp [hr], fun _ h => h⟩)

/-- `vg_aes_ccm_open`, for its arguments. -/
theorem open_wp'_frame (v : UpdateImpl) [UpdateFits v] {s : State} {K W SP N A D T : Addr} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D R nl al n tl) (Tb : TagBuf W SP D n T tl) (hTc : Covers [⟨T, tl⟩] (s.rd ++ s.wr))
    (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa («open» v.callee v.ctr.callee) s fun s' => (gprPreserved s s' ∧
      match Spec.Ccm.decryptWith (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl) (bytesAt s.mem D n)
          (bytesAt s.mem A al) (bytesAt s.mem T tl) with
      | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem D n = pt
      | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem D n = zeros n) ∧ EntryFrame s s' W SP D n T tl := by
  have L := Ar.lay
  obtain hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
  obtain ⟨s₁, run₁, E₁, S₁, sv₁, f₁, rd₁, wr₁⟩ :=
    entry_ok Ar.perm hsp Ar.args Ar.argsW hD hn hW htl hdi hsi hdx hcx hr8 hr9
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain hent : ∀ {P : Addr} {len : Nat}, Buf K W SP s P len → bytesAt s₁.mem P len = bytesAt s.mem P len :=
    fun hP => bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega_arith)
  obtain hK₁ : Spec.Ccm.ctxCiph s₁.mem K R = Spec.Ccm.ctxCiph s.mem K R :=
    ctxCiph_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb
  refine WP.seq ?_
  -- `Ctr₀`.
  refine WP.seq (WP.mono (ctrs_ok E₁ S₁ (Ar.nonce.of_eq rd₁ wr₁) Ar.h7 Ar.h13) fun s₂ ⟨E₂, f₂, c₂, rd₂, wr₂⟩ => ?_)
  rw [hent Ar.nonce] at c₂
  obtain f₂' : Frame (wR W SP) s₁.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
  obtain S₂ := slots_mut L Ar.data.w (f₂'.sub (wR_mut W SP D n)) S₁
  -- Counter mode: the plaintext.
  obtain C₂ : CtrCtx K W SP s₂ R (bytesAt s.mem N nl) D n :=
    ⟨L, Ar.rounds, S₂.rounds, by rw [length_bytesAt]; exact Ar.h7, by rw [length_bytesAt]; exact Ar.h13,
      by rw [length_bytesAt]; exact Ar.hn, c₂, Ar.data.of_eq (rd₂.trans rd₁) (wr₂.trans wr₁),
      by rw [wr₂, wr₁]; exact Ar.dw, Ar.dk⟩
  refine WP.seq (WP.mono (ctr_ok v.ctr C₂ E₂ S₂) fun s₃ ⟨E₃, rd₃, wr₃, f₃, h₃⟩ => ?_)
  obtain f₁₃ : Frame (mutR W SP D n) s₁.mem s₃.mem := (f₂'.sub (wR_mut W SP D n)).trans (f₃.sub (ctrR_mut W SP D n))
  obtain S₃ := slots_mut L Ar.data.w f₁₃ S₁
  obtain c₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N nl) 0 := by
    rw [bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by have := tailBytes_le; have := tailBytes_ge; have := scratchBytes_le; omega)
      · exact (L.stk_w' (by decide)).symm
      · exact (Ar.data.w.sub_right (Lay.wSub (by decide))).symm) (by decide), c₂]
  obtain rd₁₃ : s₃.rd = s.rd := by rw [rd₃, rd₂, rd₁]
  obtain wr₁₃ : s₃.wr = s.wr := by rw [wr₃, wr₂, wr₁]
  -- The encrypted MAC of the plaintext at `W + 96`.
  refine macTag_ok v L E₃ S₃ Ar.rounds (length_bytesAt _ _ _) Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.hn c₃ (y := 96)
    (.inr rfl) (Ar.aad.of_eq rd₁₃ wr₁₃) (Ar.data.of_eq rd₁₃ wr₁₃) fun s₄ E₄ rd₄ wr₄ f₄ _ h₄ => ?_
  obtain f₁₄ : Frame (mutR W SP D n) s₁.mem s₄.mem :=
    f₁₃.trans ((f₄.sub (tagR_wR W SP (by decide))).sub (wR_mut W SP D n))
  obtain rd₁₄ : s₄.rd = s.rd := by rw [rd₄, rd₁₃]
  obtain wr₁₄ : s₄.wr = s.wr := by rw [wr₄, wr₁₃]
  obtain f₀₄ : Frame (entryR W :: mutR W SP D n) s.mem s₄.mem :=
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩).trans
    (f₁₄.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
  obtain hT₄ : s₄.mem.readW (SP + BitVec.ofNat 64 24) 64 = T := by rw [argT_kept f₀₄ Ar.argsW Ar.argsD, hT]
  obtain hTr₄ : InRegions (s₄.rd ++ s₄.wr) (SP + BitVec.ofNat 64 24) 8 := by
    obtain h := in_off (d := 16) (n := 8) Ar.args (by decide) (by decide)
    rw [add_ofNat_assoc] at h
    rw [rd₁₄, wr₁₄]; exact h
  refine WP.mono (openTail_ok L E₄ (slots_mut L Ar.data.w f₁₄ S₁) (Ar.data.of_eq rd₁₄ wr₁₄)
    (by rw [wr₁₄]; exact Ar.dw) (by have := Ar.t4; omega_arith) Ar.t16 (saved_mut L Ar.data.w f₁₄ sv₁) hT₄ hTr₄
    (by rw [rd₁₄, wr₁₄]; exact hTc) Tb.w)
    fun s₅ ⟨hg₅, hsp₅, hax₅, hd₅, f₅⟩ => ⟨⟨⟨fun r hr => ?_, ?_⟩, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₅ (.rbx, 112) (by decide)
    · exact hg₅ (.rbp, 120) (by decide)
    · rw [hsp₅, hsp]
    · exact hg₅ (.r12, 128) (by decide)
    · exact hg₅ (.r13, 136) (by decide)
    · exact hg₅ (.r14, 144) (by decide)
    · exact hg₅ (.r15, 152) (by decide)
  · have fall : Frame (entryR W :: mutR W SP D n) s.mem s₅.mem :=
      f₀₄.trans (f₅.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨wK W, by simp, Offset.sub W (by decide) (by decide)⟩
        · exact ⟨wC W, by simp, Offset.sub W (by decide) (by have := tailBytes_le; have := tailBytes_ge; have := scratchBytes_le; omega)⟩
        · exact ⟨_, by simp, fun _ h => h⟩)
    rw [hsp]
    exact fall.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (ret_disj L Ar.retW Ar.retD) (by decide)
  · -- The plaintext and the comparison.
    obtain hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m K R) := fun _ x => Proof.Cmac.aesWith_length _ _ x
    obtain c₂' : Spec.Ccm.ctxCiph s₂.mem K R = Spec.Ccm.ctxCiph s.mem K R := by
      rw [ciph_mut L Ar.dk Ar.rounds (f₂'.sub (wR_mut W SP D n)), hK₁]
    obtain c₃' : Spec.Ccm.ctxCiph s₃.mem K R = Spec.Ccm.ctxCiph s.mem K R := by
      rw [ciph_mut L Ar.dk Ar.rounds f₁₃, hK₁]
    obtain d₂ : bytesAt s₂.mem D n = bytesAt s.mem D n := by rw [buf_wR Ar.data f₂', hent Ar.data]
    obtain a₃ : bytesAt s₃.mem A al = bytesAt s.mem A al := by rw [buf_mut Ar.aad Ar.ad f₁₃, hent Ar.aad]
    obtain p₃ : bytesAt s₃.mem D n =
        Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem N nl) (bytesAt s.mem D n) := by
      rw [h₃, c₂', d₂, crypt_eq (hBC _)]
    obtain p₄ : bytesAt s₄.mem D n =
        Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem N nl) (bytesAt s.mem D n) := by
      rw [buf_wR Ar.data (f₄.sub (tagR_wR W SP (by decide))), p₃]
    obtain hT : bytesAt s₄.mem T tl = bytesAt s.mem T tl := tag_kept Tb Ar.t16 f₀₄
    rw [c₃', a₃, p₃] at h₄
    obtain hY := congrArg List.length h₄
    rw [length_bytesAt, length_xorFrom] at hY
    obtain hl : (bytesAt s.mem N nl).length ≤ 15 := by rw [length_bytesAt]; have := Ar.h13; omega_arith
    obtain hV : bytesAt s₄.mem (W + BitVec.ofNat 64 96) tl =
        Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl)
          (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl) (bytesAt s.mem A al)
            (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem N nl) (bytesAt s.mem D n))) := by
      rw [bytesAt_prefix s₄.mem _ Ar.t16, h₄, take_xorFrom_zero (hBC _) _ hY.symm Ar.t16, ← mac_eq _ _ hl]
    obtain hML : (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl) (bytesAt s.mem A al)
        (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem N nl) (bytesAt s.mem D n))).length = tl := by
      rw [mac_eq _ _ hl, List.length_take, ← hY]; have := Ar.t16; omega_arith
    obtain key : bytesAt s₄.mem (W + BitVec.ofNat 64 96) tl = bytesAt s₄.mem T tl ↔
        Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl) (bytesAt s.mem T tl) =
          Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl) (bytesAt s.mem A al)
            (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem N nl) (bytesAt s.mem D n)) := by
      rw [hV, hT, cryptTag_eq_iff (hBC _) Ar.t16 _ hML (length_bytesAt _ _ _), eq_comm]
    simp only [Spec.Ccm.decryptWith]
    by_cases hk : Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl) (bytesAt s.mem T tl) =
        Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem K R) tl (bytesAt s.mem N nl) (bytesAt s.mem A al)
          (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem K R) (bytesAt s.mem N nl) (bytesAt s.mem D n))
    · have hk' := key.mpr hk
      simp only [hk, ↓reduceIte]
      exact ⟨by rw [hax₅]; simp only [hk', ↓reduceIte]; rfl, by rw [hd₅]; simp only [hk', ↓reduceIte, p₄]⟩
    · have hk' : ¬ bytesAt s₄.mem (W + BitVec.ofNat 64 96) tl = bytesAt s₄.mem T tl := fun e => hk (key.mp e)
      simp only [hk, ↓reduceIte]
      exact ⟨by rw [hax₅]; simp only [hk', ↓reduceIte]; rfl, by rw [hd₅]; simp only [hk', ↓reduceIte]⟩

  · obtain ⟨tp, p, ep, ap, mp⟩ := entryRestore_run run₁ E₁ sv₁ hsp
      (f₁.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [hsp]; exact Ar.retW.sub_right (Lay.wSub (by decide))) (by decide))
    refine ⟨tp, p, ep, ap, ?_⟩
    rw [mp]
    apply Frame.mono (f₁₄.trans (f₅.sub ?_)) (List.subset_append_left ..)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨wK W, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨wC W, by simp, Region.sub_prefix tailBytes_ge⟩
    · exact ⟨_, by simp, fun _ h => h⟩

/-- `vg_aes_ccm_open`. -/
theorem open_wp_frame (v : UpdateImpl) [UpdateFits v] {s : State} (h : openX86_64.pre s) :
    WP isa («open» v.callee v.ctr.callee) s fun s' => (gprPreserved s s' ∧ openX86_64.post s s') ∧
      EntryFrame s s' (stackArg s 4) (s.gpr .rsp) (stackArg s 0) (stackArg s 1).toNat
        (stackArg s 2) (stackArg s 3).toNat :=
  have A := args_of_open h
  open_wp'_frame v A.1.1 A.1.2 A.2 rfl rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl rfl
    (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm

theorem open_wp (v : UpdateImpl) [UpdateFits v] {s : State} (h : openX86_64.pre s) :
    WP isa («open» v.callee v.ctr.callee) s fun s' => gprPreserved s s' ∧ openX86_64.post s s' :=
  WP.mono (open_wp_frame v h) (fun _ h => h.1)

end VG.Proof.AesCcm.X86_64

end

end

/-!
# AES-CCM on x86-64: `vg_aes_ccm_open` is constant time

Untrusted: everything here is checked by Lean. As `seal` (`SealCT.lean`),
with counter mode before the MAC; the comparison, which leaves `ok` at
`W + 224`, and the mask and the exit are checked by the taint analysis from
the public arguments, between which correctness says each run keeps them
(`openCmp_ok`), and the received tag is read from the same address `tag`,
which correctness says is still on the stack (`loadTag_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr recv cmp)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

theorem openLoad_check : ∃ hc, (taint.check (ccmT [])
    (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem openCmp_check : ∃ hc, (taint.check (ccmT [.rbx, .rsi])
    (.seq recv (.seq (cmp uO) (.block [.store (at_ .r15 okO) .rax]))) hc).isSome = true := ⟨_, by taint_decide⟩

theorem openMask_check : ∃ hc, (taint.check (ccmT [])
    (.seq mask (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++ restore))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A run with the received tag `T`, of `tl` bytes, which it may read, apart
from `W`. -/
def TagR (W : Addr) (T : Addr) (tl : Nat) (s : State) : Prop :=
  Covers [⟨T, tl⟩] (s.rd ++ s.wr) ∧ (⟨T, tl⟩ : Region).Disjoint ⟨W, 2560⟩

/-- The tag length and the address of the received tag loaded, in a run. -/
theorem openLoad_one {K W SP : Addr} {R : Nat} {N A D T : Addr} {nl al n tl : Nat} {s : State}
    (h : Mid K W SP R N A D nl al n tl T s) :
    WP isa (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))]) s fun s' =>
      One K W SP R N A D nl al n tl s' ∧ s'.gpr .rbx = BitVec.ofNat 64 tl ∧ s'.gpr .rsi = T ∧ s'.rd = s.rd := by
  obtain ⟨o, -, -, -, hT⟩ := h
  obtain ⟨s₁, run₁, hm₁, hbx₁, hsi₁, hg₁, hrd₁, hwr₁⟩ := loadTag_ok o.env o.sl hT.val hT.rd
  refine WP.of_runBlock ⟨s₁, run₁, ⟨o.env.keep (fun r hr => hg₁ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    hrd₁ hwr₁, by rw [hm₁]; exact o.sl, hwr₁.trans o.wr⟩, hbx₁, hsi₁, hrd₁⟩

/-- The comparison keeps the public arguments. -/
theorem openCmp_one {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr} {nl al n tl : Nat}
    (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) {s : State} (h : Mid K W SP R N A D nl al n tl T s) (hT : TagR W T tl s) :
    WP isa (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))]) (.seq recv
      (.seq (cmp uO) (.block [.store (at_ .r15 okO) .rax])))) s (One K W SP R N A D nl al n tl) := by
  obtain ⟨o, -, -, hD, hA⟩ := h
  refine WP.mono (openCmp_ok L o.env o.sl (by omega_using [ht4]) ht16 hA.val hA.rd hT.1 hT.2) fun s₄ ⟨E₄, _, wr₄, f₄, _⟩ => ?_
  refine ⟨E₄, slots_mut L hD.w (f₄.sub fun r hr => ?_) o.sl, wr₄.trans o.wr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨wK W, by simp, Offset.sub W (by decide) (by decide)⟩
  · exact ⟨wC W, by simp, Offset.sub W (by decide) (by decide)⟩

/-- `open` after its entry, up to the comparison, in one run. -/
theorem openFront_mid (v : UpdateImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr}
    {nl al n tl : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl)
    (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hn' : n < 256 ^ (15 - nl)) (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩)
    {s : State} (h : Pre₀ K W SP R N A D nl al n tl T s) :
    WP isa (openFront v.callee v.ctr.callee) s fun s' => Mid K W SP R N A D nl al n tl T s' ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨o, hN, hA, hD, hT⟩ := h
  obtain ⟨t, s', e, q⟩ := WP.seq (WP.mono (ctrs_mid L o hN hA hD hT h7 h13) fun _ h₁ =>
    WP.seq (WP.mono (ctr_mid v.ctr L hR h7 h13 hn' hdk h₁) fun _ h₂ =>
    WP.seq (WP.mono (mac_mid v L hR h7 h13 ht4 ht16 hte hn' (.inr rfl) h₂) fun _ h₃ =>
    tag_mid v.ctr L hR h7 h13 (.inr rfl) h₃)))
  exact ⟨t, s', e, q, Exec.rdwr e⟩

/-- `open` after its entry, in two runs. -/
theorem openBody_rel (v : UpdateImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} {N A D T : Addr}
    {nl al n tl : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hn : n ≤ 2 ^ 64) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0)
    (hal : al < 2 ^ 64) (hn' : n < 256 ^ (15 - nl)) (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩)
    {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → (Pre₀ K W SP R N A D nl al n tl T s₁ ∧ TagR W T tl s₁) ∧
      (Pre₀ K W SP R N A D nl al n tl T s₂ ∧ TagR W T tl s₂)) :
    RelCT isa P (.seq (openFront v.callee v.ctr.callee)
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 24))]) (.seq recv (.seq (cmp uO)
      (.seq (.block [.store (at_ .r15 okO) .rax]) (.seq mask
        (.block (([.mov .rax (.mem (at_ .r15 okO))] : List Instr) ++ restore)))))))) fun _ _ => True := by
  have hy : uO = 0 ∨ uO = 96 := .inr rfl
  have r₁ := (rel_taintC [] hDW hn (fun s₁ s₂ h => by
      obtain ⟨⟨⟨o₁, -⟩, -⟩, ⟨⟨o₂, -⟩, -⟩⟩ := hP _ _ h; exact Both.of o₁ o₂ fun _ h => nomatch h) ctrs_check).wp
    (F₁ := Mid K W SP R N A D nl al n tl T) (F₂ := Mid K W SP R N A D nl al n tl T) fun s₁ s₂ h => by
      obtain ⟨⟨⟨o₁, n₁, a₁, d₁, t₁⟩, -⟩, ⟨⟨o₂, n₂, a₂, d₂, t₂⟩, -⟩⟩ := hP _ _ h
      exact ⟨ctrs_mid L o₁ n₁ a₁ d₁ t₁ h7 h13, ctrs_mid L o₂ n₂ a₂ d₂ t₂ h7 h13⟩
  have r₂ := (rel_of_pt (c := ctr v.ctr.callee)
    (P := fun s₁ s₂ => True ∧ Mid K W SP R N A D nl al n tl T s₁ ∧ Mid K W SP R N A D nl al n tl T s₂)
    fun σ₁ σ₂ h => by
      obtain ⟨_, C₁⟩ := h.2.1.ctx L hR h7 h13 hn' hdk
      obtain ⟨_, C₂⟩ := h.2.2.ctx L hR h7 h13 hn' hdk
      exact crypt_rel v.ctr C₁ C₂ h.2.1.1 h.2.2.1).wp
    (F₁ := Mid K W SP R N A D nl al n tl T) (F₂ := Mid K W SP R N A D nl al n tl T)
    fun _ _ h => ⟨ctr_mid v.ctr L hR h7 h13 hn' hdk h.2.1, ctr_mid v.ctr L hR h7 h13 hn' hdk h.2.2⟩
  have r₃ := (mac_rel v L hR hDW hn h7 h13 ht4 ht16 hte hal hn' hy
    (Q := fun s₁ s₂ => True ∧ Mid K W SP R N A D nl al n tl T s₁ ∧ Mid K W SP R N A D nl al n tl T s₂)
    fun _ _ h => ⟨⟨h.2.1.1, h.2.1.2.1, h.2.1.2.2.1, h.2.1.2.2.2.1⟩,
      ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩⟩).wp
    (F₁ := Mid K W SP R N A D nl al n tl T) (F₂ := Mid K W SP R N A D nl al n tl T)
    fun _ _ h => ⟨mac_mid v L hR h7 h13 ht4 ht16 hte hn' hy h.2.1, mac_mid v L hR h7 h13 ht4 ht16 hte hn' hy h.2.2⟩
  have r₄ := (tag_rel v.ctr L hR hDW hn h7 h13 hy
    (Q := fun s₁ s₂ => True ∧ Mid K W SP R N A D nl al n tl T s₁ ∧ Mid K W SP R N A D nl al n tl T s₂)
    fun _ _ h => ⟨⟨h.2.1.1, h.2.1.2.1⟩, ⟨h.2.2.1, h.2.2.2.1⟩⟩).wp
    (F₁ := Mid K W SP R N A D nl al n tl T) (F₂ := Mid K W SP R N A D nl al n tl T)
    fun _ _ h => ⟨tag_mid v.ctr L hR h7 h13 hy h.2.1, tag_mid v.ctr L hR h7 h13 hy h.2.2⟩
  -- The pieces before the comparison keep the permissions, so the received tag stays readable.
  have front := (RelCT.seq r₁ (RelCT.seq r₂ (RelCT.seq r₃ r₄))).wp
    (F₁ := TagR W T tl) (F₂ := TagR W T tl) fun s₁ s₂ h => by
      obtain ⟨⟨p₁, tr₁⟩, ⟨p₂, tr₂⟩⟩ := hP _ _ h
      exact ⟨WP.mono (openFront_mid v L hR h7 h13 ht4 ht16 hte hn' hdk p₁) fun _ ⟨_, rd', wr'⟩ =>
          ⟨by rw [rd', wr']; exact tr₁.1, tr₁.2⟩,
        WP.mono (openFront_mid v L hR h7 h13 ht4 ht16 hte hn' hdk p₂) fun _ ⟨_, rd', wr'⟩ =>
          ⟨by rw [rd', wr']; exact tr₂.1, tr₂.2⟩⟩
  have r₅a := (rel_taintC (K := K) (SP := SP) (R := R) (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    (P := fun s₁ s₂ => (True ∧ Mid K W SP R N A D nl al n tl T s₁ ∧ Mid K W SP R N A D nl al n tl T s₂) ∧
      TagR W T tl s₁ ∧ TagR W T tl s₂) [] hDW hn
    (fun _ _ h => Both.of h.1.2.1.1 h.1.2.2.1 fun _ h => nomatch h) openLoad_check).wp
    (F₁ := fun (s' : State) => One K W SP R N A D nl al n tl s' ∧ s'.gpr .rbx = BitVec.ofNat 64 tl ∧ s'.gpr .rsi = T)
    (F₂ := fun (s' : State) => One K W SP R N A D nl al n tl s' ∧ s'.gpr .rbx = BitVec.ofNat 64 tl ∧ s'.gpr .rsi = T)
    fun _ _ h => ⟨WP.mono (openLoad_one h.1.2.1) fun _ q => ⟨q.1, q.2.1, q.2.2.1⟩,
      WP.mono (openLoad_one h.1.2.2) fun _ q => ⟨q.1, q.2.1, q.2.2.1⟩⟩
  have r₅b := rel_taintC (K := K) (SP := SP) (R := R) (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    (c := .seq recv (.seq (cmp uO) (.block [.store (at_ .r15 okO) .rax])))
    (P := fun s₁ s₂ => True ∧
      (One K W SP R N A D nl al n tl s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 tl ∧ s₁.gpr .rsi = T) ∧
      (One K W SP R N A D nl al n tl s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 tl ∧ s₂.gpr .rsi = T)) [.rbx, .rsi] hDW hn
    (fun _ _ h => Both.of h.2.1.1 h.2.2.1 fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2, h.2.2.2.2]) openCmp_check
  have r₅ := (RelCT.seq r₅a r₅b).wp
    (F₁ := One K W SP R N A D nl al n tl) (F₂ := One K W SP R N A D nl al n tl)
    fun _ _ h => ⟨openCmp_one L ht4 ht16 h.1.2.1 h.2.1, openCmp_one L ht4 ht16 h.1.2.2 h.2.2⟩
  have r₆ := rel_taintC (K := K) (SP := SP) (R := R) (N := N) (A := A) (nl := nl) (al := al) (tl := tl)
    (P := fun s₁ s₂ => True ∧ One K W SP R N A D nl al n tl s₁ ∧ One K W SP R N A D nl al n tl s₂) [] hDW hn
    (fun _ _ h => Both.of h.2.1 h.2.2 fun _ h => nomatch h) openMask_check
  exact RelCT.seq front (rel_assoc4 (RelCT.seq r₅ r₆))

/-- What the entry of `open` leaves: a run after the entry, with the received
tag readable. -/
theorem entry_open {s : State} (hp : openX86_64.pre s) :
    WP isa (.block entry) s fun s₁ =>
      Pre₀ (s.gpr .rdi) (arg s 4) (s.gpr .rsp) (s.gpr .rsi).toNat (s.gpr .rdx) (s.gpr .r8) (arg s 0)
        (s.gpr .rcx).toNat (s.gpr .r9).toNat (arg s 1).toNat (arg s 3).toNat (arg s 2) s₁ ∧
      TagR (arg s 4) (arg s 2) (arg s 3).toNat s₁ := by
  have A := args_of_open hp
  refine WP.mono (entry_post A.1.1 rfl rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl rfl
    (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm) fun _ ⟨E, S, rd, wr, hT⟩ =>
    ⟨⟨⟨E, S, by rw [wr]; exact hp.2.1⟩, A.1.1.nonce.of_eq rd wr, A.1.1.aad.of_eq rd wr, A.1.1.data.of_eq rd wr, hT⟩,
      by rw [rd, wr]; exact A.2, A.1.2.w⟩

/-- The second run, with the first's public arguments. -/
theorem entry_open_pub {s₀ s₀' : State} (hp' : openX86_64.pre s₀') (hq : onePub s₀ s₀') :
    WP isa (.block entry) s₀' fun s₁ =>
      Pre₀ (s₀.gpr .rdi) (arg s₀ 4) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .rdx) (s₀.gpr .r8) (arg s₀ 0)
        (s₀.gpr .rcx).toNat (s₀.gpr .r9).toNat (arg s₀ 1).toNat (arg s₀ 3).toNat (arg s₀ 2) s₁ ∧
      TagR (arg s₀ 4) (arg s₀ 2) (arg s₀ 3).toNat s₁ := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, qa⟩ := hq
  rw [qa 0 (by decide), qa 1 (by decide), qa 2 (by decide), qa 3 (by decide), qa 4 (by decide), q1, q2, q3, q4,
    q5, q6, q7]
  exact entry_open hp'

/-- `vg_aes_ccm_open`, in two runs with the same public arguments. -/
theorem open_rel (v : UpdateImpl) {s₀ s₀' : State} (hp : openX86_64.pre s₀) (hp' : openX86_64.pre s₀')
    (hq : onePub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («open» v.callee v.ctr.callee) fun _ _ => True := by
  have A := args_of_open hp
  have Ar := A.1.1
  refine RelCT.seq (entry_rel (pub_regs hq) (hq.2.2.2.2.2.2.2 4 (by decide)) (argW_in Ar rfl)
    (argW_in (args_of_open hp').1.1 rfl) (entry_open hp) (entry_open_pub hp' hq)) ?_
  exact openBody_rel v Ar.lay Ar.rounds Ar.data.w (Nat.le_of_lt Ar.data.lt) Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te
    Ar.aad.lt Ar.hn Ar.dk fun _ _ h => ⟨h.2.1, h.2.2⟩

end VG.Proof.AesCcm.X86_64
