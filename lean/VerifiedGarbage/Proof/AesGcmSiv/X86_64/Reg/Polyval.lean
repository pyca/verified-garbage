module

public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Reg.Keys
public import VerifiedGarbage.Proof.GcmSiv.MulX
public import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Keys
import VerifiedGarbage.Proof.GcmSiv.Spec
import VerifiedGarbage.Proof.GcmSiv.Polyval
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# AES-GCM-SIV in registers on x86-64: POLYVAL

Untrusted: everything here is checked by Lean. POLYVAL is GHASH with the key
`mulXG H` on its blocks as little-endian numbers
(`Proof.GcmSiv.Polyval.polyvalFrom_eq`): `hkey` leaves GHASH's registers for
that key (`hkey_ok`), and each block loaded as it is and multiplied
(`mulY_ok`, `body4_ok`) is a step of `Spec.Gcm.ghashFrom`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSivReg.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64Reg
open VG.Impl.AesGcmSiv.X86_64 (akO)
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcmSiv.X86_64 (add_ofNat_assoc punpck_movq mulXG_words)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod Only zero_ok acc_ok reduce_ok constImm_ok hInvImm_ok pows_ok step1
  step4 pxor72_ok)
open VG.Proof.Gcm.Poly (φ x)
open VG.Proof.GcmSiv.Polyval (mulXG)

/-- GHASH's key for the authentication key at `W + 16`. -/
abbrev hOf (m : Mem) (W : Addr) : Spec.Gcm.Block :=
  mulXG (Spec.GcmSiv.ofBytes (bytesAt m (W + BitVec.ofNat 64 16) 16))

/-- GHASH's registers for the key `H`: the reduction constant in `xmm1` and
`H'` in `xmm3`. -/
structure GReg (H : Spec.Gcm.Block) (t : State) : Prop where
  c : t.xmm .xmm1 = Impl.Gcm.X86_64.Pclmul.poly
  h : x * φ (t.xmm .xmm3) = φ H

theorem GReg.keep {H : Spec.Gcm.Block} {rs : List XReg} {t t' : State} (g : GReg H t) (o : Only rs t t')
    (h1 : .xmm1 ∉ rs) (h3 : .xmm3 ∉ rs) : GReg H t' :=
  ⟨by rw [o.xmm _ h1, g.c], by rw [o.xmm _ h3]; exact g.h⟩

/-- The registers `mulY` writes. -/
abbrev mulRegs : List XReg :=
  [.xmm8, .xmm9, .xmm10, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm8, .xmm9, .xmm10, .xmm11, .xmm2]

/-- `mulY`: a step of GHASH, on the block in `xmm7`. -/
theorem mulY_ok {H : Spec.Gcm.Block} {t : State} (g : GReg H t) :
    WP isa (.block mulY) t fun t' =>
      t'.xmm .xmm2 = Spec.Gcm.mul (t.xmm .xmm2 ^^^ t.xmm .xmm7) H ∧ Only mulRegs t t' := by
  simp only [mulY, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok t) fun s₁ ⟨p₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pxor72_ok s₁) fun s₂ ⟨e₂, o₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (acc_ok .xmm7 .xmm3 s₂ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₃ ⟨p₃, o₃⟩ => ?_
  have c₃ : s₃.xmm .xmm1 = Impl.Gcm.X86_64.Pclmul.poly := by
    rw [o₃.xmm _ (by decide), o₂.xmm _ (by decide), o₁.xmm _ (by decide), g.c]
  refine WP.mono (reduce_ok .xmm2 s₃ (by decide) (by decide) (by decide) (by decide) c₃) fun s₄ ⟨e₄, o₄⟩ =>
    ⟨?_, o₁.trans (o₂.trans (o₃.trans o₄))⟩
  rw [e₄, p₃, o₂.prod (by decide) (by decide) (by decide), p₁, e₂, o₂.xmm .xmm3 (by decide),
    o₁.xmm .xmm2 (by decide), o₁.xmm .xmm7 (by decide), o₁.xmm .xmm3 (by decide)]
  exact step1 H _ _ _ g.h

/-- `hkey`: GHASH's registers for the key of the authentication key, and
`Y = 0`. -/
theorem hkey_ok {K W SP : Addr} {t : State} (E : Env K W SP t) :
    WP isa (.block hkey) t fun t' =>
      GReg (hOf t.mem W) t' ∧ t'.xmm .xmm2 = 0 ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 16 + 8 ≤ 488 by decide)
  have r₂ := E.perm.wR (show 24 + 8 ≤ 488 by decide)
  simp only [hkey, List.append_assoc]
  rw [WP.block_append_iff]
  obtain ⟨t₁, run₁, x7, m₁, rd₁, wr₁, g₁⟩ : ∃ t₁ : State, runBlock isa
      [.mov .rax (.mem (at_ .r15 akO)), .mov .rdx (.mem (at_ .r15 (akO + 8))), .mov .rcx (.reg .rax),
        .alu .and .rcx (imm 1), .mov32 .r8 (imm 0), .alu .sub .r8 (.reg .rcx), .shift .shr .rax 1,
        .mov .rcx (.reg .rdx), .alu .and .rcx (imm 1), .shift .ror .rcx 1, .alu .or .rax (.reg .rcx),
        .shift .shr .rdx 1, .movImm64 .rcx 0xE100000000000000, .alu .and .rcx (.reg .r8),
        .alu .xor .rdx (.reg .rcx), .xop (.movq .xmm7 .rax), .xop (.movq .xmm11 .rdx),
        .xop (.bin .punpcklqdq .xmm7 .xmm11)] t = some t₁ ∧
      t₁.xmm .xmm7 = hOf t.mem W ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr ∧
      ∀ r ∈ calleeSaved, t₁.gpr r = t.gpr r := by
    refine ⟨_, by xrun [h15, r₁, r₂], ?_, ?_, ?_, ?_, ?_⟩
    · simp (config := {decide := true}) only [gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true,
        ite_false, reduceCtorEq, xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg, xmm_arithFlags, xmm_setFlags,
        punpck_movq, add_ofNat_assoc, Nat.reduceAdd, ne_eq, not_false_eq_true]
      rw [hOf, GcmSiv.ofBytes_bytesAt, add_ofNat_assoc, ← mulXG_words]
      rfl
    · rfl
    · rfl
    · rfl
    · intro r hr; simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [gpr_setXmm, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq]
  refine WP.of_runBlock ⟨t₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (constImm_ok .xmm1 Impl.Gcm.X86_64.Pclmul.poly t₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hInvImm_ok s₂) fun s₃ ⟨h₃, o₃⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, isa, State.setXmm,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show s₃.xmm .xmm1 = _
    rw [o₃.xmm _ (by decide), c₂]
  · show x * φ (s₃.xmm .xmm3) = _
    rw [h₃, o₂.xmm _ (by decide), x7]
  · show XBinOp.eval .pxor (s₃.xmm .xmm2) (s₃.xmm .xmm2) = 0
    exact BitVec.xor_self
  · show s₃.mem = _
    rw [o₃.mem, o₂.mem, m₁]
  · show s₃.rd = _
    rw [o₃.rd, o₂.rd, rd₁]
  · show s₃.wr = _
    rw [o₃.wr, o₂.wr, wr₁]
  · intro r hr
    have hne : r ≠ .rax := by rintro rfl; exact absurd hr (by decide)
    show s₃.gpr r = _
    rw [o₃.gpr r hne, o₂.gpr r hne, g₁ r hr]

end VG.Proof.AesGcmSivReg.X86_64
