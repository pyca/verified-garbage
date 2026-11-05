module

public import VerifiedGarbage.Proof.Rsa.X86_64.WordShadowCopy
import VerifiedGarbage.Proof.Rsa.X86_64.Loops

-- separate module: isolate public base recovery from the reducer arithmetic

/-! # Restoring the original validation workspace and copying its remainder -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.WordValidation

open VG VG.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem restore_ok {s : State} {B : Addr} {w : Nat}
    (hdi : s.gpr .rdi = off B (start w)) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))) :
    WP isa (.block WordValidation.restore) s fun t =>
      t.gpr .rdi = B ∧ t.mem = s.mem ∧ Keep [.rax, .rdi] s t := by
  have he : (BitVec.ofNat 64 (8 * (w + 2)) <<< 3) + BitVec.ofNat 64 256 = BitVec.ofNat 64 (start w) := by
    rw [shl_nat, ← BitVec.ofNat_add]
    congr 1
    simp only [start, slot, hdrBytes]
    omega_arith
  refine WP.mono (WP.keep [.rax, .rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = s.mem) (by
    xrun [WordValidation.restore, hdi, h9, sx_ofNat (show 256 < 2 ^ 31 by decide), he]
    exact BitVec.add_sub_cancel _ _) rfl) fun _ ⟨⟨hdi, hm⟩, hk⟩ => ⟨hdi, hm, hk⟩

theorem resultSetup_ok {s : State} {B : Addr} {w : Nat}
    (h : VG.Proof.Rsa.X86_64.Ws s (off B (start w)) (span w) w) :
    WP isa (.block WordValidation.resultSetup) s fun t =>
      t.gpr .rdi = B ∧ t.gpr .rsi = off B (start w + slot w WordDivide.aR) ∧
      t.gpr .rbx = off B (slot w CheckKey.aR) ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.mem = s.mem ∧ Keep [.r12, .r9, .rsi, .rax, .rdi, .rbx] s t := by
  unfold WordValidation.resultSetup
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rsa.X86_64.base_ok WordDivide.aR (r := .rsi) (by decide)
    ((k₁.gpr (by decide)).trans h.rdi) h9) fun t₂ ⟨hsi, m₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (restore_ok (((k₁.trans k₂).gpr (by decide)).trans h.rdi)
    ((k₂.gpr (by decide)).trans h9)) fun t₃ ⟨hdi₃, m₃, k₃⟩ => ?_
  refine WP.mono (VG.Proof.Rsa.X86_64.base_ok CheckKey.aR (r := .rbx) (by decide) hdi₃
    (((k₂.trans k₃).gpr (by decide)).trans h9)) fun t ⟨hbx, m₄, k₄⟩ => ?_
  refine ⟨(k₄.gpr (by decide)).trans hdi₃, ?_, hbx,
    (((k₂.trans k₃).trans k₄).gpr (by decide)).trans h12, m₄.trans (m₃.trans (m₂.trans m₁)),
    (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  rw [k₄.gpr (by decide), k₃.gpr (by decide), hsi, addr_view]

end VG.Proof.Rsa.X86_64.WordValidation
