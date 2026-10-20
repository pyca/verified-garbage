module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# AES-GCM on x86-64: copying a tag

Untrusted: everything here is checked by Lean. `copyTag` copies a tag's
`rcx` bytes from `rsi` to `rdi` as `copyLoop` does (`copyTag_ok`), a word at
a time for a whole tag of 16 bytes. AES-GCM's `recv` and `cmp` use it, and so
does AES-CCM's tag check, which shares them.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)

theorem writeW_readW64 (m src : Mem) (a b : Addr) :
    m.writeW a (src.readW b 64) = writeBytes m a (bytesAt src b 8) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (BitVec.setWidth (8 * (64 / 8)) (BitVec.setWidth 64 (src.read b (64 / 8)))) =
    src.read b 8 from by simp]
  rw [write_eq_writeBytes]
  congr 1
  simp only [bytesAt]
  refine List.map_congr_left fun j hj => ?_
  exact Mem.extractLsb'_read src b (List.mem_range.mp hj)

/-- `copyTag` leaves what `copyLoop` does (`copyLoop_ok`): for 16 bytes, both
words are loaded before either is stored. -/
theorem copyTag_ok (s : State) {S D : Addr} {n : Nat} (h : LoopPre s S D n) :
    WP isa copyTag s fun s' => s'.mem = writeBytes s.mem D (bytesAt s.mem S n) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, hz₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.alu .cmp .rcx (imm 16)] s = some s₁ ∧
      s₁.zf = some (decide (n = 16)) ∧ s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_⟩
    · rw [zf_arithFlags, h.rcx]
      exact congrArg some (Offset.ofNat_sub_ofNat_beq (by have := h.lt; omega) (by decide))
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 16)) hz₁ (fun he => ?_) (fun _ => ?_)
  · have hn : n = 16 := by simpa using he
    subst hn
    have hsi : s₁.gpr .rsi = S := by rw [hg₁, h.rsi]
    have hdi : s₁.gpr .rdi = D := by rw [hg₁, h.rdi]
    have hR : Covers [⟨S, 16⟩] (s₁.rd ++ s₁.wr) := by rw [hrd₁, hwr₁]; exact h.rd
    have hW : Covers [⟨D, 16⟩] s₁.wr := by rw [hwr₁]; exact h.wr
    have r₀ : InRegions (s₁.rd ++ s₁.wr) (S + BitVec.ofNat 64 0) 8 :=
      hR _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base S (show 0 + 8 ≤ 16 by decide) (by decide)⟩
    have r₁ : InRegions (s₁.rd ++ s₁.wr) (S + BitVec.ofNat 64 8) 8 :=
      hR _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base S (show 8 + 8 ≤ 16 by decide) (by decide)⟩
    have w₀ : InRegions s₁.wr (D + BitVec.ofNat 64 0) 8 :=
      hW _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base D (show 0 + 8 ≤ 16 by decide) (by decide)⟩
    have w₁ : InRegions s₁.wr (D + BitVec.ofNat 64 8) 8 :=
      hW _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base D (show 8 + 8 ≤ 16 by decide) (by decide)⟩
    have e0 : S + BitVec.ofNat 64 0 = S := BitVec.add_zero S
    have f0 : D + BitVec.ofNat 64 0 = D := BitVec.add_zero D
    rw [e0] at r₀
    rw [f0] at w₀
    refine WP.of_runBlock ⟨_, by xrun [hsi, hdi, r₀, r₁, w₀, w₁, e0, f0], ?_, ?_, ?_, ?_⟩
    · have e := writeBytes_append s₁.mem D (bytesAt s₁.mem S 8) (bytesAt s₁.mem (S + BitVec.ofNat 64 8) 8)
        (by simp [bytesAt])
      rw [show (bytesAt s₁.mem S 8).length = 8 by simp [bytesAt], ← Cmac.bytesAt_split] at e
      rw [writeW_readW64, writeW_readW64, ← hm₁]
      exact e
    · intro r a b; simp [gpr_setReg, a, b, hg₁]
    all_goals simp only [hrd₁, hwr₁]
  · have lp : LoopPre s₁ S D n :=
      ⟨by rw [hg₁, h.rsi], by rw [hg₁, h.rdi], by rw [hg₁, h.rcx], h.pos, h.lt, by rw [hrd₁, hwr₁]; exact h.rd,
        by rw [hwr₁]; exact h.wr, h.disj⟩
    exact WP.mono (copyLoop_ok s₁ lp) fun s' ⟨a, b, c, d⟩ =>
      ⟨by rw [a, hm₁], fun r h₁ h₂ => by rw [b r h₁ h₂, hg₁], by rw [c, hrd₁], by rw [d, hwr₁]⟩

end VG.Proof.AesGcm.X86_64
