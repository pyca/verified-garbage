module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Open
public import VerifiedGarbage.Impl.AesGcm.X86_64.FastOpen
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# AES-GCM `open`'s path for TLS records: the bytes left

Untrusted: everything here is checked by Lean. `FastOpen.tagP` leaves `K[1]`,
at `W + 1040`, the keystream of the counter block (`KOk`), which the code
until the end of `open` keeps (`pStable_kOk`). `FastOpen.tailK` decrypts the
bytes left with it, as `oneCrypt` does with a call of `vg_aes_ctr32`:
`crOk_tailK`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.FastOpen

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Spec.Gcm (Block blockAt inc32)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (Ctr xorKs)

/-- `K[1]` is the keystream of the counter block. -/
def KOk (Ctx W : Addr) (R : Nat) (s : State) : Prop :=
  blockAt s.mem (W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 16) =
    ciphOf s.mem Ctx R (blockAt s.mem (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 48))

theorem pStable_kOk : PStable KOk := by
  intro Ctx W SP R s s' L hR f h
  have e : W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 16 = W + BitVec.ofNat 64 1040 := by rw [add_ofNat_assoc]
  unfold KOk at h ⊢
  rw [blockAt_frame f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [e]; rcases hr with rfl | rfl | rfl <;> exact L.w_w (.inr (by decide)) (by decide) (by decide)),
    ciph_frame f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact L.cw'.sub_right (Lay.wSub (by decide))) hR,
    blockAt_frame f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩))]
  exact h

/-- `ctr_tail` with the keystream block anywhere: fewer than 16 bytes from a
block boundary, XORed with the keystream of the counter block. -/
theorem ctr_tailK {m m₁ : Mem} {cb ks k : Addr} {ciph : Block → Block} {icb : Block} {n : Nat}
    (h : Ctr m cb ks ciph icb n) (h0 : n % 16 = 0) (hk : blockAt m₁ k = ciph (blockAt m cb))
    {d : List Byte} (hd : d.length < 16) :
    List.zipWith (· ^^^ ·) d (bytesAt m₁ k d.length) = xorKs ciph icb n d := by
  have hcb : blockAt m cb = Nat.repeat inc32 (n / 16) icb := by rw [h.1]; congr 1; omega
  refine Proof.Gcm.zipWith_eq_xorKs (Cmac.bytesAt_length _ _ _) fun j hj => ?_
  rw [Proof.Gcm.getD_bytesAt' _ _ hj, Proof.Gcm.bytes_toBytes_blockAt m₁ k (k := j) (by omega), hk, hcb,
    Proof.Gcm.ksByte, show (n + j) / 16 = n / 16 by omega, show (n + j) % 16 = j by omega]

/-- `tailK`: the bytes left decrypted with `K[1]`. -/
theorem crOk_tailK : CrOk KOk Impl.AesGcm.X86_64.FastOpen.tailK := by
  intro Ctx W SP L R icb P₀ D n s hP hn he hR hdat hlen hd hK
  have q₂ := he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hcx₁, hz₁, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .rcx (.mem (at_ .r15 lenO)),
      .alu .test .rcx (.reg .rcx)] s = some s₁ ∧ s₁.gpr .rcx = BitVec.ofNat 64 n ∧ s₁.zf = some (decide (n = 0)) ∧
      (∀ r, r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [he.r15, q₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, hlen]
    · simp only [zf_arithFlags, hlen]
      exact congrArg some (and_self_beq (by omega))
    · intro r a; simp [gpr_setReg, a]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide)) hrd₁ hwr₁
  refine WP.ite (decide (n = 0)) (eval_e hz₁) (fun h0 => ?_) (fun h0 => ?_)
  · -- No bytes left.
    have h0' : n = 0 := of_decide_eq_true h0
    subst h0'
    exact WP.block_nil ⟨he₁, by rw [hm₁]; exact Frame.refl _ _, hrd₁, hwr₁, fun _ => by
      rw [hm₁]; rfl⟩
  · have h0' : n ≠ 0 := of_decide_eq_false h0
    have q₁ := he₁.perm.wR (show 200 + 8 ≤ 2560 by decide)
    obtain ⟨s₂, run₂, hdi₂, hsi₂, hcx₂, hg₂, hm₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
        (([.mov .rdi (.mem (at_ .r15 dataO))] : List Instr) ++ ptr .rsi .r15 (Impl.AesGcm.X86_64.Short.kO + 16)) s₁ =
          some s₂ ∧ s₂.gpr .rdi = D ∧ s₂.gpr .rsi = W + BitVec.ofNat 64 1040 ∧ s₂.gpr .rcx = BitVec.ofNat 64 n ∧
        (∀ r, r ≠ .rdi → r ≠ .rsi → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
      refine ⟨_, by xrun [he₁.r15, q₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, hm₁, hdat]
      · simp [gpr_setReg]; rfl
      · simp [gpr_setReg, hcx₁]
      · intro r a b; simp [gpr_setReg, a, b]
      all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have hlt := hd.ok.lt
    have lp : LoopPre s₂ (W + BitVec.ofNat 64 1040) D n :=
      ⟨hsi₂, hdi₂, hcx₂, by omega, by omega,
        by rw [hrd₂, hwr₂, hrd₁, hwr₁]; exact covers_left (he.perm.wC (by omega)),
        by rw [hwr₂, hwr₁]; exact hd.wr, (hd.ok.w.sub_right (Lay.wSub (by omega))).symm⟩
    refine WP.mono (xorLoop_ok s₂ lp) fun s₃ ⟨hm₃, hg₃, hrd₃, hwr₃⟩ => ?_
    rw [hm₂, hm₁] at hm₃
    have hxl := length_xorBytes s.mem D (W + BitVec.ofNat 64 1040) n
    have fw : Frame [⟨D, n⟩] s.mem s₃.mem := by rw [hm₃]; exact writeBytes_frame' _ hxl
    refine ⟨he₁.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;>
          rw [hg₃ _ (by decide) (by decide) (by decide), hg₂ _ (by decide) (by decide)])
        (by rw [hrd₃, hrd₂]) (by rw [hwr₃, hwr₂]),
      fw.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩,
      by rw [hrd₃, hrd₂, hrd₁], by rw [hwr₃, hwr₂, hwr₁], fun hc => ?_⟩
    have e : W + BitVec.ofNat 64 1024 + BitVec.ofNat 64 16 = W + BitVec.ofNat 64 1040 := by rw [add_ofNat_assoc]
    unfold KOk at hK
    rw [e] at hK
    have t := ctr_tailK hc hP hK (d := bytesAt s.mem D n) (by rw [length_bytesAt]; omega)
    rw [length_bytesAt] at t
    have hb := bytesAt_writeBytes_self s.mem D (xorBytes s.mem D (W + BitVec.ofNat 64 1040) n) (by rw [hxl]; omega)
    rw [hxl] at hb
    rw [hm₃, hb, xorBytes, t]

end VG.Proof.AesGcm.X86_64.FastOpen
