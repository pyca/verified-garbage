module

import VerifiedGarbage.Proof.AesSiv.RISCV64.Enc
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesSiv.RISCV64.CtrLoop
import VerifiedGarbage.Proof.AesSiv.RISCV64.Fn
import VerifiedGarbage.Proof.AesSiv.RISCV64.Long
public import VerifiedGarbage.Proof.AesSiv.RISCV64.Entry
public import VerifiedGarbage.Proof.AesSiv.RISCV64.S2v

/-!
# AES-SIV on RISC-V: `decrypt`

Untrusted: everything here is checked by Lean. After S2V of the associated
data (`encS2v_wp`), `decrypt` copies the received synthetic IV `V` to `W`,
decrypts the data in place by CTR from `V`'s counter, finishes S2V with the
plaintext into `W + 112`, compares the two IVs without a branch, ANDs every
byte of the data with the mask of the comparison and returns its result
(`decrypt_wp`). As on PPC64LE (`Proof/AesSiv/PPC64LE/Dec.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesSiv.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)

/-- `vg_aes_siv_decrypt`: with `P` the plaintext of the data under the
received synthetic IV `V` and `T` S2V's IV of it, the result is whether
`V = T`, and the data is `P`, or zeros if not. -/
theorem decrypt_wp {c : Cx} {s : State} (Ar : Args c s) (hA : Ads c s.mem s) :
    WP isa decrypt s fun s' => abiPreserved s s' ∧
      let mac := Spec.Siv.ctxMac s.mem c.C c.R
      let V := bytesAt s.mem c.V 16
      let P := Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem c.C c.R) (Spec.Siv.counter V) (bytesAt s.mem c.D c.n)
      let T := Spec.Siv.s2vFinish mac (Spec.Siv.s2vAcc mac (Spec.Siv.components 64 s.mem c.A c.N)) P
      s'.gpr .a0 = BitVec.ofNat 64 (if V = T then 1 else 0) ∧
        bytesAt s'.mem c.D c.n = P.map fun b => if V = T then b else 0 := by
  have L := Ar.lay
  have hn := L.n_lt
  unfold decrypt
  refine encS2v_wp Ar hA fun s₁ s₄ S _ _ => ?_
  obtain ⟨wf₄, acc₄⟩ := S.facts L hA
  have E₄ := S.inv.env
  -- The received IV in.
  refine WP.seq (WP.mono (sivIn_wp L E₄) fun s₅ ⟨pk₅, f₅, b₅⟩ => ?_)
  have E₅ := E₄.of_pk pk₅
  have wf₅ : WF c s.mem s₅.mem := wf₄.trans (WF.of f₅ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide))
  have v₅ : bytesAt s₅.mem (c.W + BitVec.ofNat 64 0) 16 = bytesAt s.mem c.V 16 := by
    rw [BitVec.add_zero, b₅]
    exact Proof.Cmac.bytesAt_frame wf₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.v_w) (by decide)
  have a₅ : bytesAt s₅.mem (c.W + BitVec.ofNat 64 dO) 16 = bytesAt s₄.mem (c.W + BitVec.ofNat 64 dO) 16 :=
    Proof.Cmac.bytesAt_frame f₅ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (Lay.w0_w (c := c) (n := 16) (d := dO) (k := 16) (by decide) (by decide)).symm) (by decide)
  -- CTR.
  refine WP.seq (WP.mono (ctr_wp L E₅ (src := 0) (by decide) (by decide)) fun s₆ ⟨pk₆, f₆, d₆⟩ => ?_)
  have E₆ := E₅.of_pk pk₆
  have v₆ : bytesAt s₆.mem (c.W + BitVec.ofNat 64 0) 16 = bytesAt s₅.mem (c.W + BitVec.ofNat 64 0) 16 :=
    Proof.Cmac.bytesAt_frame f₆ (ctrR_W0 L) (by decide)
  have a₆ : bytesAt s₆.mem (c.W + BitVec.ofNat 64 dO) 16 = bytesAt s₅.mem (c.W + BitVec.ofNat 64 dO) 16 :=
    Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (L.d_w' (by decide)).symm
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)) (by decide)
  have mac₆ : Spec.Siv.ctxMac s₆.mem c.C c.R = Spec.Siv.ctxMac s.mem c.C c.R := by
    rw [ctxMac_frame f₆ (ctrR_c L) L.rb, wf₅.ctxMac L]
  -- The plaintext as S2V's string, and S2V's end.
  refine WP.seq (wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ => WP.block_nil ?_)
  have pk₈ : PK s₆ s₈ := (PK.ofUpd u₇).trans (PK.ofUpd u₈)
  have E₈ := E₆.of_pk pk₈
  have m₈ : s₈.mem = s₆.mem := by rw [u₈.mem, u₇.mem]
  refine WP.seq (WP.mono (finish_wp L E₈ (L.bufD E₈.perm) (by rw [u₈.other _ (by decide), u₇.gpr, E₆.s9])
    (by rw [u₈.gpr, u₇.other _ (by decide), E₆.s10]) (out := tO) (.inr rfl)) fun s₉ ⟨pk₉, f₉, t₉⟩ => ?_)
  have E₉ := E₈.of_pk pk₉
  have v₉ : bytesAt s₉.mem c.W 16 = bytesAt s₈.mem c.W 16 := by
    have := Proof.Cmac.bytesAt_frame f₉ (fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)) (p := c.W + BitVec.ofNat 64 0) (n := 16)
      (by decide)
    rwa [BitVec.add_zero] at this
  have wf₉ : WF c s₈.mem s₉.mem := WF.of f₉ (oR_sub (by decide))
  -- The comparison and the mask.
  refine WP.seq (WP.mono (compare_wp L E₉) fun s₁₀ ⟨pk₁₀, m₁₀, s0₁₀⟩ => ?_)
  have E₁₀ := E₉.of_pk pk₁₀
  refine WP.seq (WP.mono (mask_wp L E₁₀ s0₁₀) fun s₁₁ ⟨pk₁₁, s0₁₁, m₁₁⟩ => ?_)
  have E₁₁ := E₁₀.of_pk pk₁₁
  refine WP.block_append_iff.mpr (wp_mv fun s₁₂ u₁₂ => WP.block_nil ?_)
  have E₁₂ := E₁₁.of_pk (PK.ofUpd u₁₂)
  have pk₁₂ : PK s₁ s₁₂ := S.inv.pk.trans (pk₅.trans (pk₆.trans (pk₈.trans (pk₉.trans (pk₁₀.trans (pk₁₁.trans
    (PK.ofUpd u₁₂)))))))
  -- Our caller's registers, in their slots.
  have fd : Frame [⟨c.D, c.n⟩] s₁₀.mem s₁₁.mem := by
    rw [m₁₁]
    exact writeBytes_frame _ _ _ (by
      rw [List.length_map, Proof.Cmac.bytesAt_length]; exact Region.contains_self _ _)
  have f₄₅ : Frame (mutR c) s₄.mem s₅.mem :=
    f₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨c.W, 128⟩, by simp, Region.sub_prefix (by decide)⟩
  have f₆₉ : Frame (mutR c) s₆.mem s₉.mem := by rw [← m₈]; exact f₉.sub (mutR_oR (by decide))
  have f₉₁₁ : Frame (mutR c) s₉.mem s₁₁.mem := by
    rw [← m₁₀]
    refine fd.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact sub_data
  have fm : Frame (mutR c) s₁.mem s₁₂.mem := by
    rw [u₁₂.mem]
    exact ((((S.inv.frame.sub mutR_wR).trans f₄₅).trans (f₆.sub mutR_ctrR)).trans f₆₉).trans f₉₁₁
  refine WP.mono (exit_wp L E₁₂ (saved_mut L fm S.en.saved) (by rw [pk₁₂.sp, S.en.sp]))
    fun s₁₃ ⟨ab, m₁₃, a0₁₃⟩ => ⟨ab, ?_⟩
  -- The IVs, the plaintext and the result.
  have hV : bytesAt s₉.mem c.W 16 = bytesAt s.mem c.V 16 := by
    have := v₆.trans v₅
    rw [BitVec.add_zero] at this
    rw [v₉, m₈, this]
  have hP : bytesAt s₉.mem c.D c.n = Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem c.C c.R)
      (Spec.Siv.counter (bytesAt s.mem c.V 16)) (bytesAt s.mem c.D c.n) := by
    rw [wf₉.data L, m₈, d₆, v₅, wf₅.ctxCiph L, wf₅.data L]
  have hT : bytesAt s₉.mem (c.W + BitVec.ofNat 64 tO) 16 = Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem c.C c.R)
      (Spec.Siv.s2vAcc (Spec.Siv.ctxMac s.mem c.C c.R) (Spec.Siv.components 64 s.mem c.A c.N))
      (Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem c.C c.R) (Spec.Siv.counter (bytesAt s.mem c.V 16))
        (bytesAt s.mem c.D c.n)) := by
    rw [t₉, m₈, mac₆, a₆, a₅, acc₄, ← hP, wf₉.data L, m₈]
  refine ⟨?_, ?_⟩
  · rw [a0₁₃, u₁₂.gpr, s0₁₁, s0₁₀, hV, hT]
  · rw [m₁₃, u₁₂.mem, m₁₁, m₁₀, hV, hT, hP]
    have key : ∀ xs : List Byte, xs.length = c.n → bytesAt (writeBytes s₉.mem c.D xs) c.D c.n = xs := by
      intro xs hx
      have := Proof.AesCcm.bytesAt_writeBytes_base s₉.mem c.D xs (n := c.n) (by omega) hn
      rwa [hx, List.drop_eq_nil_of_le (by rw [Proof.Cmac.bytesAt_length]), List.append_nil] at this
    exact key _ (by rw [List.length_map, ← hP, Proof.Cmac.bytesAt_length])

end VG.Proof.AesSiv.RISCV64
