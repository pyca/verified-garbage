module

import VerifiedGarbage.Proof.AesCcm.RISCV64.Exit
import VerifiedGarbage.Proof.AesCcm.RISCV64.Ctrs
import VerifiedGarbage.Proof.AesCcm.RISCV64.Mac
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Tag
import VerifiedGarbage.Proof.AesCcm.RISCV64.Crypt
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Impl.AesCcm.RISCV64
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Absorb
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Entry
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Env
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill

/-!
# AES-CCM on RISCV64: `vg_aes_ccm_seal`

Untrusted: everything here is checked by Lean. `seal` is `entry`, `Ctr₀`
(`ctrs`), the MAC of the payload (`mac 0`), encrypted at `W` (`tag 0`),
counter mode over the data (`ctr`), the tag copied to `tag` (`tagOut`) and
`restore` (`seal_wp`). The lemmas about what each piece keeps serve `open`
too.
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesCcm.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.RISCV64.Spill (Saved)
open VG.Proof.AesCcm (xorFrom length_bytesAt crypt_eq take_xorFrom_zero mac_eq length_xorFrom BlockCipher)

theorem other_keep : ∀ r ∈ otherRegs, r ∈ keepRegs := by decide

/-- The entry keeps a buffer missing `W`. -/
theorem entry_buf {c : Cx} {s s₁ : State} (hf : Frame [entryR c.W] s.mem s₁.mem) {P : Addr} {len : Nat}
    (hP : Buf c s P len) : bytesAt s₁.mem P len = bytesAt s.mem P len :=
  Proof.Cmac.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hP.wd (by decide)) (by have := hP.lt; omega)

theorem entry_ciph {c : Cx} (L : Lay c) {s s₁ : State} (hf : Frame [entryR c.W] s.mem s₁.mem) :
    Spec.Ccm.ctxCiph s₁.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by
  unfold Spec.Ccm.ctxCiph
  rw [Proof.Cmac.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (L.k_w' (by decide)).sub_left (Region.sub_prefix L.rb)) (by have := L.rb; omega)]

theorem c0_mut (c : Cx) : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 48, 16⟩ : Region)], ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact sub_lo (by decide)

theorem ctrR_mut (c : Cx) {y : Nat} (hy : y = 0 ∨ y = 96) : ∀ r ∈ ctrR c.W y, ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_lo (by decide)
  · exact sub_lo (by omega)
  · exact sub_hi (by decide) (by decide)

/-- A part of `W` missing the regions `rs` the pieces write in `W`. -/
theorem w_keep {c : Cx} (L : Lay c) {rs : List (Nat × Nat)} {d k : Nat}
    (h : ∀ q ∈ rs, (d + k ≤ q.1 ∨ q.1 + q.2 ≤ d) ∧ q.1 + q.2 ≤ 2560) (hd : d + k ≤ 2560) :
    ∀ r ∈ rs.map (fun q => (⟨c.W + BitVec.ofNat 64 q.1, q.2⟩ : Region)),
      (⟨c.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
  exact L.w_w (h q hq).1 hd (h q hq).2

/-- A buffer missing `W` is kept by the regions `rs` in `W`. -/
theorem bufW_keep {c : Cx} {s : State} {P : Addr} {len : Nat} (hP : Buf c s P len) {rs : List (Nat × Nat)}
    (h : ∀ q ∈ rs, q.1 + q.2 ≤ 2560) :
    ∀ r ∈ rs.map (fun q => (⟨c.W + BitVec.ofNat 64 q.1, q.2⟩ : Region)), (⟨P, len⟩ : Region).Disjoint r := by
  intro r hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
  exact hP.wd (h q hq)

theorem c0_list (W : Addr) : [(⟨W + BitVec.ofNat 64 48, 16⟩ : Region)] =
    [(48, 16)].map (fun q => (⟨W + BitVec.ofNat 64 q.1, q.2⟩ : Region)) := rfl

theorem macR_list (W : Addr) (y : Nat) : macR W y =
    [(y, 16), (32, 16), (384, 2176)].map (fun q => (⟨W + BitVec.ofNat 64 q.1, q.2⟩ : Region)) := rfl

theorem ctrR_list (W : Addr) (y : Nat) : ctrR W y =
    [(64, 16), (y, 16), (384, 2048)].map (fun q => (⟨W + BitVec.ofNat 64 q.1, q.2⟩ : Region)) := rfl

/-- Our caller's registers, kept in their slots by writes to `mutR`. -/
theorem saved_mut {c : Cx} (L : Lay c) {g : Reg → BitVec 64} {m m' : Mem} (hf : Frame (mutR c) m m')
    (h : Saved c.W g savedL m) : Saved c.W g savedL m' :=
  h.frame_in savedL_bound hf (kept_mut L ⟨by decide, by decide⟩)

/-- `vg_aes_ccm_seal`, for its arguments. -/
theorem seal_wp' {c : Cx} {N : Addr} {s : State} (Ar : Args c N s) (hTw : Covers [⟨c.T, c.tl⟩] s.wr) :
    WP isa «seal» s fun s' => abiPreserved s s' ∧
      Spec.Ccm.encryptWith (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl) (bytesAt s.mem c.D c.n)
        (bytesAt s.mem c.A c.al) = (bytesAt s'.mem c.D c.n, bytesAt s'.mem c.T c.tl) := by
  have L := Ar.lay
  have ht16 := L.t16
  have hn := L.n_lt
  unfold «seal»
  refine WP.seq (WP.mono (entry_wp Ar) fun s₁ En => ?_)
  have hN₁ : Buf c s₁ N c.nl := Ar.nonce.of_eq En.rd En.wr
  refine WP.seq (WP.mono (ctrs_wp L En.env hN₁ En.a2 En.a3) fun s₂ ⟨pk₂, f₂, c₂⟩ => ?_)
  rw [entry_buf En.frame Ar.nonce] at c₂
  have hnl : (bytesAt s.mem N c.nl).length = c.nl := length_bytesAt _ _ _
  have f₂' : Frame (mutR c) s₁.mem s₂.mem := f₂.sub (c0_mut c)
  have E₂ := En.env.of_pk pk₂
  refine WP.seq (WP.mono (mac_wp L E₂ (En.slots.mut L f₂') hnl c₂ (.inl rfl)) fun s₃ M => ?_)
  have c₃ : bytesAt s₃.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N c.nl) 0 := by
    have fM := M.frame
    rw [macR_list] at fM
    rw [Proof.Cmac.bytesAt_frame fM (w_keep L (by decide) (by decide)) (by decide), c₂]
  have E₃ := E₂.of_pk M.pk
  refine WP.seq (WP.mono (tag_wp L E₃ hnl c₃ (.inl rfl)) fun s₄ ⟨pk₄, _, f₄, h₄⟩ => ?_)
  have c₄ : bytesAt s₄.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N c.nl) 0 := by
    rw [ctrR_list] at f₄
    rw [Proof.Cmac.bytesAt_frame f₄ (w_keep L (by decide) (by decide)) (by decide), c₃]
  have E₄ := E₃.of_pk pk₄
  refine WP.seq (WP.mono (ctr_wp L E₄ hnl c₄) fun s₅ ⟨pk₅, f₅, h₅⟩ => ?_)
  have E₅ := E₄.of_pk pk₅
  have f₁₃ : Frame (mutR c) s₁.mem s₃.mem := f₂'.trans (M.frame.sub (macR_mut (.inl rfl)))
  have f₁₄ : Frame (mutR c) s₁.mem s₄.mem := f₁₃.trans (f₄.sub (ctrR_mut c (.inl rfl)))
  have f₁₅ : Frame (mutR c) s₁.mem s₅.mem := f₁₄.trans (f₅.sub (crR_mut c))
  have pk₁₅ : PK s₁ s₅ := pk₂.trans (M.pk.trans (pk₄.trans pk₅))
  have wr₅ : s₅.wr = s.wr := by rw [pk₁₅.wr, En.wr]
  refine WP.seq (WP.mono (tagOut_wp L E₅ (En.slots.mut L f₁₅) (by rw [wr₅]; exact hTw))
    fun s₆ ⟨pk₆, f₆, t₆⟩ => ?_)
  have pk₁₆ : PK s₁ s₆ := pk₁₅.trans pk₆
  have sv₆ : Saved c.W s.gpr savedL s₆.mem :=
    (saved_mut L f₁₅ En.saved).frame_in savedL_bound f₆ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.t_w.sub_right (Lay.wSub (by decide))).symm
  refine WP.mono (exit_wp L (E₅.of_pk pk₆) sv₆ (by rw [pk₁₆.sp, En.sp])
    (fun r hr => by rw [pk₁₆.gpr r (other_keep r hr), En.others r hr])) fun s' ⟨abi, hm, _⟩ => ⟨abi, ?_⟩
  -- The ciphertext and the tag.
  have hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m c.K c.R) := fun _ x => Proof.Cmac.aesWith_length _ _ x
  have k₁ := entry_ciph L En.frame
  have k₂ : Spec.Ccm.ctxCiph s₂.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [ciph_mut L f₂', k₁]
  have k₃ : Spec.Ccm.ctxCiph s₃.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [ciph_mut L f₁₃, k₁]
  have k₄ : Spec.Ccm.ctxCiph s₄.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [ciph_mut L f₁₄, k₁]
  have bD := L.bufD Ar.perm
  have bD₁ : Buf c s₁ c.D c.n := bD.of_eq En.rd En.wr
  have hd₂ : bytesAt s₂.mem c.D c.n = bytesAt s.mem c.D c.n := by
    rw [c0_list] at f₂
    rw [Proof.Cmac.bytesAt_frame f₂ (bufW_keep bD₁ (by decide)) (by omega), entry_buf En.frame bD]
  have ha₂ : bytesAt s₂.mem c.A c.al = bytesAt s.mem c.A c.al := by
    rw [aad_mut L f₂', entry_buf En.frame (L.bufA Ar.perm)]
  have hd₄ : bytesAt s₄.mem c.D c.n = bytesAt s.mem c.D c.n := by
    have fM := M.frame
    rw [macR_list] at fM
    rw [ctrR_list] at f₄
    rw [Proof.Cmac.bytesAt_frame f₄ (bufW_keep bD₁ (by decide)) (by omega),
      Proof.Cmac.bytesAt_frame fM (bufW_keep bD₁ (by decide)) (by omega), hd₂]
  have w₅ : bytesAt s₅.mem c.W c.tl = bytesAt s₄.mem c.W c.tl := by
    have h := Proof.Cmac.bytesAt_frame (p := c.W + BitVec.ofNat 64 0) (n := c.tl) f₅
      (crR_disj L (.inl (by omega))) (by omega)
    rwa [BitVec.add_zero] at h
  have e0 : c.W + BitVec.ofNat 64 0 = c.W := BitVec.add_zero c.W
  have M' := M.out
  rw [e0] at h₄ M'
  have hY : (bytesAt s₃.mem c.W 16).length = 16 := length_bytesAt _ _ _
  have d₆ : bytesAt s₆.mem c.D c.n = bytesAt s₅.mem c.D c.n :=
    Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.t_d.symm) (by omega)
  simp only [Spec.Ccm.encryptWith, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · rw [hm, d₆, h₅, k₄, hd₄, crypt_eq (hBC _)]
  · rw [hm, t₆, w₅, Proof.AesCcm.bytesAt_prefix s₄.mem c.W L.t16, h₄, k₃,
      take_xorFrom_zero (hBC _) _ hY L.t16, M', k₂, ha₂, hd₂, mac_eq _ _ (by rw [hnl]; have := L.h13; omega)]
    rfl

/-- `vg_aes_ccm_seal`. -/
theorem seal_wp {s : State} (h : sealRISCV64.pre s) :
    WP isa «seal» s fun s' => abiPreserved s s' ∧ sealRISCV64.post s s' := by
  have A := args_of_seal h
  refine WP.mono (seal_wp' A.1 A.2) fun s' ⟨ga, hp⟩ => ⟨ga, ?_⟩
  simp only [sealRISCV64]
  simpa only [cxOf] using hp

end VG.Proof.AesCcm.RISCV64
