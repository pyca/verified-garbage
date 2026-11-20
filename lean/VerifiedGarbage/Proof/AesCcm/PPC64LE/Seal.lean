module

import VerifiedGarbage.Proof.AesCcm.PPC64LE.Ctrs
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Mac
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Crypt
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Impl.AesCcm.PPC64LE
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Header
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Entry
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Env
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill

/-! ### `AesCcm.PPC64LE.Exit`, which this module and modules that import it used -/

section

/-!
# AES-CCM on PPC64LE: the exit

Untrusted: everything here is checked by Lean. `restore` reloads the return
address and our caller's registers from the slots the entry filled at
`W + 128` (`exit_wp`), `r14`, the base, last.
-/

@[expose] public section

namespace VG.Proof.AesCcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCcm.PPC64LE
open VG.PPC64LE.Spill (Saved restoreCode restore_wp)
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_ld wp_mtlr)

theorem saved_sub : ∀ p ∈ saved, p ∈ savedL := fun _ hp => List.mem_cons_of_mem _ hp

theorem other_of_preserved : ∀ r ∈ preserved, r ∉ saved.map Prod.fst → r ∈ otherRegs := by decide

theorem saved_ne_r0 : ∀ p ∈ saved, p.1 ≠ .r0 := by decide

/-- `restore`: our caller's registers and return address back, for `s₀` the
state at the entry. -/
theorem exit_wp {c : Cx} {s₀ s : State} (E : Env c s) (sv : Saved c.W (saveG s₀) savedL s.mem)
    (hsp : s.sp = s₀.sp) (ho : ∀ r ∈ otherRegs, s.gpr r = s₀.gpr r) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .r3 = s.gpr .r3 := by
  unfold restore
  simp only [List.cons_append, List.nil_append]
  refine wp_ld (a := c.W + BitVec.ofNat 64 lrO) (by decide) (by decide) (by rw [E.r14])
    (E.perm.wR (by decide)) fun s₁ u₁ => wp_mtlr fun s₂ u₂ => ?_
  change WP isa (.block (restoreCode .r14 saved)) s₂ _
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have g₂ : ∀ r, r ≠ .r0 → s₂.gpr r = s.gpr r := fun r h => by rw [u₂.gpr, u₁.other _ h]
  have sv₂ : Saved c.W (saveG s₀) saved s₂.mem := by rw [m₂]; exact sv.sub saved_sub
  refine WP.mono (restore_wp (b := .r14) (B := c.W) (by decide) (by rw [g₂ _ (by decide), E.r14]) (by decide)
    (by decide) (fun p hp => by
      have := saved_bound p hp
      rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]
      exact E.perm.wR (by omega_using [this])) sv₂) fun s' R => ?_
  have lr₂ : s₂.lr = s₀.lr := by
    rw [u₂.lr, u₁.gpr, sv (.r0, lrO) List.mem_cons_self]
    simp [saveG, State.write]
  refine ⟨⟨fun r hr => ?_, by rw [R.sp, u₂.sp, u₁.sp, hsp], by rw [R.lr, lr₂]⟩, by rw [R.mem, m₂],
    by rw [R.other _ (by decide), g₂ _ (by decide)]⟩
  by_cases hs : r ∈ saved.map Prod.fst
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
    rw [R.gpr p hp]
    simp [saveG, State.write, saved_ne_r0 p hp]
  · have hr0 : r ≠ .r0 := fun h => by subst h; exact absurd hr (by decide)
    rw [R.other r hs, g₂ r hr0, ho r (other_of_preserved r hr hs)]

end VG.Proof.AesCcm.PPC64LE

end

end

/-!
# AES-CCM on PPC64LE: `vg_aes_ccm_seal`

Untrusted: everything here is checked by Lean. `seal` is `entry`, `Ctr₀`
(`ctrs`), the MAC of the payload (`mac 0`), encrypted at `W` (`tag 0`),
counter mode over the data (`ctr`), the tag copied to `tag` (`tagOut`) and
`restore` (`seal_wp`). The lemmas about what each piece keeps serve `open`
too.
-/

@[expose] public section

namespace VG.Proof.AesCcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCcm.PPC64LE VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.PPC64LE.Spill (Saved)
open VG.Proof.AesCcm (xorFrom length_bytesAt crypt_eq take_xorFrom_zero mac_eq length_xorFrom BlockCipher)

theorem other_keep : ∀ r ∈ otherRegs, r ∈ keepRegs := by decide

theorem savedL_bound : ∀ p ∈ savedL, 128 ≤ p.2 ∧ p.2 + 8 ≤ 128 + 120 := by decide

/-- The entry keeps a buffer missing `W`. -/
theorem entry_buf {c : Cx} {s s₁ : State} (hf : Frame [entryR c.W] s.mem s₁.mem) {P : Addr} {len : Nat}
    (hP : Buf c s P len) : bytesAt s₁.mem P len = bytesAt s.mem P len :=
  Proof.Cmac.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hP.wd (by decide)) (by have := hP.lt; omega_using [this])

theorem entry_ciph {c : Cx} (L : Lay c) {s s₁ : State} (hf : Frame [entryR c.W] s.mem s₁.mem) :
    Spec.Ccm.ctxCiph s₁.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by
  unfold Spec.Ccm.ctxCiph
  rw [Proof.Cmac.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (L.k_w' (by decide)).sub_left (Region.sub_prefix L.rb)) (by have := L.rb; omega_using [this])]

theorem c0_mut (c : Cx) : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 48, 16⟩ : Region)], ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact sub_lo (by decide)

theorem ctrR_mut (c : Cx) {y : Nat} (hy : y = 0 ∨ y = 96) : ∀ r ∈ ctrR c.W y, ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact sub_lo (by decide)
  · exact sub_lo (by omega_using [hy])

/-- A part of `W` missing the regions `rs` the pieces write in `W`. -/
theorem w_keep {c : Cx} (L : Lay c) {rs : List (Nat × Nat)} {d k : Nat}
    (h : ∀ q ∈ rs, (d + k ≤ q.1 ∨ q.1 + q.2 ≤ d) ∧ q.1 + q.2 ≤ 448) (hd : d + k ≤ 448) :
    ∀ r ∈ rs.map (fun q => (⟨c.W + BitVec.ofNat 64 q.1, q.2⟩ : Region)),
      (⟨c.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
  exact L.w_w (h q hq).1 hd (h q hq).2

/-- A buffer missing `W` is kept by the regions `rs` in `W`. -/
theorem bufW_keep {c : Cx} {s : State} {P : Addr} {len : Nat} (hP : Buf c s P len) {rs : List (Nat × Nat)}
    (h : ∀ q ∈ rs, q.1 + q.2 ≤ 448) :
    ∀ r ∈ rs.map (fun q => (⟨c.W + BitVec.ofNat 64 q.1, q.2⟩ : Region)), (⟨P, len⟩ : Region).Disjoint r := by
  intro r hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
  exact hP.wd (h q hq)

theorem c0_list (W : Addr) : [(⟨W + BitVec.ofNat 64 48, 16⟩ : Region)] =
    [(48, 16)].map (fun q => (⟨W + BitVec.ofNat 64 q.1, q.2⟩ : Region)) := rfl

theorem macR_list (W : Addr) (y : Nat) : macR W y =
    [(y, 16), (32, 16), (384, 64)].map (fun q => (⟨W + BitVec.ofNat 64 q.1, q.2⟩ : Region)) := rfl

theorem ctrR_list (W : Addr) (y : Nat) : ctrR W y =
    [(64, 16), (y, 16)].map (fun q => (⟨W + BitVec.ofNat 64 q.1, q.2⟩ : Region)) := rfl

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
  refine WP.seq (WP.mono (ctrs_wp L En.env hN₁ En.r5 En.r6) fun s₂ ⟨pk₂, f₂, c₂⟩ => ?_)
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
  have sv₆ : Saved c.W (saveG s) savedL s₆.mem :=
    (saved_mut L f₁₅ En.saved).frame_in savedL_bound f₆ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.t_w.sub_right (Lay.wSub (by decide))).symm
  refine WP.mono (exit_wp (E₅.of_pk pk₆) sv₆ (by rw [pk₁₆.sp, En.sp])
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
    rw [Proof.Cmac.bytesAt_frame f₂ (bufW_keep bD₁ (by decide)) (by omega_using [hn]), entry_buf En.frame bD]
  have ha₂ : bytesAt s₂.mem c.A c.al = bytesAt s.mem c.A c.al := by
    rw [aad_mut L f₂', entry_buf En.frame (L.bufA Ar.perm)]
  have hd₄ : bytesAt s₄.mem c.D c.n = bytesAt s.mem c.D c.n := by
    have fM := M.frame
    rw [macR_list] at fM
    rw [ctrR_list] at f₄
    rw [Proof.Cmac.bytesAt_frame f₄ (bufW_keep bD₁ (by decide)) (by omega_using [hn]),
      Proof.Cmac.bytesAt_frame fM (bufW_keep bD₁ (by decide)) (by omega_using [hn]), hd₂]
  have w₅ : bytesAt s₅.mem c.W c.tl = bytesAt s₄.mem c.W c.tl := by
    have h := Proof.Cmac.bytesAt_frame (p := c.W + BitVec.ofNat 64 0) (n := c.tl) f₅
      (crR_disj L (.inl (by omega_using [ht16]))) (by omega_using [ht16])
    rwa [BitVec.add_zero] at h
  have e0 : c.W + BitVec.ofNat 64 0 = c.W := BitVec.add_zero c.W
  have M' := M.out
  rw [e0] at h₄ M'
  have hY : (bytesAt s₃.mem c.W 16).length = 16 := length_bytesAt _ _ _
  have d₆ : bytesAt s₆.mem c.D c.n = bytesAt s₅.mem c.D c.n :=
    Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.t_d.symm) (by omega_using [hn])
  simp only [Spec.Ccm.encryptWith, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · rw [hm, d₆, h₅, k₄, hd₄, crypt_eq (hBC _)]
  · rw [hm, t₆, w₅, Proof.AesCcm.bytesAt_prefix s₄.mem c.W L.t16, h₄, k₃,
      take_xorFrom_zero (hBC _) _ hY L.t16, M', k₂, ha₂, hd₂, mac_eq _ _ (by rw [hnl]; have := L.h13; omega_using [this])]
    rfl

/-- `vg_aes_ccm_seal`. -/
theorem seal_wp {s : State} (h : sealPPC64LE.pre s) :
    WP isa «seal» s fun s' => abiPreserved s s' ∧ sealPPC64LE.post s s' := by
  have A := args_of_seal h
  refine WP.mono (seal_wp' A.1 A.2) fun s' ⟨ga, hp⟩ => ⟨ga, ?_⟩
  simp only [sealPPC64LE]
  simpa only [cxOf] using hp

end VG.Proof.AesCcm.PPC64LE
