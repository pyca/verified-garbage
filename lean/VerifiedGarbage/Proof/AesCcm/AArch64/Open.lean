import VerifiedGarbage.Proof.AesCcm.AArch64.Seal

/-!
# AES-CCM on AArch64: `vg_aes_ccm_open`

Untrusted: everything here is checked by Lean. `open` is `entry`, `Ctr₀`
(`ctrs`), counter mode over the data (`ctr`), which decrypts it, the MAC of
the plaintext (`mac 96`), encrypted at `W + 96` (`tag 96`), the comparison
with the received tag at `tag`, whose address the entry keeps in `W`
(`loadTag_ok`, `cmp`), the result, the data masked with it (`mask`) and
`restore` (`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)
open VG.Proof.AesGcm.AArch64 (SavedAt exit_ok covers_left Others)
open VG.Impl.AesGcm.AArch64 (imm)
open VG.Proof.AesCcm (xorFrom length_bytesAt crypt_eq take_xorFrom_zero mac_eq length_xorFrom BlockCipher
  cryptTag_eq_iff)

theorem cmpR_mut (c : Cx) : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 256, 32⟩ : Region)], ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact sub_hi (by decide) (by decide)

theorem maskR_mut (c : Cx) : ∀ r ∈ [(⟨c.D, c.n⟩ : Region)], ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact sub_data

/-- `x0 := 1 − x10`. -/
theorem ret_ok {s : State} {b : Bool} (h10 : s.gpr .x10 = BitVec.ofNat 64 (if b then 0 else 1)) :
    WP isa (.block [imm .x0 1, .sub .x .x0 .x0 .x10]) s fun s' =>
      s'.gpr .x0 = BitVec.ofNat 64 (if b then 1 else 0) ∧ Others [.x0] s s' ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [gpr_write, BitVec.setWidth_eq, ite_true, h10]; cases b <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; simp [gpr_write, hr]

theorem length_chain {ciph : Spec.Ccm.Cipher} (hc : BlockCipher ciph) :
    ∀ (ms : List (List Byte)) (c : List Byte), c.length = 16 → (Spec.Cmac.chain ciph c ms).length = 16
  | [], _, h => h
  | _ :: ms, _, _ => length_chain hc ms _ (hc _)

/-- `vg_aes_ccm_open`, for its arguments. -/
theorem open_wp' (v : Proof.CmacAes.AArch64.UpdateImpl) {c : Cx} {N : Addr} {s : State} (Ar : Args c N s) :
    WP isa («open» v.callee v.ctr.callee) s fun s' => GprAbi s s' ∧
      openOut (Spec.Ccm.decryptWith (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl)
          (bytesAt s.mem c.D c.n) (bytesAt s.mem c.A c.al) (bytesAt s.mem c.T c.tl)) (s'.gpr .x0)
        (bytesAt s'.mem c.D c.n) c.n := by
  have L := Ar.lay
  have ht16 := L.t16
  refine WP.seq (WP.mono (entry_ok Ar) fun s₁ En => ?_)
  have hN₁ : Buf c s₁ N c.nl := Ar.nonce.of_eq En.rd En.wr
  refine WP.seq (WP.mono (ctrs_ok L En.env hN₁ En.x2 En.x3) fun s₂ ⟨E₂, f₂, c₂, rd₂, wr₂⟩ => ?_)
  rw [entry_buf En.frame Ar.nonce] at c₂
  have hnl : (bytesAt s.mem N c.nl).length = c.nl := length_bytesAt _ _ _
  have f₂' : Frame (mutR c) s₁.mem s₂.mem := f₂.sub (frame_ctrs_mut c)
  refine WP.seq (WP.mono (ctr_ok v.ctr L E₂ hnl c₂) fun s₃ ⟨E₃, rd₃, wr₃, f₃, h₃⟩ => ?_)
  have f₁₃ : Frame (mutR c) s₁.mem s₃.mem := f₂'.trans (f₃.sub (ctrR_mut c))
  have S₃ := En.slots.mut L f₁₃
  have c₃ : bytesAt s₃.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N c.nl) 0 := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₃ (ctrR_disj L (.inl (by decide))) (by decide), c₂]
  refine WP.seq (WP.mono (mac_ok v L E₃ S₃ hnl c₃ (.inr rfl)) fun s₄ M => ?_)
  have c₄ : bytesAt s₄.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N c.nl) 0 := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame M.frame (macR_c0 L (.inr rfl)) (by decide), c₃]
  refine WP.seq (WP.mono (tag_ok v.ctr L M.env hnl c₄ (.inr rfl)) fun s₅ ⟨E₅, rd₅, wr₅, f₅, h₅⟩ => ?_)
  have f₁₄ : Frame (mutR c) s₁.mem s₄.mem := f₁₃.trans (M.frame.sub (macR_mut (.inr rfl)))
  have f₁₅ : Frame (mutR c) s₁.mem s₅.mem := f₁₄.trans (f₅.sub (tagR_mut c (.inr rfl)))
  -- The address of the received tag, from its slot.
  refine WP.seq (WP.mono (loadTag_ok E₅ (En.slots.mut L f₁₅) .x12) fun s₉ ⟨x12₉, og₉, m₉, sp₉, rd₉, wr₉⟩ => ?_)
  have E₉ : Env c s₉ := E₅.others og₉ (by decide) sp₉ rd₉ wr₉
  refine WP.seq (WP.mono (cmp_ok L E₉ x12₉) fun s₆ ⟨x10₆, E₆, og₆, f₆⟩ => ?_)
  rw [m₉] at x10₆ f₆
  refine WP.seq (WP.mono (ret_ok (b := decide (bytesAt s₅.mem (c.W + BitVec.ofNat 64 96) c.tl =
      bytesAt s₅.mem c.T c.tl)) (by rw [x10₆]; congr 1; simp)) fun s₇ ⟨x0₇, og₇, hm₇, sp₇, rd₇, wr₇⟩ => ?_)
  have E₇ : Env c s₇ := E₆.others og₇ (by decide) sp₇ rd₇ wr₇
  refine WP.seq (WP.mono (mask_ok L E₇ (ok := decide (bytesAt s₅.mem (c.W + BitVec.ofNat 64 96) c.tl =
      bytesAt s₅.mem c.T c.tl)) (by rw [og₇ _ (by decide), x10₆]; congr 1; simp))
    fun s₈ ⟨hd₈, E₈, og₈, f₈⟩ => ?_)
  have f₁₆ : Frame (mutR c) s₁.mem s₆.mem := f₁₅.trans (f₆.sub (cmpR_mut c))
  have f₁₈ : Frame (mutR c) s₁.mem s₈.mem := by
    rw [hm₇] at f₈; exact f₁₆.trans (f₈.sub (maskR_mut c))
  have sv₈ : SavedAt s₈.mem c.W s := saved_mut L f₁₈ En.saved
  refine WP.mono (exit_ok E₈.x19 (by rw [E₈.sp, Ar.sp]) (covers_left E₈.perm.w) sv₈)
    fun s' ⟨ga, hm, x0', _, _⟩ => ⟨ga, ?_⟩
  -- The result.
  have hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m c.K c.R) := fun _ x => Proof.Cmac.aesWith_length _ _ x
  have k₁ := entry_ciph L En.frame
  have k₂ : Spec.Ccm.ctxCiph s₂.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [ciph_mut L f₂', k₁]
  have k₃ : Spec.Ccm.ctxCiph s₃.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [ciph_mut L f₁₃, k₁]
  have k₄ : Spec.Ccm.ctxCiph s₄.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [ciph_mut L f₁₄, k₁]
  have hd₂ : bytesAt s₂.mem c.D c.n = bytesAt s.mem c.D c.n := by
    rw [Proof.AesGcm.AArch64.bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.d_w' (by decide)) (by have := L.n_lt; omega_arith),
      entry_buf En.frame (L.bufD Ar.perm)]
  have ha₃ : bytesAt s₃.mem c.A c.al = bytesAt s.mem c.A c.al := by
    rw [aad_mut L f₁₃, entry_buf En.frame (L.bufA Ar.perm)]
  have hpt : bytesAt s₃.mem c.D c.n =
      Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem N c.nl) (bytesAt s.mem c.D c.n) := by
    rw [h₃, k₂, hd₂, crypt_eq (hBC _)]
  have hd₇ : bytesAt s₇.mem c.D c.n = bytesAt s₃.mem c.D c.n := by
    rw [hm₇, Proof.AesGcm.AArch64.bytesAt_frame f₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.d_w' (by decide)) (by have := L.n_lt; omega_arith),
      Proof.AesGcm.AArch64.bytesAt_frame f₅ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact L.d_w' (by decide)) (by have := L.n_lt; omega_arith),
      buf_macR (L.bufD M.env.perm) (by decide) M.frame]
  have hrecv : bytesAt s₅.mem c.T c.tl = bytesAt s.mem c.T c.tl := by
    rw [tag_mut L f₁₅ ht16, Proof.AesGcm.AArch64.bytesAt_frame En.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.t_w.sub_right (Lay.wSub (by decide))) (by omega_arith)]
  have hY := congrArg List.length h₅
  rw [length_bytesAt, length_xorFrom] at hY
  have hcomp : bytesAt s₅.mem (c.W + BitVec.ofNat 64 96) c.tl =
      Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl)
        (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl) (bytesAt s.mem c.A c.al)
          (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem N c.nl) (bytesAt s.mem c.D c.n))) := by
    rw [show c.W + BitVec.ofNat 64 96 = c.W + BitVec.ofNat 64 uO from rfl, Proof.AesCcm.bytesAt_prefix s₅.mem _ L.t16, h₅, k₄, take_xorFrom_zero (hBC _) _ hY.symm L.t16, M.out, k₃,
      ha₃, hpt, ← mac_eq _ _ (by rw [hnl]; have := L.h13; omega_arith)]
  have hmlen : (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl) (bytesAt s.mem c.A c.al)
      (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem N c.nl) (bytesAt s.mem c.D c.n))).length =
      c.tl := by
    rw [mac_eq _ _ (by rw [hnl]; have := L.h13; omega_arith), List.length_take,
      length_chain (hBC _) _ _ (by simp [Spec.Cmac.zeros])]
    omega_arith
  have hiff := cryptTag_eq_iff (hBC s.mem) L.t16 (bytesAt s.mem N c.nl) hmlen (length_bytesAt s.mem c.T c.tl)
  simp only [openOut, Spec.Ccm.decryptWith]
  rw [hcomp, hrecv] at hd₈ x0₇
  by_cases he : Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl)
      (bytesAt s.mem c.T c.tl) = Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl)
        (bytesAt s.mem c.A c.al) (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem N c.nl)
          (bytesAt s.mem c.D c.n))
  · have hq : Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl)
        (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl) (bytesAt s.mem c.A c.al)
          (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem N c.nl) (bytesAt s.mem c.D c.n))) =
        bytesAt s.mem c.T c.tl := hiff.mpr he.symm
    simp only [he, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · rw [x0', og₈ _ (by decide), x0₇]; simp [hq]
    · rw [hm, hd₈]; simp only [hq, decide_true, ↓reduceIte]; rw [hd₇, hpt]
  · have hq : ¬ Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl)
        (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl) (bytesAt s.mem c.A c.al)
          (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem N c.nl) (bytesAt s.mem c.D c.n))) =
        bytesAt s.mem c.T c.tl := fun h => he (hiff.mp h).symm
    simp only [he, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · rw [x0', og₈ _ (by decide), x0₇]; simp [hq]
    · rw [hm, hd₈]; simp only [hq, decide_false, Bool.false_eq_true, ↓reduceIte]

/-- `vg_aes_ccm_open`. -/
theorem open_wp (v : Proof.CmacAes.AArch64.UpdateImpl) {s : State} (h : openAArch64.pre s) :
    WP isa («open» v.callee v.ctr.callee) s fun s' => GprAbi s s' ∧ openAArch64.post s s' := by
  have Ar := args_of_open h
  refine WP.mono (open_wp' v Ar) fun s' ⟨ga, hp⟩ => ⟨ga, ?_⟩
  exact hp

end VG.Proof.AesCcm.AArch64
