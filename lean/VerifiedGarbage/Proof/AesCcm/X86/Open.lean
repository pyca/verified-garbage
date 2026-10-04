import VerifiedGarbage.Proof.AesCcm.X86.Seal
import VerifiedGarbage.Proof.AesCcm.X86.Mask

/-!
# AES-CCM on x86: `vg_aes_ccm_open`

Untrusted: everything here is checked by Lean. `open` is the start (the
entry and `Ctr₀`), counter mode over the data, which decrypts it (`ctr_ok`),
the MAC of the plaintext at `W + 96` (`mac_ok`), encrypted (`tag_ok`), the
received tag padded (AES-GCM's `recv_ok`) and compared with it without a branch
(AES-GCM's `cmp_ok`), the data masked (`mask_ok`) and the exit
(`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot cmp recv tglO tpO rO vO)
open VG.Proof.AesGcm.X86 (w64 slotv SavedAt exit_ok ofNat_toNat32 length_bytesAt covers_left WEnv)

theorem ofNat_ite (p : Prop) [Decidable p] :
    BitVec.ofNat 32 (if p then 1 else 0) = if decide p = true then 1 else 0 := by
  by_cases h : p <;> simp [h]

theorem append_zeros_iff {x y : List Byte} {k : Nat} :
    x ++ Spec.Gcm.zeros k = y ++ Spec.Gcm.zeros k ↔ x = y :=
  ⟨List.append_cancel_right, fun h => by rw [h]⟩

/-- `vg_aes_ccm_open`, for its arguments. -/
theorem open_wp' (v : Ctr32Impl) {s : State} {K W SP N A D T : BitVec 32} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D T R nl al n tl) (hsp : s.gpr .esp = SP) (a0 : arg s 0 = K)
    (a1 : arg s 1 = BitVec.ofNat 32 R) (a2 : arg s 2 = N) (a3 : arg s 3 = BitVec.ofNat 32 nl) (a4 : arg s 4 = A)
    (a5 : arg s 5 = BitVec.ofNat 32 al) (a6 : arg s 6 = D) (a7 : arg s 7 = BitVec.ofNat 32 n) (a8 : arg s 8 = T)
    (a9 : arg s 9 = BitVec.ofNat 32 tl) (a10 : arg s 10 = W) :
    WP isa («open» v.callee v.suffix) s fun s' => abiPreserved s s' ∧
      match Spec.Ccm.decryptWith (Spec.Ccm.ctxCiph s.mem (w64 K) R) tl (bytesAt s.mem (w64 N) nl)
          (bytesAt s.mem (w64 D) n) (bytesAt s.mem (w64 A) al) (bytesAt s.mem (w64 T) tl) with
      | some pt => s'.gpr .eax = 1 ∧ bytesAt s'.mem (w64 D) n = pt
      | none => s'.gpr .eax = 0 ∧ bytesAt s'.mem (w64 D) n = Spec.Ccm.zeros n := by
  have L := Ar.lay
  have hnl := length_bytesAt s.mem (w64 N) nl
  have h7' : 7 ≤ (bytesAt s.mem (w64 N) nl).length := by rw [hnl]; exact Ar.h7
  have h13' : (bytesAt s.mem (w64 N) nl).length ≤ 13 := by rw [hnl]; exact Ar.h13
  have ht16 := Ar.t16
  have ht4 := Ar.t4
  refine seq_assoc (WP.seq (WP.mono (start_ok Ar hsp a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) fun s₂ St => ?_))
  -- Counter mode: the plaintext.
  have C₂ : CtrCtx K W SP s₂ R (bytesAt s.mem (w64 N) nl) D n :=
    ⟨L, Ar.rounds, h7', h13', by rw [hnl]; exact Ar.hn, Ar.n32, St.c0, Ar.data.of_eq St.rd St.wr,
      by rw [St.wr]; exact Ar.dw, Ar.dk⟩
  refine WP.seq (WP.mono (ctr_ok v C₂ St.env St.slots.ctx St.slots.rounds St.slots.data St.slots.len)
    fun s₃ ⟨E₃, rd₃, wr₃, f₃, h₃⟩ => ?_)
  have f₂₃ : Frame (mutR W SP D n) s₂.mem s₃.mem := frame_toMut f₃ (inMut_ctrR W SP D n)
  obtain ⟨S₃, -, -, -, -⟩ := St.mut Ar f₂₃
  have hc₃ : bytesAt s₃.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem (w64 N) nl) 0 :=
    C₂.c0_kept f₃
  have rd₃' : s₃.rd = s.rd := by rw [rd₃, St.rd]
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, St.wr]
  -- The MAC of the plaintext.
  refine WP.seq (WP.mono (mac_ok v L E₃ Ar.rounds S₃ hnl Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.al32 Ar.hn
    Ar.n32 hc₃ (y := 96) (.inr rfl) (Ar.aad.of_eq rd₃' wr₃') (Ar.data.of_eq rd₃' wr₃')) fun s₄ A₄ => ?_)
  have f₂₄ : Frame (mutR W SP D n) s₂.mem s₄.mem := f₂₃.trans (frame_toMut A₄.frame (inMut_macR W SP D n (.inr rfl)))
  obtain ⟨S₄, -, -, -, -⟩ := St.mut Ar f₂₄
  have hc₄ : bytesAt s₄.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem (w64 N) nl) 0 := by
    rw [c0_kept (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) A₄.frame, hc₃]
  -- The tag of the plaintext.
  refine WP.seq (WP.mono (tag_ok v L A₄.env Ar.rounds S₄.ctx S₄.rounds h7' h13' hc₄ (y := 96) (.inr rfl))
    fun s₅ ⟨E₅, rd₅, wr₅, f₅, h₅⟩ => ?_)
  have f₂₅ : Frame (mutR W SP D n) s₂.mem s₅.mem := f₂₄.trans (frame_toMut f₅ (inMut_tag W SP D n (.inr rfl)))
  obtain ⟨S₅, -, -, -, -⟩ := St.mut Ar f₂₅
  have rd₅' : s₅.rd = s.rd := by rw [rd₅, A₄.rd, rd₃']
  have wr₅' : s₅.wr = s.wr := by rw [wr₅, A₄.wr, wr₃']
  -- The received tag.
  have Tb₅ := Ar.tag.of_eq rd₅' wr₅'
  refine WP.seq (WP.mono (Proof.AesGcm.X86.recv_ok ⟨E₅.ebp, E₅.perm.w, L.fw⟩ S₅.tl S₅.tp Tb₅.rd Tb₅.wrap Tb₅.w
    (by omega) ht16) fun s₆ ⟨b₆, f₆, bp₆, _, sp₆, rd₆, wr₆⟩ => ?_)
  have E₆ : Env K W SP s₆ := ⟨by rw [bp₆, E₅.ebp], by rw [sp₆, E₅.esp], E₅.perm.of_eq rd₆ wr₆⟩
  -- The comparison.
  have hv₆ : slotv s₆.mem W tglO = BitVec.ofNat 32 tl := by
    show s₆.mem.readW (w64 W + BitVec.ofNat 64 tglO) 32 = _
    rw [f₆.readW (r := ⟨w64 W + BitVec.ofNat 64 tglO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide)]
    exact S₅.tl
  refine WP.seq (WP.mono (Proof.AesGcm.X86.cmp_ok (o := uO) ⟨E₆.ebp, E₆.perm.w, L.fw⟩ hv₆ (by omega) ht16 (by decide))
    fun s₇ ⟨ax₇, f₇, bp₇, _, sp₇, rd₇, wr₇⟩ => ?_)
  rw [ofNat_ite] at ax₇
  generalize hc : decide (bytesAt s₆.mem (w64 W + BitVec.ofNat 64 uO) tl ++ Spec.Gcm.zeros (16 - tl) =
    bytesAt s₆.mem (w64 W + BitVec.ofNat 64 rO) 16) = c at ax₇
  have E₇ : Env K W SP s₇ := ⟨by rw [bp₇, E₆.ebp], by rw [sp₇, E₆.esp], E₆.perm.of_eq rd₇ wr₇⟩
  -- `ok` kept.
  obtain ⟨s₈, run₈, hm₈, bp₈, sp₈, rd₈, wr₈⟩ : ∃ s₈, runBlock isa [.store (at_ .ebp okO) .eax] s₇ = some s₈ ∧
      s₈.mem = s₇.mem.writeW (w64 W + BitVec.ofNat 64 okO) (if c = true then (1 : BitVec 32) else 0) ∧
      s₈.gpr .ebp = W ∧ s₈.gpr .esp = SP ∧ s₈.rd = s₇.rd ∧ s₈.wr = s₇.wr := by
    refine ⟨_, by crun [E₇.ebp, L.aW, E₇.perm.wW], ?_, ?_, ?_, ?_, ?_⟩
    · cmems [ax₇]
    · cregs [E₇.ebp]
    · cregs [E₇.esp]
    all_goals cmems []
  refine WP.seq (WP.of_runBlock ⟨s₈, run₈, ?_⟩)
  have E₈ : Env K W SP s₈ := ⟨bp₈, sp₈, E₇.perm.of_eq rd₈ wr₈⟩
  have f₅₈ : Frame (mutR W SP D n) s₅.mem s₈.mem := by
    rw [hm₈]
    refine (((f₆.sub fun r hr => ?_).trans (f₇.sub fun r hr => ?_)).writeW (r := wO W) (by simp) _
      (Region.contains_self _ _))
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨wT W, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
  have f₂₈ : Frame (mutR W SP D n) s₂.mem s₈.mem := f₂₅.trans f₅₈
  obtain ⟨S₈, -, -, -, -⟩ := St.mut Ar f₂₈
  have rd₈' : s₈.rd = s.rd := by rw [rd₈, rd₇, rd₆, rd₅']
  have wr₈' : s₈.wr = s.wr := by rw [wr₈, wr₇, wr₆, wr₅']
  -- The data masked.
  have hok : slotv s₈.mem W okO = if c = true then 1 else 0 := by rw [hm₈]; exact Mem.readW_writeW_self32 _ _ _
  refine WP.seq (WP.mono (mask_ok L E₈ S₈.data S₈.len Ar.n32 (Ar.data.of_eq rd₈' wr₈') (by rw [wr₈']; exact Ar.dw) hok)
    fun s₉ ⟨E₉, rd₉, wr₉, hm₉⟩ => ?_)
  have f₈₉ : Frame (mutR W SP D n) s₈.mem s₉.mem := by
    rw [hm₉]
    exact writeBytes_frame _ _ _ (by
      rw [Proof.AesCcm.X86.length_mask]; exact Region.contains_self _ _) |>.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  have f₂₉ : Frame (mutR W SP D n) s₂.mem s₉.mem := f₂₈.trans f₈₉
  obtain ⟨S₉, sv₉, -, -, rt₉⟩ := St.mut Ar f₂₉
  have hok₉ : slotv s₉.mem W okO = if c = true then 1 else 0 := by
    rw [hm₉]
    refine (writeBytes_frame _ _ _ (R := ⟨w64 D, n⟩) (by rw [length_mask]; exact Region.contains_self _ _)).readW
      (r := ⟨w64 W + BitVec.ofNat 64 okO, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide) |>.trans hok
    simp only [List.mem_singleton] at hr; subst hr; exact (Ar.data.w.sub_right (Lay.wSub (by decide))).symm
  -- `ok` returned.
  obtain ⟨s₁₀, run₁₀, hm₁₀, ax₁₀, bp₁₀, sp₁₀, rd₁₀, wr₁₀⟩ : ∃ s₁₀, runBlock isa [.mov .eax (slot okO)] s₉ = some s₁₀ ∧
      s₁₀.mem = s₉.mem ∧ s₁₀.gpr .eax = (if c = true then 1 else 0) ∧ s₁₀.gpr .ebp = W ∧ s₁₀.gpr .esp = SP ∧
      s₁₀.rd = s₉.rd ∧ s₁₀.wr = s₉.wr := by
    refine ⟨_, by crun [E₉.ebp, L.aW, E₉.perm.wR, hok₉], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs [hok₉]
    · cregs [E₉.ebp]
    · cregs [E₉.esp]
    all_goals cmems []
  refine WP.seq (WP.of_runBlock ⟨s₁₀, run₁₀, ?_⟩)
  -- The exit.
  have rd₁₀' : s₁₀.rd = s.rd := by rw [rd₁₀, rd₉, rd₈']
  have wr₁₀' : s₁₀.wr = s.wr := by rw [wr₁₀, wr₉, wr₈']
  refine WP.mono (exit_ok (W := W) (s₀ := s) bp₁₀ (by rw [sp₁₀, hsp])
    (by rw [rd₁₀', wr₁₀']; exact covers_left Ar.perm.w) L.fw (by rw [hm₁₀]; exact sv₉)
    (by rw [hm₁₀, hsp]; exact rt₉)) fun s' ⟨abi, m', ax', _, _⟩ => ⟨abi, ?_⟩
  -- The plaintext, the tags and the comparison.
  have hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m (w64 K) R) := fun _ x => Proof.Cmac.aesWith_length _ _ x
  have ci₃ := (St.mut Ar f₂₃).2.2.1
  have ci₄ := (St.mut Ar f₂₄).2.2.1
  have aa₃ := (St.mut Ar f₂₃).2.2.2.1
  have dW : ∀ (r : Region), Region.Sub r ⟨w64 W, 2560⟩ ∨ r = below SP 56 → (⟨w64 D, n⟩ : Region).Disjoint r :=
    fun r h => by rcases h with h | rfl; exact Ar.data.w.sub_right h; exact Ar.data.stk.symm
  have pt₃ : bytesAt s₃.mem (w64 D) n =
      Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 D) n) := by
    rw [h₃, St.ciph, St.dataB, crypt_eq (hBC _)]
  have pt₈ : bytesAt s₈.mem (w64 D) n = bytesAt s₃.mem (w64 D) n := by
    rw [hm₈, bytesAt_writeW_sep _ _ (Ar.data.w.sub_right (Lay.wSub (by decide))) (by have := Ar.data.lt; omega),
      Proof.AesGcm.X86.bytesAt_frame f₇ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.data.w.sub_right (Lay.wSub (by decide)))
        (by have := Ar.data.lt; omega),
      Proof.AesGcm.X86.bytesAt_frame f₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.data.w.sub_right (Lay.wSub (by decide)))
        (by have := Ar.data.lt; omega),
      buf_kept' Ar.data (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact .inl (Lay.wSub (by decide))
        · exact .inl (Lay.wSub (by decide))
        · exact .inl (Lay.wSub (by decide))
        · exact .inr rfl) f₅,
      buf_kept Ar.data (y := 96) (by decide) A₄.frame]
  have tg₅ : bytesAt s₅.mem (w64 T) tl = bytesAt s.mem (w64 T) tl := by
    rw [buf_mut Ar.tag Ar.td f₂₅, St.tagB]
  have hl : (bytesAt s.mem (w64 N) nl).length ≤ 15 := by rw [hnl]; have := Ar.h13; omega
  have o₄ := A₄.out
  rw [ci₃, aa₃, pt₃] at o₄
  have hY := congrArg List.length o₄
  rw [length_bytesAt] at hY
  have hV : bytesAt s₆.mem (w64 W + BitVec.ofNat 64 uO) tl =
      Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem (w64 K) R) tl (bytesAt s.mem (w64 N) nl)
        (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem (w64 K) R) tl (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 A) al)
          (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 D) n))) := by
    rw [Proof.AesGcm.X86.bytesAt_frame f₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Lay.w_w (.inl (by simp only [uO, rO]; omega)) (by simp only [uO]; omega) (by decide)) (by omega),
      Proof.AesCcm.bytesAt_prefix s₅.mem _ ht16, h₅, ci₄, o₄, take_xorFrom_zero (hBC _) _ hY.symm ht16,
      ← Proof.AesCcm.mac_eq _ _ hl]
  have hML : (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem (w64 K) R) tl (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 A) al)
      (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 D) n))).length =
        tl := by
    rw [Proof.AesCcm.mac_eq _ _ hl, List.length_take, length_bytesAt] at *; omega
  have key : c = true ↔
      Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem (w64 K) R) tl (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 T) tl) =
        Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem (w64 K) R) tl (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 A) al)
          (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 D) n)) := by
    rw [← hc, b₆, tg₅, hV, decide_eq_true_iff,
      append_zeros_iff, cryptTag_eq_iff (hBC _) ht16 _ hML (length_bytesAt _ _ _), eq_comm]
  simp only [Spec.Ccm.decryptWith]
  have hD₉ : bytesAt s'.mem (w64 D) n = if c then bytesAt s₈.mem (w64 D) n else Spec.Ccm.zeros n := by
    rw [m', hm₁₀, hm₉, bytesAt_writeBytes_base _ _ _ (by rw [length_mask]) (by have := Ar.data.lt; omega),
      List.drop_eq_nil_of_le (by rw [length_mask, length_bytesAt]), List.append_nil]
  by_cases hk : c = true
  · have hk' := key.mp hk
    simp only [hk', ↓reduceIte]
    refine ⟨by rw [ax', ax₁₀, hk]; rfl, by rw [hD₉, hk]; simp only [↓reduceIte]; rw [pt₈, pt₃]⟩
  · have hk' : ¬ _ := fun e => hk (key.mpr e)
    simp only [hk', ↓reduceIte]
    have hf : c = false := by simpa using hk
    refine ⟨by rw [ax', ax₁₀, hf]; rfl, by rw [hD₉, hf]; rfl⟩

end VG.Proof.AesCcm.X86
