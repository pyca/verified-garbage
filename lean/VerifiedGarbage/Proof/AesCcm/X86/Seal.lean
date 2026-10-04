import VerifiedGarbage.Proof.AesCcm.X86.Mask

/-!
# AES-CCM on x86: `vg_aes_ccm_seal`

Untrusted: everything here is checked by Lean. `seal` is the start (the
entry and `Ctr₀`, `start_ok`), the MAC of the payload at `W` (`mac_ok`),
encrypted (`tag_ok`), counter mode over the data (`ctr_ok`), the tag copied
to `tag` (`tagOut_ok`) and the exit (`seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Proof.AesGcm.X86 (w64 slotv SavedAt exit_ok ofNat_toNat32 length_bytesAt covers_left writeBytes_frame'
  bytesAt_writeBytes_self)

/-- What `tag y` writes, in `mutR`. -/
theorem inMut_tag (W SP D : BitVec 32) (n : Nat) {y : Nat} (hy : y = 0 ∨ y = 96) :
    InMut W SP D n [⟨w64 W + BitVec.ofNat 64 64, 16⟩, ⟨w64 W + BitVec.ofNat 64 y, 16⟩, wC W, below SP 56] := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨wA W, by simp, Offset.sub_base _ (by decide)⟩
  · exact ⟨wA W, by simp, by rcases hy with rfl | rfl <;> exact Offset.sub_base _ (by decide)⟩
  · exact ⟨wC W, by simp, fun _ h => h⟩
  · exact ⟨below SP 56, by simp, fun _ h => h⟩

/-- A buffer apart from `W` and the stack keeps its bytes across a frame of
parts of `W` and the stack. -/
theorem buf_kept' {W SP : BitVec 32} {s : State} {P : BitVec 32} {len : Nat} (hP : Buf W SP s P len)
    {rs : List Region} (hrs : ∀ r ∈ rs, Region.Sub r ⟨w64 W, 2560⟩ ∨ r = below SP 56) {m m' : Mem}
    (hf : Frame rs m m') : bytesAt m' (w64 P) len = bytesAt m (w64 P) len :=
  Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => by
    rcases hrs r hr with h | rfl
    · exact hP.w.sub_right h
    · exact hP.stk.symm) (by have := hP.lt; omega)

/-- `Ctr₀` is kept by a frame of parts of `W` apart from it. -/
theorem c0_kept {W : BitVec 32} {rs : List Region}
    (hrs : ∀ r ∈ rs, (⟨w64 W + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r) {m m' : Mem} (hf : Frame rs m m') :
    bytesAt m' (w64 W + BitVec.ofNat 64 48) 16 = bytesAt m (w64 W + BitVec.ofNat 64 48) 16 :=
  Proof.AesGcm.X86.bytesAt_frame hf hrs (by decide)

/-- `vg_aes_ccm_seal`, for its arguments. -/
theorem seal_wp' (v : Ctr32Impl) {s : State} {K W SP N A D T : BitVec 32} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D T R nl al n tl) (hsp : s.gpr .esp = SP) (a0 : arg s 0 = K)
    (a1 : arg s 1 = BitVec.ofNat 32 R) (a2 : arg s 2 = N) (a3 : arg s 3 = BitVec.ofNat 32 nl) (a4 : arg s 4 = A)
    (a5 : arg s 5 = BitVec.ofNat 32 al) (a6 : arg s 6 = D) (a7 : arg s 7 = BitVec.ofNat 32 n) (a8 : arg s 8 = T)
    (a9 : arg s 9 = BitVec.ofNat 32 tl) (a10 : arg s 10 = W) (tw : Covers [⟨w64 T, tl⟩] s.wr) :
    WP isa («seal» v.callee v.suffix) s fun s' => abiPreserved s s' ∧
      Spec.Ccm.encryptWith (Spec.Ccm.ctxCiph s.mem (w64 K) R) tl (bytesAt s.mem (w64 N) nl) (bytesAt s.mem (w64 D) n)
        (bytesAt s.mem (w64 A) al) = (bytesAt s'.mem (w64 D) n, bytesAt s'.mem (w64 T) tl) := by
  have L := Ar.lay
  have hnl := length_bytesAt s.mem (w64 N) nl
  have h7' : 7 ≤ (bytesAt s.mem (w64 N) nl).length := by rw [hnl]; exact Ar.h7
  have h13' : (bytesAt s.mem (w64 N) nl).length ≤ 13 := by rw [hnl]; exact Ar.h13
  refine seq_assoc (WP.seq (WP.mono (start_ok Ar hsp a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) fun s₂ St => ?_))
  -- The MAC.
  refine WP.seq (WP.mono (mac_ok v L St.env Ar.rounds St.slots hnl Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.al32 Ar.hn
    Ar.n32 St.c0 (y := 0) (.inl rfl) (Ar.aad.of_eq St.rd St.wr) (Ar.data.of_eq St.rd St.wr)) fun s₃ A₃ => ?_)
  have f₃ : Frame (mutR W SP D n) s₂.mem s₃.mem := frame_toMut A₃.frame (inMut_macR W SP D n (.inl rfl))
  obtain ⟨S₃, -, -, -, -⟩ := St.mut Ar f₃
  have hc₃ : bytesAt s₃.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem (w64 N) nl) 0 := by
    rw [c0_kept (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) A₃.frame, St.c0]
  -- The tag.
  refine WP.seq (WP.mono (tag_ok v L A₃.env Ar.rounds S₃.ctx S₃.rounds h7' h13' hc₃ (y := 0) (.inl rfl))
    fun s₄ ⟨E₄, rd₄, wr₄, f₄, h₄⟩ => ?_)
  have f₂₄ : Frame (mutR W SP D n) s₂.mem s₄.mem := f₃.trans (frame_toMut f₄ (inMut_tag W SP D n (.inl rfl)))
  obtain ⟨S₄, -, -, -, -⟩ := St.mut Ar f₂₄
  have hc₄ : bytesAt s₄.mem (w64 W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem (w64 N) nl) 0 := by
    rw [c0_kept (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) f₄, hc₃]
  have rd₄' : s₄.rd = s.rd := by rw [rd₄, A₃.rd, St.rd]
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, A₃.wr, St.wr]
  have hD₄ : bytesAt s₄.mem (w64 D) n = bytesAt s.mem (w64 D) n := by
    rw [buf_kept' Ar.data (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact .inl (Lay.wSub (by decide))
        · exact .inl (Lay.wSub (by decide))
        · exact .inl (Lay.wSub (by decide))
        · exact .inr rfl) f₄,
      buf_kept Ar.data (y := 0) (by decide) A₃.frame, St.dataB]
  -- Counter mode.
  have C₄ : CtrCtx K W SP s₄ R (bytesAt s.mem (w64 N) nl) D n :=
    ⟨L, Ar.rounds, h7', h13', by rw [hnl]; exact Ar.hn, Ar.n32, hc₄, Ar.data.of_eq rd₄' wr₄',
      by rw [wr₄']; exact Ar.dw, Ar.dk⟩
  refine WP.seq (WP.mono (ctr_ok v C₄ E₄ S₄.ctx S₄.rounds S₄.data S₄.len) fun s₅ ⟨E₅, rd₅, wr₅, f₅, h₅⟩ => ?_)
  have f₂₅ : Frame (mutR W SP D n) s₂.mem s₅.mem := f₂₄.trans (frame_toMut f₅ (inMut_ctrR W SP D n))
  obtain ⟨S₅, sv₅, ci₅, -, rt₅⟩ := St.mut Ar f₂₅
  have rd₅' : s₅.rd = s.rd := by rw [rd₅, rd₄']
  have wr₅' : s₅.wr = s.wr := by rw [wr₅, wr₄']
  -- The tag copied out.
  refine WP.seq (WP.mono (tagOut_ok L E₅ S₅.tl S₅.tp (by have := Ar.t4; omega) Ar.t16
    (Ar.tag.of_eq rd₅' wr₅') (by rw [wr₅']; exact tw)) fun s₆ ⟨m₆', E₆, rd₆, wr₆⟩ => ?_)
  have hTl : tl < 2 ^ 64 := by have := Ar.t16; omega
  have fT : Frame [⟨w64 T, tl⟩] s₅.mem s₆.mem := by
    rw [m₆']; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  have tW : ∀ {d k : Nat}, d + k ≤ 2560 → ∀ r ∈ [(⟨w64 T, tl⟩ : Region)],
      (⟨w64 W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := fun hk r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (Ar.tag.w.sub_right (Lay.wSub hk)).symm
  have sv₆ : SavedAt s₆.mem W s := sv₅.frame fT (tW (by decide))
  have rt₆ : s₆.mem.readW (w64 SP) 32 = s.mem.readW (w64 SP) 32 := by
    rw [Proof.AesGcm.X86.ret_kept fT (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Ar.retT), rt₅]
  -- The exit.
  refine WP.mono (exit_ok (W := W) (s₀ := s) E₆.ebp (by rw [E₆.esp, hsp])
    (by rw [rd₆, wr₆, rd₅', wr₅']; exact covers_left Ar.perm.w) L.fw sv₆ (by rw [hsp]; exact rt₆))
    fun s₇ ⟨abi, m₇, _, _, _⟩ => ⟨abi, ?_⟩
  have hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m (w64 K) R) := fun _ x => Proof.Cmac.aesWith_length _ _ x
  have ci₄ : Spec.Ccm.ctxCiph s₄.mem (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R :=
    (St.mut Ar f₂₄).2.2.1
  have ci₃ : Spec.Ccm.ctxCiph s₃.mem (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R :=
    (St.mut Ar f₃).2.2.1
  have hW₅ : bytesAt s₅.mem (w64 W) tl = bytesAt s₄.mem (w64 W) tl := by
    have ht := Ar.t16
    exact Proof.AesGcm.X86.bytesAt_frame f₅ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · simpa using Lay.w_w (W := W) (a := 0) (n := tl) (d := 64) (k := 32) (.inl (by omega)) (by omega) (by decide)
      · simpa using Lay.w_w (W := W) (a := 0) (n := tl) (d := 240) (k := 2320) (.inl (by omega)) (by omega)
          (by decide)
      · exact (L.stk_w.sub_right (Region.sub_prefix (by omega))).symm
      · exact (Ar.data.w.sub_right (Region.sub_prefix (by omega))).symm) (by omega)
  have e0 : w64 W + BitVec.ofNat 64 0 = w64 W := BitVec.add_zero _
  have o₃ := A₃.out
  rw [e0] at h₄ o₃
  have hY := congrArg List.length o₃
  rw [length_bytesAt] at hY
  simp only [Spec.Ccm.encryptWith, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · rw [m₇, Proof.AesGcm.X86.bytesAt_frame fT (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.td.symm) (by have := Ar.data.lt; omega), h₅, ci₄, hD₄, crypt_eq (hBC _)]
  · have hT₇ : bytesAt s₇.mem (w64 T) tl = bytesAt s₅.mem (w64 W) tl := by
      have := bytesAt_writeBytes_self s₅.mem (w64 T) (bytesAt s₅.mem (w64 W) tl) (by rw [length_bytesAt]; omega)
      rw [length_bytesAt] at this
      rw [m₇, m₆', this]
    rw [hT₇, hW₅, Proof.AesCcm.bytesAt_prefix s₄.mem (w64 W) Ar.t16, h₄,
      take_xorFrom_zero (hBC _) _ (by rw [length_bytesAt]) Ar.t16, o₃, ci₃,
      ← Proof.AesCcm.mac_eq _ _ (by rw [hnl]; have := Ar.h13; omega), St.ciph, St.aadB, St.dataB]

end VG.Proof.AesCcm.X86
