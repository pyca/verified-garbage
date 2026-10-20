module

public import VerifiedGarbage.Proof.AesXts.X86.Unit.Enc
import VerifiedGarbage.Proof.Cmac.Frame

/-!
# XTS-AES of data units on x86: decryption

`decrypt_wp`: the tweak; without a partial block the call on the whole
blocks; with one, the call on the first `M - 1`, the tweak of block `M` at
`zO` and the call on the last whole block from it (`PP`), the swap and the
call on the last whole block from the tweak of block `M - 1`; then the
epilogue. `esi` keeps `B` throughout.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86.Unit

open VG VG.X86 VG.Impl.AesXts.X86Unit
open VG.Proof.AesXts.Unit (swapMem encWith decWith)
open VG.Spec.Aes (bytesAt)

/-- Before the call on the last whole block from the tweak of block `M`,
which is at `zO`. -/
structure DecL1 (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (W s₀) (Zv s₀) (Lv s₀) (S s₀) 1 (R s₀)
  mem : ∃ m, AllMem false s₀ (M s₀ - 1) m ∧ Frame [⟨Zp s₀, 16⟩] m s.mem ∧
    bytesAt s.mem (Zp s₀) 16 = Spec.Xts.mulAlpha (bytesAt m (Tp s₀) 16)
  esi : s.gpr .esi = BitVec.ofNat 32 (B s₀)

/-- The memory after the call on the last whole block from the tweak of
block `M`: `PP` there, from the memory `m` after the first `M - 1` blocks. -/
def DecMem (s₀ : State) (m₅ : Mem) : Prop :=
  ∃ m, AllMem false s₀ (M s₀ - 1) m ∧
    bytesAt m₅ (L s₀) 16 = Spec.Xts.block (ciph s₀ false) (Spec.Xts.next (t0 s₀) (M s₀)) (bytesAt m (L s₀) 16) ∧
    bytesAt m₅ (Da s₀) (16 * (M s₀ - 1)) = bytesAt m (Da s₀) (16 * (M s₀ - 1)) ∧
    bytesAt m₅ (L s₀ + 16) (B s₀) = bytesAt m (L s₀ + 16) (B s₀) ∧
    bytesAt m₅ (Tp s₀) 16 = Spec.Xts.next (t0 s₀) (M s₀ - 1)

/-- After the call on the last whole block from the tweak of block `M`. -/
structure DecL2 (s₀ s : State) : Prop where
  inv : Inv s₀ s
  mem : DecMem s₀ s.mem
  esi : s.gpr .esi = BitVec.ofNat 32 (B s₀)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- The arguments of the call on all but the last whole block. -/
theorem head_wp {s : State} (h : TwPost s₀ s) :
    WP isa (.block argsHead) s fun s' => BlocksReady s₀ (M s₀ - 1) s' ∧ s'.gpr .esi = s.gpr .esi :=
  blk (argsHead_wp (Inv.args hp h.inv) hp.m_pos fun s₂ c ax cx dx bx di bp => WP.block_nil (by
    have h₂ := TwPost.keep hp h (c.gpr _ (by decide)) c.mem c.rd c.wr
    exact ⟨⟨h₂, xpre_blocks hp h₂.inv.rd h₂.inv.wr h₂.inv.esp (N := M s₀ - 1) (by rw [len_eq s₀]; omega) ax
      (by rw [cx, r_ofNat]) dx bx di bp⟩, c.gpr _ (by decide)⟩))

/-- The tweak of block `M`, at `zO`, and the arguments of the call on the
last whole block from it. -/
theorem decL1_wp {s₂ : State} (h₂ : AllPost false s₀ (M s₀ - 1) s₂) (hsi : s₂.gpr .esi = BitVec.ofNat 32 (B s₀)) :
    WP isa (.block (nextT ++ argsL zO)) s₂ (DecL1 s₀) := by
  refine nextT_wp hp (Inv.args hp h₂.inv) h₂.inv.wr fun s₃ c₃ => ?_
  have f₃ : Frame [⟨Zp s₀, 16⟩] s₂.mem s₃.mem := by
    rw [c₃.mem]; exact (copy4_frame _ _ _).trans (Proof.AesXts.X86.alphaMem_frame _ _)
  have inv₃ : Inv s₀ s₃ := Inv.step hp h₂.inv (rs := [⟨Zp s₀, 16⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl z_sub)) f₃ (c₃.gpr _ (by decide)) c₃.rd c₃.wr
  have si₃ : s₃.gpr .esi = BitVec.ofNat 32 (B s₀) := by rw [c₃.gpr _ (by decide), hsi]
  refine blk (argsL_wp (o := zO) (Inv.args hp inv₃) hp si₃ fun s₆ c₆ ax cx dx bx di bp => WP.block_nil ?_)
  have inv₆ : Inv s₀ s₆ := Inv.step hp inv₃ (rs := []) (fun _ h => by simp at h)
    (by rw [c₆.mem]; exact Frame.refl _ _) (c₆.gpr _ (by decide)) c₆.rd c₆.wr
  refine ⟨inv₆, xpre_last hp inv₆.rd inv₆.wr inv₆.esp (.inr rfl) ax (by rw [cx, r_ofNat]) dx bx di bp,
    ⟨s₂.mem, h₂.mem, by rw [c₆.mem]; exact f₃, ?_⟩, by rw [c₆.gpr _ (by decide), si₃]⟩
  rw [c₆.mem, c₃.mem, Proof.AesXts.X86.alphaMem_bytes, copy4_bytes]

/-- The call on the last whole block from the tweak of block `M`. -/
theorem decL2_wp {d : Impl.Aes.X86.Blocks} (hf : XFn false d) {s : State} (h : DecL1 s₀ s) :
    WP isa (xcall d) s (DecL2 s₀) := by
  have hm := hp.m_pos
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  obtain ⟨m, ⟨hout, htw, hfr⟩, f₃, z₃⟩ := h.mem
  have aZ := hp.scrW (d := zO) (by decide)
  have aL := hp.lA
  refine WP.mono (xts_call false hf.ok hf.nosp hf.stack h.pre) fun s₇ c₇ => ?_
  have tL : Region.Sub ⟨Tp s₀, 16⟩ (scrR s₀) := sub_trans t_sub s_sub
  have zL : Region.Sub ⟨Zp s₀, 16⟩ (scrR s₀) := sub_trans z_sub s_sub
  have zL' : Region.Sub ⟨(Zv s₀).setWidth 64, 16⟩ (scrR s₀) := by rw [aZ]; exact zL
  have eW := hp.sched_frame h.inv.frame (fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)
  refine ⟨Inv.call hp h.inv (by rw [aZ]; exact z_sub) (.inl (by rw [aL]; exact hp.l_sub)) c₇,
    ⟨m, ⟨hout, htw, hfr⟩, ?_, ?_, ?_, ?_⟩, by rw [c₇.saved .esi (by simp [calleeSaved]), h.esi]⟩
  · have o := c₇.out
    rw [aZ, aL] at o
    rw [Proof.AesXts.Unit.crypt_one_of o, eW, z₃, htw, ← Proof.AesXts.next_succ,
      Nat.sub_add_cancel hm,
      Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_scr.sub_left hp.l_sub).sub_right zL) (by decide)]
  · rw [call_keeps hp (X := ⟨Da s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega)) (by rw [aL]; exact hp.hd_l) zL'
      h.inv.esp c₇ (by dsimp only; have := hp.wrapD; omega)]
    exact Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left (blocks_sub (by omega))).sub_right zL) (by dsimp only; have := hp.wrapD; omega)
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub (by rw [aL]; exact tl_l) zL' h.inv.esp c₇
      (by dsimp only; omega)]
    exact Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left hp.tl_sub).sub_right zL) (by dsimp only; omega)
  · rw [Proof.Cmac.bytesAt_frame c₇.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [aZ]; exact hp.t_z
        · rw [aL]; exact (hp.data_scr.symm.sub_left tL).sub_right hp.l_sub
        · exact hp.t_wk
        · rw [hp.stk_eq h.inv.esp]; exact (hp.stk_scr.sub_right tL).symm) (by decide),
      Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.t_z) (by decide), htw]

/-- The call on the last whole block from the tweak of block `M - 1`, and
the data unit's plaintext. -/
theorem decLast_wp {d : Impl.Aes.X86.Blocks} (hf : XFn false d) {s : State} {m₅ : Mem}
    (h : LastReady tO s₀ s m₅) (hm₅ : DecMem s₀ m₅) (hB : B s₀ ≠ 0) :
    WP isa (xcall d) s (Fin false s₀) := by
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  have hm := hp.m_pos
  obtain ⟨m, ⟨hout, htw, hfr⟩, h5L, h5H, h5T, tw₅⟩ := hm₅
  have aT := hp.scrW (d := tO) (by decide)
  have aL := hp.lA
  refine WP.mono (xts_call false hf.ok hf.nosp hf.stack h.pre) fun s₁₂ c₁₂ => ?_
  refine ⟨Inv.call hp h.inv (by rw [aT]; exact t_sub) (.inl (by rw [aL]; exact hp.l_sub)) c₁₂, ?_⟩
  have sw := Proof.AesXts.Unit.swapMem_frame m₅ (L s₀) (B s₀)
  have tL : Region.Sub ⟨Tp s₀, 16⟩ (scrR s₀) := sub_trans t_sub s_sub
  have tL' : Region.Sub ⟨(S s₀ + BitVec.ofNat 32 tO).setWidth 64, 16⟩ (scrR s₀) := by rw [aT]; exact tL
  have eW' := hp.sched_frame h.inv.frame (fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)
  rw [len_eq s₀]
  refine Proof.AesXts.Unit.dec_steal (m₃ := m) (m₅ := m₅) hm (Nat.pos_of_ne_zero hB) hb hout
    ⟨?_, ?_⟩ ⟨h5L, h5H, h5T⟩ ⟨?_, ?_, ?_⟩
  · exact Proof.Cmac.bytesAt_frame hfr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.l_hd
      · exact hp.data_scr.sub_left hp.l_sub
      · exact hp.stk_data.symm.sub_left hp.l_sub) (by decide)
  · exact Proof.Cmac.bytesAt_frame hfr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.hd_tl.symm
      · exact hp.data_scr.sub_left hp.tl_sub
      · exact hp.stk_data.symm.sub_left hp.tl_sub) (by omega)
  · have o := c₁₂.out
    rw [aT, aL] at o
    rw [Proof.AesXts.Unit.crypt_one_of o, eW', h.mem,
      Proof.Cmac.bytesAt_frame sw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_scr.symm.sub_left tL).sub_right hp.lb_sub) (by decide), tw₅]
  · rw [call_keeps hp (X := ⟨Da s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega)) (by rw [aL]; exact hp.hd_l) tL'
      h.inv.esp c₁₂ (by dsimp only; have := hp.wrapD; omega), h.mem]
    exact Proof.Cmac.bytesAt_frame sw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.hd_lb) (by dsimp only; have := hp.wrapD; omega)
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub (by rw [aL]; exact tl_l) tL' h.inv.esp c₁₂
      (by dsimp only; omega), h.mem]

/-- The steal of decryption, after the tweak. -/
theorem decSteal_wp {d : Impl.Aes.X86.Blocks} (hf : XFn false d) {s : State} (h : TwPost s₀ s)
    (hsi : s.gpr .esi = BitVec.ofNat 32 (B s₀)) (hB : B s₀ ≠ 0) : WP isa (decSteal d) s (Fin false s₀) := by
  refine WP.seq (WP.mono (head_wp hp h) fun s₁ ⟨h₁, e₁⟩ => ?_)
  refine WP.seq (WP.mono (blocks_call hp hf (by rw [len_eq s₀]; omega) h₁.tw h₁.pre) fun s₂ ⟨h₂, e₂⟩ => ?_)
  refine WP.seq (WP.mono (decL1_wp hp h₂ (by rw [e₂, e₁, hsi])) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (decL2_wp hp hf h₃) fun s₄ h₄ => ?_)
  exact steal_wp hp h₄.inv h₄.esi hB fun _ h' => decLast_wp hp hf h' h₄.mem hB

theorem split_tw_wp {s : State} (h : TwPost s₀ s) :
    WP isa (.block split) s fun s' =>
      TwPost s₀ s' ∧ s'.gpr .esi = BitVec.ofNat 32 (B s₀) ∧ s'.zf = some (decide (B s₀ = 0)) :=
  blk (split_wp (Inv.args hp h.inv) fun _ c si zf => WP.block_nil
    ⟨TwPost.keep hp h (c.gpr _ (by decide)) c.mem c.rd c.wr, si, zf⟩)

theorem decrypt_wp {e d : Impl.Aes.X86.Blocks} (he : XFn true e) (hd : XFn false d) :
    WP isa (decrypt e d) s₀ fun s' => abiPreserved s₀ s' ∧ (unitX86 false).post s₀ s' := by
  refine WP.seq (WP.mono (tweak_wp hp he) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (split_tw_wp hp h₁) fun s₂ ⟨h₂, si₂, z₂⟩ => ?_)
  refine WP.seq (WP.mono (WP.ite (decide (B s₀ = 0)) (eval_b z₂) (fun hb => ?_)
    (fun hb => decSteal_wp hp hd h₂ si₂ (by simpa using hb))) fun s₅ h₅ => ?_)
  · refine WP.seq (WP.mono (ready_wp hp h₂) fun s₃ h₃ => ?_)
    exact WP.mono (blocks_call hp hd (by rw [len_eq s₀]; omega) h₃.tw h₃.pre)
      fun s₄ h₄ => whole_fin h₄.1 (by simpa using hb)
  · exact WP.mono (fin_wp hp h₅.inv) fun s' ⟨g, m⟩ => ⟨g, unit_post hp (by rw [m]; exact h₅.data)⟩

end

end VG.Proof.AesXts.X86.Unit
