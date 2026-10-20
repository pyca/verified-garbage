module

public import VerifiedGarbage.Proof.AesXts.Arm.Unit.Enc
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesXts.Arm.Unit.Steps
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.RegUpd

/-!
# XTS-AES of data units on ARMv7: decryption

`decrypt_wp`: the tweak, and either the call on all the whole blocks or,
for a partial block, the call on all but the last, the tweak of block `M`
(`nextT`), the call on the last whole block from it (`PP`), the swap, and
the call on the last whole block from the tweak of block `M - 1`; then the
epilogue. The data unit is `decWith` of the inverse cipher and the tweak.
-/

@[expose] public section

namespace VG.Proof.AesXts.Arm.Unit

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesXts.ArmUnit
open VG.Proof.AesXts.Unit (swapMem encWith decWith)
open VG.Spec.Aes (bytesAt)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- Before the call on the last whole block from the tweak of block `M`,
which is at `zO`. -/
structure DecL1 (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (W s₀) (Zv s₀) (Lv s₀) (S s₀) 1 (R s₀)
  mem : ∃ m, AllMem false s₀ (M s₀ - 1) m ∧ Frame [⟨Zp s₀, 16⟩] m s.mem ∧
    bytesAt s.mem (Zp s₀) 16 = Spec.Xts.mulAlpha (bytesAt m (Tp s₀) 16)

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

/-- The arguments of the call on all but the last whole block. -/
theorem argsHead_wp {s : State} (h : TwPost s₀ s) : WP isa (.block argsHead) s (BlocksReady s₀ (M s₀ - 1)) := by
  have hm := hp.m_pos
  obtain ⟨s₁, run₁, x0₁, x1₁, x2₁, x3₁, x12₁, lr₁, cs₁, sp₁, mem₁, rd₁, wr₁⟩ :=
    argsHead_ok s (by rw [h.inv.r7]; exact hm)
  have h₁ := TwPost.keep hp h cs₁ sp₁ mem₁ rd₁ wr₁
  exact WP.of_runBlock ⟨s₁, run₁, h₁, xpre_blocks hp h₁.inv.rd h₁.inv.wr h₁.inv.sp (N := M s₀ - 1)
    (by rw [len_eq s₀]; omega) (by rw [x0₁, h.inv.r4]) (by rw [x1₁, h.inv.r5, r1_ofNat])
    (by rw [x2₁, h.inv.r8]) (by rw [x3₁, h.inv.r9]) (by rw [x12₁, h.inv.r7]) (by rw [lr₁, h.inv.r8])⟩

/-- The tweak of block `M`, at `zO`, and the arguments of the call on the
last whole block from it. -/
theorem decL1_wp {s₂ : State} (h₂ : AllPost false s₀ (M s₀ - 1) s₂) :
    WP isa (.block (nextT ++ split ++ argsL zO)) s₂ (DecL1 s₀) := by
  have wr₂ : s₂.wr = [dataR s₀, scrR s₀] := by rw [h₂.inv.wr, hp.wr]
  have rdwr₂ : s₂.rd ++ s₂.wr = [schR s₀, tschR s₀, iR s₀, argsR s₀, dataR s₀, scrR s₀] := by
    rw [h₂.inv.rd, h₂.inv.wr, hp.rd, hp.wr]; rfl
  obtain ⟨s₃, run₃, g₃, sp₃, f₃, z₃, rd₃, wr₃⟩ := nextT_ok s₂ (T := Tp s₀) (Z := Zp s₀) (by rw [h₂.inv.r8])
    (by rw [h₂.inv.r8]) (by rw [h₂.inv.r8]; have := hp.scr_fit; omega)
    (fun d n h => by rw [rdwr₂, Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (hp.cS _ _ (by
      simp only [tO]; omega)))
    (fun d n h => by rw [wr₂, Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (hp.cS _ _ (by
      simp only [zO]; omega)))
  have inv₃ : Inv s₀ s₃ := Inv.step hp h₂.inv (rs := [⟨Zp s₀, 16⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl z_sub)) f₃
    (fun r hr => by
      simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact g₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) sp₃ rd₃ wr₃
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  rw [WP.block_append_iff]
  refine split_wp inv₃ fun s₄ x0₄ _ _ g₄ sp₄ mem₄ rd₄ wr₄ => ?_
  obtain ⟨s₆, run₆, x0₆, x1₆, x2₆, x3₆, x12₆, lr₆, cs₆, sp₆, mem₆, rd₆, wr₆⟩ := argsL_ok s₄ (o := zO) ez
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  have inv₄ : Inv s₀ s₄ := Inv.step hp inv₃ (rs := []) (fun _ h => by simp at h)
    (by rw [mem₄]; exact Frame.refl _ _) (keep_r0r1 g₄) sp₄ rd₄ wr₄
  have inv₆ : Inv s₀ s₆ := Inv.step hp inv₄ (rs := []) (fun _ h => by simp at h)
    (by rw [mem₆]; exact Frame.refl _ _) (fun r hr => cs₆ r (pinned_pres r hr).1 (pinned_pres r hr).2) sp₆ rd₆ wr₆
  have m₆ : s₆.mem = s₃.mem := by rw [mem₆, mem₄]
  refine ⟨inv₆, xpre_last hp inv₆.rd inv₆.wr inv₆.sp (.inr rfl) (by rw [x0₆, inv₄.r4])
    (by rw [x1₆, inv₄.r5, r1_ofNat]) (by rw [x2₆, inv₄.r8]) (by rw [x3₆]; exact last_of hp inv₄.r9 x0₄) x12₆
    (by rw [lr₆, inv₄.r8]),
    ⟨s₂.mem, h₂.mem, by rw [m₆]; exact f₃, by rw [m₆]; exact z₃⟩⟩

/-- The call on the last whole block from the tweak of block `M`. -/
theorem decL2_wp {s : State} (h : DecL1 s₀ s) : WP isa decCall s (DecL2 s₀) := by
  have hm := hp.m_pos
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  obtain ⟨m, ⟨hout, htw, hfr⟩, f₃, z₃⟩ := h.mem
  have aZ := hp.scrA (d := zO) (by decide)
  have aL := hp.lA
  refine WP.mono (xts_call false h.pre) fun s₇ c₇ => ?_
  have tL : Region.Sub ⟨Tp s₀, 16⟩ (scrR s₀) := sub_trans t_sub s_sub
  have zL : Region.Sub ⟨Zp s₀, 16⟩ (scrR s₀) := sub_trans z_sub s_sub
  have zL' : Region.Sub ⟨State.addr (Zv s₀), 16⟩ (scrR s₀) := by rw [aZ]; exact zL
  have eW := hp.sched_frame h.inv.frame (fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)
  refine ⟨Inv.call hp h.inv (by rw [aZ]; exact z_sub) (.inl (by rw [aL]; exact hp.l_sub)) c₇, m,
    ⟨hout, htw, hfr⟩, ?_, ?_, ?_, ?_⟩
  · have o := c₇.out
    rw [aZ, aL] at o
    rw [Proof.AesXts.Unit.crypt_one_of o, eW, z₃, htw, ← Proof.AesXts.next_succ,
      Nat.sub_add_cancel hm,
      Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_scr.sub_left hp.l_sub).sub_right zL) (by decide)]
  · rw [call_keeps hp (X := ⟨Da s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega)) (by rw [aL]; exact hp.hd_l) zL'
      h.inv.sp c₇ (by dsimp only; have := hp.wrapD; omega)]
    exact Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left (blocks_sub (by omega))).sub_right zL) (by dsimp only; have := hp.wrapD; omega)
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub (by rw [aL]; exact tl_l) zL' h.inv.sp c₇
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
        · rw [UPre.stk_eq h.inv.sp]; exact (hp.stk_scr.sub_right tL).symm) (by decide),
      Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.t_z) (by decide), htw]

/-- The call on the last whole block from the tweak of block `M - 1`, and
the data unit's plaintext. -/
theorem decLast_wp {s : State} {m₅ : Mem} (h : LastReady tO s₀ s m₅) (hm₅ : DecMem s₀ m₅) (hB : B s₀ ≠ 0) :
    WP isa decCall s (Fin false s₀) := by
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  have hm := hp.m_pos
  obtain ⟨m, ⟨hout, htw, hfr⟩, h5L, h5H, h5T, tw₅⟩ := hm₅
  have aT := hp.scrA (d := tO) (by decide)
  have aL := hp.lA
  refine WP.mono (xts_call false h.pre) fun s₁₂ c₁₂ => ?_
  refine ⟨Inv.call hp h.inv (by rw [aT]; exact t_sub) (.inl (by rw [aL]; exact hp.l_sub)) c₁₂, ?_⟩
  have sw := Proof.AesXts.Unit.swapMem_frame m₅ (L s₀) (B s₀)
  have tL : Region.Sub ⟨Tp s₀, 16⟩ (scrR s₀) := sub_trans t_sub s_sub
  have tL' : Region.Sub ⟨State.addr (S s₀ + BitVec.ofNat 32 tO), 16⟩ (scrR s₀) := by rw [aT]; exact tL
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
      h.inv.sp c₁₂ (by dsimp only; have := hp.wrapD; omega), h.mem]
    exact Proof.Cmac.bytesAt_frame sw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.hd_lb) (by dsimp only; have := hp.wrapD; omega)
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub (by rw [aL]; exact tl_l) tL' h.inv.sp c₁₂
      (by dsimp only; omega), h.mem]

/-- Before the call on the last whole block from the tweak of block `M - 1`:
`Pₘ` and `CC` swapped into place. -/
def DecL3 (s₀ s : State) : Prop := ∃ m₅, DecMem s₀ m₅ ∧ LastReady tO s₀ s m₅

/-- The swap, after the call from the tweak of block `M`. -/
theorem decL3_wp {s : State} (h : DecL2 s₀ s) (hB : B s₀ ≠ 0) :
    WP isa (.seq (.seq (.block (split ++ lastAddr)) swap) (.block (argsL tO))) s (DecL3 s₀) := by
  refine WP.assoc' (WP.seq ?_)
  rw [WP.block_append_iff]
  refine split_wp h.inv fun s₈ x0₈ x1₈ _ g₈ sp₈ mem₈ rd₈ wr₈ => ?_
  have inv₈ : Inv s₀ s₈ := Inv.step hp h.inv (rs := []) (fun _ h => by simp at h)
    (by rw [mem₈]; exact Frame.refl _ _) (keep_r0r1 g₈) sp₈ rd₈ wr₈
  refine lastAddr_wp hp inv₈ x0₈ fun s₉ x2₉ g₉ sp₉ mem₉ rd₉ wr₉ => ?_
  have inv₉ : Inv s₀ s₉ := Inv.step hp inv₈ (rs := []) (fun _ h => by simp at h)
    (by rw [mem₉]; exact Frame.refl _ _) (keep_r2 g₉) sp₉ rd₉ wr₉
  exact WP.mono (steal_wp hp (.inl rfl) inv₉ (by rw [g₉ _ (by decide), x0₈])
    (by rw [g₉ _ (by decide), x1₈]) x2₉ hB) fun _ h₂ => ⟨_, by rw [mem₉, mem₈]; exact h.mem, h₂⟩

/-- The steal of decryption, after the tweak. -/
theorem decSteal_wp {s : State} (h : TwPost s₀ s) (hB : B s₀ ≠ 0) : WP isa decSteal s (Fin false s₀) := by
  refine WP.seq (WP.mono (argsHead_wp hp h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (blocks_call hp false (by rw [len_eq s₀]; omega) h₁.tw h₁.pre) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (decL1_wp hp h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (decL2_wp hp h₃) fun s₄ h₄ => ?_)
  exact WP.assoc (WP.assoc (WP.seq (WP.mono (decL3_wp hp h₄ hB) fun _ ⟨_, hm, h'⟩ => decLast_wp hp h' hm hB)))

theorem split_tw_wp {s : State} (h : TwPost s₀ s) :
    WP isa (.block split) s fun s' => TwPost s₀ s' ∧ s'.z = decide (B s₀ = 0) :=
  split_wp h.inv fun _ _ _ z₂ g₂ sp₂ mem₂ rd₂ wr₂ =>
    ⟨TwPost.keep hp h (fun r hr hl => g₂ r (preserved_ne r hr hl).1 (preserved_ne r hr hl).2.1)
      sp₂ mem₂ rd₂ wr₂, z₂⟩

theorem decrypt_wp :
    WP isa Impl.AesXts.ArmUnit.decrypt s₀ fun s' => abiPreserved s₀ s' ∧ (unitArm false).post s₀ s' := by
  refine WP.seq (WP.mono (tweak_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (split_tw_wp hp h₁) fun s₂ ⟨h₂, z₂⟩ => ?_)
  refine WP.seq (WP.mono (WP.ite (decide (B s₀ = 0)) (eval_b z₂) (fun hb => ?_)
    (fun hb => decSteal_wp hp h₂ (by simpa using hb))) fun s₅ h₅ => ?_)
  · refine WP.seq (WP.mono (argsAll_wp hp h₂) fun s₃ h₃ => ?_)
    exact WP.mono (blocks_call hp false (by rw [len_eq s₀]; omega) h₃.tw h₃.pre)
      fun s₄ h₄ => whole_fin h₄ (by simpa using hb)
  · exact WP.mono (fin_wp hp h₅.inv) fun s' ⟨g, m⟩ => ⟨g, unit_post hp (by rw [m]; exact h₅.data)⟩

end

end VG.Proof.AesXts.Arm.Unit
