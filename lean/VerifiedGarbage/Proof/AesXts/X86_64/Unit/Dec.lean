module

public import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Enc
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Steps
import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Pre
import VerifiedGarbage.Proof.AesCbc.X86_64.Body
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# XTS-AES of data units on x86-64: decryption

`decrypt_wp`: the tweak, then without a partial block the call on the whole
blocks; otherwise the call on all but the last whole block, the next tweak
(that of block `M`, `nextT`), the call on the last whole block from it, the
swap, and the call on the last whole block from the tweak of block `M - 1`;
then the epilogue, for any implementation `v` of the whole-block functions.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Unit

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesXts.X86_64Unit
open VG.Proof.AesCbc.X86_64 (modeX86_64 in_rw)
open VG.Proof.AesXts.Unit (swapMem encWith decWith)
open VG.Spec.Aes (bytesAt)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- Before the call on the last whole block from the tweak of block `M`,
which is at `zO`. -/
structure DecL1 (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (W s₀) (Zp s₀) (L s₀) (S s₀) 1 (R s₀)
  mem : ∃ m, AllMem false s₀ (M s₀ - 1) m ∧ Frame [⟨Zp s₀, 16⟩] m s.mem ∧
    bytesAt s.mem (Zp s₀) 16 = Spec.Xts.mulAlpha (bytesAt m (Tp s₀) 16)

/-- The memory after the call on the last whole block from the tweak of
block `M`: `PP` there, from the memory `m` after the first `M - 1` blocks. -/
def DecMem (s₀ : State) (m₅ : Mem) : Prop :=
  ∃ m, AllMem false s₀ (M s₀ - 1) m ∧
    bytesAt m₅ (L s₀) 16 = Spec.Xts.block (ciph s₀ false) (Spec.Xts.next (t0 s₀) (M s₀)) (bytesAt m (L s₀) 16) ∧
    bytesAt m₅ (D s₀) (16 * (M s₀ - 1)) = bytesAt m (D s₀) (16 * (M s₀ - 1)) ∧
    bytesAt m₅ (L s₀ + 16) (B s₀) = bytesAt m (L s₀ + 16) (B s₀) ∧
    bytesAt m₅ (Tp s₀) 16 = Spec.Xts.next (t0 s₀) (M s₀ - 1)

/-- After the call on the last whole block from the tweak of block `M`. -/
structure DecL2 (s₀ s : State) : Prop where
  inv : Inv s₀ s
  mem : DecMem s₀ s.mem

/-- Before the call on the last whole block from the tweak of block `M - 1`:
`Pₘ` and `CC` swapped into place. -/
structure DecL3 (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (W s₀) (Tp s₀) (L s₀) (S s₀) 1 (R s₀)
  mem : ∃ m₅, DecMem s₀ m₅ ∧ s.mem = swapMem m₅ (L s₀) (B s₀)

/-- The arguments of the call on all but the last whole block. -/
theorem argsHead_wp {s : State} (h : TwPost s₀ s) : WP isa (.block argsHead) s (BlocksReady s₀ (M s₀ - 1)) := by
  have hm := hp.m_pos
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, cs₁, mem₁, rd₁, wr₁⟩ :=
    argsHead_ok s (by rw [h.inv.r13]; exact hm)
  have h₁ := TwPost.keep hp h cs₁ mem₁ rd₁ wr₁
  exact WP.of_runBlock ⟨s₁, run₁, h₁, xpre_blocks hp h₁.inv.rd h₁.inv.wr h₁.inv.rsp (N := M s₀ - 1)
    (by rw [len_eq s₀]; omega) (by rw [rdi₁, h.inv.rbx]) (by rw [rsi₁, h.inv.rbp, rsi_ofNat])
    (by rw [rdx₁, h.inv.r15]) (by rw [rcx₁, h.inv.r12]) (by rw [r8₁, h.inv.r13]) (by rw [r9₁, h.inv.r15])⟩

/-- The tweak of block `M`, at `zO`, and the arguments of the call on the
last whole block from it. -/
theorem decL1_wp {s₂ : State} (h₂ : AllPost false s₀ (M s₀ - 1) s₂) :
    WP isa (.block (nextT ++ split ++ lastAddr ++ argsL zO)) s₂ (DecL1 s₀) := by
  have hm := hp.m_pos
  have wr₂ : s₂.wr = [dataR s₀, scrR s₀] := by rw [h₂.inv.wr, hp.wr]
  have rdwr₂ : s₂.rd ++ s₂.wr = [schR s₀, tschR s₀, iR s₀, argR s₀, dataR s₀, scrR s₀] := by
    rw [h₂.inv.rd, h₂.inv.wr, hp.rd, hp.wr]; rfl
  obtain ⟨s₃, run₃, g₃, f₃, z₃, rd₃, wr₃⟩ := nextT_ok s₂ (T := Tp s₀) (Z := Zp s₀) (by rw [h₂.inv.r15])
    (by rw [h₂.inv.r15, ← Offset.add_add]) (by rw [h₂.inv.r15]) (by rw [h₂.inv.r15, ← Offset.add_add])
    (by rw [rdwr₂]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [tO])))
    (by rw [rdwr₂, Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [tO])))
    (by rw [wr₂]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [zO])))
    (by rw [wr₂, Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [zO])))
  have inv₃ : Inv s₀ s₃ := Inv.step hp h₂.inv (rs := [⟨Zp s₀, 16⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl z_sub)) f₃
    (fun r hr => g₃ r (pinned_ne hr).1 (pinned_ne hr).2.1 (pinned_ne hr).2.2.1) rd₃ wr₃
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  rw [WP.block_append_iff]
  refine split_wp inv₃ fun s₄ rax₄ _ _ g₄ mem₄ rd₄ wr₄ => ?_
  rw [WP.block_append_iff]
  obtain ⟨s₅, run₅, rdx₅, g₅, mem₅, rd₅, wr₅⟩ := lastAddr_ok s₄
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  obtain ⟨s₆, run₆, rdi₆, rsi₆, rdx₆, rcx₆, r8₆, r9₆, cs₆, mem₆, rd₆, wr₆⟩ := argsL_ok s₅ (o := zO) rfl
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  have k₆ (r : Reg) (hr : r ∈ pinned) : s₆.gpr r = s₃.gpr r := by
    have n := pinned_ne hr
    rw [cs₆ r (pinned_cs r hr), g₅ r n.2.2.1, g₄ r n.1 n.2.2.2.1]
  have m₆ : s₆.mem = s₃.mem := by rw [mem₆, mem₅, mem₄]
  have inv₆ : Inv s₀ s₆ := Inv.step hp inv₃ (rs := []) (fun _ h => by simp at h)
    (by rw [m₆]; exact Frame.refl _ _) k₆ (by rw [rd₆, rd₅, rd₄]) (by rw [wr₆, wr₅, wr₄])
  refine ⟨inv₆, xpre_last hp inv₆.rd inv₆.wr inv₆.rsp (.inr rfl) (by rw [rdi₆, g₅ _ (by decide), g₄ _ (by decide)
      (by decide), inv₃.rbx]) (by rw [rsi₆, g₅ _ (by decide), g₄ _ (by decide) (by decide), inv₃.rbp, rsi_ofNat])
    (by rw [rdx₆, g₅ _ (by decide), g₄ _ (by decide) (by decide), inv₃.r15])
    (by rw [rcx₆, rdx₅, g₄ _ (by decide) (by decide), rax₄, inv₃.r12,
      last_eq _ hm (by have := hp.m_lt; omega)]) r8₆
    (by rw [r9₆, g₅ _ (by decide), g₄ _ (by decide) (by decide), inv₃.r15]),
    ⟨s₂.mem, h₂.mem, by rw [m₆]; exact f₃, by rw [m₆]; exact z₃⟩⟩

/-- The call on the last whole block from the tweak of block `M`. -/
theorem decL2_wp (v : XtsImpl) {s : State} (h : DecL1 s₀ s) :
    WP isa (.call v.dec.name v.dec.code) s (DecL2 s₀) := by
  have hm := hp.m_pos
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  obtain ⟨m, ⟨hout, htw, hfr⟩, f₃, z₃⟩ := h.mem
  refine WP.mono (xts_call false v.decOk v.decNosp v.decDepth h.pre) fun s₇ c₇ => ?_
  have tL : Region.Sub ⟨Tp s₀, 16⟩ (scrR s₀) := sub_trans t_sub s_sub
  have zL : Region.Sub ⟨Zp s₀, 16⟩ (scrR s₀) := sub_trans z_sub s_sub
  have eW := hp.sched_frame h.inv.frame (fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)
  refine ⟨Inv.call hp h.inv z_sub (.inl hp.l_sub) c₇, m, ⟨hout, htw, hfr⟩, ?_, ?_, ?_, ?_⟩
  · rw [Proof.AesXts.Unit.crypt_one_of c₇.out, eW, z₃, htw, ← Proof.AesXts.next_succ,
      Nat.sub_add_cancel hm,
      Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_scr.sub_left hp.l_sub).sub_right zL) (by decide)]
  · rw [call_keeps hp (X := ⟨D s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega)) hp.hd_l zL h.inv.rsp c₇
      (by dsimp only; have := hp.wrapD; omega)]
    exact Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left (blocks_sub (by omega))).sub_right zL) (by dsimp only; have := hp.wrapD; omega)
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub tl_l zL h.inv.rsp c₇ (by dsimp only; omega)]
    exact Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left hp.tl_sub).sub_right zL) (by dsimp only; omega)
  · rw [Proof.Cmac.bytesAt_frame c₇.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hp.t_z
        · exact (hp.data_scr.symm.sub_left tL).sub_right hp.l_sub
        · exact hp.t_wk
        · rw [stk, h.inv.rsp]; exact (hp.stk_scr.sub_right tL).symm) (by decide),
      Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.t_z) (by decide), htw]

/-- `Pₘ` and `CC` swapped into place, and the arguments of the call on the
last whole block from the tweak of block `M - 1`. -/
theorem decL3_wp {s : State} (h : DecL2 s₀ s) (hB : B s₀ ≠ 0) :
    WP isa (.seq (.seq (.block (split ++ stealPre)) swap) (.block (argsL tO))) s (DecL3 s₀) := by
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  refine WP.seq (WP.seq ?_)
  rw [WP.block_append_iff]
  refine split_wp h.inv fun s₈ rax₈ r8₈ _ g₈ mem₈ rd₈ wr₈ => ?_
  refine stealPre_wp hp (by rw [g₈ _ (by decide) (by decide), h.inv.r12]) rax₈
    fun s₉ rdx₉ rcx₉ g₉ mem₉ rd₉ wr₉ => ?_
  have wr₉' : s₉.wr = [dataR s₀, scrR s₀] := by rw [wr₉, wr₈, h.inv.wr, hp.wr]
  refine WP.mono (swap_ok s₉ (Nat.pos_of_ne_zero hB) hb rdx₉ rcx₉
    (by rw [g₉ _ (by decide) (by decide), r8₈]) (fun i hi => by
      rw [wr₉']
      exact in_rw (r := dataR s₀) (by simp)
        (hp.lb_sub _ (Offset.contains_base (L s₀) (d := i) (n := 1) (k := 16 + B s₀) (by omega) (by omega)))))
    fun s₁₀ ⟨mem₁₀, g₁₀, rd₁₀, wr₁₀⟩ => ?_
  obtain ⟨s₁₁, run₁₁, rdi₁₁, rsi₁₁, rdx₁₁, rcx₁₁, r8₁₁, r9₁₁, cs₁₁, mem₁₁, rd₁₁, wr₁₁⟩ := argsL_ok s₁₀ (o := tO) rfl
  refine WP.of_runBlock ⟨s₁₁, run₁₁, ?_⟩
  have k₁₀ (r : Reg) (hr : r ∈ pinned) : s₁₀.gpr r = s.gpr r := by
    have n := pinned_ne hr
    rw [g₁₀ r n.1 n.2.2.2.2 n.2.1, g₉ r n.2.2.1 n.2.1, g₈ r n.1 n.2.2.2.1]
  have m₁₀ : s₁₀.mem = swapMem s.mem (L s₀) (B s₀) := by rw [mem₁₀, mem₉, mem₈]
  have inv₁₀ : Inv s₀ s₁₀ := Inv.step hp h.inv (rs := [⟨L s₀, 16 + B s₀⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inl hp.lb_sub)
    (by rw [m₁₀]; exact Proof.AesXts.Unit.swapMem_frame _ _ _) k₁₀ (by rw [rd₁₀, rd₉, rd₈])
    (by rw [wr₁₀, wr₉, wr₈])
  have inv₁₁ : Inv s₀ s₁₁ := Inv.step hp inv₁₀ (rs := []) (fun _ h => by simp at h)
    (by rw [mem₁₁]; exact Frame.refl _ _) (fun r hr => cs₁₁ r (pinned_cs r hr)) rd₁₁ wr₁₁
  exact ⟨inv₁₁, xpre_last hp inv₁₁.rd inv₁₁.wr inv₁₁.rsp (.inl rfl) (by rw [rdi₁₁, inv₁₀.rbx])
    (by rw [rsi₁₁, inv₁₀.rbp, rsi_ofNat]) (by rw [rdx₁₁, inv₁₀.r15])
    (by rw [rcx₁₁, g₁₀ _ (by decide) (by decide) (by decide), rdx₉]) r8₁₁ (by rw [r9₁₁, inv₁₀.r15]),
    s.mem, h.mem, by rw [mem₁₁, m₁₀]⟩

/-- The call on the last whole block from the tweak of block `M - 1`, and
the data unit's plaintext. -/
theorem decLast_wp (v : XtsImpl) {s : State} (h : DecL3 s₀ s) (hB : B s₀ ≠ 0) :
    WP isa (.call v.dec.name v.dec.code) s (Fin false s₀) := by
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  have hm := hp.m_pos
  obtain ⟨m₅, ⟨m, ⟨hout, htw, hfr⟩, h5L, h5H, h5T, tw₅⟩, m₁₀⟩ := h.mem
  refine WP.mono (xts_call false v.decOk v.decNosp v.decDepth h.pre) fun s₁₂ c₁₂ => ?_
  refine ⟨Inv.call hp h.inv t_sub (.inl hp.l_sub) c₁₂, ?_⟩
  have sw := Proof.AesXts.Unit.swapMem_frame m₅ (L s₀) (B s₀)
  have tL : Region.Sub ⟨Tp s₀, 16⟩ (scrR s₀) := sub_trans t_sub s_sub
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
  · rw [Proof.AesXts.Unit.crypt_one_of c₁₂.out, eW', m₁₀,
      Proof.Cmac.bytesAt_frame sw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_scr.symm.sub_left tL).sub_right hp.lb_sub) (by decide), tw₅]
  · rw [call_keeps hp (X := ⟨D s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega)) hp.hd_l tL h.inv.rsp c₁₂
      (by dsimp only; have := hp.wrapD; omega), m₁₀]
    exact Proof.Cmac.bytesAt_frame sw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.hd_lb) (by dsimp only; have := hp.wrapD; omega)
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub tl_l tL h.inv.rsp c₁₂ (by dsimp only; omega), m₁₀]

/-- The steal of decryption, after the tweak. -/
theorem decSteal_wp (v : XtsImpl) {s : State} (h : TwPost s₀ s) (hB : B s₀ ≠ 0) :
    WP isa (decSteal v.dec) s (Fin false s₀) := by
  refine WP.seq (WP.mono (argsHead_wp hp h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (blocks_call hp false v.decOk v.decNosp v.decDepth (by rw [len_eq s₀]; omega) h₁.tw
    h₁.pre) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (decL1_wp hp h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (decL2_wp hp v h₃) fun s₄ h₄ => ?_)
  exact WP.assoc (WP.assoc (WP.seq (WP.mono (decL3_wp hp h₄ hB) fun _ h₅ => decLast_wp hp v h₅ hB)))

theorem split_tw_wp {s : State} (h : TwPost s₀ s) :
    WP isa (.block split) s fun s' => TwPost s₀ s' ∧ s'.zf = some (decide (B s₀ = 0)) :=
  split_wp h.inv fun _ _ _ zf₂ g₂ mem₂ rd₂ wr₂ =>
    ⟨TwPost.keep hp h (fun r hr => g₂ r (AesCbc.X86_64.calleeSaved_ne_rax hr) (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) mem₂ rd₂ wr₂, zf₂⟩

theorem decrypt_wp (v : XtsImpl) :
    WP isa (Impl.AesXts.X86_64Unit.decrypt v.xts) s₀ fun s' => gprPreserved s₀ s' ∧ (unitX86_64 false).post s₀ s' := by
  refine WP.seq (WP.mono (tweak_wp hp v.encOk v.encNosp v.encDepth) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (split_tw_wp hp h₁) fun s₂ ⟨h₂, zf₂⟩ => ?_)
  refine WP.seq (WP.mono (WP.ite (decide (B s₀ = 0)) zf₂ (fun hb => ?_)
    (fun hb => decSteal_wp hp v h₂ (by simpa using hb))) fun s₅ h₅ => ?_)
  · refine WP.seq (WP.mono (argsAll_wp hp h₂) fun s₃ h₃ => ?_)
    exact WP.mono (blocks_call hp false v.decOk v.decNosp v.decDepth (by rw [len_eq s₀]; omega) h₃.tw h₃.pre)
      fun s₄ h₄ => whole_fin h₄ (by simpa using hb)
  · exact WP.mono (fin_wp hp h₅.inv) fun s' ⟨g, m⟩ => ⟨g, unit_post hp (by rw [m]; exact h₅.data)⟩

end

end VG.Proof.AesXts.X86_64.Unit
