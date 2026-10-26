module

public import VerifiedGarbage.Proof.AesXts.RISCV64.Unit.Enc
public import VerifiedGarbage.Proof.AesXts.RISCV64.Steps
import VerifiedGarbage.Proof.AesXts.Unit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesXts.RISCV64.Unit.Pre
import VerifiedGarbage.Proof.AesXts.RISCV64.Unit.Steps

/-!
# XTS-AES of data units on PPC64LE: decryption

As on PPC64LE (`Proof/AesXts/PPC64LE/Unit/Dec.lean`). `decrypt_wp`: the
tweak, then without a partial block the call on the whole blocks; with one,
the call on all but the last whole block, the tweak of block `M` (`nextT`),
the call on the last whole block from it, the swap, and the call on the
last whole block from the tweak of block `M - 1`; then the epilogue.
-/

@[expose] public section

namespace VG.Proof.AesXts.RISCV64.Unit

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesXts.RISCV64Unit
open VG.Proof.AesXts.Unit (swapMem encWith decWith)
open VG.Spec.Aes (bytesAt)

/-- A callee-saved register is none that `mulA` writes. -/
theorem pres_not_mul {r : Reg} (hr : r ∈ preserved) : r ∉ AesXts.RISCV64.mulRegs := by
  revert hr; cases r <;> decide

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- Before the call on the last whole block from the tweak of block `M`,
which is at `zO`. -/
structure DecL1 (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (W s₀) (Zp s₀) (L s₀) (Wk s₀) 1 (R s₀)
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

/-- The arguments of the call on all but the last whole block. -/
theorem argsHead_wp {s : State} (h : TwPost s₀ s) : WP isa (.block argsHead) s (BlocksReady s₀ (M s₀ - 1)) := by
  have hm := hp.m_pos
  refine WP.mono (argsHead_wp' s (by rw [h.inv.s5]; exact hm))
    fun s₁ ⟨r3₁, r4₁, r5₁, r6₁, r7₁, r8₁, cs₁, mem₁, rd₁, wr₁, sp₁⟩ => ?_
  have h₁ := TwPost.keep hp h cs₁ sp₁ mem₁ rd₁ wr₁
  exact ⟨h₁, xpre_blocks hp h₁.inv.rd h₁.inv.wr (N := M s₀ - 1)
    (by rw [len_eq s₀]; omega) (by rw [r3₁, h.inv.s1]) (by rw [r4₁, h.inv.s2, a2_ofNat])
    (by rw [r5₁, h.inv.s6]) (by rw [r6₁, h.inv.s4]) (by rw [r7₁, h.inv.s5]) (by rw [r8₁, h.inv.s6])⟩

/-- The tweak of block `M`, at `zO`, and the arguments of the call on the
last whole block from it. -/
theorem decL1_wp {s₂ : State} (h₂ : AllPost false s₀ (M s₀ - 1) s₂) :
    WP isa (.block (nextT ++ split ++ argsL zO)) s₂ (DecL1 s₀) := by
  have wr₂ : s₂.wr = [dataR s₀, scrR s₀] := by rw [h₂.inv.wr, hp.wr]
  have rdwr₂ : s₂.rd ++ s₂.wr = [schR s₀, tschR s₀, iR s₀, dataR s₀, scrR s₀] := by
    rw [h₂.inv.rd, h₂.inv.wr, hp.rd, hp.wr]; rfl
  have inS (d n : Nat) (i : Nat) (h : d + i + n ≤ 2432) :
      (scrR s₀).Contains (S s₀ + BitVec.ofNat 64 d + BitVec.ofNat 64 i) n := by
    rw [Offset.add_add]; exact cS s₀ _ _ h
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (nextT_wp s₂ (T := Tp s₀) (Z := Zp s₀) (by rw [h₂.inv.s6]) (by rw [h₂.inv.s6])
    hp.t_z.symm
    (fun i hi => by rw [rdwr₂]; exact in_rw (r := scrR s₀) (by simp) (inS _ _ _ (by simp [tO]; omega)))
    (fun i hi => by rw [wr₂]; exact in_rw (r := scrR s₀) (by simp) (inS _ _ _ (by simp [zO]; omega)))
    (fun d hd => by rw [rdwr₂]; exact in_rw (r := scrR s₀) (by simp) (inS _ _ _ (by simp [zO]; omega)))
    (fun d hd => by rw [wr₂]; exact in_rw (r := scrR s₀) (by simp) (inS _ _ _ (by simp [zO]; omega))))
    fun s₃ ⟨g₃, _, f₃, z₃, rd₃, wr₃, sp₃⟩ => ?_
  have inv₃ : Inv s₀ s₃ := Inv.step hp h₂.inv (rs := [⟨Zp s₀, 16⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨tzR s₀, by simp, z_sub⟩) f₃
    (fun r hr h3 => g₃ r (pres_not_mul hr) h3) sp₃ rd₃ wr₃
  rw [WP.block_append_iff]
  refine WP.mono (split_wp inv₃) fun s₄ ⟨t1₄, _, g₄, sp₄, mem₄, rd₄, wr₄⟩ => ?_
  refine WP.mono (argsL_wp' s₄ (o := zO) (by decide))
    fun s₆ ⟨r3₆, r4₆, r5₆, r6₆, r7₆, r8₆, cs₆, mem₆, rd₆, wr₆, sp₆⟩ => ?_
  have inv₄ : Inv s₀ s₄ := Inv.regs hp inv₃ (keep_t1t2 g₄) sp₄ mem₄ rd₄ wr₄
  have inv₆ : Inv s₀ s₆ := Inv.regs hp inv₄ (fun r hr _ => cs₆ r hr) sp₆ mem₆ rd₆ wr₆
  have m₆ : s₆.mem = s₃.mem := by rw [mem₆, mem₄]
  refine ⟨inv₆, xpre_last hp inv₆.rd inv₆.wr (.inr rfl) (by rw [r3₆, inv₄.s1])
    (by rw [r4₆, inv₄.s2, a2_ofNat]) (by rw [r5₆, inv₄.s6]) (by rw [r6₆]; exact last_of hp inv₄.s4 t1₄) r7₆
    (by rw [r8₆, inv₄.s6]),
    ⟨s₂.mem, h₂.mem, by rw [m₆]; exact f₃, by rw [m₆]; exact z₃⟩⟩

/-- The call on the last whole block from the tweak of block `M`. -/
theorem decL2_wp (ok : XtsOk false Impl.AesXts.RISCV64.decrypt)
    (nf : Impl.AesXts.RISCV64.decrypt.noFrames = true) {s : State} (h : DecL1 s₀ s) :
    WP isa decCall s (DecL2 s₀) := by
  have hm := hp.m_pos
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  obtain ⟨m, ⟨hout, htw, hfr⟩, f₃, z₃⟩ := h.mem
  refine WP.mono (xts_call false ok nf h.pre) fun s₇ c₇ => ?_
  have tL : Region.Sub ⟨Tp s₀, 16⟩ (scrR s₀) := sub_trans t_sub tz_sub
  have zL : Region.Sub ⟨Zp s₀, 16⟩ (scrR s₀) := sub_trans z_sub tz_sub
  have eW := hp.sched_frame h.inv.frame (fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp)
  refine ⟨Inv.call hp h.inv z_sub (.inl hp.l_sub) c₇, m, ⟨hout, htw, hfr⟩, ?_, ?_, ?_, ?_⟩
  · rw [Proof.AesXts.Unit.crypt_one_of c₇.out, eW, z₃, htw, ← Proof.AesXts.next_succ,
      Nat.sub_add_cancel hm,
      Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_scr.sub_left hp.l_sub).sub_right zL) (by decide)]
  · rw [call_keeps hp (X := ⟨D s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega)) hp.hd_l zL c₇
      (by dsimp only; have := hp.wrapD; omega)]
    exact Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left (blocks_sub (by omega))).sub_right zL) (by dsimp only; have := hp.wrapD; omega)
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub tl_l zL c₇ (by dsimp only; omega)]
    exact Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left hp.tl_sub).sub_right zL) (by dsimp only; omega)
  · rw [Proof.Cmac.bytesAt_frame c₇.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.t_z
        · exact (hp.data_scr.symm.sub_left tL).sub_right hp.l_sub
        · exact hp.t_wk) (by decide),
      Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.t_z) (by decide), htw]

/-- The call on the last whole block from the tweak of block `M - 1`, and
the data unit's plaintext. -/
theorem decLast_wp (ok : XtsOk false Impl.AesXts.RISCV64.decrypt)
    (nf : Impl.AesXts.RISCV64.decrypt.noFrames = true)
    {s : State} {m₅ : Mem} (h : LastReady tO s₀ s m₅) (hm₅ : DecMem s₀ m₅) (hB : B s₀ ≠ 0) :
    WP isa decCall s (Fin false s₀) := by
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  have hm := hp.m_pos
  obtain ⟨m, ⟨hout, htw, hfr⟩, h5L, h5H, h5T, tw₅⟩ := hm₅
  refine WP.mono (xts_call false ok nf h.pre) fun s₁₂ c₁₂ => ?_
  refine ⟨Inv.call hp h.inv t_sub (.inl hp.l_sub) c₁₂, ?_⟩
  have sw := Proof.AesXts.Unit.swapMem_frame m₅ (L s₀) (B s₀)
  have tL : Region.Sub ⟨Tp s₀, 16⟩ (scrR s₀) := sub_trans t_sub tz_sub
  have eW' := hp.sched_frame h.inv.frame (fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp)
  rw [len_eq s₀]
  refine Proof.AesXts.Unit.dec_steal (m₃ := m) (m₅ := m₅) hm (Nat.pos_of_ne_zero hB) hb hout
    ⟨?_, ?_⟩ ⟨h5L, h5H, h5T⟩ ⟨?_, ?_, ?_⟩
  · exact Proof.Cmac.bytesAt_frame hfr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.l_hd
      · exact hp.data_scr.sub_left hp.l_sub) (by decide)
  · exact Proof.Cmac.bytesAt_frame hfr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.hd_tl.symm
      · exact hp.data_scr.sub_left hp.tl_sub) (by omega)
  · rw [Proof.AesXts.Unit.crypt_one_of c₁₂.out, eW', h.mem,
      Proof.Cmac.bytesAt_frame sw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_scr.symm.sub_left tL).sub_right hp.lb_sub) (by decide), tw₅]
  · rw [call_keeps hp (X := ⟨D s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega)) hp.hd_l tL c₁₂
      (by dsimp only; have := hp.wrapD; omega), h.mem]
    exact Proof.Cmac.bytesAt_frame sw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.hd_lb) (by dsimp only; have := hp.wrapD; omega)
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub tl_l tL c₁₂ (by dsimp only; omega), h.mem]

/-- Before the call on the last whole block from the tweak of block `M - 1`:
`Pₘ` and `CC` swapped into place. -/
def DecL3 (s₀ s : State) : Prop := ∃ m₅, DecMem s₀ m₅ ∧ LastReady tO s₀ s m₅

/-- The swap, after the call from the tweak of block `M`. -/
theorem decL3_wp {s : State} (h : DecL2 s₀ s) (hB : B s₀ ≠ 0) :
    WP isa (.seq (.seq (.block (split ++ lastAddr)) swap) (.block (argsL tO))) s (DecL3 s₀) := by
  refine WP.assoc' (WP.seq ?_)
  rw [WP.block_append_iff]
  refine WP.mono (split_wp h.inv) fun s₈ ⟨t1₈, t2₈, g₈, sp₈, mem₈, rd₈, wr₈⟩ => ?_
  have inv₈ : Inv s₀ s₈ := Inv.regs hp h.inv (keep_t1t2 g₈) sp₈ mem₈ rd₈ wr₈
  refine WP.mono (lastAddr_wp hp inv₈ t1₈) fun s₉ ⟨t3₉, g₉, sp₉, mem₉, rd₉, wr₉⟩ => ?_
  have inv₉ : Inv s₀ s₉ := Inv.regs hp inv₈ (keep_t3 g₉) sp₉ mem₉ rd₉ wr₉
  exact WP.mono (steal_wp hp (.inl rfl) inv₉ (by rw [g₉ _ (by decide), t1₈])
    (by rw [g₉ _ (by decide), t2₈]) t3₉ hB) fun _ h₂ => ⟨_, by rw [mem₉, mem₈]; exact h.mem, h₂⟩

/-- The steal of decryption, after the tweak. -/
theorem decSteal_wp (ok : XtsOk false Impl.AesXts.RISCV64.decrypt)
    (nf : Impl.AesXts.RISCV64.decrypt.noFrames = true)
    {s : State} (h : TwPost s₀ s) (hB : B s₀ ≠ 0) :
    WP isa decSteal s (Fin false s₀) := by
  refine WP.seq (WP.mono (argsHead_wp hp h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (blocks_call hp false ok nf (by rw [len_eq s₀]; omega) h₁.tw h₁.pre) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (decL1_wp hp h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (decL2_wp hp ok nf h₃) fun s₄ h₄ => ?_)
  exact WP.assoc (WP.assoc (WP.seq (WP.mono (decL3_wp hp h₄ hB) fun _ ⟨_, hm, h'⟩ => decLast_wp hp ok nf h' hm hB)))

theorem split_tw_wp {s : State} (h : TwPost s₀ s) :
    WP isa (.block split) s fun s' => TwPost s₀ s' ∧ s'.gpr .t2 = BitVec.ofNat 64 (B s₀) :=
  WP.mono (split_wp h.inv) fun _ ⟨_, t2₂, g₂, sp₂, mem₂, rd₂, wr₂⟩ =>
    ⟨TwPost.keep hp h (fun r hr => g₂ r (pres_ne hr (by decide)) (pres_ne hr (by decide))) sp₂ mem₂ rd₂ wr₂,
      t2₂⟩

theorem decrypt_wp (okE : XtsOk true Impl.AesXts.RISCV64.encrypt)
    (nfE : Impl.AesXts.RISCV64.encrypt.noFrames = true)
    (okD : XtsOk false Impl.AesXts.RISCV64.decrypt) (nfD : Impl.AesXts.RISCV64.decrypt.noFrames = true) :
    WP isa Impl.AesXts.RISCV64Unit.decrypt s₀ fun s' => Restored s₀ s' ∧ (unitRISCV64 false).post s₀ s' := by
  refine WP.seq (WP.mono (tweak_wp hp okE nfE) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (split_tw_wp hp h₁) fun s₂ ⟨h₂, t2₂⟩ => ?_)
  refine WP.seq (WP.mono (WP.ite (decide (B s₀ = 0)) (eval_b t2₂) (fun hb => ?_)
    (fun hb => decSteal_wp hp okD nfD h₂ (by simpa using hb))) fun s₅ h₅ => ?_)
  · refine WP.seq (WP.mono (argsAll_wp hp h₂) fun s₃ h₃ => ?_)
    exact WP.mono (blocks_call hp false okD nfD (by rw [len_eq s₀]; omega) h₃.tw h₃.pre)
      fun s₄ h₄ => whole_fin h₄ (by simpa using hb)
  · exact WP.mono (fin_wp hp h₅.inv) fun s' ⟨g, m, _⟩ => ⟨g, unit_post hp (by rw [m]; exact h₅.data)⟩

end

end VG.Proof.AesXts.RISCV64.Unit
