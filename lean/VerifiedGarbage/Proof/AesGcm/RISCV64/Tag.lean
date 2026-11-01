module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Crypt
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.AesGcm.RISCV64.Ghash1
import VerifiedGarbage.Proof.AesGcm.RISCV64.Init
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Callee
public import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-GCM on RISC-V: the tag (`tag o`)

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/Tag.lean`): `tag o` absorbs the lengths block of `s4`
and `s6` bytes, copies the accumulator `S` to `W + o` and XORs
`CIPH_K(J₀)` into it with `vg_aes_ctr32`, from the counter block `J₀` at the
state (`tag_ok`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom toBytes ofBytes)
open VG.Proof.Gcm (lensBlock)

/-- The regions `tag o` writes. -/
abbrev tagFrame (st w : Addr) (o : Nat) (sp : Addr) : List Region :=
  [⟨st, 32⟩, ⟨w + BitVec.ofNat 64 96, 16⟩, ⟨w + BitVec.ofNat 64 o, 16⟩, ⟨w + BitVec.ofNat 64 512, 2048⟩,
    below sp 2048]

/-- After `tag o`, from `m₀`: the tag of the accumulator `Y` (before the
lengths block) and the counter block `J`. -/
structure TagOut (V : Reg → BitVec 64) (sp : Addr) (o R : Nat) (H Y J : Block) (aLen cLen : Nat) (m₀ : Mem)
    (s : State) : Prop where
  env : Env V sp s
  out : bytesAt s.mem (V .s0 + BitVec.ofNat 64 o) 16 =
    toBytes (ghashFrom H Y [ofBytes (lensBlock aLen cLen)] ^^^ ciphOf m₀ (V .s2) R J)
  frame : Frame (tagFrame (V .s1) (V .s0) o sp) m₀ s.mem

/-- After the lengths block: what the arguments of the call need. -/
structure TagMid (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (H Y J : Block) (aLen cLen : Nat) (m₀ : Mem)
    (s : State) : Prop where
  env : Env V sp s
  hY : blockAt s.mem (V .s1 + BitVec.ofNat 64 16) = ghashFrom H Y [ofBytes (lensBlock aLen cLen)]
  hJ : blockAt s.mem (V .s1) = J
  hc : ciphOf s.mem (V .s2) R = ciphOf m₀ (V .s2) R
  frame : Frame (tFrame (V .s1) (V .s0) 16 sp) m₀ s.mem

/-- A 16-byte copy by two doublewords. -/
theorem bytesAt_copy2 (m : Mem) {p q : Addr} (hd : (⟨p, 8⟩ : Region).Disjoint ⟨q + BitVec.ofNat 64 8, 8⟩) :
    bytesAt ((m.writeW p (m.readW q 64)).writeW (p + BitVec.ofNat 64 8)
      ((m.writeW p (m.readW q 64)).readW (q + BitVec.ofNat 64 8) 64)) p 16 = bytesAt m q 16 := by
  rw [Proof.Cmac.bytesAt_store2, Mem.readW_writeW_sep (Region.Disjoint.sep hd.symm (Region.contains_self _ _)
    (Region.contains_self _ _)) (by decide), Proof.Cmac.le8_readW, Proof.Cmac.le8_readW,
    ← Proof.Cmac.bytesAt_split]

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s1) (V .s0))
include L

/-- The counter block `J₀` is apart from what `flush` and `lens` write. -/
theorem j_tFrame (hk : StkOk (V .s2) (V .s1) (V .s0) sp) :
    ∀ r ∈ tFrame (V .s1) (V .s0) 16 sp, (⟨V .s1, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using Lay.st_st (st := V .s1) (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide)
      (by decide)
  · simpa using L.st_w (a := 0) (n := 16) (d := 96) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
  · simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 256) (by decide) (.inr ⟨by decide, by decide⟩)
  · exact hk.st.sub_left (Region.sub_prefix (by decide))

/-- The lengths block absorbed, before the copy. -/
theorem tagLens_ok {R : Nat} {H J : Block} {s : State} (he : Env V sp s) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H) (hJ : blockAt s.mem (V .s1) = J) :
    WP isa (lens 16) s (TagMid V sp R H (blockAt s.mem (V .s1 + BitVec.ofNat 64 16)) J
      (s.gpr .s4).toNat (s.gpr .s6).toNat s.mem) := by
  refine WP.mono (lens_ok L (.inr rfl) he hH) fun s₁ ⟨he₁, _, hY₁, _, f₁⟩ => ?_
  exact ⟨he₁, hY₁, by rw [blockAt_frame f₁ (j_tFrame L he.stk'), hJ], ciph_frame f₁ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.cs.sub_right (Lay.stSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact he.stk'.c) hR, f₁⟩

/-- The accumulator copied to `W + o`, and the arguments of `vg_aes_ctr32`. -/
theorem tagArgs_ok {o : Nat} (ho : o = 0 ∨ o = 112) {s : State} (he : Env V sp s) :
    WP isa (.block (tagArgs o)) s fun s' =>
      s'.mem = (s.mem.writeW (V .s0 + BitVec.ofNat 64 o) (s.mem.readW (V .s1 + BitVec.ofNat 64 16) 64)).writeW
        (V .s0 + BitVec.ofNat 64 (o + 8))
        ((s.mem.writeW (V .s0 + BitVec.ofNat 64 o) (s.mem.readW (V .s1 + BitVec.ofNat 64 16) 64)).readW
          (V .s1 + BitVec.ofNat 64 24) 64) ∧
      s'.gpr .a0 = V .s2 ∧ s'.gpr .a1 = V .s3 ∧ s'.gpr .a2 = V .s1 ∧
      s'.gpr .a3 = V .s0 + BitVec.ofNat 64 o ∧ s'.gpr .a4 = BitVec.ofNat 64 1 ∧
      s'.gpr .a5 = V .s0 + BitVec.ofNat 64 512 ∧
      (∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → r ≠ .a4 → r ≠ .a5 → s'.gpr r = s.gpr r) ∧
      Keeps' s s' := by
  have h28 := he.s3; have h29 := he.s2; have h30 := he.s1; have h31 := he.s0
  have ho8 : o % 8 = 0 := by omega
  have hob : o + 16 ≤ 128 := by omega
  simp only [tagArgs]
  refine Steps.wp_ld (off := 16) (a := V .s1 + BitVec.ofNat 64 16) (by decide) (by rw [h30])
    (L.stal (by decide) (by decide)) (he.perm.stR (by decide)) fun s₁ u₁ => ?_
  refine Steps.wp_sd (off := o) (a := V .s0 + BitVec.ofNat 64 o) (by omega)
    (by rw [u₁.other _ (by decide), h31]) (L.wal8 ho8 (by omega))
    (by rw [u₁.wr]; exact he.perm.wW (by omega)) fun s₂ u₂ => ?_
  refine Steps.wp_ld (off := 24) (a := V .s1 + BitVec.ofNat 64 24) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide), h30]) (L.stal (by decide) (by decide))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact he.perm.stR (by decide)) fun s₃ u₃ => ?_
  refine Steps.wp_sd (off := o + 8) (a := V .s0 + BitVec.ofNat 64 (o + 8)) (by omega)
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h31]) (L.wal8 (by omega) (by omega))
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact he.perm.wW (by omega)) fun s₄ u₄ => ?_
  have g : ∀ r, r ≠ .t0 → s₄.gpr r = s.gpr r := fun r hr => by
    rw [u₄.gpr, u₃.other _ hr, u₂.gpr, u₁.other _ hr]
  refine Steps.wp_mv fun s₅ u₅ => Steps.wp_mv fun s₆ u₆ => Steps.wp_mv fun s₇ u₇ =>
    Steps.wp_addi (imm := o) (by omega) fun s₈ u₈ => Steps.wp_li (imm := 1) (by decide) fun s₉ u₉ =>
    Steps.wp_addi (imm := scrO) (by decide) fun s₁₀ u₁₀ => WP.block_nil ?_
  have g₉ : ∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → r ≠ .a4 → s₉.gpr r = s.gpr r :=
    fun r h0 h1 h2 h3 h4 h5 => by
      rw [u₉.other _ h5, u₈.other _ h4, u₇.other _ h3, u₆.other _ h2, u₅.other _ h1, g _ h0]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h0 h1 h2 h3 h4 h5 h6 => by rw [u₁₀.other _ h6, g₉ r h0 h1 h2 h3 h4 h5],
    ⟨?_, ?_, ?_⟩⟩
  · rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.gpr, u₁.mem]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.gpr, g _ (by decide), h29]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.gpr, u₅.other _ (by decide), g _ (by decide), h28]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
      u₆.other _ (by decide), u₅.other _ (by decide), g _ (by decide), h30]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), g _ (by decide), h31]
  · rw [u₁₀.other _ (by decide), u₉.gpr]
  · rw [u₁₀.gpr, g₉ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h31]; rfl
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-- The arguments of `vg_aes_ctr32` on the tag at `W + o`, with the counter block `J₀` at the state. -/
theorem ctrTag_mk {o R : Nat} (ho : o = 0 ∨ o = 112) {s : State} (he : Env V sp s)
    (h3 : s.gpr .a0 = V .s2) (h4 : s.gpr .a1 = BitVec.ofNat 64 R) (h5 : s.gpr .a2 = V .s1)
    (h6 : s.gpr .a3 = V .s0 + BitVec.ofNat 64 o) (h7 : s.gpr .a4 = BitVec.ofNat 64 1)
    (h8 : s.gpr .a5 = V .s0 + BitVec.ofNat 64 512) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    CtrCall s (V .s2) (V .s1) (V .s0 + BitVec.ofNat 64 o) (V .s0 + BitVec.ofNat 64 512) R 1 := by
  have hoW : o + 16 ≤ 16 ∨ (96 ≤ o ∧ o + 16 ≤ 2560) := by omega
  refine ⟨h3, h4, h5, h6, h7, h8, hR, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
  · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by omega))
  · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
  · simpa using L.st_w (a := 0) (n := 16) (d := o) (k := 16) (by decide) hoW
  · simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 2048) (by decide) (.inr ⟨by decide, by decide⟩)
  · simpa using Lay.w_w (w := V .s0) (a := o) (n := 16) (d := 512) (k := 2048) (by omega) (by omega)
      (by decide)
  · have := L.ww
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega
  · exact Covers.cons (covers_prefix he.perm.ctx (by decide)) (Covers.cons
      (covers_left (covers_prefix he.perm.st (by decide))) (Covers.cons (covers_left (he.perm.wC (by omega)))
        (Covers.cons (covers_left (he.perm.wC (by decide))) Covers.nil)))
  · exact Covers.cons (covers_prefix he.perm.st (by decide)) (Covers.cons (he.perm.wC (by omega))
      (Covers.cons (he.perm.wC (by decide)) Covers.nil))

/-- The copy and the call of `vg_aes_ctr32` on it. -/
theorem tagCall_ok {o R : Nat} (ho : o = 0 ∨ o = 112) {H Y J : Block} {aLen cLen : Nat} {m₀ : Mem} {s : State}
    (h : TagMid V sp R H Y J aLen cLen m₀ s) (h28 : V .s3 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    WP isa (.seq (.block (tagArgs o)) ctrCall) s (TagOut V sp o R H Y J aLen cLen m₀) := by
  have he := h.env
  have hoW : o + 16 ≤ 16 ∨ (96 ≤ o ∧ o + 16 ≤ 2560) := by omega
  refine WP.seq (WP.mono (tagArgs_ok L ho he) fun s₂ ⟨hm₂, a3, a4, a5, a6, a7, a8, hg₂, hk₂⟩ => ?_)
  rw [show V .s0 + BitVec.ofNat 64 (o + 8) = V .s0 + BitVec.ofNat 64 o + BitVec.ofNat 64 8 from
      (add_ofNat_assoc _ _ _).symm,
    show V .s1 + BitVec.ofNat 64 24 = V .s1 + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 by
      rw [BitVec.add_assoc]; rfl] at hm₂
  have he₂ : Env V sp s₂ := he.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr
  have f₂ : Frame [⟨V .s0 + BitVec.ofNat 64 o, 16⟩] s.mem s₂.mem := by
    rw [hm₂]; exact Proof.Cmac.frame_store2 _ _ _
  have hT : bytesAt s₂.mem (V .s0 + BitVec.ofNat 64 o) 16 = bytesAt s.mem (V .s1 + BitVec.ofNat 64 16) 16 := by
    rw [hm₂, bytesAt_copy2 _ (by
      rw [add_ofNat_assoc]; exact (L.st_w (a := 24) (n := 8) (d := o) (k := 8) (by decide) (by omega)).symm)]
  have dJo : (⟨V .s1, 16⟩ : Region).Disjoint ⟨V .s0 + BitVec.ofNat 64 o, 16⟩ := by
    simpa using L.st_w (a := 0) (n := 16) (d := o) (k := 16) (by decide) hoW
  have hJ₂ : blockAt s₂.mem (V .s1) = J := by
    rw [blockAt_frame f₂ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dJo, h.hJ]
  have hc₂ : ciphOf s₂.mem (V .s2) R = ciphOf m₀ (V .s2) R := by
    rw [ciph_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cw'.sub_right (Lay.wSub (by omega))) hR, h.hc]
  have hcall := ctrTag_mk L ho he₂ a3 (by rw [a4, h28]) a5 a6 a7 a8 hR
  refine WP.mono (ctr_call hcall) fun s₃ g => ?_
  have gout := g.out; have gframe := g.frame
  rw [blocksAt_one, blocksAt_one, ctr32_single, List.cons.injEq] at gout
  refine ⟨he₂.of_saved g.saved g.sp g.rd g.wr, ?_, ?_⟩
  · rw [Proof.Cmac.bytesAt_blockAt, gout.1, hJ₂,
      show Spec.Gcm.aesWith R (bytesAt s₂.mem (V .s2) (16 * (R + 1))) = ciphOf s₂.mem (V .s2) R from rfl,
      hc₂, show blockAt s₂.mem (V .s0 + BitVec.ofNat 64 o) = blockAt s.mem (V .s1 + BitVec.ofNat 64 16)
        by rw [blockAt, blockAt, hT], h.hY]
  · have fA : Frame (tagFrame (V .s1) (V .s0) o sp) m₀ s.mem := h.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., by simpa using Offset.sub_base (V .s1) (show 16 + 16 ≤ 32 by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨⟨V .s0 + BitVec.ofNat 64 512, 2048⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    refine (fA.trans (f₂.sub fun r hr => ?_)).trans (gframe.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩

/-- `tag o`, for `o` of 0 or 112. -/
theorem tag_ok {o R : Nat} (ho : o = 0 ∨ o = 112) {H J : Block} {s : State} (he : Env V sp s)
    (h28 : V .s3 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hH : blockAt s.mem (V .s2 + BitVec.ofNat 64 240) = H) (hJ : blockAt s.mem (V .s1) = J) :
    WP isa (tag o) s (TagOut V sp o R H (blockAt s.mem (V .s1 + BitVec.ofNat 64 16)) J
      (s.gpr .s4).toNat (s.gpr .s6).toNat s.mem) :=
  WP.seq (WP.mono (tagLens_ok L he hR hH hJ) fun _ hm => tagCall_ok L ho hm h28 hR)

end

end VG.Proof.AesGcm.RISCV64
