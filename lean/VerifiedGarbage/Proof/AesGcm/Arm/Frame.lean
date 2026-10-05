import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
import VerifiedGarbage.Spec.Gcm.Contract
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratch
import VerifiedGarbage.Proof.Framework.Arm.RegScratch

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.Tag`. -/
section

/-!
# AES-GCM on ARMv7: the tag (`tag o`)

Untrusted: everything here is checked by Lean. `tag o` absorbs the lengths
block of `r5:r4` and `r7:r6` bytes, copies the accumulator `S` to `W + o`
and XORs `CIPH_K(J₀)` into it with `vg_aes_ctr32`, from the counter block
`J₀` at the state (`tag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom toBytes ofBytes)
open VG.Proof.Gcm (lensBlock)
open VG.Proof.Cmac (store4)

/-- The regions `tag o` writes. -/
abbrev tagFrame (st w sp : BitVec 32) (o : Nat) : List Region :=
  [⟨State.addr st, 32⟩, ⟨State.addr w + BitVec.ofNat 64 96, 16⟩, ⟨State.addr w + BitVec.ofNat 64 o, 16⟩,
    ⟨State.addr w + BitVec.ofNat 64 512, 2048⟩, below sp]

/-- After `tag o`, from `m₀`: the tag of the accumulator `Y` (before the
lengths block) and the counter block `J`. -/
structure TagOut (c st w sp k7 k8 : BitVec 32) (o R : Nat) (H Y J : Block) (aLen cLen : Nat) (m₀ : Mem) (s : State) :
    Prop where
  env : Env c st w sp k7 k8 s
  out : bytesAt s.mem (State.addr w + BitVec.ofNat 64 o) 16 =
    toBytes (ghashFrom H Y [ofBytes (lensBlock aLen cLen)] ^^^ ciphOf m₀ (State.addr c) R J)
  frame : Frame (VG.Proof.AesGcm.Arm.tagFrame st w sp o) m₀ s.mem

/-- After the lengths block: what the arguments of the call need. -/
structure TagMid (c st w sp k7 k8 : BitVec 32) (R : Nat) (H Y J : Block) (aLen cLen : Nat) (m₀ : Mem) (s : State) :
    Prop where
  env : Env c st w sp k7 k8 s
  hY : blockAt s.mem (State.addr st + BitVec.ofNat 64 16) = ghashFrom H Y [ofBytes (lensBlock aLen cLen)]
  hJ : blockAt s.mem (State.addr st) = J
  hc : ciphOf s.mem (State.addr c) R = ciphOf m₀ (State.addr c) R
  frame : Frame (Proof.AesGcm.Arm.tFrame st w sp 16) m₀ s.mem

theorem bytesAt_copy4 (m : Mem) (p q : Addr) :
    bytesAt (store4 m p (m.readW q 32) (m.readW (q + BitVec.ofNat 64 4) 32) (m.readW (q + BitVec.ofNat 64 8) 32)
      (m.readW (q + BitVec.ofNat 64 12) 32)) p 16 = bytesAt m q 16 := by
  rw [Cmac.bytesAt_store4, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW, ← Cmac.bytesAt_split4]

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

/-- The lengths block absorbed, before the copy. -/
theorem tagLens_ok {R : Nat} {H J : Block} {s : State} (he : Env c st w sp k7 k8 s) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H) (hJ : blockAt s.mem (State.addr st) = J) :
    WP isa (lens 16) s (VG.Proof.AesGcm.Arm.TagMid c st w sp k7 k8 R H (blockAt s.mem (State.addr st + BitVec.ofNat 64 16)) J
      (s.gpr .r5 ++ s.gpr .r4).toNat (s.gpr .r7 ++ s.gpr .r6).toNat s.mem) := by
  refine WP.mono (lens_ok L (yo := 16) (.inr rfl) he hH) fun s₁ ⟨he₁, _, hY₁, f₁⟩ => ?_
  have dJ : ∀ r ∈ Proof.AesGcm.Arm.tFrame st w sp 16, (⟨State.addr st, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa using Lay.st_st (st := st) (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide)
        (by decide)
    · simpa using L.st_w (a := 0) (n := 16) (d := 96) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 256) (by decide) (.inr ⟨by decide, by decide⟩)
    · simpa using (L.stk_st (a := 0) (n := 16) (by decide)).symm
  refine ⟨he₁, hY₁, by rw [blockAt_frame f₁ dJ, hJ], ciph_frame f₁ (fun r hr => ?_) hR, f₁⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.kc.symm

omit L in
theorem sepW {m : Mem} {a b : Addr} {v : BitVec 32} (h : (⟨a, 4⟩ : Region).Disjoint ⟨b, 4⟩) :
    (m.writeW b v).readW a 32 = m.readW a 32 :=
  Mem.readW_writeW_sep (h.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)

/-- The accumulator copied to `W + o`, and the arguments of `vg_aes_ctr32`. -/
theorem tagArgs_ok {o : Nat} (ho : o = 0 ∨ o = 112) {s : State} (he : Env c st w sp k7 k8 s) :
    ∃ s', runBlock isa (tagArgs o) s = some s' ∧
      s'.mem = store4 s.mem (State.addr w + BitVec.ofNat 64 o) (s.mem.readW (State.addr st + BitVec.ofNat 64 16) 32)
        (s.mem.readW (State.addr st + BitVec.ofNat 64 16 + BitVec.ofNat 64 4) 32)
        (s.mem.readW (State.addr st + BitVec.ofNat 64 16 + BitVec.ofNat 64 8) 32)
        (s.mem.readW (State.addr st + BitVec.ofNat 64 16 + BitVec.ofNat 64 12) 32) ∧
      s'.gpr .r0 = c ∧ s'.gpr .r1 = k8 ∧ s'.gpr .r2 = st ∧ s'.gpr .r3 = w + BitVec.ofNat 32 o ∧
      s'.gpr .r12 = BitVec.ofNat 32 1 ∧ s'.gpr .lr = w + BitVec.ofNat 32 512 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h8 := he.r8; have h9 := he.r9; have h10 := he.r10; have h11 := he.r11
  have hoW : o + 16 ≤ 16 ∨ (96 ≤ o ∧ o + 16 ≤ 2560) := by omega
  have r₀ := he.perm.stR (show 16 + 4 ≤ 80 by decide)
  have r₁ := he.perm.stR (show 20 + 4 ≤ 80 by decide)
  have r₂ := he.perm.stR (show 24 + 4 ≤ 80 by decide)
  have r₃ := he.perm.stR (show 28 + 4 ≤ 80 by decide)
  have w₀ := he.perm.wW (show o + 4 ≤ 2560 by omega)
  have w₁ := he.perm.wW (show o + 4 + 4 ≤ 2560 by omega)
  have w₂ := he.perm.wW (show o + 8 + 4 ≤ 2560 by omega)
  have w₃ := he.perm.wW (show o + 12 + 4 ≤ 2560 by omega)
  have q : ∀ a d, a + 4 ≤ 80 → d + 4 ≤ o + 16 → o ≤ d →
      (⟨State.addr st + BitVec.ofNat 64 a, 4⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, 4⟩ :=
    fun a d h₁ h₂ h₃ => L.st_w h₁ (by omega)
  have o₀ : o < 4096 := by omega
  have o₁ : o + 4 < 4096 := by omega
  have o₂ : o + 8 < 4096 := by omega
  have o₃ : o + 12 < 4096 := by omega
  have eo : encodable (BitVec.ofNat 32 o) = true := by rcases ho with rfl | rfl <;> decide
  have e₁ := L.wA (d := o) (by omega)
  have e₂ := L.wA (d := o + 4) (by omega)
  have e₃ := L.wA (d := o + 8) (by omega)
  have e₄ := L.wA (d := o + 12) (by omega)
  have p₁ := fun m v => VG.Proof.AesGcm.Arm.sepW (m := m) (v := v) (q 20 o (by decide) (by omega) (by omega))
  have p₂ := fun m v => VG.Proof.AesGcm.Arm.sepW (m := m) (v := v) (q 24 o (by decide) (by omega) (by omega))
  have p₃ := fun m v => VG.Proof.AesGcm.Arm.sepW (m := m) (v := v) (q 24 (o + 4) (by decide) (by omega) (by omega))
  have p₄ := fun m v => VG.Proof.AesGcm.Arm.sepW (m := m) (v := v) (q 28 o (by decide) (by omega) (by omega))
  have p₅ := fun m v => VG.Proof.AesGcm.Arm.sepW (m := m) (v := v) (q 28 (o + 4) (by decide) (by omega) (by omega))
  have p₆ := fun m v => VG.Proof.AesGcm.Arm.sepW (m := m) (v := v) (q 28 (o + 8) (by decide) (by omega) (by omega))
  refine ⟨_, by simp only [tagArgs]; arun [h10, h11, L.stA, e₁, e₂, e₃, e₄, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, o₀, o₁, o₂,
    o₃, eo, p₁, p₂, p₃, p₄, p₅, p₆], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc]
  · simp [gpr_setReg, h9]
  · simp [gpr_setReg, h8]
  · simp [gpr_setReg, h10]
  · simp [gpr_setReg, h11]
  · simp [gpr_setReg]
  · simp [gpr_setReg, h11]
  · intro r a b d e f i; simp [gpr_setReg, a, b, d, e, f, i]
  all_goals rfl

/-- The arguments of `vg_aes_ctr32` on the tag at `W + o`, with the counter block `J₀` at the state. -/
theorem ctrTag_mk {o R : Nat} (ho : o = 0 ∨ o = 112) {s : State} (he : Env c st w sp k7 k8 s)
    (h0 : s.gpr .r0 = c) (h1 : s.gpr .r1 = BitVec.ofNat 32 R) (h2 : s.gpr .r2 = st)
    (h3 : s.gpr .r3 = w + BitVec.ofNat 32 o) (h12 : s.gpr .r12 = BitVec.ofNat 32 1)
    (hlr : s.gpr .lr = w + BitVec.ofNat 32 512) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    CtrCall s c st (w + BitVec.ofNat 32 o) (w + BitVec.ofNat 32 512) R 1 := by
  have hoW : o + 16 ≤ 16 ∨ (96 ≤ o ∧ o + 16 ≤ 2560) := by omega
  have hk := he.sp
  have eT := L.wA (d := o) (by omega)
  have eS := L.wA (d := 512) (by decide)
  have dJo : (⟨State.addr st, 16⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 o, 16⟩ := by
    simpa using L.st_w (a := 0) (n := 16) (by decide) hoW
  have hS : (⟨State.addr st, 16⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 512, 2048⟩ := by
    simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 2048) (by decide) (.inr ⟨by decide, by decide⟩)
  refine ⟨h0, h1, h2, h3, h12, hlr, hR, by rw [hk]; exact L.sp8, by have := L.cw; omega,
    by have := L.sw; omega, by rw [L.wN (by omega)]; have := L.ww; omega, by rw [L.wN (by decide)]; have := L.ww; omega,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [eT, eS, hk]
  · exact L.cs.sub_left (Region.sub_prefix (by decide)) |>.sub_right (Region.sub_prefix (by decide))
  · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by omega))
  · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
  · simpa using dJo
  · exact hS
  · simpa using Lay.w_w (w := w) (a := o) (n := 16) (d := 512) (k := 2048) (by omega) (by omega) (by decide)
  · exact L.kc.sub_right (Region.sub_prefix (by decide))
  · simpa using L.stk_st (a := 0) (n := 16) (by decide)
  · simpa using L.stk_w (a := o) (n := 16) (by omega)
  · exact L.stk_w (by decide)
  · exact covers_prefix he.perm.ctx (by decide)
  · exact covers_cons (covers_prefix he.perm.st (by decide))
      (covers_cons (he.perm.wC (by omega)) (he.perm.wC (by decide)))

/-- The copy and the call of `vg_aes_ctr32` on it. -/
theorem tagCall_ok {o R : Nat} (ho : o = 0 ∨ o = 112) {H Y J : Block} {aLen cLen : Nat} {m₀ : Mem} {s : State}
    (h : VG.Proof.AesGcm.Arm.TagMid c st w sp k7 k8 R H Y J aLen cLen m₀ s) (h8 : k8 = BitVec.ofNat 32 R) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    WP isa (.seq (.block (tagArgs o)) ctrFrame) s (VG.Proof.AesGcm.Arm.TagOut c st w sp k7 k8 o R H Y J aLen cLen m₀) := by
  have he := h.env
  have hoW : o + 16 ≤ 16 ∨ (96 ≤ o ∧ o + 16 ≤ 2560) := by omega
  obtain ⟨s₂, run₂, hm₂, h0, h1, h2, h3, h12, hlr, hg₂, hrd₂, hwr₂, hsp₂⟩ := VG.Proof.AesGcm.Arm.tagArgs_ok L ho he
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have he₂ : Env c st w sp k7 k8 s₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hsp₂ hrd₂ hwr₂
  have hk := he₂.sp
  have eT := L.wA (d := o) (by omega)
  have eS := L.wA (d := 512) (by decide)
  have f₂ : Frame [⟨State.addr w + BitVec.ofNat 64 o, 16⟩] s.mem s₂.mem := by rw [hm₂]; exact Cmac.frame_store4 _ _ _ _ _
  have hT : bytesAt s₂.mem (State.addr w + BitVec.ofNat 64 o) 16 = bytesAt s.mem (State.addr st + BitVec.ofNat 64 16) 16 := by
    rw [hm₂, VG.Proof.AesGcm.Arm.bytesAt_copy4]
  have dJo : (⟨State.addr st, 16⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 o, 16⟩ := by
    simpa using L.st_w (a := 0) (n := 16) (by decide) hoW
  have hJ₂ : blockAt s₂.mem (State.addr st) = J := by
    rw [blockAt_frame f₂ fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dJo, h.hJ]
  have hc₂ : ciphOf s₂.mem (State.addr c) R = ciphOf m₀ (State.addr c) R := by
    rw [ciph_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cw'.sub_right (Lay.wSub (by omega))) hR, h.hc]
  have hS : (⟨State.addr st, 16⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 512, 2048⟩ := by
    simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 2048) (by decide) (.inr ⟨by decide, by decide⟩)
  have hcall : CtrCall s₂ c st (w + BitVec.ofNat 32 o) (w + BitVec.ofNat 32 512) R 1 :=
    VG.Proof.AesGcm.Arm.ctrTag_mk L ho he₂ h0 (by rw [h1, h8]) h2 h3 h12 hlr hR
  refine WP.mono (ctr_call hcall) fun s₃ g => ?_
  have gout := g.out; have gframe := g.frame
  simp only [eT, eS, hk] at gout gframe
  rw [blocksAt_one, blocksAt_one, ctr32_single, List.cons.injEq] at gout
  refine ⟨he₂.of_saved g.saved g.sp g.rd g.wr, ?_, ?_⟩
  · rw [Cmac.bytesAt_blockAt, gout.1, hJ₂,
      show Spec.Gcm.aesWith R (bytesAt s₂.mem (State.addr c) (16 * (R + 1))) = ciphOf s₂.mem (State.addr c) R from rfl,
      hc₂, show blockAt s₂.mem (State.addr w + BitVec.ofNat 64 o) = blockAt s.mem (State.addr st + BitVec.ofNat 64 16)
        by rw [blockAt, blockAt, hT], h.hY]
  · have fA : Frame (VG.Proof.AesGcm.Arm.tagFrame st w sp o) m₀ s.mem := h.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., by simpa using Offset.sub_base (State.addr st) (show 16 + 16 ≤ 32 by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨⟨State.addr w + BitVec.ofNat 64 512, 2048⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    refine (fA.trans (f₂.sub fun r hr => ?_)).trans (gframe.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩

/-- `tag o`, for `o` of 0 or 112. -/
theorem tag_ok {o R : Nat} (ho : o = 0 ∨ o = 112) {H J : Block} {s : State} (he : Env c st w sp k7 k8 s)
    (h8 : k8 = BitVec.ofNat 32 R) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H) (hJ : blockAt s.mem (State.addr st) = J) :
    WP isa (tag o) s (VG.Proof.AesGcm.Arm.TagOut c st w sp k7 k8 o R H (blockAt s.mem (State.addr st + BitVec.ofNat 64 16)) J
      (s.gpr .r5 ++ s.gpr .r4).toNat (s.gpr .r7 ++ s.gpr .r6).toNat s.mem) :=
  WP.seq (WP.mono (VG.Proof.AesGcm.Arm.tagLens_ok L he hR hH hJ) fun _ hm => VG.Proof.AesGcm.Arm.tagCall_ok L ho hm h8 hR)

end

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.J0`. -/
section

/-!
# AES-GCM on ARMv7: the pre-counter block (`j0`)

Untrusted: everything here is checked by Lean. `j0` writes `J₀` for the
`r5`-byte nonce at `r4` to the state: its words and `0x00000001` for a
12-byte nonce (`j012_ok`), and otherwise GHASH of the nonce padded with
zeros and the lengths block, with `absorb`, `flush` and `lens` on the
accumulator at the state's first block (`j0hash_ok`), the nonce's length
kept in `r7`. `initState` then zeroes the accumulator and writes the first
counter block `inc₃₂(J₀)` (`initState_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashFrom ghash blocks zeros padLen ofBytes inc32)
open VG.Proof.Gcm (Absorbed lensBlock)
open VG.Proof.Cmac (le4 store4)

theorem inc32_words (a b c d : BitVec 32) : inc32 (a ++ b ++ c ++ d) = a ++ b ++ c ++ (d + 1) := by
  have h₁ : (a ++ b ++ c ++ d).extractLsb' 32 96 = a ++ b ++ c := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
    simp only [show ¬ (32 + i < 32) by omega, ite_false, show 32 + i - 32 = i by omega]
  have h₂ : (a ++ b ++ c ++ d).extractLsb' 0 32 = d := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]; simp [hi]
  simp only [inc32, h₁, h₂]

theorem le4_one : le4 (BitVec.ofNat 32 0x01000000) = [0, 0, 0, 1] := by decide

/-- A block from the bytes of its four little-endian words. -/
theorem ofBytes_le4 (a b c d : BitVec 32) :
    ofBytes (le4 a ++ le4 b ++ le4 c ++ le4 d) = byteRev32 a ++ byteRev32 b ++ byteRev32 c ++ byteRev32 d := by
  have h := Cmac.le4_rev4 (byteRev32 a) (byteRev32 b) (byteRev32 c) (byteRev32 d)
  rw [Cmac.byteRev32_byteRev32, Cmac.byteRev32_byteRev32, Cmac.byteRev32_byteRev32,
    Cmac.byteRev32_byteRev32] at h
  rw [h, Cmac.ofBytes_toBytes]

/-- The regions `j0` writes. -/
abbrev j0Frame (st w sp : BitVec 32) : List Region :=
  [⟨State.addr st, 80⟩, ⟨State.addr w + BitVec.ofNat 64 96, 16⟩, ⟨State.addr w + BitVec.ofNat 64 512, 256⟩, below sp]

/-- Before `j0`: the `n`-byte nonce at `Np`. -/
structure J0In (c st w sp k7 k8 : BitVec 32) (H : Block) (Np : BitVec 32) (n : Nat) (s : State) : Prop where
  env : Env c st w sp k7 k8 s
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H
  r4 : s.gpr .r4 = Np
  r5 : s.gpr .r5 = BitVec.ofNat 32 n
  data : DataOk st w sp s Np n

/-- `J₀` written, from `m₀`, with some value of `r7`. -/
structure J0Mid (c st w sp k8 : BitVec 32) (H : Block) (iv : List Byte) (m₀ : Mem) (s : State) : Prop where
  env : ∃ k7, Env c st w sp k7 k8 s
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H
  j0 : blockAt s.mem (State.addr st) = Spec.Gcm.j0 H iv
  frame : Frame (VG.Proof.AesGcm.Arm.j0Frame st w sp) m₀ s.mem

/-- After `j0`: `J₀`, the accumulator zeroed and the first counter block. -/
structure J0Out (c st w sp k8 : BitVec 32) (H : Block) (iv : List Byte) (m₀ : Mem) (s : State) : Prop where
  env : ∃ k7, Env c st w sp k7 k8 s
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H
  j0 : blockAt s.mem (State.addr st) = Spec.Gcm.j0 H iv
  y : blockAt s.mem (State.addr st + BitVec.ofNat 64 16) = 0
  cb : blockAt s.mem (State.addr st + BitVec.ofNat 64 48) = inc32 (Spec.Gcm.j0 H iv)
  frame : Frame (VG.Proof.AesGcm.Arm.j0Frame st w sp) m₀ s.mem

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

theorem ctx_j0Frame : ∀ r ∈ VG.Proof.AesGcm.Arm.j0Frame st w sp, (⟨State.addr c + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.cs.sub_left (Lay.ctxSub (by decide))
  · exact L.ctx_w (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact (L.stk_ctx (by decide)).symm

omit L in
theorem st_j0Frame {m m' : Mem} {d k : Nat} (h : Frame [⟨State.addr st + BitVec.ofNat 64 d, k⟩] m m')
    (hk : d + k ≤ 80) : Frame (VG.Proof.AesGcm.Arm.j0Frame st w sp) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., Lay.stSub hk⟩

/-- `J₀` of a 12-byte nonce. -/
theorem j012_ok {H : Block} {Np : BitVec 32} {s : State} (h : VG.Proof.AesGcm.Arm.J0In c st w sp k7 k8 H Np 12 s) :
    WP isa (.block j012) s (VG.Proof.AesGcm.Arm.J0Mid c st w sp k8 H (bytesAt s.mem (State.addr Np) 12) s.mem) := by
  have he := h.env
  have h10 := he.r10
  have hd := h.data
  have a₁ := hd.addr (j := 4) (by decide)
  have a₂ := hd.addr (j := 8) (by decide)
  have r₀ := in_off hd.rd (show 0 + 4 ≤ 12 by decide) (by decide)
  have r₁ := in_off hd.rd (show 4 + 4 ≤ 12 by decide) (by decide)
  have r₂ := in_off hd.rd (show 8 + 4 ≤ 12 by decide) (by decide)
  simp only [add_ofNat_zero] at r₀
  have w₀ := he.perm.stW (show 0 + 4 ≤ 80 by decide)
  have w₁ := he.perm.stW (show 4 + 4 ≤ 80 by decide)
  have w₂ := he.perm.stW (show 8 + 4 ≤ 80 by decide)
  have w₃ := he.perm.stW (show 12 + 4 ≤ 80 by decide)
  simp only [add_ofNat_zero] at w₀
  have h4 := h.r4
  obtain ⟨s', run, hm, hg, hrd, hwr, hsp⟩ : ∃ s', runBlock isa j012 s = some s' ∧
      s'.mem = store4 s.mem (State.addr st) (s.mem.readW (State.addr Np) 32)
        (s.mem.readW (State.addr Np + BitVec.ofNat 64 4) 32) (s.mem.readW (State.addr Np + BitVec.ofNat 64 8) 32)
        (BitVec.ofNat 32 0x01000000) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
    refine ⟨_, by simp only [j012]; arun [h4, h10, add_ofNat_zero, a₁, a₂, L.stA, r₀, r₁, r₂, w₀, w₁, w₂, w₃],
      ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, reduceCtorEq, store4_eq]
    · intro r a b d e; simp [gpr_setReg, a, b, d, e]
    all_goals rfl
  refine WP.of_runBlock ⟨s', run, ?_⟩
  have f : Frame [⟨State.addr st + BitVec.ofNat 64 0, 16⟩] s.mem s'.mem := by
    rw [hm]; simpa using Cmac.frame_store4 (m := s.mem) (State.addr st) _ _ _ _
  refine ⟨⟨k7, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide) (by decide) (by decide))
      hsp hrd hwr⟩, ?_, ?_, VG.Proof.AesGcm.Arm.st_j0Frame f (by decide)⟩
  · rw [blockAt_frame f fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by decide), h.hH]
  · have hb : bytesAt s.mem (State.addr Np) 12 = bytesAt s.mem (State.addr Np) 4 ++
        bytesAt s.mem (State.addr Np + BitVec.ofNat 64 4) 4 ++ bytesAt s.mem (State.addr Np + BitVec.ofNat 64 8) 4 := by
      rw [show (12 : Nat) = 4 + 8 from rfl, bytesAt_add, show (8 : Nat) = 4 + 4 from rfl, bytesAt_add,
        add_ofNat_assoc, List.append_assoc]
    rw [Proof.Gcm.j0_12 _ (length_bytesAt _ _ _), blockAt, hm, Cmac.bytesAt_store4, Cmac.le4_readW,
      Cmac.le4_readW, Cmac.le4_readW, VG.Proof.AesGcm.Arm.le4_one, hb]

/-- The first counter block, and the accumulator zeroed. -/
theorem initState_ok {H : Block} {iv : List Byte} {m₀ : Mem} {s : State} (h : VG.Proof.AesGcm.Arm.J0Mid c st w sp k8 H iv m₀ s) :
    WP isa (.block initState) s (VG.Proof.AesGcm.Arm.J0Out c st w sp k8 H iv m₀) := by
  obtain ⟨k7', he⟩ := h.env
  have h10 := he.r10
  have r₀ := he.perm.stR (show 0 + 4 ≤ 80 by decide)
  have r₁ := he.perm.stR (show 4 + 4 ≤ 80 by decide)
  have r₂ := he.perm.stR (show 8 + 4 ≤ 80 by decide)
  have r₃ := he.perm.stR (show 12 + 4 ≤ 80 by decide)
  simp only [add_ofNat_zero] at r₀
  have w₀ := he.perm.stW (show 48 + 4 ≤ 80 by decide)
  have w₁ := he.perm.stW (show 52 + 4 ≤ 80 by decide)
  have w₂ := he.perm.stW (show 56 + 4 ≤ 80 by decide)
  have w₃ := he.perm.stW (show 60 + 4 ≤ 80 by decide)
  have z₀ := he.perm.stW (show 16 + 4 ≤ 80 by decide)
  have z₁ := he.perm.stW (show 20 + 4 ≤ 80 by decide)
  have z₂ := he.perm.stW (show 24 + 4 ≤ 80 by decide)
  have z₃ := he.perm.stW (show 28 + 4 ≤ 80 by decide)
  generalize hw : s.mem.readW (State.addr st + BitVec.ofNat 64 12) 32 = w3
  have split : initState =
      [.ldr .r0 .r10 0, .ldr .r1 .r10 4, .ldr .r2 .r10 8, .ldr .r3 .r10 12, .rev .r3 .r3, addI .r3 .r3 1,
        .rev .r3 .r3, .str .r0 .r10 48, .str .r1 .r10 52, .str .r2 .r10 56, .str .r3 .r10 60] ++
      [.mov .r0 (imm 0), .str .r0 .r10 16, .str .r0 .r10 20, .str .r0 .r10 24, .str .r0 .r10 28] := rfl
  obtain ⟨s₁, run₁, hm₁, hg₁, hrd₁, hwr₁, hsp₁⟩ : ∃ s₁, runBlock isa
      [.ldr .r0 .r10 0, .ldr .r1 .r10 4, .ldr .r2 .r10 8, .ldr .r3 .r10 12, .rev .r3 .r3, addI .r3 .r3 1,
        .rev .r3 .r3, .str .r0 .r10 48, .str .r1 .r10 52, .str .r2 .r10 56, .str .r3 .r10 60] s = some s₁ ∧
      s₁.mem = store4 s.mem (State.addr st + BitVec.ofNat 64 48) (s.mem.readW (State.addr st) 32)
        (s.mem.readW (State.addr st + BitVec.ofNat 64 4) 32) (s.mem.readW (State.addr st + BitVec.ofNat 64 8) 32)
        (byteRev32 (byteRev32 w3 + BitVec.ofNat 32 1)) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
      s₁.sp = s.sp := by
    refine ⟨_, by arun [h10, add_ofNat_zero, L.stA, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, gpr_setReg, ite_true, ite_false, reduceCtorEq, store4_eq, add_ofNat_assoc,
        rev_eq, hw, Nat.reduceAdd]
    · intro r a b d e; simp [gpr_setReg, a, b, d, e]
    all_goals rfl
  have h10' : s₁.gpr .r10 = st := by rw [hg₁ _ (by decide) (by decide) (by decide) (by decide), h10]
  rw [← hwr₁] at z₀ z₁ z₂ z₃
  obtain ⟨s', run, hm, hg, hrd, hwr, hsp⟩ : ∃ s', runBlock isa
      [.mov .r0 (imm 0), .str .r0 .r10 16, .str .r0 .r10 20, .str .r0 .r10 24, .str .r0 .r10 28] s₁ = some s' ∧
      s'.mem = store4 s₁.mem (State.addr st + BitVec.ofNat 64 16) 0 0 0 0 ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s₁.gpr r) ∧ s'.rd = s₁.rd ∧ s'.wr = s₁.wr ∧ s'.sp = s₁.sp := by
    refine ⟨_, by arun [h10', L.stA, z₀, z₁, z₂, z₃], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc, Nat.reduceAdd]; rfl
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  rw [split]
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s', run, ?_⟩⟩)
  have f₄ : Frame [⟨State.addr st + BitVec.ofNat 64 48, 16⟩] s.mem s₁.mem := by
    rw [hm₁]; exact Cmac.frame_store4 _ _ _ _ _
  have fz : Frame [⟨State.addr st + BitVec.ofNat 64 16, 16⟩] s₁.mem s'.mem := by
    rw [hm]; exact Cmac.frame_store4 _ _ _ _ _
  have dz : (⟨State.addr st + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint ⟨State.addr st + BitVec.ofNat 64 16, 16⟩ :=
    Lay.st_st (.inr (by decide)) (by decide) (by decide)
  have ff : Frame [⟨State.addr st + BitVec.ofNat 64 0, 80⟩] s.mem s'.mem := by
    refine (f₄.sub fun r hr => ?_).trans (fz.sub fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr <;>
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  have hJ : blockAt s'.mem (State.addr st) = blockAt s.mem (State.addr st) := by
    rw [blockAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simpa using Lay.st_st (st := st) (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide)
          (by decide)),
      blockAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simpa using Lay.st_st (st := st) (a := 0) (n := 16) (d := 48) (k := 16) (.inl (by decide)) (by decide)
          (by decide))]
  refine ⟨⟨k7', he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        rw [hg _ (by decide), hg₁ _ (by decide) (by decide) (by decide) (by decide)])
      (hsp.trans hsp₁) (hrd.trans hrd₁) (hwr.trans hwr₁)⟩, ?_, by rw [hJ, h.j0], ?_, ?_,
    h.frame.trans (VG.Proof.AesGcm.Arm.st_j0Frame ff (by decide))⟩
  · rw [blockAt_frame ff (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by decide)), h.hH]
  · rw [blockAt, hm, Cmac.bytesAt_store4, Cmac.le4_zero]; decide
  · rw [blockAt, bytesAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dz) (by decide),
      hm₁, Cmac.bytesAt_store4, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW, ← h.j0, blockAt,
      Cmac.ofBytes_rev4, ← Cmac.le4_readW s.mem (State.addr st), ← Cmac.le4_readW, ← Cmac.le4_readW, VG.Proof.AesGcm.Arm.ofBytes_le4, hw,
      Cmac.byteRev32_byteRev32, VG.Proof.AesGcm.Arm.inc32_words]
    rfl

end

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

omit L in
theorem abs_j0Frame {m m' : Mem} (h : Frame (absFrame st w sp 0) m m') : Frame (VG.Proof.AesGcm.Arm.j0Frame st w sp) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

omit L in
theorem t_j0Frame {m m' : Mem} (h : Frame (tFrame st w sp 0) m m') : Frame (VG.Proof.AesGcm.Arm.j0Frame st w sp) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

/-- The first block of `j0hash`: the accumulator at the state zeroed, the
nonce's length kept in `r7`. -/
theorem j0zero_ok {H : Block} {Np : BitVec 32} {n : Nat} {s : State} (h : VG.Proof.AesGcm.Arm.J0In c st w sp k7 k8 H Np n s) :
    WP isa (.block [.mov .r0 (imm 0), .str .r0 .r10 0, .str .r0 .r10 4, .str .r0 .r10 8, .str .r0 .r10 12,
      .mov .r7 (.reg .r5), .mov .r6 (imm 0)]) s
      (fun s' => AbsIn c st w sp (BitVec.ofNat 32 n) k8 0 H [] Np n s' ∧
        blockAt s'.mem (State.addr st + BitVec.ofNat 64 0) = 0 ∧
        bytesAt s'.mem (State.addr Np) n = bytesAt s.mem (State.addr Np) n ∧
        Frame [⟨State.addr st, 16⟩] s.mem s'.mem) := by
  have he := h.env
  have hd := h.data
  have h10 := he.r10
  have z₀ := he.perm.stW (show 0 + 4 ≤ 80 by decide)
  have z₁ := he.perm.stW (show 4 + 4 ≤ 80 by decide)
  have z₂ := he.perm.stW (show 8 + 4 ≤ 80 by decide)
  have z₃ := he.perm.stW (show 12 + 4 ≤ 80 by decide)
  simp only [add_ofNat_zero] at z₀
  obtain ⟨s₁, run₁, hm₁, h6, h7, hg₁, hrd₁, hwr₁, hsp₁⟩ : ∃ s₁, runBlock isa [.mov .r0 (imm 0), .str .r0 .r10 0,
      .str .r0 .r10 4, .str .r0 .r10 8, .str .r0 .r10 12, .mov .r7 (.reg .r5), .mov .r6 (imm 0)] s = some s₁ ∧
      s₁.mem = store4 s.mem (State.addr st) 0 0 0 0 ∧ s₁.gpr .r6 = BitVec.ofNat 32 0 ∧
      s₁.gpr .r7 = BitVec.ofNat 32 n ∧ (∀ r, r ≠ .r0 → r ≠ .r6 → r ≠ .r7 → s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.sp = s.sp := by
    refine ⟨_, by arun [h10, add_ofNat_zero, L.stA, z₀, z₁, z₂, z₃], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, store4_eq]; rfl
    · simp [gpr_setReg]
    · simp [gpr_setReg, h.r5]
    · intro r a b d; simp [gpr_setReg, a, b, d]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have he₁ := he.set7 h7 (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)) hsp₁ hrd₁ hwr₁
  have f₁ : Frame [⟨State.addr st, 16⟩] s.mem s₁.mem := by rw [hm₁]; exact Cmac.frame_store4 _ _ _ _ _
  have dD : ∀ r ∈ [(⟨State.addr st, 16⟩ : Region)], (⟨State.addr Np, n⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hd.st.sub_right (Region.sub_prefix (by decide))
  refine ⟨⟨he₁, by rw [hg₁ _ (by decide) (by decide) (by decide), h.r4],
    by rw [hg₁ _ (by decide) (by decide) (by decide), h.r5], h6, hd.of_eq hrd₁ hwr₁, ?_⟩, ?_,
    bytesAt_frame f₁ dD (by have := hd.lt; omega), f₁⟩
  · rw [blockAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using L.ctx_st (a := 240) (n := 16) (d := 0) (k := 16) (by decide) (by decide)), h.hH]
  · rw [add_ofNat_zero, blockAt, hm₁, Cmac.bytesAt_store4, Cmac.le4_zero]; decide

/-- `J₀` of a nonce of any length but 12: GHASH of the nonce padded and of
the lengths block. -/
theorem j0hash_ok {H : Block} {Np : BitVec 32} {n : Nat} {s : State} (h : VG.Proof.AesGcm.Arm.J0In c st w sp k7 k8 H Np n s)
    (hn : n ≠ 12) :
    WP isa j0hash s (VG.Proof.AesGcm.Arm.J0Mid c st w sp k8 H (bytesAt s.mem (State.addr Np) n) s.mem) := by
  have hd := h.data
  have hlt := hd.lt32
  refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.j0zero_ok L h) fun s₁ ⟨hai, hY₁, hiv, f₁⟩ => ?_)
  refine WP.seq (WP.mono (absorb_ok L (yo := 0) (.inl rfl) hai) fun s₂ ho => ?_)
  rw [List.nil_append, hiv] at ho
  have hab₂ := ho.abs (Proof.Gcm.absorbed_nil H hY₁)
  have he₂ := ho.env
  have hH₂ : blockAt s₂.mem (State.addr c + BitVec.ofNat 64 240) = H := by
    rw [blockAt_frame ho.frame (ctx_absFrame L (.inl rfl)), hai.hH]
  obtain ⟨s₃, run₃, h6₃, hg₃, hk₃⟩ : ∃ s₃, runBlock isa [.dp .and .r6 .r7 (imm 15)] s₂ = some s₃ ∧
      s₃.gpr .r6 = BitVec.ofNat 32 (n % 16) ∧ (∀ r, r ≠ .r6 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
    have hand := and15 (BitVec.ofNat 32 n)
    rw [toNat32 hlt] at hand
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, he₂.r7, hand]
    · intro r a; simp [gpr_setReg, a]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hk₃.sp hk₃.rd hk₃.wr
  refine WP.seq (WP.mono (flush_ok L (yo := 0) (.inl rfl) (x := bytesAt s.mem (State.addr Np) n) ⟨he₃, by
    rw [hk₃.mem, hH₂]⟩ (by rw [h6₃, length_bytesAt])) fun s₄ hf => ?_)
  have he₄ := hf.env
  obtain ⟨s₅, run₅, h4₅, h5₅, h6₅, h7₅, hg₅, hk₅⟩ : ∃ s₅, runBlock isa [.mov .r4 (imm 0), .mov .r5 (imm 0),
      .mov .r6 (.reg .r7), .mov .r7 (imm 0)] s₄ = some s₅ ∧
      s₅.gpr .r4 = 0 ∧ s₅.gpr .r5 = 0 ∧ s₅.gpr .r6 = BitVec.ofNat 32 n ∧ s₅.gpr .r7 = 0 ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · simp [gpr_setReg, he₄.r7]
    · simp [gpr_setReg]
    · intro r a b d e; simp [gpr_setReg, a, b, d, e]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ := he₄.set7 h7₅ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide) (by decide) (by decide))
    hk₅.sp hk₅.rd hk₅.wr
  refine WP.mono (lens_ok L (yo := 0) (.inl rfl) (H := H) he₅ (by rw [hk₅.mem]; exact hf.hH))
    fun s₆ ⟨he₆, hH₆, hY₆, f₆⟩ => ?_
  refine ⟨⟨_, he₆⟩, hH₆, ?_, ?_⟩
  · have hw := (hf.abs (by rw [hk₃.mem]; exact hab₂)).whole_eq (by
      simp only [List.length_append, length_bytesAt, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod n)
    rw [length_bytesAt] at hw
    rw [h4₅, h5₅, h6₅, h7₅, show ((0 : BitVec 32) ++ (0 : BitVec 32)).toNat = 0 from rfl,
      show ((0 : BitVec 32) ++ BitVec.ofNat 32 n).toNat = n by
        rw [Proof.Gcm.toNat_append, toNat32 hlt]; simp, hk₅.mem, hw] at hY₆
    rw [Proof.Gcm.j0_eq H (by rw [length_bytesAt]; exact hn), length_bytesAt, ← hY₆, add_ofNat_zero]
  · have g₁ : Frame (VG.Proof.AesGcm.Arm.j0Frame st w sp) s.mem s₁.mem := f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
    have g₄ := VG.Proof.AesGcm.Arm.t_j0Frame hf.frame
    have g₆ := VG.Proof.AesGcm.Arm.t_j0Frame f₆
    rw [hk₃.mem] at g₄
    rw [hk₅.mem] at g₆
    exact ((g₁.trans (VG.Proof.AesGcm.Arm.abs_j0Frame ho.frame)).trans g₄).trans g₆

/-- `j0`: the streaming state's `J₀`, accumulator and first counter block. -/
theorem j0_ok {H : Block} {Np : BitVec 32} {n : Nat} {s : State} (h : VG.Proof.AesGcm.Arm.J0In c st w sp k7 k8 H Np n s) :
    WP isa j0 s (VG.Proof.AesGcm.Arm.J0Out c st w sp k8 H (bytesAt s.mem (State.addr Np) n) s.mem) := by
  have hlt := h.data.lt32
  obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmpk_ok s .r5 h.r5 hlt (k := 12) (by decide) (by decide)
  have h₁ : VG.Proof.AesGcm.Arm.J0In c st w sp k7 k8 H Np n s₁ :=
    ⟨h.env.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁, by rw [hm₁]; exact h.hH, by rw [hg₁]; exact h.r4,
      by rw [hg₁]; exact h.r5, h.data.of_eq hrd₁ hwr₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  rw [← hm₁]
  refine WP.seq (WP.ite (decide (n = 12)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_))
  · have h12 : n = 12 := by simpa using ht
    subst h12
    exact WP.mono (VG.Proof.AesGcm.Arm.j012_ok L h₁) fun _ hm => VG.Proof.AesGcm.Arm.initState_ok L hm
  · exact WP.mono (VG.Proof.AesGcm.Arm.j0hash_ok L h₁ (by simpa using hf)) fun _ hm => VG.Proof.AesGcm.Arm.initState_ok L hm

end

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.Fn`. -/
section

/-!
# AES-GCM on ARMv7: what every function does

Untrusted: everything here is checked by Lean. Each function saves our
caller's `r4`–`r11` and `lr` at `W + 128` (`save_ok`) and restores them
(`restore_ok`, `exit_ok`); the pieces it runs in between never write there.

The postconditions quantify over what the state represents (the nonce, the
additional data, the text so far), which the code never looks at: each
function runs the same for all of them, so one run satisfies each instance
of its proof (`WP.forall_det`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.MdStream.Arm (saveMem saveList_ok readW_writeW_save)

/-- A run that satisfies `R`, and for each `i` with `P i`, `Q i`. -/
theorem WP.forall_det {c : Prog isa} {s : State} {ι : Sort _} {P : ι → Prop} {Q : ι → State → Prop}
    {R : State → Prop} (h₀ : WP isa c s R) (h : ∀ i, P i → WP isa c s (Q i)) :
    WP isa c s fun s' => R s' ∧ ∀ i, P i → Q i s' := by
  obtain ⟨t, s', e, r⟩ := h₀
  refine ⟨t, s', e, r, fun i hi => ?_⟩
  obtain ⟨t', s'', e', q⟩ := h i hi
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact q

/-- Code never changes the permissions or the stack pointer. -/
theorem WP.with_rdwr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨t, s', e, q⟩ := h
  obtain ⟨-, hw, -⟩ := Exec.rdwr e
  exact ⟨t, s', e, q, (Exec.rdwr e).1, hw, Exec.sp e⟩

/-- Where `save` puts our caller's registers. -/
def SavedAt (m : Mem) (w : BitVec 32) (s₀ : State) : Prop :=
  ∀ p ∈ saved, m.readW (State.addr w + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1

/-- The saved registers' slots. -/
abbrev savedR (w : BitVec 32) : Region := ⟨State.addr w + BitVec.ofNat 64 128, 36⟩

theorem saved_bound : ∀ p ∈ saved, 128 ≤ p.2 ∧ p.2 + 4 ≤ 164 := by decide

theorem saveMem_frame_off (m : Mem) (B : Addr) (g : Reg → BitVec 32) {lo L : Nat} (hL : lo + L < 2 ^ 32) :
    ∀ (l : List (Reg × Nat)), (∀ p ∈ l, lo ≤ p.2 ∧ p.2 + 4 ≤ lo + L) →
      Frame [⟨B + BitVec.ofNat 64 lo, L⟩] m (VG.Arm.Spill.saveMem m B g l) := by
  intro l
  induction l generalizing m with
  | nil => intro _; exact Frame.refl _ _
  | cons p l ih =>
    intro hl
    have h := hl p (by simp)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ h.1 (by omega) (by omega))).trans
      (ih _ fun q hq => hl q (List.mem_cons_of_mem _ hq))

set_option simprocs false in
theorem saveMem_slot (m : Mem) (B : Addr) (g : Reg → BitVec 32) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (VG.Arm.Spill.saveMem m B g saved).readW (B + BitVec.ofNat 64 d) 32 = g r := by
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  simp (disch := decide) only [saved, VG.Arm.Spill.saveMem, Mem.readW_writeW_self32, readW_writeW_save]

/-- Saving the registers at `b + 128`, where `b` holds `W`. -/
theorem save_ok {s : State} {b : Reg} {w : BitVec 32} (hb : s.gpr b = w) (hfit : w.toNat + 2560 ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr w, 2560⟩] s.wr) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → VG.Proof.AesGcm.Arm.SavedAt s'.mem w s →
      Frame [VG.Proof.AesGcm.Arm.savedR w] s.mem s'.mem → WP isa (.block rest) s' Q) :
    WP isa (.block (save b ++ rest)) s Q := by
  refine VG.Arm.Spill.saveList_ok (b := b) saved s Q (fun p hp => ?_) fun s' g rd wr sp m => k s' g rd wr sp ?_ ?_
  · have hbd := VG.Proof.AesGcm.Arm.saved_bound p hp
    rw [hb]
    exact ⟨by omega, by omega, in_off hw (by omega) (by decide)⟩
  · intro p hp
    rw [m, hb]; exact VG.Proof.AesGcm.Arm.saveMem_slot _ _ _ hp
  · rw [m, hb]; exact VG.Proof.AesGcm.Arm.saveMem_frame_off _ _ _ (by decide) saved fun p hp => VG.Proof.AesGcm.Arm.saved_bound p hp

/-- The saved registers stay where they are, outside a frame. -/
theorem SavedAt.frame {m m' : Mem} {w : BitVec 32} {s₀ : State} (h : VG.Proof.AesGcm.Arm.SavedAt m w s₀) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (VG.Proof.AesGcm.Arm.savedR w).Disjoint r) : VG.Proof.AesGcm.Arm.SavedAt m' w s₀ := by
  intro p hp
  have hb := VG.Proof.AesGcm.Arm.saved_bound p hp
  have hs : Region.Sub ⟨State.addr w + BitVec.ofNat 64 p.2, 4⟩ (VG.Proof.AesGcm.Arm.savedR w) := Offset.sub _ hb.1 (by omega)
  rw [hf.readW (r := ⟨State.addr w + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left hs) (by decide), h p hp]

/-- The end of every function: our caller's registers restored. -/
theorem restore_ok {s s₀ : State} {w : BitVec 32} (h11 : s.gpr .r11 = w) (hfit : w.toNat + 2560 ≤ 2 ^ 32)
    (hr : Covers [⟨State.addr w, 2560⟩] (s.rd ++ s.wr)) (hs : VG.Proof.AesGcm.Arm.SavedAt s.mem w s₀) (hsp : s.sp = s₀.sp) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .r0 = s.gpr .r0 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hA : ∀ d, d < 2560 → State.addr (w + BitVec.ofNat 32 d) = State.addr w + BitVec.ofNat 64 d :=
    fun d hd => addr_add (by omega)
  have r₁ := in_off hr (show 128 + 4 ≤ 2560 by decide) (by decide)
  have r₂ := in_off hr (show 132 + 4 ≤ 2560 by decide) (by decide)
  have r₃ := in_off hr (show 136 + 4 ≤ 2560 by decide) (by decide)
  have r₄ := in_off hr (show 140 + 4 ≤ 2560 by decide) (by decide)
  have r₅ := in_off hr (show 144 + 4 ≤ 2560 by decide) (by decide)
  have r₆ := in_off hr (show 148 + 4 ≤ 2560 by decide) (by decide)
  have r₇ := in_off hr (show 152 + 4 ≤ 2560 by decide) (by decide)
  have r₈ := in_off hr (show 156 + 4 ≤ 2560 by decide) (by decide)
  have r₉ := in_off hr (show 160 + 4 ≤ 2560 by decide) (by decide)
  have e : ∀ p ∈ saved, s.mem.readW (State.addr w + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1 := hs
  have e₁ := e (.r4, 128) (by simp [saved]); have e₂ := e (.r5, 132) (by simp [saved])
  have e₃ := e (.r6, 136) (by simp [saved]); have e₄ := e (.r7, 140) (by simp [saved])
  have e₅ := e (.r8, 144) (by simp [saved]); have e₆ := e (.r9, 148) (by simp [saved])
  have e₇ := e (.r10, 152) (by simp [saved]); have e₈ := e (.r11, 156) (by simp [saved])
  have e₉ := e (.lr, 160) (by simp [saved])
  simp only at e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
  refine WP.of_runBlock ⟨_, by simp only [restore, restored, List.map]; arun [h11, hA, r₁, r₂, r₃, r₄, r₅, r₆, r₇,
    r₈, r₉], ⟨fun r hr => ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [gpr_setReg, e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉]
  all_goals first | rfl | simp [gpr_setReg, sp_setReg, mem_setReg, rd_setReg, wr_setReg, hsp]

/-- The layout, from disjointness of the context, the state, `W` and the stack. -/
theorem Lay.of {c st w sp : BitVec 32} (cw : c.toNat + 256 ≤ 2 ^ 32) (sw : st.toNat + 80 ≤ 2 ^ 32)
    (ww : w.toNat + 2560 ≤ 2 ^ 32) (sp8 : 8 ≤ sp.toNat) (cs : (⟨State.addr c, 256⟩ : Region).Disjoint ⟨State.addr st, 80⟩)
    (cW : (⟨State.addr c, 256⟩ : Region).Disjoint ⟨State.addr w, 2560⟩)
    (sW : (⟨State.addr st, 80⟩ : Region).Disjoint ⟨State.addr w, 2560⟩)
    (kc : (below sp).Disjoint ⟨State.addr c, 256⟩) (ks : (below sp).Disjoint ⟨State.addr st, 80⟩)
    (kw : (below sp).Disjoint ⟨State.addr w, 2560⟩) : Lay c st w sp :=
  ⟨cw, sw, ww, sp8, cs, cW, sW.sub_right (Region.sub_prefix (by decide)), sW.sub_right (Lay.wSub (by decide)),
    kc, ks, kw⟩

theorem ctxH_eq (m : Mem) (p : Addr) : Spec.Gcm.ctxH m p = Spec.Gcm.blockAt m (p + BitVec.ofNat 64 240) := rfl

theorem toNat_mod16 (n : Nat) : (BitVec.ofNat 64 n).toNat % 16 = n % 16 := by
  rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide)]

theorem ofNat_lit (n : Nat) : (OfNat.ofNat n : Addr) = BitVec.ofNat 64 n := rfl

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp)
include L

theorem saved_absFrame {yo : Nat} (hyo : yo = 0 ∨ yo = 16) : ∀ r ∈ absFrame st w sp yo, (VG.Proof.AesGcm.Arm.savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem saved_tFrame {yo : Nat} (hyo : yo = 0 ∨ yo = 16) : ∀ r ∈ tFrame st w sp yo, (VG.Proof.AesGcm.Arm.savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by omega) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem saved_tagFrame {o : Nat} (ho : o = 0 ∨ o = 112) : ∀ r ∈ VG.Proof.AesGcm.Arm.tagFrame st w sp o, (VG.Proof.AesGcm.Arm.savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · simpa using (L.st_w (a := 0) (n := 32) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inr (by omega)) (by decide) (by omega)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem saved_j0Frame : ∀ r ∈ VG.Proof.AesGcm.Arm.j0Frame st w sp, (VG.Proof.AesGcm.Arm.savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using (L.st_w (a := 0) (n := 80) (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

theorem saved_crFrame {c k7 k8 : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (hd : DataW c st w sp k7 k8 s D n) :
    ∀ r ∈ crFrame st w sp D n, (VG.Proof.AesGcm.Arm.savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.ok.w.sub_right (Lay.wSub (by decide))).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

end

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.Contract`. -/
section

/-!
# AES-GCM on ARMv7: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Gcm/Contract.lean`, which imply these
(`Verified.lean`). Every function calls others in frames that push their
stack arguments in the 8 bytes below the stack pointer (`below`), which no
buffer overlaps.
-/

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr KeyRepr ctxCiph ctxH gctr inc32 j0 fullTag tagLenOk zeros encryptWith openResult)

/-- The 8 bytes below the stack pointer. -/
abbrev bel (s : State) : Region := ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩

/-- The `i`-th argument on the stack. -/
abbrev arg (s : State) (i : Nat) : BitVec 32 := stackArg s i

/-- The arguments on the stack, `n` words of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 4 * n⟩

abbrev roundsOk (s : State) : Prop :=
  (s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14

/-- A 64-bit argument on the stack, from word `i`. -/
abbrev arg64 (s : State) (i : Nat) : BitVec 64 := stackArg s (i + 1) ++ stackArg s i

/-- `vg_aes_gcm_init(key = r0, key_len = r1, ctx = r2, scratch = r3)`. -/
def initArm : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let ctx : Region := ⟨State.addr (s.gpr .r2), 256⟩
    let scr : Region := ⟨State.addr (s.gpr .r3), 2560⟩
    s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧
      (VG.Proof.AesGcm.Arm.bel s).Disjoint key ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint ctx ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint scr ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 256 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 2560 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧
      ((s.gpr .r1).toNat = 16 ∨ (s.gpr .r1).toNat = 24 ∨ (s.gpr .r1).toNat = 32)
  post s s' := KeyRepr s'.mem (State.addr (s.gpr .r2)) (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3

/-- `vg_aes_gcm_stream_init(ctx = r0, nonce = r1, nonce_len = r2, state = r3, scratch = [sp])`. -/
def streamInitArm : Contract isa where
  pre s :=
    let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
    let nonce : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
    let st : Region := ⟨State.addr (s.gpr .r3), 80⟩
    let scr : Region := ⟨State.addr (VG.Proof.AesGcm.Arm.arg s 0), 2560⟩
    s.rd = [ctx, nonce, VG.Proof.AesGcm.Arm.args s 1] ∧ s.wr = [st, scr] ∧
      ctx.Disjoint st ∧ ctx.Disjoint scr ∧ nonce.Disjoint st ∧ nonce.Disjoint scr ∧ st.Disjoint scr ∧
      st.Disjoint (VG.Proof.AesGcm.Arm.args s 1) ∧ scr.Disjoint (VG.Proof.AesGcm.Arm.args s 1) ∧
      (VG.Proof.AesGcm.Arm.bel s).Disjoint ctx ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint nonce ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint st ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint scr ∧
      (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 80 ≤ 2 ^ 32 ∧ (VG.Proof.AesGcm.Arm.arg s 0).toNat + 2560 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧
      s.sp.toNat + 4 ≤ 2 ^ 32
  post s s' := ∀ ciph, StreamRepr s'.mem (State.addr (s.gpr .r3)) ciph (ctxH s.mem (State.addr (s.gpr .r0)))
    (bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat) [] []
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ VG.Proof.AesGcm.Arm.arg s₁ 0 = VG.Proof.AesGcm.Arm.arg s₂ 0

/-- `vg_aes_gcm_stream_aad(ctx = r0, state = r1, aad_len = r3:r2, data = [sp], len = [sp + 4],
scratch = [sp + 8])`. -/
def streamAadArm : Contract isa where
  pre s :=
    let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
    let st : Region := ⟨State.addr (s.gpr .r1), 80⟩
    let data : Region := ⟨State.addr (VG.Proof.AesGcm.Arm.arg s 0), (VG.Proof.AesGcm.Arm.arg s 1).toNat⟩
    let scr : Region := ⟨State.addr (VG.Proof.AesGcm.Arm.arg s 2), 2560⟩
    s.rd = [ctx, data, VG.Proof.AesGcm.Arm.args s 3] ∧ s.wr = [st, scr] ∧
      ctx.Disjoint st ∧ ctx.Disjoint scr ∧ data.Disjoint st ∧ data.Disjoint scr ∧ st.Disjoint scr ∧
      st.Disjoint (VG.Proof.AesGcm.Arm.args s 3) ∧ scr.Disjoint (VG.Proof.AesGcm.Arm.args s 3) ∧
      (VG.Proof.AesGcm.Arm.bel s).Disjoint ctx ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint data ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint st ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint scr ∧
      (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 80 ≤ 2 ^ 32 ∧
      (VG.Proof.AesGcm.Arm.arg s 0).toNat + (VG.Proof.AesGcm.Arm.arg s 1).toNat ≤ 2 ^ 32 ∧ (VG.Proof.AesGcm.Arm.arg s 2).toNat + 2560 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧
      s.sp.toNat + 12 ≤ 2 ^ 32
  post s s' := ∀ ciph iv a, StreamRepr s.mem (State.addr (s.gpr .r1)) ciph (ctxH s.mem (State.addr (s.gpr .r0))) iv a [] →
    (s.gpr .r3 ++ s.gpr .r2) = BitVec.ofNat 64 a.length →
    StreamRepr s'.mem (State.addr (s.gpr .r1)) ciph (ctxH s.mem (State.addr (s.gpr .r0))) iv
      (a ++ bytesAt s.mem (State.addr (VG.Proof.AesGcm.Arm.arg s 0)) (VG.Proof.AesGcm.Arm.arg s 1).toNat) []
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ VG.Proof.AesGcm.Arm.arg s₁ 0 = VG.Proof.AesGcm.Arm.arg s₂ 0 ∧ VG.Proof.AesGcm.Arm.arg s₁ 1 = VG.Proof.AesGcm.Arm.arg s₂ 1 ∧ VG.Proof.AesGcm.Arm.arg s₁ 2 = VG.Proof.AesGcm.Arm.arg s₂ 2

/-- What `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt` need:
`(ctx = r0, rounds = r1, state = r2, aad_len = [sp + 4]:[sp], text_len = [sp + 12]:[sp + 8],
data = [sp + 16], len = [sp + 20], scratch = [sp + 24])`. -/
def streamCryptPre (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let st : Region := ⟨State.addr (s.gpr .r2), 80⟩
  let data : Region := ⟨State.addr (VG.Proof.AesGcm.Arm.arg s 4), (VG.Proof.AesGcm.Arm.arg s 5).toNat⟩
  let scr : Region := ⟨State.addr (VG.Proof.AesGcm.Arm.arg s 6), 2560⟩
  s.rd = [ctx, VG.Proof.AesGcm.Arm.args s 7] ∧ s.wr = [st, data, scr] ∧
    ctx.Disjoint st ∧ ctx.Disjoint data ∧ ctx.Disjoint scr ∧
    st.Disjoint data ∧ st.Disjoint scr ∧ st.Disjoint (VG.Proof.AesGcm.Arm.args s 7) ∧ data.Disjoint scr ∧
    data.Disjoint (VG.Proof.AesGcm.Arm.args s 7) ∧ scr.Disjoint (VG.Proof.AesGcm.Arm.args s 7) ∧
    (VG.Proof.AesGcm.Arm.bel s).Disjoint ctx ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint st ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint data ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint scr ∧
    (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 80 ≤ 2 ^ 32 ∧
    (VG.Proof.AesGcm.Arm.arg s 4).toNat + (VG.Proof.AesGcm.Arm.arg s 5).toNat ≤ 2 ^ 32 ∧ (VG.Proof.AesGcm.Arm.arg s 6).toNat + 2560 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧
    s.sp.toNat + 28 ≤ 2 ^ 32 ∧ VG.Proof.AesGcm.Arm.roundsOk s

def streamCryptPub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    ∀ i < 7, VG.Proof.AesGcm.Arm.arg s₁ i = VG.Proof.AesGcm.Arm.arg s₂ i

/-- `vg_aes_gcm_stream_encrypt`. -/
def streamEncryptArm : Contract isa where
  pre := VG.Proof.AesGcm.Arm.streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
    let h := ctxH s.mem (State.addr (s.gpr .r0))
    ∀ iv a p, StreamRepr s.mem (State.addr (s.gpr .r2)) ciph h iv a (gctr ciph (inc32 (j0 h iv)) p) →
      VG.Proof.AesGcm.Arm.arg64 s 0 = BitVec.ofNat 64 a.length → (VG.Proof.AesGcm.Arm.arg64 s 2).toNat = p.length →
      let c := gctr ciph (inc32 (j0 h iv)) (p ++ bytesAt s.mem (State.addr (VG.Proof.AesGcm.Arm.arg s 4)) (VG.Proof.AesGcm.Arm.arg s 5).toNat)
      StreamRepr s'.mem (State.addr (s.gpr .r2)) ciph h iv a c ∧
        bytesAt s'.mem (State.addr (VG.Proof.AesGcm.Arm.arg s 4)) (VG.Proof.AesGcm.Arm.arg s 5).toNat = c.drop p.length
  pub := VG.Proof.AesGcm.Arm.streamCryptPub

/-- `vg_aes_gcm_stream_decrypt`. -/
def streamDecryptArm : Contract isa where
  pre := VG.Proof.AesGcm.Arm.streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
    let h := ctxH s.mem (State.addr (s.gpr .r0))
    ∀ iv a c, StreamRepr s.mem (State.addr (s.gpr .r2)) ciph h iv a c →
      VG.Proof.AesGcm.Arm.arg64 s 0 = BitVec.ofNat 64 a.length → (VG.Proof.AesGcm.Arm.arg64 s 2).toNat = c.length →
      let c' := c ++ bytesAt s.mem (State.addr (VG.Proof.AesGcm.Arm.arg s 4)) (VG.Proof.AesGcm.Arm.arg s 5).toNat
      StreamRepr s'.mem (State.addr (s.gpr .r2)) ciph h iv a c' ∧
        bytesAt s'.mem (State.addr (VG.Proof.AesGcm.Arm.arg s 4)) (VG.Proof.AesGcm.Arm.arg s 5).toNat = (gctr ciph (inc32 (j0 h iv)) c').drop c.length
  pub := VG.Proof.AesGcm.Arm.streamCryptPub

/-- What `vg_aes_gcm_stream_finish` and `vg_aes_gcm_stream_verify` both need:
`(ctx = r0, rounds = r1, state = r2, aad_len = [sp + 4]:[sp], text_len = [sp + 12]:[sp + 8], …)`,
with `n` words of stack arguments and `work` the `wi`-th (`streamFinishPreArm.fin`,
`streamVerifyPreArm.fin`). -/
def finPre (n wi : Nat) (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let st : Region := ⟨State.addr (s.gpr .r2), 80⟩
  let work : Region := ⟨State.addr (VG.Proof.AesGcm.Arm.arg s wi), 2560⟩
  (ctx ∈ s.rd ∧ VG.Proof.AesGcm.Arm.args s n ∈ s.rd) ∧ (st ∈ s.wr ∧ work ∈ s.wr ∧ ∀ r ∈ s.wr, (VG.Proof.AesGcm.Arm.args s n).Disjoint r) ∧
    ctx.Disjoint st ∧ ctx.Disjoint work ∧ st.Disjoint work ∧ st.Disjoint (VG.Proof.AesGcm.Arm.args s n) ∧
    work.Disjoint (VG.Proof.AesGcm.Arm.args s n) ∧
    (VG.Proof.AesGcm.Arm.bel s).Disjoint ctx ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint st ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint work ∧
    (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 80 ≤ 2 ^ 32 ∧ (VG.Proof.AesGcm.Arm.arg s wi).toNat + 2560 ≤ 2 ^ 32 ∧
    8 ≤ s.sp.toNat ∧ s.sp.toNat + 4 * n ≤ 2 ^ 32 ∧ VG.Proof.AesGcm.Arm.roundsOk s

def finPub (n : Nat) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    ∀ i < n, VG.Proof.AesGcm.Arm.arg s₁ i = VG.Proof.AesGcm.Arm.arg s₂ i

/-- What `vg_aes_gcm_stream_finish` needs: `(ctx = r0, rounds = r1, state = r2,
aad_len = [sp + 4]:[sp], text_len = [sp + 12]:[sp + 8], tag = [sp + 16], work = [sp + 20])`. -/
def streamFinishPreArm (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let st : Region := ⟨State.addr (s.gpr .r2), 80⟩
  let tag : Region := ⟨State.addr (VG.Proof.AesGcm.Arm.arg s 4), 16⟩
  let work : Region := ⟨State.addr (VG.Proof.AesGcm.Arm.arg s 5), 2560⟩
  s.rd = [ctx, VG.Proof.AesGcm.Arm.args s 6] ∧ s.wr = [st, tag, work] ∧
    ctx.Disjoint st ∧ ctx.Disjoint tag ∧ ctx.Disjoint work ∧ st.Disjoint tag ∧ st.Disjoint work ∧
    st.Disjoint (VG.Proof.AesGcm.Arm.args s 6) ∧ tag.Disjoint work ∧ tag.Disjoint (VG.Proof.AesGcm.Arm.args s 6) ∧ work.Disjoint (VG.Proof.AesGcm.Arm.args s 6) ∧
    (VG.Proof.AesGcm.Arm.bel s).Disjoint ctx ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint st ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint tag ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint work ∧
    (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 80 ≤ 2 ^ 32 ∧ (VG.Proof.AesGcm.Arm.arg s 4).toNat + 16 ≤ 2 ^ 32 ∧
    (VG.Proof.AesGcm.Arm.arg s 5).toNat + 2560 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧ s.sp.toNat + 24 ≤ 2 ^ 32 ∧ VG.Proof.AesGcm.Arm.roundsOk s

/-- `vg_aes_gcm_stream_finish`. -/
def streamFinishArm : Contract isa where
  pre := VG.Proof.AesGcm.Arm.streamFinishPreArm
  post s s' :=
    let ciph := ctxCiph s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
    let h := ctxH s.mem (State.addr (s.gpr .r0))
    ∀ iv a c, StreamRepr s.mem (State.addr (s.gpr .r2)) ciph h iv a c →
      VG.Proof.AesGcm.Arm.arg64 s 0 = BitVec.ofNat 64 a.length → (VG.Proof.AesGcm.Arm.arg64 s 2).toNat = c.length →
      bytesAt s'.mem (State.addr (VG.Proof.AesGcm.Arm.arg s 4)) 16 = fullTag ciph h iv a c
  pub := VG.Proof.AesGcm.Arm.finPub 6

/-- What `vg_aes_gcm_stream_verify` needs: `(ctx = r0, rounds = r1, state = r2,
aad_len = [sp + 4]:[sp], text_len = [sp + 12]:[sp + 8], tag = [sp + 16], tag_len = [sp + 20],
work = [sp + 24])`. -/
def streamVerifyPreArm (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let st : Region := ⟨State.addr (s.gpr .r2), 80⟩
  let tag : Region := ⟨State.addr (VG.Proof.AesGcm.Arm.arg s 4), (VG.Proof.AesGcm.Arm.arg s 5).toNat⟩
  let work : Region := ⟨State.addr (VG.Proof.AesGcm.Arm.arg s 6), 2560⟩
  s.rd = [ctx, tag, VG.Proof.AesGcm.Arm.args s 7] ∧ s.wr = [st, work] ∧
    ctx.Disjoint st ∧ ctx.Disjoint work ∧ st.Disjoint tag ∧ st.Disjoint work ∧ st.Disjoint (VG.Proof.AesGcm.Arm.args s 7) ∧
    tag.Disjoint work ∧ work.Disjoint (VG.Proof.AesGcm.Arm.args s 7) ∧
    (VG.Proof.AesGcm.Arm.bel s).Disjoint ctx ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint st ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint tag ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint work ∧
    (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 80 ≤ 2 ^ 32 ∧
    (VG.Proof.AesGcm.Arm.arg s 4).toNat + (VG.Proof.AesGcm.Arm.arg s 5).toNat ≤ 2 ^ 32 ∧ (VG.Proof.AesGcm.Arm.arg s 6).toNat + 2560 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧
    s.sp.toNat + 28 ≤ 2 ^ 32 ∧ VG.Proof.AesGcm.Arm.roundsOk s

/-- `vg_aes_gcm_stream_verify`. -/
def streamVerifyArm : Contract isa where
  pre := VG.Proof.AesGcm.Arm.streamVerifyPreArm
  post s s' :=
    let ciph := ctxCiph s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
    let h := ctxH s.mem (State.addr (s.gpr .r0))
    let tl := (VG.Proof.AesGcm.Arm.arg s 5).toNat
    ∀ iv a c, StreamRepr s.mem (State.addr (s.gpr .r2)) ciph h iv a c →
      VG.Proof.AesGcm.Arm.arg64 s 0 = BitVec.ofNat 64 a.length → (VG.Proof.AesGcm.Arm.arg64 s 2).toNat = c.length →
      let t := fullTag ciph h iv a c
      if tagLenOk tl ∧ t.take tl = bytesAt s.mem (State.addr (VG.Proof.AesGcm.Arm.arg s 4)) tl then s'.gpr .r0 = 1
      else s'.gpr .r0 = 0
  pub := VG.Proof.AesGcm.Arm.finPub 7

/-- What `vg_aes_gcm_seal` and `vg_aes_gcm_open` both need: `(ctx = r0, rounds = r1, nonce = r2,
nonce_len = r3, aad = [sp], aad_len = [sp + 4], data = [sp + 8], len = [sp + 12], …)`, with `n`
words of stack arguments and `work` the `wi`-th (`sealPreArm.one`, `openPreArm.one`). -/
def onePre (n wi : Nat) (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let aad : Region := ⟨State.addr (VG.Proof.AesGcm.Arm.arg s 0), (VG.Proof.AesGcm.Arm.arg s 1).toNat⟩
  let data : Region := ⟨State.addr (VG.Proof.AesGcm.Arm.arg s 2), (VG.Proof.AesGcm.Arm.arg s 3).toNat⟩
  let work : Region := ⟨State.addr (VG.Proof.AesGcm.Arm.arg s wi), 2560⟩
  (ctx ∈ s.rd ∧ nonce ∈ s.rd ∧ aad ∈ s.rd ∧ VG.Proof.AesGcm.Arm.args s n ∈ s.rd) ∧
    (data ∈ s.wr ∧ work ∈ s.wr ∧ ∀ r ∈ s.wr, (VG.Proof.AesGcm.Arm.args s n).Disjoint r) ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (VG.Proof.AesGcm.Arm.args s n) ∧ work.Disjoint (VG.Proof.AesGcm.Arm.args s n) ∧
    (VG.Proof.AesGcm.Arm.bel s).Disjoint ctx ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint nonce ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint aad ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint data ∧
    (VG.Proof.AesGcm.Arm.bel s).Disjoint work ∧
    (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (VG.Proof.AesGcm.Arm.arg s 0).toNat + (VG.Proof.AesGcm.Arm.arg s 1).toNat ≤ 2 ^ 32 ∧ (VG.Proof.AesGcm.Arm.arg s 2).toNat + (VG.Proof.AesGcm.Arm.arg s 3).toNat ≤ 2 ^ 32 ∧
    (VG.Proof.AesGcm.Arm.arg s wi).toNat + 2560 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧ s.sp.toNat + 4 * n ≤ 2 ^ 32 ∧ VG.Proof.AesGcm.Arm.roundsOk s

def onePub (n : Nat) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ ∀ i < n, VG.Proof.AesGcm.Arm.arg s₁ i = VG.Proof.AesGcm.Arm.arg s₂ i

/-- What `vg_aes_gcm_seal` needs: `(ctx = r0, rounds = r1, nonce = r2, nonce_len = r3, aad = [sp],
aad_len = [sp + 4], data = [sp + 8], len = [sp + 12], tag = [sp + 16], work = [sp + 20])`. -/
def sealPreArm (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let aad : Region := ⟨State.addr (VG.Proof.AesGcm.Arm.arg s 0), (VG.Proof.AesGcm.Arm.arg s 1).toNat⟩
  let data : Region := ⟨State.addr (VG.Proof.AesGcm.Arm.arg s 2), (VG.Proof.AesGcm.Arm.arg s 3).toNat⟩
  let tag : Region := ⟨State.addr (VG.Proof.AesGcm.Arm.arg s 4), 16⟩
  let work : Region := ⟨State.addr (VG.Proof.AesGcm.Arm.arg s 5), 2560⟩
  s.rd = [ctx, nonce, aad, VG.Proof.AesGcm.Arm.args s 6] ∧ s.wr = [data, tag, work] ∧
    ctx.Disjoint data ∧ ctx.Disjoint tag ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    nonce.Disjoint work ∧ aad.Disjoint data ∧ aad.Disjoint tag ∧ aad.Disjoint work ∧
    data.Disjoint tag ∧ data.Disjoint work ∧ data.Disjoint (VG.Proof.AesGcm.Arm.args s 6) ∧ tag.Disjoint work ∧
    tag.Disjoint (VG.Proof.AesGcm.Arm.args s 6) ∧ work.Disjoint (VG.Proof.AesGcm.Arm.args s 6) ∧
    (VG.Proof.AesGcm.Arm.bel s).Disjoint ctx ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint nonce ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint aad ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint data ∧
    (VG.Proof.AesGcm.Arm.bel s).Disjoint tag ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint work ∧
    (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (VG.Proof.AesGcm.Arm.arg s 0).toNat + (VG.Proof.AesGcm.Arm.arg s 1).toNat ≤ 2 ^ 32 ∧ (VG.Proof.AesGcm.Arm.arg s 2).toNat + (VG.Proof.AesGcm.Arm.arg s 3).toNat ≤ 2 ^ 32 ∧
    (VG.Proof.AesGcm.Arm.arg s 4).toNat + 16 ≤ 2 ^ 32 ∧ (VG.Proof.AesGcm.Arm.arg s 5).toNat + 2560 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧
    s.sp.toNat + 24 ≤ 2 ^ 32 ∧ VG.Proof.AesGcm.Arm.roundsOk s

/-- `vg_aes_gcm_seal`. -/
def sealArm : Contract isa where
  pre := VG.Proof.AesGcm.Arm.sealPreArm
  post s s' :=
    encryptWith (ctxCiph s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) (ctxH s.mem (State.addr (s.gpr .r0))) 16
        (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) (bytesAt s.mem (State.addr (VG.Proof.AesGcm.Arm.arg s 2)) (VG.Proof.AesGcm.Arm.arg s 3).toNat)
        (bytesAt s.mem (State.addr (VG.Proof.AesGcm.Arm.arg s 0)) (VG.Proof.AesGcm.Arm.arg s 1).toNat) =
      (bytesAt s'.mem (State.addr (VG.Proof.AesGcm.Arm.arg s 2)) (VG.Proof.AesGcm.Arm.arg s 3).toNat, bytesAt s'.mem (State.addr (VG.Proof.AesGcm.Arm.arg s 4)) 16)
  pub := VG.Proof.AesGcm.Arm.onePub 6

/-- What `vg_aes_gcm_open` needs: `(ctx = r0, rounds = r1, nonce = r2, nonce_len = r3, aad = [sp],
aad_len = [sp + 4], data = [sp + 8], len = [sp + 12], tag = [sp + 16], tag_len = [sp + 20],
work = [sp + 24])`. -/
def openPreArm (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let aad : Region := ⟨State.addr (VG.Proof.AesGcm.Arm.arg s 0), (VG.Proof.AesGcm.Arm.arg s 1).toNat⟩
  let data : Region := ⟨State.addr (VG.Proof.AesGcm.Arm.arg s 2), (VG.Proof.AesGcm.Arm.arg s 3).toNat⟩
  let tag : Region := ⟨State.addr (VG.Proof.AesGcm.Arm.arg s 4), (VG.Proof.AesGcm.Arm.arg s 5).toNat⟩
  let work : Region := ⟨State.addr (VG.Proof.AesGcm.Arm.arg s 6), 2560⟩
  s.rd = [ctx, nonce, aad, tag, VG.Proof.AesGcm.Arm.args s 7] ∧ s.wr = [data, work] ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ data.Disjoint tag ∧ data.Disjoint work ∧
    data.Disjoint (VG.Proof.AesGcm.Arm.args s 7) ∧ tag.Disjoint work ∧ work.Disjoint (VG.Proof.AesGcm.Arm.args s 7) ∧
    (VG.Proof.AesGcm.Arm.bel s).Disjoint ctx ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint nonce ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint aad ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint data ∧
    (VG.Proof.AesGcm.Arm.bel s).Disjoint tag ∧ (VG.Proof.AesGcm.Arm.bel s).Disjoint work ∧
    (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (VG.Proof.AesGcm.Arm.arg s 0).toNat + (VG.Proof.AesGcm.Arm.arg s 1).toNat ≤ 2 ^ 32 ∧ (VG.Proof.AesGcm.Arm.arg s 2).toNat + (VG.Proof.AesGcm.Arm.arg s 3).toNat ≤ 2 ^ 32 ∧
    (VG.Proof.AesGcm.Arm.arg s 4).toNat + (VG.Proof.AesGcm.Arm.arg s 5).toNat ≤ 2 ^ 32 ∧ (VG.Proof.AesGcm.Arm.arg s 6).toNat + 2560 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧
    s.sp.toNat + 28 ≤ 2 ^ 32 ∧ VG.Proof.AesGcm.Arm.roundsOk s

/-- What `vg_aes_gcm_open` computes, in a state. -/
abbrev openRes (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) (ctxH s.mem (State.addr (s.gpr .r0)))
    (VG.Proof.AesGcm.Arm.arg s 5).toNat (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
    (bytesAt s.mem (State.addr (VG.Proof.AesGcm.Arm.arg s 2)) (VG.Proof.AesGcm.Arm.arg s 3).toNat) (bytesAt s.mem (State.addr (VG.Proof.AesGcm.Arm.arg s 0)) (VG.Proof.AesGcm.Arm.arg s 1).toNat)
    (bytesAt s.mem (State.addr (VG.Proof.AesGcm.Arm.arg s 4)) (VG.Proof.AesGcm.Arm.arg s 5).toNat)

/-- `vg_aes_gcm_open`. -/
def openArm : Contract isa where
  pre := VG.Proof.AesGcm.Arm.openPreArm
  post s s' :=
    match VG.Proof.AesGcm.Arm.openRes s with
    | some pt => s'.gpr .r0 = 1 ∧ bytesAt s'.mem (State.addr (VG.Proof.AesGcm.Arm.arg s 2)) (VG.Proof.AesGcm.Arm.arg s 3).toNat = pt
    | none => s'.gpr .r0 = 0 ∧
        bytesAt s'.mem (State.addr (VG.Proof.AesGcm.Arm.arg s 2)) (VG.Proof.AesGcm.Arm.arg s 3).toNat = bytesAt s.mem (State.addr (VG.Proof.AesGcm.Arm.arg s 2)) (VG.Proof.AesGcm.Arm.arg s 3).toNat
  pub s₁ s₂ := VG.Proof.AesGcm.Arm.onePub 7 s₁ s₂ ∧ (VG.Proof.AesGcm.Arm.roundsOk s₁ → (VG.Proof.AesGcm.Arm.openRes s₁).isSome = (VG.Proof.AesGcm.Arm.openRes s₂).isSome)

/-! ## The shared preconditions, from each function's -/

theorem streamFinishPreArm.fin {s : State} (h : VG.Proof.AesGcm.Arm.streamFinishPreArm s) : VG.Proof.AesGcm.Arm.finPre 6 5 s := by
  obtain ⟨hrd, hwr, cs, -, cw, -, sw, sa, -, ta, wa, bc, bs, -, bw, fc, fs, -, fw, sp8, spf, hR⟩ := h
  refine ⟨⟨by rw [hrd]; simp, by rw [hrd]; simp⟩, ⟨by rw [hwr]; simp, by rw [hwr]; simp, fun r hr => ?_⟩,
    cs, cw, sw, sa, wa, bc, bs, bw, fc, fs, fw, sp8, spf, hR⟩
  rw [hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sa.symm
  · exact ta.symm
  · exact wa.symm

theorem streamVerifyPreArm.fin {s : State} (h : VG.Proof.AesGcm.Arm.streamVerifyPreArm s) : VG.Proof.AesGcm.Arm.finPre 7 6 s := by
  obtain ⟨hrd, hwr, cs, cw, -, sw, sa, -, wa, bc, bs, -, bw, fc, fs, -, fw, sp8, spf, hR⟩ := h
  refine ⟨⟨by rw [hrd]; simp, by rw [hrd]; simp⟩, ⟨by rw [hwr]; simp, by rw [hwr]; simp, fun r hr => ?_⟩,
    cs, cw, sw, sa, wa, bc, bs, bw, fc, fs, fw, sp8, spf, hR⟩
  rw [hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact sa.symm
  · exact wa.symm

theorem sealPreArm.one {s : State} (h : VG.Proof.AesGcm.Arm.sealPreArm s) : VG.Proof.AesGcm.Arm.onePre 6 5 s := by
  obtain ⟨hrd, hwr, cd, -, cw, nd, -, nw, ad, -, aw, -, dw, da, -, ta, wa, bc, bn, ba, bd, -, bw, fc, fn, fa, fd,
    -, fw, sp8, spf, hR⟩ := h
  refine ⟨⟨by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp⟩,
    ⟨by rw [hwr]; simp, by rw [hwr]; simp, fun r hr => ?_⟩,
    cd, cw, nd, nw, ad, aw, dw, da, wa, bc, bn, ba, bd, bw, fc, fn, fa, fd, fw, sp8, spf, hR⟩
  rw [hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact da.symm
  · exact ta.symm
  · exact wa.symm

theorem openPreArm.one {s : State} (h : VG.Proof.AesGcm.Arm.openPreArm s) : VG.Proof.AesGcm.Arm.onePre 7 6 s := by
  obtain ⟨hrd, hwr, cd, cw, nd, nw, ad, aw, -, dw, da, -, wa, bc, bn, ba, bd, -, bw, fc, fn, fa, fd, -, fw, sp8, spf,
    hR⟩ := h
  refine ⟨⟨by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp, by rw [hrd]; simp⟩,
    ⟨by rw [hwr]; simp, by rw [hwr]; simp, fun r hr => ?_⟩,
    cd, cw, nd, nw, ad, aw, dw, da, wa, bc, bn, ba, bd, bw, fc, fn, fa, fd, fw, sp8, spf, hR⟩
  rw [hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact da.symm
  · exact wa.symm

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.Entry`. -/
section

/-!
# AES-GCM on ARMv7: the stack arguments, and the entry of the functions

Untrusted: everything here is checked by Lean. The functions other than
`init` load `W` from the stack (`ldr r12, [sp, #off]`) and save our caller's
registers there (`entry_ok`); they read their other stack arguments when they
need them, which no write changes (`arg_frame`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)

theorem stackArg_eq (s : State) (k : Nat) :
    stackArg s k = s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (4 * k))) 32 := rfl

theorem stackArg_zero (s : State) : stackArg s 0 = s.mem.readW (State.addr s.sp) 32 := by
  simp only [stackArg, stackArgAddr, Nat.mul_zero, add_ofNat_zero]

/-- The stack argument `i` (of `n`) is readable. -/
theorem arg_in {s : State} {n i : Nat} (hi : i < n) (hf : s.sp.toNat + 4 * n ≤ 2 ^ 32) (h : VG.Proof.AesGcm.Arm.args s n ∈ s.rd) :
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 (4 * i))) 4 := by
  have e : State.addr (s.sp + BitVec.ofNat 32 (4 * i)) = stackArgAddr s 0 + BitVec.ofNat 64 (4 * i) := by
    simp only [stackArgAddr, Nat.mul_zero, add_ofNat_zero]; exact addr_add (by omega)
  rw [e]; exact in_off (covers_of_mem (List.mem_append_left _ h)) (by omega) (by omega)

/-- The stack arguments stay where they are, outside a frame. -/
theorem arg_frame {s s' : State} {n : Nat} {rs : List Region} (hsp : s'.sp = s.sp)
    (hf : s.sp.toNat + 4 * n ≤ 2 ^ 32) (hfr : Frame rs s.mem s'.mem) (hd : ∀ r ∈ rs, (VG.Proof.AesGcm.Arm.args s n).Disjoint r)
    {i : Nat} (hi : i < n) : stackArg s' i = stackArg s i := by
  have e : stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (4 * i) := by
    simp only [stackArgAddr, Nat.mul_zero, add_ofNat_zero]; exact addr_add (by omega)
  have hs : Region.Sub ⟨stackArgAddr s i, 4⟩ (VG.Proof.AesGcm.Arm.args s n) := by rw [e]; exact Offset.sub_base _ (by omega)
  simp only [stackArg, show stackArgAddr s' i = stackArgAddr s i by simp only [stackArgAddr, hsp]]
  exact hfr.readW (Region.contains_self _ _) (fun r hr => (hd r hr).sub_left hs) (by decide)

/-- The entry: `W` loaded from the stack into `r12`, and our caller's
registers saved there. -/
theorem entry_ok {s : State} {off : Nat} (hoff : off < 4096)
    (harg : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 off)) 4)
    (hfit : (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32).toNat + 2560 ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32), 2560⟩] s.wr)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr .r12 = s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32 →
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      VG.Proof.AesGcm.Arm.SavedAt s'.mem (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32) s →
      Frame [VG.Proof.AesGcm.Arm.savedR (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32)] s.mem s'.mem →
      WP isa (.block rest) s' Q) :
    WP isa (.block (.ldrSp .r12 off :: (save .r12 ++ rest))) s Q := by
  rw [← List.singleton_append]
  refine WP.block_append (WP.of_runBlock ⟨s.setReg .r12 (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32), ?_, ?_⟩)
  · arun [hoff, harg]
  refine VG.Proof.AesGcm.Arm.save_ok (s := s.setReg .r12 (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32)) (b := .r12) (by simp [gpr_setReg]) hfit hw fun s' g rd wr sp sv fr => k s' ?_ ?_ rd wr sp ?_ fr
  · rw [g]; simp [gpr_setReg]
  · intro r hr; rw [g]; simp [gpr_setReg, hr]
  · intro p hp
    rw [sv p hp]
    have : p.1 ≠ .r12 := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp [gpr_setReg, this]

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.Args`. -/
section

/-!
# AES-GCM on ARMv7: stack arguments read after other code

Untrusted: everything here is checked by Lean. `ArgsKeep n s₀ s`: the stack
pointer, the permissions and the first `n` stack arguments of `s` are those
of `s₀`; code that writes only regions apart from the arguments keeps it
(`ArgsKeep.frame`), and `ldr rX, [sp, #4i]` then loads argument `i` of `s₀`
(`ArgsKeep.read`).
-/

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm

theorem argAddr_zero (s : State) : stackArgAddr s 0 = State.addr s.sp := by
  simp only [stackArgAddr, Nat.mul_zero, add_ofNat_zero]

theorem args_sp {s s' : State} (h : s'.sp = s.sp) (n : Nat) : VG.Proof.AesGcm.Arm.args s' n = VG.Proof.AesGcm.Arm.args s n := by
  simp only [VG.Proof.AesGcm.Arm.args, stackArgAddr, h]

/-- The stack below `sp` is apart from the stack arguments. -/
theorem below_args (s : State) {n : Nat} (hf : s.sp.toNat + 4 * n ≤ 2 ^ 32) : (below s.sp).Disjoint (VG.Proof.AesGcm.Arm.args s n) := by
  simp only [VG.Proof.AesGcm.Arm.args, VG.Proof.AesGcm.Arm.argAddr_zero]
  exact (Offset.base_disjoint_below (State.addr s.sp) (n := 8) (k := 4 * n) (by omega)).symm

/-- The low word of a 64-bit length gives it modulo 16. -/
theorem low_mod16 {hi lo : BitVec 32} {L : Nat} (h : hi ++ lo = BitVec.ofNat 64 L) : lo.toNat % 16 = L % 16 := by
  have e := congrArg BitVec.toNat h
  rw [Proof.Gcm.toNat_append, BitVec.toNat_ofNat] at e
  have : L % 2 ^ 64 % 16 = L % 16 := Nat.mod_mod_of_dvd _ (by decide)
  omega

structure ArgsKeep (n : Nat) (s₀ s : State) : Prop where
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  arg : ∀ i < n, stackArg s i = stackArg s₀ i

theorem ArgsKeep.refl (n : Nat) (s : State) : VG.Proof.AesGcm.Arm.ArgsKeep n s s := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

theorem ArgsKeep.of_eq {n : Nat} {s₀ s s' : State} (h : VG.Proof.AesGcm.Arm.ArgsKeep n s₀ s) (hm : s'.mem = s.mem) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.Arm.ArgsKeep n s₀ s' :=
  ⟨hsp.trans h.sp, hrd.trans h.rd, hwr.trans h.wr, fun i hi => by
    rw [← h.arg i hi]; simp only [stackArg, stackArgAddr, hm, hsp]⟩

theorem ArgsKeep.frame {n : Nat} {s₀ s s' : State} (h : VG.Proof.AesGcm.Arm.ArgsKeep n s₀ s) (hf : s₀.sp.toNat + 4 * n ≤ 2 ^ 32)
    {rs : List Region} (hfr : Frame rs s.mem s'.mem) (hd : ∀ r ∈ rs, (VG.Proof.AesGcm.Arm.args s₀ n).Disjoint r) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.Arm.ArgsKeep n s₀ s' := by
  refine ⟨hsp.trans h.sp, hrd.trans h.rd, hwr.trans h.wr, fun i hi => ?_⟩
  rw [← h.arg i hi]
  exact VG.Proof.AesGcm.Arm.arg_frame hsp (by rw [h.sp]; exact hf) hfr (fun r hr => by rw [VG.Proof.AesGcm.Arm.args_sp h.sp]; exact hd r hr) hi

theorem ArgsKeep.trans {n : Nat} {s₀ s s' : State} (h : VG.Proof.AesGcm.Arm.ArgsKeep n s₀ s) (h' : VG.Proof.AesGcm.Arm.ArgsKeep n s s') : VG.Proof.AesGcm.Arm.ArgsKeep n s₀ s' :=
  ⟨h'.sp.trans h.sp, h'.rd.trans h.rd, h'.wr.trans h.wr, fun i hi => (h'.arg i hi).trans (h.arg i hi)⟩

theorem ArgsKeep.read {n : Nat} {s₀ s : State} (h : VG.Proof.AesGcm.Arm.ArgsKeep n s₀ s) (hf : s₀.sp.toNat + 4 * n ≤ 2 ^ 32)
    (hin : VG.Proof.AesGcm.Arm.args s₀ n ∈ s₀.rd) {i : Nat} (hi : i < n) :
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 (4 * i))) 4 ∧
      s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (4 * i))) 32 = stackArg s₀ i :=
  ⟨VG.Proof.AesGcm.Arm.arg_in hi (by rw [h.sp]; exact hf) (by rw [h.rd, VG.Proof.AesGcm.Arm.args_sp h.sp]; exact hin), h.arg i hi⟩

/-- `ArgsKeep.read`, at a literal offset. -/
theorem ArgsKeep.at {n : Nat} {s₀ s : State} (h : VG.Proof.AesGcm.Arm.ArgsKeep n s₀ s) (hf : s₀.sp.toNat + 4 * n ≤ 2 ^ 32)
    (hin : VG.Proof.AesGcm.Arm.args s₀ n ∈ s₀.rd) (i : Nat) {off : Nat} (hi : i < n) (hoff : 4 * i = off) :
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 off)) 4 ∧
      s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32 = stackArg s₀ i := by
  subst hoff; exact h.read hf hin hi

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.TextAbsorb`. -/
section

/-!
# AES-GCM on ARMv7: absorbing the text (`textAbsorb`)

Untrusted: everything here is checked by Lean. `textAbsorb` absorbs the `len`
bytes at `data` into GHASH as text: before the first text (`text_len` 0) it
pads the additional data first (`firstFlush`), and it does nothing for no
bytes (`textAbsorb_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput zeros padLen)
open VG.Proof.Gcm (Absorbed)

/-- The regions `textAbsorb` writes. -/
abbrev taFrame (st w sp : BitVec 32) : List Region :=
  [⟨State.addr st + BitVec.ofNat 64 16, 16⟩, ⟨State.addr st + BitVec.ofNat 64 32, 16⟩,
    ⟨State.addr w + BitVec.ofNat 64 96, 16⟩, ⟨State.addr w + BitVec.ofNat 64 512, 256⟩, below sp]

theorem lowTo_mod16 {hi lo : BitVec 32} {P : Nat} (h : (hi ++ lo).toNat = P) : lo.toNat % 16 = P % 16 := by
  rw [Proof.Gcm.toNat_append] at h; omega

theorem z_sub0 (x : BitVec 32) : (x - 0#32 == 0) = decide (x.toNat = 0) := by
  by_cases h : x.toNat = 0 <;> simp [BitVec.toNat_eq, h]

theorem or_zero_iff (lo hi : BitVec 32) : (lo ||| hi).toNat = 0 ↔ (hi ++ lo).toNat = 0 := by
  constructor
  · intro h
    have : lo ||| hi = 0#32 := BitVec.eq_of_toNat_eq (by simpa using h)
    rw [BitVec.or_eq_zero_iff] at this
    obtain ⟨rfl, rfl⟩ := this; rfl
  · intro h
    rw [Proof.Gcm.toNat_append] at h
    have h1 : lo = 0#32 := BitVec.eq_of_toNat_eq (by simp; omega)
    have h2 : hi = 0#32 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst h1 h2; rfl

/-- After `textAbsorb`, from `m₀`: GHASH has absorbed `x`. -/
structure TaOut (c st w sp k7 k8 : BitVec 32) (s₀ : State) (H : Block) (x₀ x : List Byte) (m₀ : Mem) (s : State) :
    Prop where
  env : Env c st w sp k7 k8 s
  args : VG.Proof.AesGcm.Arm.ArgsKeep 7 s₀ s
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H
  abs : Absorbed m₀ (State.addr st + BitVec.ofNat 64 16) (State.addr st + BitVec.ofNat 64 32) H x₀ →
    Absorbed s.mem (State.addr st + BitVec.ofNat 64 16) (State.addr st + BitVec.ofNat 64 32) H x
  frame : Frame (VG.Proof.AesGcm.Arm.taFrame st w sp) m₀ s.mem

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

omit L in
theorem abs_taFrame {m m' : Mem} (h : Frame (absFrame st w sp 16) m m') : Frame (VG.Proof.AesGcm.Arm.taFrame st w sp) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp

omit L in
theorem t_taFrame {m m' : Mem} (h : Frame (tFrame st w sp 16) m m') : Frame (VG.Proof.AesGcm.Arm.taFrame st w sp) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp

theorem textAbsorb_ok {s₀ s : State} {H : Block} {a ct : List Byte} (he : Env c st w sp k7 k8 s)
    (hk : VG.Proof.AesGcm.Arm.ArgsKeep 7 s₀ s) (hf : s₀.sp.toNat + 4 * 7 ≤ 2 ^ 32) (hin : VG.Proof.AesGcm.Arm.args s₀ 7 ∈ s₀.rd)
    (hA : ∀ r ∈ VG.Proof.AesGcm.Arm.taFrame st w sp, (VG.Proof.AesGcm.Arm.args s₀ 7).Disjoint r)
    (hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H)
    (hd : DataOk st w sp s (VG.Proof.AesGcm.Arm.arg s₀ 4) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat)
    (ha : a.length % 16 = (VG.Proof.AesGcm.Arm.arg s₀ 0).toNat % 16) (hP : (VG.Proof.AesGcm.Arm.arg s₀ 3 ++ VG.Proof.AesGcm.Arm.arg s₀ 2).toNat = ct.length) :
    WP isa textAbsorb s (VG.Proof.AesGcm.Arm.TaOut c st w sp k7 k8 s₀ H (ghashInput a ct)
      (ghashInput a (ct ++ bytesAt s.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4)) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat)) s.mem) := by
  have hn := (VG.Proof.AesGcm.Arm.arg s₀ 5).isLt
  obtain ⟨i5, v5⟩ := hk.at hf hin 5 (by decide) (show 4 * 5 = 20 from rfl)
  obtain ⟨s₁, run₁, h5₁, hz₁, hg₁, hK₁⟩ : ∃ s₁, runBlock isa [.ldrSp .r5 20, .cmp .r5 (imm 0)] s = some s₁ ∧
      s₁.gpr .r5 = VG.Proof.AesGcm.Arm.arg s₀ 5 ∧ s₁.z = decide ((VG.Proof.AesGcm.Arm.arg s₀ 5).toNat = 0) ∧ (∀ r, r ≠ .r5 → s₁.gpr r = s.gpr r) ∧
      Keeps s s₁ := by
    refine ⟨_, by arun [i5, v5], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, v5]
    · simp only [z_subFlags, gpr_setReg, ite_true, v5]
      exact VG.Proof.AesGcm.Arm.z_sub0 _
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide)) hK₁.sp hK₁.rd hK₁.wr
  have hk₁ := hk.of_eq hK₁.mem hK₁.sp hK₁.rd hK₁.wr
  refine WP.ite _ (eval_eq' hz₁) (fun ht => ?_) (fun hf' => ?_)
  · have h0 : (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat = 0 := by simpa using ht
    rw [h0]
    refine WP.block_nil ⟨he₁, hk₁, by rw [hK₁.mem]; exact hH, fun hab => ?_, by rw [hK₁.mem]; exact Frame.refl _ _⟩
    simp only [bytesAt, List.range_zero, List.map_nil, List.append_nil, hK₁.mem]; exact hab
  have h0 : (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat ≠ 0 := by simpa using hf'
  -- `Z` iff no text so far
  obtain ⟨i2, v2⟩ := hk₁.at hf hin 2 (by decide) (show 4 * 2 = 8 from rfl)
  obtain ⟨i3, v3⟩ := hk₁.at hf hin 3 (by decide) (show 4 * 3 = 12 from rfl)
  obtain ⟨s₂, run₂, hz₂, hg₂, hK₂⟩ : ∃ s₂, runBlock isa tlenZero s₁ = some s₂ ∧
      s₂.z = decide (ct.length = 0) ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    refine ⟨_, by simp only [tlenZero]; arun [i2, v2, i3, v3], ?_, ?_, ?_⟩
    · simp only [z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, v2, v3]
      rw [VG.Proof.AesGcm.Arm.z_sub0, ← hP]
      exact decide_eq_decide.mpr (VG.Proof.AesGcm.Arm.or_zero_iff _ _)
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have he₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hK₂.sp hK₂.rd hK₂.wr
  have hk₂ := hk₁.of_eq hK₂.mem hK₂.sp hK₂.rd hK₂.wr
  have hm₂ : s₂.mem = s.mem := hK₂.mem.trans hK₁.mem
  -- the additional data padded, before the first text
  let x' := if ct = [] then a ++ zeros (padLen a.length) else ghashInput a ct
  have hx' : x'.length % 16 = ct.length % 16 := by
    by_cases hc : ct = []
    · subst hc; simp only [x', ite_true, List.length_append, Proof.Gcm.length_zeros, List.length_nil]
      exact Proof.Gcm.length_pad_mod _
    · simp only [x', hc, ite_false, Proof.Gcm.ghashInput_of_ne hc, List.length_append, Proof.Gcm.length_zeros]
      have := Proof.Gcm.length_pad_mod a.length; omega
  have hlt := Nat.mod_lt a.length (show 16 > 0 by decide)
  have mid : WP isa (.ite .eq firstFlush (.block [])) s₂ fun s₄ => Env c st w sp k7 k8 s₄ ∧ VG.Proof.AesGcm.Arm.ArgsKeep 7 s₀ s₄ ∧
      blockAt s₄.mem (State.addr c + BitVec.ofNat 64 240) = H ∧
      (Absorbed s.mem (State.addr st + BitVec.ofNat 64 16) (State.addr st + BitVec.ofNat 64 32) H (ghashInput a ct) →
        Absorbed s₄.mem (State.addr st + BitVec.ofNat 64 16) (State.addr st + BitVec.ofNat 64 32) H x') ∧
      Frame (tFrame st w sp 16) s.mem s₄.mem := by
    refine WP.ite _ (eval_eq' hz₂) (fun ht => ?_) (fun hf₂ => ?_)
    · have hc : ct = [] := List.eq_nil_of_length_eq_zero (by simpa using ht)
      obtain ⟨i0, v0⟩ := hk₂.at hf hin 0 (by decide) (show 4 * 0 = 0 from rfl)
      obtain ⟨s₃, run₃, h6₃, hg₃, hK₃⟩ : ∃ s₃, runBlock isa [.ldrSp .r6 0, .dp .and .r6 .r6 (imm 15)] s₂ = some s₃ ∧
          s₃.gpr .r6 = BitVec.ofNat 32 (a.length % 16) ∧ (∀ r, r ≠ .r6 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
        refine ⟨_, by arun [i0, v0], ?_, ?_, ?_⟩
        · simp only [gpr_setReg, ite_true, v0, and15, ha]
        · intro r a; simp [gpr_setReg, a]
        · exact ⟨rfl, rfl, rfl, rfl⟩
      refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
      have he₃ := he₂.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hK₃.sp hK₃.rd hK₃.wr
      have hm₃ : s₃.mem = s.mem := hK₃.mem.trans hm₂
      refine WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl) (x := a) (H := H) ⟨he₃, by rw [hm₃]; exact hH⟩ h6₃))
        fun s₄ hh => ?_
      obtain ⟨hfl, rd₄, wr₄, sp₄⟩ := hh
      have hf₄ := hfl.frame
      rw [hm₃] at hf₄
      refine ⟨hfl.env, (hk₂.of_eq hK₃.mem hK₃.sp hK₃.rd hK₃.wr).frame hf hfl.frame
          (fun r hr => hA r (by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
            rcases hr with rfl | rfl | rfl | rfl <;> simp)) sp₄ rd₄ wr₄, hfl.hH, fun hab => ?_, hf₄⟩
      simp only [x', hc, ite_true]
      refine hfl.abs ?_
      rw [hm₃]; subst hc; exact hab
    · have hc : ct ≠ [] := fun e => by subst e; simp at hf₂
      refine WP.block_nil ⟨he₂, hk₂, by rw [hm₂]; exact hH, fun hab => ?_, by rw [hm₂]; exact Frame.refl _ _⟩
      simp only [x', hc, ite_false, hm₂]; exact hab
  refine WP.seq (WP.mono mid fun s₄ ⟨he₄, hk₄, hH₄, hab₄, hf₄⟩ => ?_)
  -- the arguments of `absorb`
  obtain ⟨i4, v4⟩ := hk₄.at hf hin 4 (by decide) (show 4 * 4 = 16 from rfl)
  obtain ⟨i5', v5'⟩ := hk₄.at hf hin 5 (by decide) (show 4 * 5 = 20 from rfl)
  obtain ⟨i2', v2'⟩ := hk₄.at hf hin 2 (by decide) (show 4 * 2 = 8 from rfl)
  obtain ⟨s₅, run₅, h4₅, h5₅, h6₅, hg₅, hK₅⟩ : ∃ s₅, runBlock isa textArgs s₄ = some s₅ ∧
      s₅.gpr .r4 = VG.Proof.AesGcm.Arm.arg s₀ 4 ∧ s₅.gpr .r5 = VG.Proof.AesGcm.Arm.arg s₀ 5 ∧ s₅.gpr .r6 = BitVec.ofNat 32 ((VG.Proof.AesGcm.Arm.arg s₀ 2).toNat % 16) ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    refine ⟨_, by simp only [textArgs]; arun [i4, v4, i5', v5', i2', v2'], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, v4]
    · simp [gpr_setReg, v5']
    · simp only [gpr_setReg, ite_true, v2', and15]
    · intro r a b d; simp [gpr_setReg, a, b, d]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide) (by decide)) hK₅.sp hK₅.rd hK₅.wr
  have hk₅ := hk₄.of_eq hK₅.mem hK₅.sp hK₅.rd hK₅.wr
  have hrd₅ : s₅.rd = s.rd := hk₅.rd.trans hk.rd.symm
  have hwr₅ : s₅.wr = s.wr := hk₅.wr.trans hk.wr.symm
  have hai : AbsIn c st w sp k7 k8 16 H x' (VG.Proof.AesGcm.Arm.arg s₀ 4) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat s₅ :=
    ⟨he₅, h4₅, by rw [h5₅]; simp, by rw [h6₅, hx', VG.Proof.AesGcm.Arm.lowTo_mod16 hP], hd.of_eq hrd₅ hwr₅, by rw [hK₅.mem]; exact hH₄⟩
  refine WP.mono (WP.with_rdwr (absorb_ok L (.inr rfl) hai)) fun s₆ hh => ?_
  obtain ⟨ho, rd₆, wr₆, sp₆⟩ := hh
  have hdat : bytesAt s₅.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4)) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat =
      bytesAt s.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4)) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat := by
    rw [hK₅.mem]
    exact bytesAt_frame hf₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hd.st.sub_right (Lay.stSub (by decide))
      · exact hd.w.sub_right (Lay.wSub (by decide))
      · exact hd.w.sub_right (Lay.wSub (by decide))
      · exact hd.stk.symm) (by have := hd.lt; omega)
  have hne : bytesAt s.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4)) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat ≠ [] := by
    intro e; have := congrArg List.length e; rw [length_bytesAt] at this; exact h0 (by simpa using this)
  refine ⟨ho.env, hk₅.frame hf ho.frame (fun r hr => hA r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp)) sp₆ rd₆ wr₆, ?_, ?_, ?_⟩
  · rw [blockAt_frame ho.frame (ctx_absFrame L (.inr rfl)), hK₅.mem, hH₄]
  · intro hab
    have := ho.abs (by rw [hK₅.mem]; exact hab₄ hab)
    rw [hdat] at this
    rw [Proof.Gcm.ghashInput_append _ _ _ hne]
    exact this
  · rw [hK₅.mem] at ho
    exact (VG.Proof.AesGcm.Arm.t_taFrame hf₄).trans (VG.Proof.AesGcm.Arm.abs_taFrame ho.frame)

end

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.FinTag`. -/
section

/-!
# AES-GCM on ARMv7: the tag of a streaming state (`finTag o`)

Untrusted: everything here is checked by Lean. `finTag o` pads the buffered
bytes (of the additional data if there is no text, of the text otherwise)
and absorbs them, then the lengths block, and writes the tag to `W + o`
(`finTag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput ghash ghashFrom blocks zeros padLen toBytes ofBytes)
open VG.Proof.Gcm (Absorbed lensBlock padded)

theorem disj_sub {X : Region} {rs rs' : List Region} (h : ∀ r ∈ rs', X.Disjoint r)
    (hs : ∀ r ∈ rs, ∃ r' ∈ rs', Region.Sub r r') : ∀ r ∈ rs, X.Disjoint r := fun r hr => by
  obtain ⟨r', hr', hsub⟩ := hs r hr; exact (h r' hr').sub_right hsub

/-- `tFrame` is within `tagFrame`. -/
theorem tFrame_sub {st w sp : BitVec 32} {o : Nat} :
    ∀ r ∈ tFrame st w sp 16, ∃ r' ∈ VG.Proof.AesGcm.Arm.tagFrame st w sp o, Region.Sub r r' := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by simpa using Offset.sub_base (State.addr st) (show 16 + 16 ≤ 32 by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 512, 2048⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem t_tagFrame {st w sp : BitVec 32} {o : Nat} {m m' : Mem} (h : Frame (tFrame st w sp 16) m m') :
    Frame (VG.Proof.AesGcm.Arm.tagFrame st w sp o) m m' := h.sub VG.Proof.AesGcm.Arm.tFrame_sub

/-- After `finTag o`, from `m₀`. -/
structure FinOut (c st w sp k8 : BitVec 32) (na : Nat) (s₀ : State) (o R : Nat) (H : Block) (a ct : List Byte)
    (m₀ : Mem) (s : State) : Prop where
  env : ∃ k7, Env c st w sp k7 k8 s
  args : VG.Proof.AesGcm.Arm.ArgsKeep na s₀ s
  out : Absorbed m₀ (State.addr st + BitVec.ofNat 64 16) (State.addr st + BitVec.ofNat 64 32) H (ghashInput a ct) →
    bytesAt s.mem (State.addr w + BitVec.ofNat 64 o) 16 =
      toBytes (ghashFrom H (ghash H (blocks (padded a ct))) [ofBytes (lensBlock (VG.Proof.AesGcm.Arm.arg s₀ 1 ++ VG.Proof.AesGcm.Arm.arg s₀ 0).toNat ct.length)]
        ^^^ ciphOf m₀ (State.addr c) R (blockAt m₀ (State.addr st)))
  frame : Frame (VG.Proof.AesGcm.Arm.tagFrame st w sp o) m₀ s.mem

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

theorem finTag_ok {na : Nat} (hna : 4 ≤ na) {s₀ s : State} {o R : Nat} (ho : o = 0 ∨ o = 112) {H : Block}
    {a ct : List Byte} (he : Env c st w sp k7 k8 s) (hk : VG.Proof.AesGcm.Arm.ArgsKeep na s₀ s) (hf : s₀.sp.toNat + 4 * na ≤ 2 ^ 32)
    (hin : VG.Proof.AesGcm.Arm.args s₀ na ∈ s₀.rd) (hA : ∀ r ∈ VG.Proof.AesGcm.Arm.tagFrame st w sp o, (VG.Proof.AesGcm.Arm.args s₀ na).Disjoint r)
    (h8 : k8 = BitVec.ofNat 32 R) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H)
    (ha : a.length % 16 = (VG.Proof.AesGcm.Arm.arg s₀ 0).toNat % 16) (hP : (VG.Proof.AesGcm.Arm.arg s₀ 3 ++ VG.Proof.AesGcm.Arm.arg s₀ 2).toNat = ct.length) :
    WP isa (finTag o) s (VG.Proof.AesGcm.Arm.FinOut c st w sp k8 na s₀ o R H a ct s.mem) := by
  have hlt := Nat.mod_lt (ghashInput a ct).length (show 16 > 0 by decide)
  obtain ⟨i2, v2⟩ := hk.at hf hin 2 (by omega) (show 4 * 2 = 8 from rfl)
  obtain ⟨i3, v3⟩ := hk.at hf hin 3 (by omega) (show 4 * 3 = 12 from rfl)
  obtain ⟨s₁, run₁, hz₁, hg₁, hK₁⟩ : ∃ s₁, runBlock isa tlenZero s = some s₁ ∧
      s₁.z = decide (ct.length = 0) ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by simp only [tlenZero]; arun [i2, v2, i3, v3], ?_, ?_, ?_⟩
    · simp only [z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, v2, v3]
      rw [VG.Proof.AesGcm.Arm.z_sub0, ← hP]
      exact decide_eq_decide.mpr (VG.Proof.AesGcm.Arm.or_zero_iff _ _)
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hk₁ := hk.of_eq hK₁.mem hK₁.sp hK₁.rd hK₁.wr
  -- `r6`: the length of the buffered bytes, modulo 16
  have mid : WP isa (.ite .eq (.block [.ldrSp .r6 0]) (.block [.ldrSp .r6 8])) s₁ fun s₂ =>
      (s₂.gpr .r6).toNat % 16 = (ghashInput a ct).length % 16 ∧ (∀ r, r ≠ .r6 → s₂.gpr r = s₁.gpr r) ∧
        Keeps s₁ s₂ := by
    refine WP.ite _ (eval_eq' hz₁) (fun ht => ?_) (fun hf₁ => ?_)
    · have hc : ct = [] := List.eq_nil_of_length_eq_zero (by simpa using ht)
      subst hc
      obtain ⟨i0, v0⟩ := hk₁.at hf hin 0 (by omega) (show 4 * 0 = 0 from rfl)
      refine WP.of_runBlock ⟨_, by arun [i0, v0], ?_, ?_, ?_⟩
      · simp [gpr_setReg, v0, Proof.Gcm.ghashInput_nil, ha]
      · intro r hr; simp [gpr_setReg, hr]
      · exact ⟨rfl, rfl, rfl, rfl⟩
    · have hc : ct ≠ [] := fun e => by subst e; simp at hf₁
      obtain ⟨i2', v2'⟩ := hk₁.at hf hin 2 (by omega) (show 4 * 2 = 8 from rfl)
      refine WP.of_runBlock ⟨_, by arun [i2', v2'], ?_, ?_, ?_⟩
      · simp only [gpr_setReg, ite_true, v2', Proof.Gcm.ghashInput_of_ne hc, List.length_append,
          Proof.Gcm.length_zeros, VG.Proof.AesGcm.Arm.lowTo_mod16 hP]
        have := Proof.Gcm.length_pad_mod a.length; omega
      · intro r hr; simp [gpr_setReg, hr]
      · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.mono mid fun s₂ ⟨h6₂, hg₂, hK₂⟩ => ?_)
  obtain ⟨s₃, run₃, h6₃, hg₃, hK₃⟩ : ∃ s₃, runBlock isa [.dp .and .r6 .r6 (imm 15)] s₂ = some s₃ ∧
      s₃.gpr .r6 = BitVec.ofNat 32 ((ghashInput a ct).length % 16) ∧ (∀ r, r ≠ .r6 → s₃.gpr r = s₂.gpr r) ∧
      Keeps s₂ s₃ := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, and15, h6₂]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have hK₀₃ : Keeps s s₃ := (hK₁.trans hK₂).trans hK₃
  have he₃ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [hg₃ _ (by decide), hg₂ _ (by decide), hg₁ _ (by decide) (by decide)]) hK₀₃.sp hK₀₃.rd hK₀₃.wr
  have hk₃ := hk.of_eq hK₀₃.mem hK₀₃.sp hK₀₃.rd hK₀₃.wr
  refine WP.seq (WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl) (x := ghashInput a ct) (H := H)
    ⟨he₃, by rw [hK₀₃.mem]; exact hH⟩ h6₃)) fun s₄ hh => ?_)
  obtain ⟨hfl, rd₄, wr₄, sp₄⟩ := hh
  have hk₄ := hk₃.frame hf hfl.frame (VG.Proof.AesGcm.Arm.disj_sub hA VG.Proof.AesGcm.Arm.tFrame_sub) sp₄ rd₄ wr₄
  have hf₄ := hfl.frame
  rw [hK₀₃.mem] at hf₄
  -- the lengths
  obtain ⟨j0, w0⟩ := hk₄.at hf hin 0 (by omega) (show 4 * 0 = 0 from rfl)
  obtain ⟨j1, w1⟩ := hk₄.at hf hin 1 (by omega) (show 4 * 1 = 4 from rfl)
  obtain ⟨j2, w2⟩ := hk₄.at hf hin 2 (by omega) (show 4 * 2 = 8 from rfl)
  obtain ⟨j3, w3⟩ := hk₄.at hf hin 3 (by omega) (show 4 * 3 = 12 from rfl)
  obtain ⟨s₅, run₅, h4₅, h5₅, h6₅, h7₅, hg₅, hK₅⟩ : ∃ s₅, runBlock isa [.ldrSp .r4 0, .ldrSp .r5 4, .ldrSp .r6 8,
      .ldrSp .r7 12] s₄ = some s₅ ∧ s₅.gpr .r4 = VG.Proof.AesGcm.Arm.arg s₀ 0 ∧ s₅.gpr .r5 = VG.Proof.AesGcm.Arm.arg s₀ 1 ∧ s₅.gpr .r6 = VG.Proof.AesGcm.Arm.arg s₀ 2 ∧
      s₅.gpr .r7 = VG.Proof.AesGcm.Arm.arg s₀ 3 ∧ (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    refine ⟨_, by arun [j0, w0, j1, w1, j2, w2, j3, w3], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, w0]
    · simp [gpr_setReg, w1]
    · simp [gpr_setReg, w2]
    · simp [gpr_setReg, w3]
    · intro r a b d e; simp [gpr_setReg, a, b, d, e]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ := hfl.env.set7 h7₅ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide) (by decide) (by decide))
    hK₅.sp hK₅.rd hK₅.wr
  have hk₅ := hk₄.of_eq hK₅.mem hK₅.sp hK₅.rd hK₅.wr
  refine WP.mono (WP.with_rdwr (VG.Proof.AesGcm.Arm.tag_ok L ho he₅ h8 hR (H := H) (by rw [hK₅.mem]; exact hfl.hH) rfl)) fun s₆ hh => ?_
  obtain ⟨tg, rd₆, wr₆, sp₆⟩ := hh
  rw [h4₅, h5₅, h6₅, h7₅, hP, hK₅.mem] at tg
  refine ⟨⟨_, tg.env⟩, hk₄.frame hf tg.frame hA (sp₆.trans hK₅.sp) (rd₆.trans hK₅.rd) (wr₆.trans hK₅.wr), fun hab => ?_, ?_⟩
  · rw [tg.out]
    have hw := (hfl.abs (by rw [hK₀₃.mem]; exact hab)).whole_eq (by
      simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _)
    rw [show ghashInput a ct ++ zeros (padLen (ghashInput a ct).length) = padded a ct from rfl] at hw
    rw [hw, ciph_frame hf₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact L.cs.sub_right (Lay.stSub (by decide))
        · exact L.cw'.sub_right (Lay.wSub (by decide))
        · exact L.cw'.sub_right (Lay.wSub (by decide))
        · exact L.kc.symm) hR,
      blockAt_frame hf₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · simpa using Lay.st_st (st := st) (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide)
            (by decide)
        · simpa using L.st_w (a := 0) (n := 16) (d := 96) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
        · simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 256) (by decide) (.inr ⟨by decide, by decide⟩)
        · simpa using (L.stk_st (a := 0) (n := 16) (by decide)).symm)]
  · exact (VG.Proof.AesGcm.Arm.t_tagFrame hf₄).trans tg.frame

end

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.StreamCrypt`. -/
section

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt`

Untrusted: everything here is checked by Lean. Both save our caller's
registers in `scratch` (`W`); `encrypt` XORs the keystream into the data
(`crypt`) and then absorbs the ciphertext into GHASH (`textAbsorb`), and
`decrypt` the other way round (`streamEncrypt_wp`, `streamDecrypt_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput gctr inc32 j0)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

theorem scLay {s₀ : State} (h : VG.Proof.AesGcm.Arm.streamCryptPre s₀) : Lay (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp := by
  obtain ⟨-, -, dcs, -, dcW, -, dsW, -, -, -, -, bc, bs, -, bW, fc, fs, -, fW, sp8, -, -⟩ := h
  exact Lay.of fc fs fW sp8 dcs dcW dsW bc bs bW

/-- The rounds, as `r1` holds them. -/
abbrev scR (s₀ : State) : Nat := (s₀.gpr .r1).toNat

/-- After the entry, from `s₀`. -/
structure SC1 (s₀ s₁ : State) : Prop where
  env : Env (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp (s₀.gpr .r7) (s₀.gpr .r1) s₁
  args : VG.Proof.AesGcm.Arm.ArgsKeep 7 s₀ s₁
  saved : VG.Proof.AesGcm.Arm.SavedAt s₁.mem (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀
  frame : Frame [VG.Proof.AesGcm.Arm.savedR (VG.Proof.AesGcm.Arm.arg s₀ 6)] s₀.mem s₁.mem

theorem sc_argsW {s₀ : State} (h : VG.Proof.AesGcm.Arm.streamCryptPre s₀) : ∀ r ∈ [VG.Proof.AesGcm.Arm.savedR (VG.Proof.AesGcm.Arm.arg s₀ 6)], (VG.Proof.AesGcm.Arm.args s₀ 7).Disjoint r := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, dWA, -⟩ := h
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact (dWA.sub_left (Lay.wSub (by decide))).symm

theorem sc1_wp {s₀ : State} (h : VG.Proof.AesGcm.Arm.streamCryptPre s₀) {Q : State → Prop} (k : ∀ s₁, VG.Proof.AesGcm.Arm.SC1 s₀ s₁ → Q s₁) :
    WP isa (.block cryptEntry) s₀ Q := by
  have hA := VG.Proof.AesGcm.Arm.sc_argsW h
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fW, -, spf, -⟩ := h
  have hC : Covers [⟨State.addr (s₀.gpr .r0), 256⟩] (s₀.rd ++ s₀.wr) := by
    rw [hrd]; exact covers_of_mem (by simp)
  have hS : Covers [⟨State.addr (s₀.gpr .r2), 80⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have hW : Covers [⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have ha : ∀ i < 7, InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 (4 * i))) 4 :=
    fun i hi => VG.Proof.AesGcm.Arm.arg_in (n := 7) hi spf (by rw [hrd]; simp)
  refine VG.Proof.AesGcm.Arm.entry_ok (off := 24) (by decide) (ha 6 (by decide)) fW hW fun s₁ g12 g rd wr sp sv fr => ?_
  have hk : VG.Proof.AesGcm.Arm.ArgsKeep 7 s₀ s₁ := (ArgsKeep.refl 7 s₀).frame spf fr hA sp rd wr
  refine WP.of_runBlock ⟨_, by arun [], ?_⟩
  refine k _ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩, ?_, sv, fr⟩
  any_goals (simp [gpr_setReg, g, g12]; done)
  · simp [gpr_setReg, g, g12]; rfl
  · exact sp
  · change Covers _ (s₁.rd ++ s₁.wr); rw [rd, wr]; exact hC
  · change Covers _ s₁.wr; rw [wr]; exact hS
  · change Covers _ s₁.wr; rw [wr]; exact hW
  · exact hk.of_eq rfl rfl rfl rfl

theorem textArgs_run {s₀ s : State} (hk : VG.Proof.AesGcm.Arm.ArgsKeep 7 s₀ s) (hf : s₀.sp.toNat + 4 * 7 ≤ 2 ^ 32)
    (hin : VG.Proof.AesGcm.Arm.args s₀ 7 ∈ s₀.rd) :
    ∃ s', runBlock isa textArgs s = some s' ∧
      s'.gpr .r4 = VG.Proof.AesGcm.Arm.arg s₀ 4 ∧ s'.gpr .r5 = VG.Proof.AesGcm.Arm.arg s₀ 5 ∧ s'.gpr .r6 = BitVec.ofNat 32 ((VG.Proof.AesGcm.Arm.arg s₀ 2).toNat % 16) ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain ⟨i4, v4⟩ := hk.at hf hin 4 (by decide) (show 4 * 4 = 16 from rfl)
  obtain ⟨i5, v5⟩ := hk.at hf hin 5 (by decide) (show 4 * 5 = 20 from rfl)
  obtain ⟨i2, v2⟩ := hk.at hf hin 2 (by decide) (show 4 * 2 = 8 from rfl)
  refine ⟨_, by simp only [textArgs]; arun [i4, v4, i5, v5, i2, v2], ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, v4]
  · simp [gpr_setReg, v5]
  · simp only [gpr_setReg, ite_true, v2, and15]
  · intro r a b d; simp [gpr_setReg, a, b, d]
  · exact ⟨rfl, rfl, rfl, rfl⟩

section
variable {s₀ : State} (h : VG.Proof.AesGcm.Arm.streamCryptPre s₀)
include h

/-- The data, as `crypt` needs it. -/
theorem sc_dataW {k7 : BitVec 32} {s : State} (hk : VG.Proof.AesGcm.Arm.ArgsKeep 7 s₀ s) :
    DataW (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s (VG.Proof.AesGcm.Arm.arg s₀ 4) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat := by
  obtain ⟨hrd, hwr, -, dcD, -, dsD, -, -, dDW, -, -, -, -, bD, -, -, -, fD, -, -, -, -⟩ := h
  have hD : Covers [⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4), (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat⟩] s.wr := by
    rw [hk.wr, hwr]; exact covers_of_mem (by simp)
  exact ⟨⟨covers_left hD, (VG.Proof.AesGcm.Arm.arg s₀ 5).isLt, fD, dsD.symm, dDW, bD⟩, hD, dcD⟩

/-- The input of `crypt`, for `P` bytes of text so far. -/
theorem sc_crIn {k7 : BitVec 32} {s : State} (he : Env (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s)
    (hk : VG.Proof.AesGcm.Arm.ArgsKeep 7 s₀ s) (h4 : s.gpr .r4 = VG.Proof.AesGcm.Arm.arg s₀ 4) (h5 : s.gpr .r5 = VG.Proof.AesGcm.Arm.arg s₀ 5)
    (h6 : s.gpr .r6 = BitVec.ofNat 32 ((VG.Proof.AesGcm.Arm.arg s₀ 2).toNat % 16)) (icb : Block) {P : Nat}
    (hP : (VG.Proof.AesGcm.Arm.arg s₀ 3 ++ VG.Proof.AesGcm.Arm.arg s₀ 2).toNat = P) :
    CrIn (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) (VG.Proof.AesGcm.Arm.scR s₀) icb P (VG.Proof.AesGcm.Arm.arg s₀ 4) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat s :=
  ⟨he, h4, by rw [h5]; simp, by rw [h6, VG.Proof.AesGcm.Arm.lowTo_mod16 hP], by rw [he.r8]; simp, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    VG.Proof.AesGcm.Arm.sc_dataW h hk⟩

/-- The stack arguments are apart from what the pieces write. -/
theorem sc_argsCr : ∀ r ∈ crFrame (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp (VG.Proof.AesGcm.Arm.arg s₀ 4) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat, (VG.Proof.AesGcm.Arm.args s₀ 7).Disjoint r := by
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, dsA, -, dDA, dWA, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact dDA.symm
  · exact (dsA.sub_left (Lay.stSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (VG.Proof.AesGcm.Arm.below_args s₀ spf).symm

theorem sc_argsTa : ∀ r ∈ VG.Proof.AesGcm.Arm.taFrame (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp, (VG.Proof.AesGcm.Arm.args s₀ 7).Disjoint r := by
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, dsA, -, -, dWA, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (dsA.sub_left (Lay.stSub (by decide))).symm
  · exact (dsA.sub_left (Lay.stSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (VG.Proof.AesGcm.Arm.below_args s₀ spf).symm

end

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp)
include L

theorem stp_crFrame {k7 k8 : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (hd : DataW c st w sp k7 k8 s D n)
    {d k : Nat} (h1 : d + k ≤ 48) :
    ∀ r ∈ crFrame st w sp D n, (⟨State.addr st + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.ok.st.sub_right (Lay.stSub (by omega))).symm
  · exact Lay.st_st (.inl h1) (by omega) (by decide)
  · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · exact (L.stk_st (by omega)).symm

theorem stp_taFrame {d k : Nat} (hd : d + k ≤ 16 ∨ 48 ≤ d ∧ d + k ≤ 80) :
    ∀ r ∈ VG.Proof.AesGcm.Arm.taFrame st w sp, (⟨State.addr st + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Lay.st_st (by omega) (by omega) (by decide)
  · exact Lay.st_st (by omega) (by omega) (by decide)
  · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · exact (L.stk_st (by omega)).symm

theorem stp_saved {d k : Nat} (h1 : d + k ≤ 80) :
    ∀ r ∈ [VG.Proof.AesGcm.Arm.savedR w], (⟨State.addr st + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact L.st_w h1 (.inr ⟨by decide, by decide⟩)

theorem ctx_saved : ∀ r ∈ [VG.Proof.AesGcm.Arm.savedR w], (⟨State.addr c, 256⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact L.cw'.sub_right (Lay.wSub (by decide))

theorem ctx_taFrame : ∀ r ∈ VG.Proof.AesGcm.Arm.taFrame st w sp, (⟨State.addr c, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.kc.symm

omit L in
theorem data_taFrame {s : State} {D : BitVec 32} {n : Nat} (hd : DataOk st w sp s D n) :
    ∀ r ∈ VG.Proof.AesGcm.Arm.taFrame st w sp, (⟨State.addr D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hd.st.sub_right (Lay.stSub (by decide))
  · exact hd.st.sub_right (Lay.stSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · exact hd.stk.symm

omit L in
theorem data_saved {s : State} {D : BitVec 32} {n : Nat} (hd : DataOk st w sp s D n) :
    ∀ r ∈ [VG.Proof.AesGcm.Arm.savedR w], (⟨State.addr D, n⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact hd.w.sub_right (Lay.wSub (by decide))

theorem saved_taFrame : ∀ r ∈ VG.Proof.AesGcm.Arm.taFrame st w sp, (VG.Proof.AesGcm.Arm.savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

omit L in
/-- `ciphOf` is `ctxCiph`, and a frame apart from the context keeps it. -/
theorem ciph_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨State.addr c, 256⟩ : Region).Disjoint r) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    ciphOf m' (State.addr c) R = ctxCiph m (State.addr c) R := ciph_frame hf hd hR

omit L in
theorem ctxH_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨State.addr c, 256⟩ : Region).Disjoint r) :
    blockAt m' (State.addr c + BitVec.ofNat 64 240) = ctxH m (State.addr c) := by
  rw [VG.Proof.AesGcm.Arm.ctxH_eq, blockAt_frame hf (fun r hr => (hd r hr).sub_left (Lay.ctxSub (by decide)))]

end

/-- What `encrypt` (or `decrypt`) does, for the counter block `icb`, the
additional data `a` and the text `ct` so far (only their lengths matter to
the code). -/
structure EncOut (s₀ : State) (icb : Block) (a ct : List Byte) (dec : Bool) (s : State) : Prop where
  ctr : Ctr s₀.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48) (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (VG.Proof.AesGcm.Arm.scR s₀)) icb ct.length →
    Ctr s.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48) (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (VG.Proof.AesGcm.Arm.scR s₀)) icb (ct.length + (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat)
  out : Ctr s₀.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48) (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (VG.Proof.AesGcm.Arm.scR s₀)) icb ct.length →
    bytesAt s.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4)) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat =
      xorKs (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (VG.Proof.AesGcm.Arm.scR s₀)) icb ct.length
        (bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4)) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat)
  abs : Ctr s₀.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48) (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (VG.Proof.AesGcm.Arm.scR s₀)) icb ct.length →
    Absorbed s₀.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 16) (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 32)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (ghashInput a ct) →
    Absorbed s.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 16) (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 32)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (ghashInput a (ct ++ if dec then bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4)) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat else
        xorKs (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (VG.Proof.AesGcm.Arm.scR s₀)) icb ct.length
          (bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4)) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat)))
  j : blockAt s.mem (State.addr (s₀.gpr .r2)) = blockAt s₀.mem (State.addr (s₀.gpr .r2))

theorem enc_run {s₀ : State} (h : VG.Proof.AesGcm.Arm.streamCryptPre s₀) (icb : Block) {a ct : List Byte}
    (ha : a.length % 16 = (VG.Proof.AesGcm.Arm.arg s₀ 0).toNat % 16) (hP : (VG.Proof.AesGcm.Arm.arg s₀ 3 ++ VG.Proof.AesGcm.Arm.arg s₀ 2).toNat = ct.length) :
    WP isa streamEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ VG.Proof.AesGcm.Arm.EncOut s₀ icb a ct false s' := by
  have L := VG.Proof.AesGcm.Arm.scLay h
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have fW := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : VG.Proof.AesGcm.Arm.args s₀ 7 ∈ s₀.rd := by rw [h.1]; simp
  refine WP.seq (WP.block_append (VG.Proof.AesGcm.Arm.sc1_wp h fun s₁ h1 => ?_))
  obtain ⟨s₂, run₂, h4, h5, h6, hg₂, hK₂⟩ := VG.Proof.AesGcm.Arm.textArgs_run h1.args spf hin
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have he₂ := h1.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hK₂.sp hK₂.rd hK₂.wr
  have hk₂ := h1.args.of_eq hK₂.mem hK₂.sp hK₂.rd hK₂.wr
  have ci := VG.Proof.AesGcm.Arm.sc_crIn h he₂ hk₂ h4 h5 h6 icb hP
  have hd₂ := ci.data
  refine WP.seq (WP.mono (WP.with_rdwr (crypt_ok L ci)) fun s₃ hh => ?_)
  obtain ⟨co, rd₃, wr₃, sp₃⟩ := hh
  have hk₃ := hk₂.frame spf co.frame (VG.Proof.AesGcm.Arm.sc_argsCr h) sp₃ rd₃ wr₃
  have hd₃ := (VG.Proof.AesGcm.Arm.sc_dataW (k7 := s₀.gpr .r7) h hk₃).ok
  have f₂ : Frame [VG.Proof.AesGcm.Arm.savedR (VG.Proof.AesGcm.Arm.arg s₀ 6)] s₀.mem s₂.mem := by rw [hK₂.mem]; exact h1.frame
  have hH₃ : blockAt s₃.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0)) := by
    rw [blockAt_frame co.frame (fun r hr => (ctx_crFrame L hd₂ r hr).sub_left (Lay.ctxSub (by decide))),
      VG.Proof.AesGcm.Arm.ctxH_keep f₂ (VG.Proof.AesGcm.Arm.ctx_saved L)]
  refine WP.seq (WP.mono (WP.with_rdwr (VG.Proof.AesGcm.Arm.textAbsorb_ok L co.env hk₃ spf hin (VG.Proof.AesGcm.Arm.sc_argsTa h) hH₃ hd₃ ha hP))
    fun s₄ hh => ?_)
  obtain ⟨ta, rd₄, wr₄, sp₄⟩ := hh
  have sv₄ : VG.Proof.AesGcm.Arm.SavedAt s₄.mem (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀ :=
    (((hK₂.mem ▸ h1.saved : VG.Proof.AesGcm.Arm.SavedAt s₂.mem (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀)).frame co.frame (VG.Proof.AesGcm.Arm.saved_crFrame L hd₂)).frame ta.frame
      (VG.Proof.AesGcm.Arm.saved_taFrame L)
  refine WP.mono (VG.Proof.AesGcm.Arm.restore_ok ta.env.r11 fW (covers_left ta.env.perm.w) sv₄ ta.env.sp) fun s' hh => ⟨hh.1, ?_⟩
  have hm : s'.mem = s₄.mem := hh.2.1
  have hc : ciphOf s₂.mem (State.addr (s₀.gpr .r0)) (VG.Proof.AesGcm.Arm.scR s₀) = ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (VG.Proof.AesGcm.Arm.scR s₀) :=
    VG.Proof.AesGcm.Arm.ciph_keep f₂ (VG.Proof.AesGcm.Arm.ctx_saved L) hR
  have ctr₂ : ∀ {P : Nat}, Ctr s₀.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48)
      (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (VG.Proof.AesGcm.Arm.scR s₀)) icb P →
      Ctr s₂.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48)
      (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64) (ciphOf s₂.mem (State.addr (s₀.gpr .r0)) (VG.Proof.AesGcm.Arm.scR s₀)) icb P :=
    fun hc₀ => by
      rw [hc]
      exact hc₀.congr (blockAt_frame f₂ (VG.Proof.AesGcm.Arm.stp_saved L (by decide))) (blockAt_frame f₂ (VG.Proof.AesGcm.Arm.stp_saved L (by decide)))
  have dat₂ : bytesAt s₂.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4)) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat =
      bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4)) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat :=
    bytesAt_frame f₂ (VG.Proof.AesGcm.Arm.data_saved hd₂.ok) (by have := hd₂.ok.lt; omega)
  have out₃ : Ctr s₀.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48)
      (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (VG.Proof.AesGcm.Arm.scR s₀)) icb ct.length →
      bytesAt s₃.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4)) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat =
        xorKs (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (VG.Proof.AesGcm.Arm.scR s₀)) icb ct.length
          (bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4)) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat) := fun hc₀ => by
    rw [co.out (ctr₂ hc₀), hc, dat₂]
  refine ⟨fun hc₀ => ?_, fun hc₀ => ?_, fun hc₀ hab => ?_, ?_⟩
  · rw [hm]
    have := co.ctr (ctr₂ hc₀)
    rw [hc] at this
    exact this.congr (blockAt_frame ta.frame (VG.Proof.AesGcm.Arm.stp_taFrame L (.inr ⟨by decide, by decide⟩)))
      (blockAt_frame ta.frame (VG.Proof.AesGcm.Arm.stp_taFrame L (.inr ⟨by decide, by decide⟩)))
  · rw [hm, bytesAt_frame ta.frame (VG.Proof.AesGcm.Arm.data_taFrame hd₃) (by have := hd₃.lt; omega)]
    exact out₃ hc₀
  · rw [hm]
    have hb := Nat.mod_lt (ghashInput a ct).length (show 16 > 0 by decide)
    have hab₃ : Absorbed s₃.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 16)
        (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 32) (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (ghashInput a ct) :=
      (hab.congr (blockAt_frame f₂ (VG.Proof.AesGcm.Arm.stp_saved L (by decide)))
        (bytesAt_frame f₂ (VG.Proof.AesGcm.Arm.stp_saved L (by omega)) (by omega))).congr
        (blockAt_frame co.frame (VG.Proof.AesGcm.Arm.stp_crFrame L hd₂ (by decide)))
        (bytesAt_frame co.frame (VG.Proof.AesGcm.Arm.stp_crFrame L hd₂ (by omega)) (by omega))
    have := ta.abs hab₃
    rw [out₃ hc₀] at this
    exact this
  · rw [hm, blockAt_frame ta.frame (by simpa using VG.Proof.AesGcm.Arm.stp_taFrame L (d := 0) (k := 16) (.inl (by decide))),
      blockAt_frame co.frame (by simpa using VG.Proof.AesGcm.Arm.stp_crFrame L hd₂ (d := 0) (k := 16) (by decide)),
      blockAt_frame f₂ (by simpa using VG.Proof.AesGcm.Arm.stp_saved L (d := 0) (k := 16) (by decide))]

theorem dec_run {s₀ : State} (h : VG.Proof.AesGcm.Arm.streamCryptPre s₀) (icb : Block) {a ct : List Byte}
    (ha : a.length % 16 = (VG.Proof.AesGcm.Arm.arg s₀ 0).toNat % 16) (hP : (VG.Proof.AesGcm.Arm.arg s₀ 3 ++ VG.Proof.AesGcm.Arm.arg s₀ 2).toNat = ct.length) :
    WP isa streamDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ VG.Proof.AesGcm.Arm.EncOut s₀ icb a ct true s' := by
  have L := VG.Proof.AesGcm.Arm.scLay h
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have fW := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : VG.Proof.AesGcm.Arm.args s₀ 7 ∈ s₀.rd := by rw [h.1]; simp
  refine WP.seq (VG.Proof.AesGcm.Arm.sc1_wp h fun s₁ h1 => ?_)
  have hd₁ := (VG.Proof.AesGcm.Arm.sc_dataW (k7 := s₀.gpr .r7) h h1.args).ok
  have hH₁ : blockAt s₁.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0)) :=
    VG.Proof.AesGcm.Arm.ctxH_keep h1.frame (VG.Proof.AesGcm.Arm.ctx_saved L)
  refine WP.seq (WP.mono (WP.with_rdwr (VG.Proof.AesGcm.Arm.textAbsorb_ok L h1.env h1.args spf hin (VG.Proof.AesGcm.Arm.sc_argsTa h) hH₁ hd₁ ha hP))
    fun s₂ hh => ?_)
  obtain ⟨ta, rd₂, wr₂, sp₂⟩ := hh
  obtain ⟨s₃, run₃, h4, h5, h6, hg₃, hK₃⟩ := VG.Proof.AesGcm.Arm.textArgs_run ta.args spf hin
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ := ta.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide) (by decide)) hK₃.sp hK₃.rd hK₃.wr
  have hk₃ := ta.args.of_eq hK₃.mem hK₃.sp hK₃.rd hK₃.wr
  have ci := VG.Proof.AesGcm.Arm.sc_crIn h he₃ hk₃ h4 h5 h6 icb hP
  have hd₃ := ci.data
  refine WP.seq (WP.mono (WP.with_rdwr (crypt_ok L ci)) fun s₄ hh => ?_)
  obtain ⟨co, rd₄, wr₄, sp₄⟩ := hh
  have f₃ : Frame (VG.Proof.AesGcm.Arm.taFrame (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp) s₁.mem s₃.mem := by rw [hK₃.mem]; exact ta.frame
  have sv₄ : VG.Proof.AesGcm.Arm.SavedAt s₄.mem (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀ :=
    ((h1.saved.frame f₃ (VG.Proof.AesGcm.Arm.saved_taFrame L))).frame co.frame (VG.Proof.AesGcm.Arm.saved_crFrame L hd₃)
  refine WP.mono (VG.Proof.AesGcm.Arm.restore_ok co.env.r11 fW (covers_left co.env.perm.w) sv₄ co.env.sp) fun s' hh => ⟨hh.1, ?_⟩
  have hm : s'.mem = s₄.mem := hh.2.1
  have hc : ciphOf s₃.mem (State.addr (s₀.gpr .r0)) (VG.Proof.AesGcm.Arm.scR s₀) = ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (VG.Proof.AesGcm.Arm.scR s₀) := by
    rw [VG.Proof.AesGcm.Arm.ciph_keep f₃ (VG.Proof.AesGcm.Arm.ctx_taFrame L) hR]; exact VG.Proof.AesGcm.Arm.ciph_keep h1.frame (VG.Proof.AesGcm.Arm.ctx_saved L) hR
  have ctr₃ : ∀ {P : Nat}, Ctr s₀.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48)
      (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (VG.Proof.AesGcm.Arm.scR s₀)) icb P →
      Ctr s₃.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 48)
      (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 64) (ciphOf s₃.mem (State.addr (s₀.gpr .r0)) (VG.Proof.AesGcm.Arm.scR s₀)) icb P :=
    fun hc₀ => by
      rw [hc]
      exact (hc₀.congr (blockAt_frame h1.frame (VG.Proof.AesGcm.Arm.stp_saved L (by decide)))
        (blockAt_frame h1.frame (VG.Proof.AesGcm.Arm.stp_saved L (by decide)))).congr
        (blockAt_frame f₃ (VG.Proof.AesGcm.Arm.stp_taFrame L (.inr ⟨by decide, by decide⟩)))
        (blockAt_frame f₃ (VG.Proof.AesGcm.Arm.stp_taFrame L (.inr ⟨by decide, by decide⟩)))
  have dat₁ : bytesAt s₁.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4)) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat =
      bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4)) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat :=
    bytesAt_frame h1.frame (VG.Proof.AesGcm.Arm.data_saved hd₁) (by have := hd₁.lt; omega)
  have dat₃ : bytesAt s₃.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4)) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat =
      bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4)) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat := by
    rw [bytesAt_frame f₃ (VG.Proof.AesGcm.Arm.data_taFrame hd₁) (by have := hd₁.lt; omega), dat₁]
  refine ⟨fun hc₀ => ?_, fun hc₀ => ?_, fun hc₀ hab => ?_, ?_⟩
  · rw [hm]
    have := co.ctr (ctr₃ hc₀)
    rwa [hc] at this
  · rw [hm, co.out (ctr₃ hc₀), hc, dat₃]
  · rw [hm]
    have hb := Nat.mod_lt (ghashInput a ct).length (show 16 > 0 by decide)
    have hab₂ := ta.abs ((hab.congr (blockAt_frame h1.frame (VG.Proof.AesGcm.Arm.stp_saved L (by decide)))
        (bytesAt_frame h1.frame (VG.Proof.AesGcm.Arm.stp_saved L (by omega)) (by omega))))
    rw [dat₁] at hab₂
    rw [← hK₃.mem] at hab₂
    have hb' := Nat.mod_lt (ghashInput a (ct ++ bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4)) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat)).length
      (show 16 > 0 by decide)
    exact hab₂.congr (blockAt_frame co.frame (VG.Proof.AesGcm.Arm.stp_crFrame L hd₃ (by decide)))
      (bytesAt_frame co.frame (VG.Proof.AesGcm.Arm.stp_crFrame L hd₃ (by omega)) (by omega))
  · rw [hm, blockAt_frame co.frame (by simpa using VG.Proof.AesGcm.Arm.stp_crFrame L hd₃ (d := 0) (k := 16) (by decide)),
      blockAt_frame f₃ (by simpa using VG.Proof.AesGcm.Arm.stp_taFrame L (d := 0) (k := 16) (.inl (by decide))),
      blockAt_frame h1.frame (by simpa using VG.Proof.AesGcm.Arm.stp_saved L (d := 0) (k := 16) (by decide))]

theorem streamEncrypt_wp {s₀ : State} (h : streamEncryptArm.pre s₀) :
    WP isa streamEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ streamEncryptArm.post s₀ s' := by
  have h' : VG.Proof.AesGcm.Arm.streamCryptPre s₀ := h
  have h₀ := VG.Proof.AesGcm.Arm.enc_run h' 0 (a := List.replicate ((VG.Proof.AesGcm.Arm.arg s₀ 0).toNat % 16) 0)
    (ct := List.replicate (VG.Proof.AesGcm.Arm.arg s₀ 3 ++ VG.Proof.AesGcm.Arm.arg s₀ 2).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte × List Byte =>
      let ciph := ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat
      let hh := ctxH s₀.mem (State.addr (s₀.gpr .r0))
      StreamRepr s₀.mem (State.addr (s₀.gpr .r2)) ciph hh i.1 i.2.1 (gctr ciph (inc32 (j0 hh i.1)) i.2.2) ∧
        VG.Proof.AesGcm.Arm.arg64 s₀ 0 = BitVec.ofNat 64 i.2.1.length ∧ (VG.Proof.AesGcm.Arm.arg64 s₀ 2).toNat = i.2.2.length)
    fun i hi => VG.Proof.AesGcm.Arm.enc_run h' (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) i.1)) (a := i.2.1)
      (ct := gctr (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
        (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) i.1)) i.2.2)
      (VG.Proof.AesGcm.Arm.low_mod16 hi.2.1).symm (by rw [Proof.Gcm.length_gctr]; exact hi.2.2))
    fun s' hh => ⟨hh.1, fun iv a p hs hl hp => ?_⟩
  obtain ⟨-, eo⟩ := hh.2 ⟨iv, a, p⟩ ⟨hs, hl, hp⟩
  rw [Proof.Gcm.streamRepr_iff] at hs
  obtain ⟨hj, hab, hct⟩ := hs
  simp only [VG.Proof.AesGcm.Arm.ofNat_lit] at hab hct
  have hl' : (gctr (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
      (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv)) p).length = p.length := Proof.Gcm.length_gctr _ _ _
  have eo₁ := eo.ctr hct
  have eo₂ := eo.out hct
  have eo₃ := eo.abs hct hab
  simp only [Bool.false_eq_true, ite_false] at eo₃
  rw [hl'] at eo₁ eo₂ eo₃
  rw [← Proof.Gcm.gctr_append] at eo₃
  refine ⟨?_, ?_⟩
  · rw [Proof.Gcm.streamRepr_iff]
    simp only [VG.Proof.AesGcm.Arm.ofNat_lit]
    refine ⟨eo.j.trans hj, eo₃, ?_⟩
    rw [Proof.Gcm.length_gctr, List.length_append, length_bytesAt]; exact eo₁
  · rw [eo₂, Proof.Gcm.gctr_append, List.drop_left' hl']

theorem streamDecrypt_wp {s₀ : State} (h : streamDecryptArm.pre s₀) :
    WP isa streamDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ streamDecryptArm.post s₀ s' := by
  have h' : VG.Proof.AesGcm.Arm.streamCryptPre s₀ := h
  have h₀ := VG.Proof.AesGcm.Arm.dec_run h' 0 (a := List.replicate ((VG.Proof.AesGcm.Arm.arg s₀ 0).toNat % 16) 0)
    (ct := List.replicate (VG.Proof.AesGcm.Arm.arg s₀ 3 ++ VG.Proof.AesGcm.Arm.arg s₀ 2).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte × List Byte =>
      let ciph := ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat
      let hh := ctxH s₀.mem (State.addr (s₀.gpr .r0))
      StreamRepr s₀.mem (State.addr (s₀.gpr .r2)) ciph hh i.1 i.2.1 i.2.2 ∧
        VG.Proof.AesGcm.Arm.arg64 s₀ 0 = BitVec.ofNat 64 i.2.1.length ∧ (VG.Proof.AesGcm.Arm.arg64 s₀ 2).toNat = i.2.2.length)
    fun i hi => VG.Proof.AesGcm.Arm.dec_run h' (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) i.1)) (a := i.2.1) (ct := i.2.2)
      (VG.Proof.AesGcm.Arm.low_mod16 hi.2.1).symm hi.2.2)
    fun s' hh => ⟨hh.1, fun iv a c hs hl hp => ?_⟩
  obtain ⟨-, eo⟩ := hh.2 ⟨iv, a, c⟩ ⟨hs, hl, hp⟩
  rw [Proof.Gcm.streamRepr_iff] at hs
  obtain ⟨hj, hab, hct⟩ := hs
  simp only [VG.Proof.AesGcm.Arm.ofNat_lit] at hab hct
  have eo₁ := eo.ctr hct
  have eo₂ := eo.out hct
  have eo₃ := eo.abs hct hab
  simp only [ite_true] at eo₃
  refine ⟨?_, ?_⟩
  · rw [Proof.Gcm.streamRepr_iff]
    simp only [VG.Proof.AesGcm.Arm.ofNat_lit]
    refine ⟨eo.j.trans hj, eo₃, ?_⟩
    rw [List.length_append, length_bytesAt]; exact eo₁
  · rw [eo₂, Proof.Gcm.gctr_append, List.drop_left' (Proof.Gcm.length_gctr _ _ _)]

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.StreamFinish`. -/
section

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_stream_finish`

Untrusted: everything here is checked by Lean. `stream_finish` saves our
caller's registers in `work` (`W`), writes the tag to its first 16 bytes
with `finTag` and copies it to `tag` (`tagOut_ok`, `streamFinish_wp`). The
entry is shared with `stream_verify` (`fin1_wp`, for `n` words of stack
arguments, `work` the `wi`-th).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput fullTag)
open VG.Proof.Gcm (Absorbed lensBlock)
open VG.Proof.Cmac (store4)

theorem lensBlock_mod (L c : Nat) : lensBlock (L % 2 ^ 64) c = lensBlock L c := by
  simp only [lensBlock]
  rw [← Proof.Gcm.be64_mod (8 * (L % 2 ^ 64)), ← Proof.Gcm.be64_mod (8 * L)]
  congr 2; omega

theorem toNat_of_eq {x : BitVec 64} {L : Nat} (h : x = BitVec.ofNat 64 L) : x.toNat = L % 2 ^ 64 := by
  rw [h, BitVec.toNat_ofNat]

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

/-- `tagOut`: the tag at `W` copied to `T`, the stack argument at `[sp + 16]`. -/
theorem tagOut_ok {s : State} (he : Env c st w sp k7 k8 s) {T : BitVec 32}
    (hTi : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 16)) 4)
    (hTv : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 16)) 32 = T)
    (hTw : Covers [⟨State.addr T, 16⟩] s.wr) (hTf : T.toNat + 16 ≤ 2 ^ 32)
    (hTd : (⟨State.addr T, 16⟩ : Region).Disjoint ⟨State.addr w, 16⟩) :
    ∃ s', runBlock isa tagOut s = some s' ∧ bytesAt s'.mem (State.addr T) 16 = bytesAt s.mem (State.addr w) 16 ∧
      Frame [⟨State.addr T, 16⟩] s.mem s'.mem ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h11 := he.r11
  have eW : ∀ d, d < 2560 → State.addr (w + BitVec.ofNat 32 d) = State.addr w + BitVec.ofNat 64 d :=
    fun d hd => L.wA hd
  have eT : ∀ d, d < 16 → State.addr (T + BitVec.ofNat 32 d) = State.addr T + BitVec.ofNat 64 d :=
    fun d hd => addr_add (by omega)
  have r₀ := he.perm.wR (show 0 + 4 ≤ 2560 by decide)
  have r₁ := he.perm.wR (show 4 + 4 ≤ 2560 by decide)
  have r₂ := he.perm.wR (show 8 + 4 ≤ 2560 by decide)
  have r₃ := he.perm.wR (show 12 + 4 ≤ 2560 by decide)
  have w₀ := in_off hTw (show 0 + 4 ≤ 16 by decide) (by decide)
  have w₁ := in_off hTw (show 4 + 4 ≤ 16 by decide) (by decide)
  have w₂ := in_off hTw (show 8 + 4 ≤ 16 by decide) (by decide)
  have w₃ := in_off hTw (show 12 + 4 ≤ 16 by decide) (by decide)
  have q : ∀ (m : Mem) (a b : Nat) (v : BitVec 32), a + 4 ≤ 16 → b + 4 ≤ 16 →
      (m.writeW (State.addr T + BitVec.ofNat 64 b) v).readW (State.addr w + BitVec.ofNat 64 a) 32 =
        m.readW (State.addr w + BitVec.ofNat 64 a) 32 := fun m a b v ha hb =>
    VG.Proof.AesGcm.Arm.sepW (m := m) ((hTd.symm.sub_left (Offset.sub_base _ ha)).sub_right (Offset.sub_base _ hb))
  have p₁ := fun m v => q m 4 0 v (by decide) (by decide)
  have p₂ := fun m v => q m 8 0 v (by decide) (by decide)
  have p₃ := fun m v => q m 8 4 v (by decide) (by decide)
  have p₄ := fun m v => q m 12 0 v (by decide) (by decide)
  have p₅ := fun m v => q m 12 4 v (by decide) (by decide)
  have p₆ := fun m v => q m 12 8 v (by decide) (by decide)
  obtain ⟨s', run, hm, hg, hk⟩ : ∃ s', runBlock isa tagOut s = some s' ∧
      s'.mem = store4 s.mem (State.addr T + BitVec.ofNat 64 0) (s.mem.readW (State.addr w + BitVec.ofNat 64 0) 32)
        (s.mem.readW (State.addr w + BitVec.ofNat 64 4) 32) (s.mem.readW (State.addr w + BitVec.ofNat 64 8) 32)
        (s.mem.readW (State.addr w + BitVec.ofNat 64 12) 32) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    refine ⟨_, by simp only [tagOut]; arun [hTi, hTv, h11, eW, eT, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, p₁, p₂, p₃, p₄,
      p₅, p₆], ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc]
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl⟩
  simp only [add_ofNat_zero] at hm
  refine ⟨s', run, by rw [hm]; exact VG.Proof.AesGcm.Arm.bytesAt_copy4 _ _ _, by rw [hm]; exact Cmac.frame_store4 _ _ _ _ _, hg, hk.1,
    hk.2.1, hk.2.2⟩

end

section
variable {n wi : Nat}

theorem finLay {s₀ : State} (h : VG.Proof.AesGcm.Arm.finPre n wi s₀) : Lay (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp := by
  obtain ⟨-, -, dcs, dcW, dsW, -, -, bc, bs, bW, fc, fs, fW, sp8, -, -⟩ := h
  exact Lay.of fc fs fW sp8 dcs dcW dsW bc bs bW

/-- After the entry, from `s₀`. -/
structure SF1 (n wi : Nat) (s₀ s₁ : State) : Prop where
  env : Env (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp (s₀.gpr .r7) (s₀.gpr .r1) s₁
  args : VG.Proof.AesGcm.Arm.ArgsKeep n s₀ s₁
  saved : VG.Proof.AesGcm.Arm.SavedAt s₁.mem (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀
  frame : Frame [VG.Proof.AesGcm.Arm.savedR (VG.Proof.AesGcm.Arm.arg s₀ wi)] s₀.mem s₁.mem

theorem fin1_wp {s₀ : State} (h : VG.Proof.AesGcm.Arm.finPre n wi s₀) (hn : wi < n) (hwi : 4 * wi < 4096) {Q : State → Prop}
    (k : ∀ s₁, VG.Proof.AesGcm.Arm.SF1 n wi s₀ s₁ → Q s₁) : WP isa (.block (finEntry (4 * wi))) s₀ Q := by
  obtain ⟨⟨hc, hin⟩, ⟨hs, hw, -⟩, -, -, -, -, dWA, -, -, -, -, -, fW, -, spf, -⟩ := h
  have hA : ∀ r ∈ [VG.Proof.AesGcm.Arm.savedR (VG.Proof.AesGcm.Arm.arg s₀ wi)], (VG.Proof.AesGcm.Arm.args s₀ n).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (dWA.sub_left (Lay.wSub (by decide))).symm
  have hC : Covers [⟨State.addr (s₀.gpr .r0), 256⟩] (s₀.rd ++ s₀.wr) :=
    covers_of_mem (List.mem_append_left _ hc)
  have hS : Covers [⟨State.addr (s₀.gpr .r2), 80⟩] s₀.wr := covers_of_mem hs
  have hW : Covers [⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ wi), 2560⟩] s₀.wr := covers_of_mem hw
  have ha : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 (4 * wi))) 4 :=
    VG.Proof.AesGcm.Arm.arg_in (n := n) hn spf hin
  refine VG.Proof.AesGcm.Arm.entry_ok (off := 4 * wi) hwi ha fW hW fun s₁ g12 g rd wr sp sv fr => ?_
  have hk : VG.Proof.AesGcm.Arm.ArgsKeep n s₀ s₁ := (ArgsKeep.refl n s₀).frame spf fr hA sp rd wr
  refine WP.of_runBlock ⟨_, by arun [], ?_⟩
  refine k _ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩, ?_, sv, fr⟩
  any_goals (simp [gpr_setReg, g, g12]; done)
  · simp [gpr_setReg, g, g12]; rfl
  · exact sp
  · change Covers _ (s₁.rd ++ s₁.wr); rw [rd, wr]; exact hC
  · change Covers _ s₁.wr; rw [wr]; exact hS
  · change Covers _ s₁.wr; rw [wr]; exact hW
  · exact hk.of_eq rfl rfl rfl rfl

theorem fin_argsTag {s₀ : State} (h : VG.Proof.AesGcm.Arm.finPre n wi s₀) {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ VG.Proof.AesGcm.Arm.tagFrame (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp o, (VG.Proof.AesGcm.Arm.args s₀ n).Disjoint r := by
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, dsA, dWA, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (dsA.sub_left (Region.sub_prefix (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by omega))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (VG.Proof.AesGcm.Arm.below_args s₀ spf).symm

/-- The tag, from the entry. -/
theorem fin_tag {s₀ s₁ : State} (h : VG.Proof.AesGcm.Arm.finPre n wi s₀) (hn : 4 ≤ n) (h1 : VG.Proof.AesGcm.Arm.SF1 n wi s₀ s₁) {o : Nat}
    (ho : o = 0 ∨ o = 112) {a ct : List Byte} (ha : a.length % 16 = (VG.Proof.AesGcm.Arm.arg s₀ 0).toNat % 16)
    (hP : (VG.Proof.AesGcm.Arm.arg s₀ 3 ++ VG.Proof.AesGcm.Arm.arg s₀ 2).toNat = ct.length) :
    WP isa (finTag o) s₁ (VG.Proof.AesGcm.Arm.FinOut (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp (s₀.gpr .r1) n s₀ o (s₀.gpr .r1).toNat
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) a ct s₁.mem) := by
  have L := VG.Proof.AesGcm.Arm.finLay h
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact VG.Proof.AesGcm.Arm.finTag_ok L hn ho h1.env h1.args spf h.1.2 (VG.Proof.AesGcm.Arm.fin_argsTag h ho) (by simp) hR
    (VG.Proof.AesGcm.Arm.ctxH_keep h1.frame (VG.Proof.AesGcm.Arm.ctx_saved L)) ha hP

/-- The tag, for a state that represents `a` and `ct`, from a memory `m₀` that
differs from the entry's only apart from the context and the state. -/
theorem fin_out {s₀ s : State} {m₀ : Mem} (h : VG.Proof.AesGcm.Arm.finPre n wi s₀) {rs : List Region} (hf₀ : Frame rs s₀.mem m₀)
    (hdc : ∀ r ∈ rs, (⟨State.addr (s₀.gpr .r0), 256⟩ : Region).Disjoint r)
    (hds : ∀ r ∈ rs, (⟨State.addr (s₀.gpr .r2), 80⟩ : Region).Disjoint r) {o : Nat} {iv a ct : List Byte}
    (hf : VG.Proof.AesGcm.Arm.FinOut (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp (s₀.gpr .r1) n s₀ o (s₀.gpr .r1).toNat
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) a ct m₀ s)
    (hs : StreamRepr s₀.mem (State.addr (s₀.gpr .r2)) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct) (hl : VG.Proof.AesGcm.Arm.arg64 s₀ 0 = BitVec.ofNat 64 a.length) :
    bytesAt s.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ wi) + BitVec.ofNat 64 o) 16 =
      fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat) (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
        iv a ct := by
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [Proof.Gcm.streamRepr_iff] at hs
  obtain ⟨hj, hab, -⟩ := hs
  simp only [VG.Proof.AesGcm.Arm.ofNat_lit] at hab hj
  have hb := Nat.mod_lt (ghashInput a ct).length (show 16 > 0 by decide)
  have dS : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ rs, (⟨State.addr (s₀.gpr .r2) + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun hd r hr => (hds r hr).sub_left (Lay.stSub hd)
  rw [hf.out (hab.congr (blockAt_frame hf₀ (dS (by decide)))
      (bytesAt_frame hf₀ (dS (by omega)) (by omega))),
    VG.Proof.AesGcm.Arm.ciph_keep hf₀ hdc hR,
    blockAt_frame hf₀ (by simpa using dS (d := 0) (k := 16) (by decide)), hj,
    VG.Proof.AesGcm.Arm.toNat_of_eq hl, VG.Proof.AesGcm.Arm.lensBlock_mod, Proof.Gcm.fullTag_eq]

end

theorem streamFinish_wp {s₀ : State} (h : streamFinishArm.pre s₀) :
    WP isa streamFinish s₀ fun s' => abiPreserved s₀ s' ∧ streamFinishArm.post s₀ s' := by
  have h' : VG.Proof.AesGcm.Arm.finPre 6 5 s₀ := streamFinishPreArm.fin h
  have L := VG.Proof.AesGcm.Arm.finLay h'
  have fW := h'.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hrd, hwr, -, -, -, -, -, -, tW, tA, -, -, -, -, -, -, -, fT, -⟩ := h
  have hin : VG.Proof.AesGcm.Arm.args s₀ 6 ∈ s₀.rd := h'.1.2
  have hTw : Covers [⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4), 16⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4), 16⟩ : Region).Disjoint
      ⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 5) + BitVec.ofNat 64 d, k⟩ := fun hd => tW.sub_right (Lay.wSub hd)
  have run : ∀ {a ct : List Byte}, a.length % 16 = (VG.Proof.AesGcm.Arm.arg s₀ 0).toNat % 16 → (VG.Proof.AesGcm.Arm.arg s₀ 3 ++ VG.Proof.AesGcm.Arm.arg s₀ 2).toNat = ct.length →
      WP isa streamFinish s₀ fun s' => abiPreserved s₀ s' ∧ ∀ iv,
        StreamRepr s₀.mem (State.addr (s₀.gpr .r2)) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
          (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct → VG.Proof.AesGcm.Arm.arg64 s₀ 0 = BitVec.ofNat 64 a.length →
        bytesAt s'.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4)) 16 =
          fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
            (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct := fun ha hP =>
    WP.seq (VG.Proof.AesGcm.Arm.fin1_wp (wi := 5) h' (by decide) (by decide) fun s₁ h1 =>
      WP.seq (WP.mono (VG.Proof.AesGcm.Arm.fin_tag h' (by decide) h1 (.inl rfl) ha hP) fun s₂ hf => by
        obtain ⟨k7, he⟩ := hf.env
        obtain ⟨i4, v4⟩ := hf.args.at spf hin 4 (by decide) (show 4 * 4 = 16 from rfl)
        obtain ⟨s₃, run₃, hb₃, hf₃, g₃, rd₃, wr₃, sp₃⟩ := VG.Proof.AesGcm.Arm.tagOut_ok L he i4 v4
          (by rw [hf.args.wr]; exact hTw) fT (by simpa using dW (d := 0) (k := 16) (by decide))
        refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
        have he₃ := he.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide)) sp₃ rd₃ wr₃
        have sv₂ := h1.saved.frame hf.frame (VG.Proof.AesGcm.Arm.saved_tagFrame L (.inl rfl))
        exact WP.mono (VG.Proof.AesGcm.Arm.restore_ok he₃.r11 fW (covers_left he₃.perm.w)
          (sv₂.frame hf₃ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact (dW (by decide)).symm)) he₃.sp)
          fun s' hh => ⟨hh.1, fun iv hs hl => by
            have := VG.Proof.AesGcm.Arm.fin_out h' h1.frame (VG.Proof.AesGcm.Arm.ctx_saved L) (fun r hr => by
              simp only [List.mem_singleton] at hr; subst hr; simpa using L.st_w (a := 0) (n := 80) (d := 128) (k := 36) (by decide) (.inr ⟨by decide, by decide⟩)) hf hs hl
            rw [add_ofNat_zero] at this
            rw [hh.2.1, hb₃, this]⟩))
  have h₀ := run (a := List.replicate ((VG.Proof.AesGcm.Arm.arg s₀ 0).toNat % 16) 0)
    (ct := List.replicate (VG.Proof.AesGcm.Arm.arg s₀ 3 ++ VG.Proof.AesGcm.Arm.arg s₀ 2).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte × List Byte =>
      StreamRepr s₀.mem (State.addr (s₀.gpr .r2)) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
          (ctxH s₀.mem (State.addr (s₀.gpr .r0))) i.1 i.2.1 i.2.2 ∧
        VG.Proof.AesGcm.Arm.arg64 s₀ 0 = BitVec.ofNat 64 i.2.1.length ∧ (VG.Proof.AesGcm.Arm.arg64 s₀ 2).toNat = i.2.2.length)
    fun i hi => WP.mono (run (a := i.2.1) (ct := i.2.2) (VG.Proof.AesGcm.Arm.low_mod16 hi.2.1).symm hi.2.2)
      fun s' hh => hh.2 i.1 hi.1 hi.2.1)
    fun s' hh => ⟨hh.1, fun iv a c hs hl hp => hh.2 ⟨iv, a, c⟩ ⟨hs, hl, hp⟩⟩

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.Compare`. -/
section

/-!
# AES-GCM on ARMv7: checking a received tag

Untrusted: everything here is checked by Lean. `tagLenOk` sets `Z` iff the
tag length in `r6` is not one §5.2.1.2 allows (`tagLenOk_ok`); `recv` and
`cmp o` copy the received tag (at `tag`) and the computed one (at `W + o`),
`r6` bytes of each, padded with zeros, to `W + 256` and `W + 240` (`recv_ok`,
`cmp_ok`), and `cmpTail` sets `r0` to 1 if they are equal and 0 if not,
without a branch (`cmpTail_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (zeros)
open VG.Proof.Cmac (le4 store4)

theorem shr31 (y : BitVec 32) : (y >>> 31).toNat = if y.msb then 1 else 0 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.msb_eq_decide]
  have := y.isLt
  by_cases h : 2 ^ (32 - 1) ≤ y.toNat
  · rw [decide_eq_true h]; simp only [ite_true]; simp only [Nat.reduceSub] at h; omega
  · rw [decide_eq_false h]; simp only [Bool.false_eq_true, ite_false]; simp only [Nat.reduceSub] at h; omega

theorem msb_or_neg (x : BitVec 32) : (x ||| (0 - x)) >>> 31 = if x = 0 then 0 else 1 := by
  apply BitVec.eq_of_toNat_eq
  have z0 : (0 : BitVec 32).toNat = 0 := rfl
  rw [VG.Proof.AesGcm.Arm.shr31, BitVec.msb_or, BitVec.msb_eq_decide, BitVec.msb_eq_decide (x := 0 - x), BitVec.toNat_sub, z0,
    Nat.add_zero]
  have := x.isLt
  by_cases h : x = 0
  · subst h; decide
  · have hx : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    have : 2 ^ (32 - 1) ≤ x.toNat ∨ 2 ^ (32 - 1) ≤ (2 ^ 32 - x.toNat) % 2 ^ 32 := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    simp only [h, ite_false, Bool.or_eq_true, decide_eq_true_eq]
    simp only [this, ite_true]; rfl
theorem le4_inj {x y : BitVec 32} (h : le4 x = le4 y) : x = y := by
  have e : ∀ k < 4, x.extractLsb' (8 * k) 8 = y.extractLsb' (8 * k) 8 := fun k hk => by
    have := congrArg (fun l => l.getD k 0) h
    simpa only [Cmac.getD_le4 _ hk] using this
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have := congrArg (fun v => v.getLsbD (j % 8)) (e (j / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb', show j % 8 < 8 from Nat.mod_lt _ (by decide), decide_true,
    Bool.true_and] at this
  rwa [show 8 * (j / 8) + j % 8 = j by omega] at this

/-- `chk k`: `r0 := 1` if `r6 = k`. -/
theorem chk_ok (k : Nat) (hk : k < 2 ^ 32) (he : encodable (BitVec.ofNat 32 k) = true) {s : State} {tl : Nat}
    (h6 : s.gpr .r6 = BitVec.ofNat 32 tl) (htl : tl < 2 ^ 32) {p : Bool}
    (h0 : s.gpr .r0 = if p then 1 else 0) :
    WP isa (chk k) s fun s' => s'.gpr .r0 = (if (tl == k || p) then 1 else 0) ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain ⟨s₁, run₁, hz, hg, hm, hrd, hwr, hsp⟩ := cmpk_ok s .r6 h6 htl hk he
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite _ (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have e : tl = k := by simpa using ht
    refine WP.of_runBlock ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp [gpr_setReg, e]
    · intro r hr; simp [gpr_setReg, hr, hg]
    · exact ⟨hm, hrd, hwr, hsp⟩
  · have e : tl ≠ k := by simpa using hf
    refine WP.block_nil ⟨?_, fun r _ => by rw [hg], ⟨hm, hrd, hwr, hsp⟩⟩
    rw [hg, h0]; simp [e]

theorem tagLenOk_eq (tl : Nat) :
    (tl == 16 || (tl == 15 || (tl == 14 || (tl == 13 || (tl == 12 || (tl == 8 || (tl == 4 || false))))))) =
      Spec.Gcm.tagLenOk tl := by
  simp only [Spec.Gcm.tagLenOk]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq, Bool.or_false]
  omega

/-- `tagLenOk`: `Z` clear iff the tag length is allowed. -/
theorem tagLenOk_ok {s : State} {tl : Nat} (h6 : s.gpr .r6 = BitVec.ofNat 32 tl) (htl : tl < 2 ^ 32) :
    WP isa tagLenOk s fun s' => s'.z = !Spec.Gcm.tagLenOk tl ∧ (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain ⟨s₀, run₀, h0₀, hg₀, hk₀⟩ : ∃ s₀, runBlock isa [.mov .r0 (imm 0)] s = some s₀ ∧
      s₀.gpr .r0 = (if false then 1 else 0) ∧ (∀ r, r ≠ .r0 → s₀.gpr r = s.gpr r) ∧ Keeps s s₀ := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₀, run₀, ?_⟩)
  have g6 : ∀ {s' : State}, (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) → s'.gpr .r6 = BitVec.ofNat 32 tl :=
    fun hg => by rw [hg _ (by decide), h6]
  refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.chk_ok 4 (by decide) (by decide) (g6 hg₀) htl h0₀) fun s₁ ⟨h0₁, hg₁, hk₁⟩ => ?_)
  have hg₁' : ∀ r, r ≠ .r0 → s₁.gpr r = s.gpr r := fun r hr => (hg₁ r hr).trans (hg₀ r hr)
  refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.chk_ok 8 (by decide) (by decide) (g6 hg₁') htl h0₁) fun s₂ ⟨h0₂, hg₂, hk₂⟩ => ?_)
  have hg₂' : ∀ r, r ≠ .r0 → s₂.gpr r = s.gpr r := fun r hr => (hg₂ r hr).trans (hg₁' r hr)
  refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.chk_ok 12 (by decide) (by decide) (g6 hg₂') htl h0₂) fun s₃ ⟨h0₃, hg₃, hk₃⟩ => ?_)
  have hg₃' : ∀ r, r ≠ .r0 → s₃.gpr r = s.gpr r := fun r hr => (hg₃ r hr).trans (hg₂' r hr)
  refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.chk_ok 13 (by decide) (by decide) (g6 hg₃') htl h0₃) fun s₄ ⟨h0₄, hg₄, hk₄⟩ => ?_)
  have hg₄' : ∀ r, r ≠ .r0 → s₄.gpr r = s.gpr r := fun r hr => (hg₄ r hr).trans (hg₃' r hr)
  refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.chk_ok 14 (by decide) (by decide) (g6 hg₄') htl h0₄) fun s₅ ⟨h0₅, hg₅, hk₅⟩ => ?_)
  have hg₅' : ∀ r, r ≠ .r0 → s₅.gpr r = s.gpr r := fun r hr => (hg₅ r hr).trans (hg₄' r hr)
  refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.chk_ok 15 (by decide) (by decide) (g6 hg₅') htl h0₅) fun s₆ ⟨h0₆, hg₆, hk₆⟩ => ?_)
  have hg₆' : ∀ r, r ≠ .r0 → s₆.gpr r = s.gpr r := fun r hr => (hg₆ r hr).trans (hg₅' r hr)
  refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.chk_ok 16 (by decide) (by decide) (g6 hg₆') htl h0₆) fun s₇ ⟨h0₇, hg₇, hk₇⟩ => ?_)
  have hg₇' : ∀ r, r ≠ .r0 → s₇.gpr r = s.gpr r := fun r hr => (hg₇ r hr).trans (hg₆' r hr)
  have hk : Keeps s s₇ := hk₀.trans (hk₁.trans (hk₂.trans (hk₃.trans (hk₄.trans (hk₅.trans (hk₆.trans hk₇))))))
  rw [VG.Proof.AesGcm.Arm.tagLenOk_eq] at h0₇
  refine WP.of_runBlock ⟨_, by arun [], ?_, ?_, ?_⟩
  · simp only [z_subFlags, h0₇]
    cases Spec.Gcm.tagLenOk tl <;> rfl
  · intro r hr; simp only [gpr_subFlags]; exact hg₇' r hr
  · exact ⟨hk.mem, hk.rd, hk.wr, hk.sp⟩

theorem store4_zero_tail (m : Mem) (p : Addr) {k : Nat} (hk : k ≤ 16) :
    bytesAt (store4 m p 0 0 0 0) (p + BitVec.ofNat 64 k) (16 - k) = zeros (16 - k) := by
  have h := store4_zero_bytes m p
  rw [show (16 : Nat) = k + (16 - k) by omega, bytesAt_add,
    show zeros (k + (16 - k)) = zeros k ++ zeros (16 - k) by rw [zeros, zeros, zeros, List.replicate_append_replicate]] at h
  exact (List.append_inj h (by simp [length_bytesAt, Proof.Gcm.length_zeros])).2

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

/-- A copy of `tl` bytes from `S` to `W + d`, which holds 16 zero bytes. -/
theorem padCopy_ok {s : State} (he : Env c st w sp k7 k8 s) {S : BitVec 32} {d tl : Nat}
    (hd : d + 16 ≤ 2560) (h1 : 1 ≤ tl) (h16 : tl ≤ 16) (hSr : Covers [⟨State.addr S, tl⟩] (s.rd ++ s.wr))
    (hSf : S.toNat + tl ≤ 2 ^ 32) (hSd : (⟨State.addr S, tl⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, 16⟩)
    {m₀ : Mem} (hm : s.mem = store4 m₀ (State.addr w + BitVec.ofNat 64 d) 0 0 0 0) (hr1 : s.gpr .r1 = S)
    (hr2 : s.gpr .r2 = w + BitVec.ofNat 32 d) (hr3 : s.gpr .r3 = BitVec.ofNat 32 tl) :
    WP isa copyLoop s fun s' => bytesAt s'.mem (State.addr w + BitVec.ofNat 64 d) 16 =
        bytesAt m₀ (State.addr S) tl ++ zeros (16 - tl) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 d, 16⟩] m₀ s'.mem ∧ LoopOut s S (w + BitVec.ofNat 32 d) tl s' := by
  have eD := L.wA (d := d) (by omega)
  have ww := L.ww
  have lp : LoopPre s S (w + BitVec.ofNat 32 d) tl := by
    refine ⟨hr1, hr2, hr3, h1, by omega, hSf, by rw [L.wN (by omega)]; omega, hSr, ?_, ?_⟩
    · rw [eD]; exact he.perm.wC (by omega)
    · rw [eD]; exact hSd.sub_right (Region.sub_prefix h16)
  refine WP.mono (copyLoop_ok s lp) fun s' ⟨hm', lo⟩ => ?_
  rw [hm, eD] at hm'
  have fz : Frame [⟨State.addr w + BitVec.ofNat 64 d, 16⟩] m₀ (store4 m₀ (State.addr w + BitVec.ofNat 64 d) 0 0 0 0) :=
    Cmac.frame_store4 _ _ _ _ _
  have hx : bytesAt (store4 m₀ (State.addr w + BitVec.ofNat 64 d) 0 0 0 0) (State.addr S) tl =
      bytesAt m₀ (State.addr S) tl :=
    bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hSd) (by omega)
  rw [hx] at hm'
  have hlen := length_bytesAt m₀ (State.addr S) tl
  refine ⟨?_, ?_, lo⟩
  · rw [hm', bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega) (by omega), hlen, VG.Proof.AesGcm.Arm.store4_zero_tail _ _ h16]
  · rw [hm']
    exact fz.trans ((writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)

/-- `zero16 d`: the 16 bytes at `W + d` zeroed. -/
theorem zero16_ok {s : State} (he : Env c st w sp k7 k8 s) {d : Nat} (hd : d + 16 ≤ 2560) (ed₁ : d + 12 < 4096) :
    ∃ s', runBlock isa (zero16 d) s = some s' ∧
      s'.mem = store4 s.mem (State.addr w + BitVec.ofNat 64 d) 0 0 0 0 ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h11 := he.r11
  have w₀ := he.perm.wW (show d + 4 ≤ 2560 by omega)
  have w₁ := he.perm.wW (show d + 4 + 4 ≤ 2560 by omega)
  have w₂ := he.perm.wW (show d + 8 + 4 ≤ 2560 by omega)
  have w₃ := he.perm.wW (show d + 12 + 4 ≤ 2560 by omega)
  have e₀ := L.wA (d := d) (by omega)
  have e₁ := L.wA (d := d + 4) (by omega)
  have e₂ := L.wA (d := d + 8) (by omega)
  have e₃ := L.wA (d := d + 12) (by omega)
  have o₀ : d < 4096 := by omega
  have o₁ : d + 4 < 4096 := by omega
  have o₂ : d + 8 < 4096 := by omega
  refine ⟨_, by simp only [zero16]; arun [h11, e₀, e₁, e₂, e₃, w₀, w₁, w₂, w₃, o₀, o₁, o₂, ed₁], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc]; rfl
  · intro r a; simp [gpr_setReg, a]
  · rfl
  · rfl
  · rfl

omit L in
/-- The four words at `p`, as bytes. -/
theorem bytes_words (m : Mem) (p : Addr) : bytesAt m p 16 = le4 (m.readW p 32) ++ le4 (m.readW (p + BitVec.ofNat 64 4) 32) ++
    le4 (m.readW (p + BitVec.ofNat 64 8) 32) ++ le4 (m.readW (p + BitVec.ofNat 64 12) 32) := by
  rw [Cmac.bytesAt_split4, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW]

omit L in
theorem words_eq_iff (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : BitVec 32) :
    le4 a₀ ++ le4 a₁ ++ le4 a₂ ++ le4 a₃ = le4 b₀ ++ le4 b₁ ++ le4 b₂ ++ le4 b₃ ↔
      a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ := by
  constructor
  · intro h
    have l := Cmac.length_le4
    obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [l])
    obtain ⟨h₁, h₃⟩ := List.append_inj h₁ (by simp [l])
    obtain ⟨h₁, h₄⟩ := List.append_inj h₁ (by simp [l])
    exact ⟨VG.Proof.AesGcm.Arm.le4_inj h₁, VG.Proof.AesGcm.Arm.le4_inj h₄, VG.Proof.AesGcm.Arm.le4_inj h₃, VG.Proof.AesGcm.Arm.le4_inj h₂⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl

omit L in
theorem cmp_value (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : BitVec 32) :
    BitVec.ofNat 32 1 - ((((a₀ ^^^ b₀ ||| a₁ ^^^ b₁) ||| a₂ ^^^ b₂) ||| a₃ ^^^ b₃) |||
      (BitVec.ofNat 32 0 - (((a₀ ^^^ b₀ ||| a₁ ^^^ b₁) ||| a₂ ^^^ b₂) ||| a₃ ^^^ b₃))) >>> 31 =
    if a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ then 1 else 0 := by
  rw [show BitVec.ofNat 32 0 = 0 from rfl, VG.Proof.AesGcm.Arm.msb_or_neg]
  by_cases h : a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    simp
  · have : ¬(((a₀ ^^^ b₀ ||| a₁ ^^^ b₁) ||| a₂ ^^^ b₂) ||| a₃ ^^^ b₃) = 0 := by
      intro e
      simp only [show (0 : BitVec 32) = 0#32 from rfl, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff] at e
      exact h ⟨e.1.1.1, e.1.1.2, e.1.2, e.2⟩
    simp only [this, h, ite_false]; rfl

omit L in
theorem runBlock_app (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

omit L in
theorem runBlock_app_of {a b : List Instr} {s s₁ s₂ : State} (h₁ : runBlock isa a s = some s₁)
    (h₂ : runBlock isa b s₁ = some s₂) : runBlock isa (a ++ b) s = some s₂ := by
  rw [VG.Proof.AesGcm.Arm.runBlock_app, h₁]; exact h₂

/-- `cmpTail`: `r0` is 1 iff the 16 bytes at `W + 240` and `W + 256` are equal. -/
theorem cmpTail_ok {s : State} (he : Env c st w sp k7 k8 s) :
    ∃ s', runBlock isa cmpTail s = some s' ∧
      s'.gpr .r0 = (if bytesAt s.mem (State.addr w + BitVec.ofNat 64 240) 16 =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 256) 16 then 1 else 0) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have h11 := he.r11
  have r₀ := he.perm.wR (show 240 + 4 ≤ 2560 by decide)
  have r₁ := he.perm.wR (show 244 + 4 ≤ 2560 by decide)
  have r₂ := he.perm.wR (show 248 + 4 ≤ 2560 by decide)
  have r₃ := he.perm.wR (show 252 + 4 ≤ 2560 by decide)
  have q₀ := he.perm.wR (show 256 + 4 ≤ 2560 by decide)
  have q₁ := he.perm.wR (show 260 + 4 ≤ 2560 by decide)
  have q₂ := he.perm.wR (show 264 + 4 ≤ 2560 by decide)
  have q₃ := he.perm.wR (show 268 + 4 ≤ 2560 by decide)
  let m := s.mem
  let a := fun k : Nat => m.readW (State.addr w + BitVec.ofNat 64 (240 + 4 * k)) 32
  let b := fun k : Nat => m.readW (State.addr w + BitVec.ofNat 64 (256 + 4 * k)) 32
  obtain ⟨s₁, run₁, g₁, h0₁, k₁⟩ : ∃ s₁, runBlock isa (xorW .r0 0 ++ xorW .r1 1 ++ [.dp .orr .r0 .r0 (.reg .r1)]) s =
      some s₁ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s₁.gpr r = s.gpr r) ∧
      s₁.gpr .r0 = (a 0 ^^^ b 0 ||| a 1 ^^^ b 1) ∧ Keeps s s₁ := by
    refine ⟨_, by simp only [xorW, vO, rO]; arun [h11, L.wA, r₀, r₁, q₀, q₁], ?_, ?_, ?_⟩
    · intro r x y z; simp [gpr_setReg, x, y, z]
    · simp [gpr_setReg, a, b, m]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have h11₁ : s₁.gpr .r11 = w := by rw [g₁ _ (by decide) (by decide) (by decide), h11]
  have hm₁ := k₁.mem
  obtain ⟨s₂, run₂, g₂, h0₂, k₂⟩ : ∃ s₂, runBlock isa (xorW .r1 2 ++ [.dp .orr .r0 .r0 (.reg .r1)] ++ xorW .r1 3 ++
      [.dp .orr .r0 .r0 (.reg .r1)]) s₁ = some s₂ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s₂.gpr r = s₁.gpr r) ∧
      s₂.gpr .r0 = ((a 0 ^^^ b 0 ||| a 1 ^^^ b 1) ||| a 2 ^^^ b 2) ||| a 3 ^^^ b 3 ∧ Keeps s₁ s₂ := by
    rw [← k₁.rd, ← k₁.wr] at r₂ r₃ q₂ q₃
    refine ⟨_, by simp only [xorW, vO, rO]; arun [h11₁, L.wA, r₂, r₃, q₂, q₃, hm₁], ?_, ?_, ?_⟩
    · intro r x y z; simp [gpr_setReg, x, y, z]
    · simp [gpr_setReg, a, b, m, h0₁, hm₁]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨s₃, run₃, g₃, h0₃, k₃⟩ : ∃ s₃, runBlock isa [.mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0),
      .dp .orr .r0 .r0 (.reg .r1), .mov .r0 (.shifted .r0 .lsr 31), .mov .r1 (imm 1), .dp .sub .r0 .r1 (.reg .r0)] s₂ =
      some s₃ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → s₃.gpr r = s₂.gpr r) ∧
      s₃.gpr .r0 = BitVec.ofNat 32 1 - ((s₂.gpr .r0 ||| (BitVec.ofNat 32 0 - s₂.gpr .r0)) >>> 31) ∧ Keeps s₂ s₃ := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · intro r x y; simp [gpr_setReg, x, y]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, Op2.eval]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨s₃, ?_, ?_, ?_, k₁.trans (k₂.trans k₃)⟩
  · rw [show cmpTail = (xorW .r0 0 ++ xorW .r1 1 ++ [.dp .orr .r0 .r0 (.reg .r1)]) ++
      ((xorW .r1 2 ++ [.dp .orr .r0 .r0 (.reg .r1)] ++ xorW .r1 3 ++ [.dp .orr .r0 .r0 (.reg .r1)]) ++
      [.mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0), .dp .orr .r0 .r0 (.reg .r1), .mov .r0 (.shifted .r0 .lsr 31),
        .mov .r1 (imm 1), .dp .sub .r0 .r1 (.reg .r0)]) from rfl]
    exact VG.Proof.AesGcm.Arm.runBlock_app_of run₁ (VG.Proof.AesGcm.Arm.runBlock_app_of run₂ run₃)
  · rw [h0₃, h0₂, VG.Proof.AesGcm.Arm.cmp_value, VG.Proof.AesGcm.Arm.bytes_words, VG.Proof.AesGcm.Arm.bytes_words]
    simp only [add_ofNat_assoc]
    congr 1
    simp only [a, b, m]
    exact propext (VG.Proof.AesGcm.Arm.words_eq_iff _ _ _ _ _ _ _ _).symm
  · intro r x y z; rw [g₃ r x y, g₂ r x y z, g₁ r x y z]

/-- `recv`: the received tag (`r6` bytes at `T`, the stack argument at `[sp + 16]`), padded
with zeros at `W + 256`. -/
theorem recv_ok {s : State} (he : Env c st w sp k7 k8 s) {T : BitVec 32} {tl : Nat}
    (hTi : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 16)) 4)
    (hTv : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 16)) 32 = T)
    (hTr : Covers [⟨State.addr T, tl⟩] (s.rd ++ s.wr)) (hTf : T.toNat + tl ≤ 2 ^ 32)
    (hTd : (⟨State.addr T, tl⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 256, 16⟩)
    (h6 : s.gpr .r6 = BitVec.ofNat 32 tl) (h1 : 1 ≤ tl) (h16 : tl ≤ 16) :
    WP isa recv s fun s' => bytesAt s'.mem (State.addr w + BitVec.ofNat 64 256) 16 =
        bytesAt s.mem (State.addr T) tl ++ zeros (16 - tl) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 256, 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s₀, run₀, h1₀, g₀, k₀⟩ : ∃ s₀, runBlock isa [.ldrSp .r1 16] s = some s₀ ∧ s₀.gpr .r1 = T ∧
      (∀ r, r ≠ .r1 → s₀.gpr r = s.gpr r) ∧ Keeps s s₀ := by
    refine ⟨_, by arun [hTi, hTv], ?_, ?_, ?_⟩
    · simp [gpr_setReg, hTv]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₀ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₀ _ (by decide)) k₀.sp k₀.rd k₀.wr
  obtain ⟨s₁, run₁, hm₁, g₁, rd₁, wr₁, sp₁⟩ := VG.Proof.AesGcm.Arm.zero16_ok L he₀ (d := rO) (by decide) (by decide)
  have h11 : s₁.gpr .r11 = w := by rw [g₁ _ (by decide), he₀.r11]
  obtain ⟨s₂, run₂, h2₂, h3₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [addI .r2 .r11 rO, .mov .r3 (.reg .r6)] s₁ = some s₂ ∧
      s₂.gpr .r2 = w + BitVec.ofNat 32 256 ∧ s₂.gpr .r3 = BitVec.ofNat 32 tl ∧
      (∀ r, r ≠ .r2 → r ≠ .r3 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    refine ⟨_, by simp only [rO]; arun [], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h11]
    · simp [gpr_setReg, g₁ .r6 (by decide), g₀ .r6 (by decide), h6]
    · intro r x y; simp [gpr_setReg, x, y]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have run : runBlock isa (.ldrSp .r1 16 :: zero16 rO ++ [addI .r2 .r11 rO, .mov .r3 (.reg .r6)]) s = some s₂ :=
    VG.Proof.AesGcm.Arm.runBlock_app_of (a := [.ldrSp .r1 16]) run₀ (VG.Proof.AesGcm.Arm.runBlock_app_of run₁ run₂)
  refine WP.seq (WP.of_runBlock ⟨s₂, run, ?_⟩)
  have he₂ := he₀.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [g₂ _ (by decide) (by decide), g₁ _ (by decide)]) (k₂.sp.trans sp₁) (k₂.rd.trans rd₁)
      (k₂.wr.trans wr₁)
  have h1₂ : s₂.gpr .r1 = T := by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide), h1₀]
  have hTr₂ : Covers [⟨State.addr T, tl⟩] (s₂.rd ++ s₂.wr) := by
    rw [k₂.rd, k₂.wr, rd₁, wr₁, k₀.rd, k₀.wr]; exact hTr
  refine WP.mono (VG.Proof.AesGcm.Arm.padCopy_ok L he₂ (d := 256) (by decide) h1 h16 hTr₂ hTf hTd (m₀ := s.mem)
    (by rw [k₂.mem, hm₁, k₀.mem]; rfl) h1₂ h2₂ h3₂) fun s₃ ⟨hb, hf, lo⟩ => ?_
  refine ⟨hb, hf, fun r a b d e f => ?_, lo.rd.trans (k₂.rd.trans (rd₁.trans k₀.rd)),
    lo.wr.trans (k₂.wr.trans (wr₁.trans k₀.wr)), lo.sp.trans (k₂.sp.trans (sp₁.trans k₀.sp))⟩
  rw [lo.other r a b d e f, g₂ r d e, g₁ r a, g₀ r b]

/-- `cmp o`: the first `r6` bytes of the tag at `W + o`, padded with zeros at
`W + 240`, compared with the received tag at `W + 256`. -/
theorem cmp_ok {s : State} (he : Env c st w sp k7 k8 s) {o : Nat} (ho : o = 0 ∨ o = 112) {tl : Nat}
    (h6 : s.gpr .r6 = BitVec.ofNat 32 tl) (h1 : 1 ≤ tl) (h16 : tl ≤ 16) :
    WP isa (cmp o) s fun s' => s'.gpr .r0 = (if bytesAt s.mem (State.addr w + BitVec.ofNat 64 o) tl ++ zeros (16 - tl) =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 256) 16 then 1 else 0) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 240, 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s₁, run₁, hm₁, g₁, rd₁, wr₁, sp₁⟩ := VG.Proof.AesGcm.Arm.zero16_ok L he (d := vO) (by decide) (by decide)
  have h11 : s₁.gpr .r11 = w := by rw [g₁ _ (by decide), he.r11]
  have eo : encodable (BitVec.ofNat 32 o) = true := by rcases ho with rfl | rfl <;> decide
  obtain ⟨s₂, run₂, h1₂, h2₂, h3₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [addI .r1 .r11 o, addI .r2 .r11 vO,
      .mov .r3 (.reg .r6)] s₁ = some s₂ ∧ s₂.gpr .r1 = w + BitVec.ofNat 32 o ∧ s₂.gpr .r2 = w + BitVec.ofNat 32 240 ∧
      s₂.gpr .r3 = BitVec.ofNat 32 tl ∧ (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    refine ⟨_, by simp only [vO]; arun [eo], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h11]
    · simp [gpr_setReg, h11]
    · simp [gpr_setReg, g₁ .r6 (by decide), h6]
    · intro r x y z; simp [gpr_setReg, x, y, z]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, VG.Proof.AesGcm.Arm.runBlock_app_of run₁ run₂, ?_⟩)
  have he₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide)]) (k₂.sp.trans sp₁) (k₂.rd.trans rd₁)
      (k₂.wr.trans wr₁)
  have hSr : Covers [⟨State.addr (w + BitVec.ofNat 32 o), tl⟩] (s₂.rd ++ s₂.wr) := by
    rw [L.wA (by omega)]; exact covers_left (he₂.perm.wC (by omega))
  have hSd : (⟨State.addr (w + BitVec.ofNat 32 o), tl⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 240, 16⟩ := by
    rw [L.wA (by omega)]; exact Lay.w_w (by omega) (by omega) (by decide)
  refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.padCopy_ok L he₂ (d := 240) (by decide) h1 h16 hSr (by rw [L.wN (by omega)]; have := L.ww; omega) hSd
    (m₀ := s.mem) (by rw [k₂.mem, hm₁]; rfl) h1₂ h2₂ h3₂) fun s₃ ⟨hb, hf, lo⟩ => ?_)
  rw [L.wA (by omega)] at hb
  have he₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact lo.other _ (by decide) (by decide) (by decide) (by decide)
      (by decide)) lo.sp lo.rd lo.wr
  obtain ⟨s₄, run₄, h0₄, g₄, k₄⟩ := VG.Proof.AesGcm.Arm.cmpTail_ok L he₃
  refine WP.of_runBlock ⟨s₄, run₄, ?_, ?_, fun r a b d e f => ?_, k₄.rd.trans (lo.rd.trans (k₂.rd.trans rd₁)),
    k₄.wr.trans (lo.wr.trans (k₂.wr.trans wr₁)), k₄.sp.trans (lo.sp.trans (k₂.sp.trans sp₁))⟩
  · have h256 : bytesAt s₃.mem (State.addr w + BitVec.ofNat 64 256) 16 =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 256) 16 :=
      bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide)
    rw [h0₄, hb, h256]
  · rw [k₄.mem]; exact hf
  · rw [g₄ r a b d, lo.other r a b d e f, g₂ r b d e, g₁ r a]

end

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.StreamVerify`. -/
section

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_stream_verify`

Untrusted: everything here is checked by Lean. `stream_verify` saves our
caller's registers in `work` (`W`), checks the tag length, and, if it is
allowed, copies the received tag (at `tag`) to `W + 256`, writes the tag to
`W` and compares the first `tag_len` bytes of each; if the length is not
allowed the result is 0 (`streamVerify_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH ctxCiph ghashInput fullTag zeros)
open VG.Proof.Cmac (store4)

theorem bytesAt_take (m : Mem) (p : Addr) {k n : Nat} (h : k ≤ n) : bytesAt m p k = (bytesAt m p n).take k := by
  rw [show n = k + (n - k) by omega, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]

theorem tagLenOk_bounds {tl : Nat} (h : Spec.Gcm.tagLenOk tl = true) : 1 ≤ tl ∧ tl ≤ 16 := by
  simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

/-- What `verify` promises, for the additional data `a` and the text `ct`. -/
def VerPost (s₀ : State) (a ct : List Byte) (s : State) : Prop :=
  ∀ iv, StreamRepr s₀.mem (State.addr (s₀.gpr .r2)) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct → VG.Proof.AesGcm.Arm.arg64 s₀ 0 = BitVec.ofNat 64 a.length →
    let t := fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct
    if Spec.Gcm.tagLenOk (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat ∧ t.take (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat = bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4))
        (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat then s.gpr .r0 = 1
    else s.gpr .r0 = 0

theorem ver_run {s₀ : State} (h : VG.Proof.AesGcm.Arm.streamVerifyPreArm s₀) {a ct : List Byte} (ha : a.length % 16 = (VG.Proof.AesGcm.Arm.arg s₀ 0).toNat % 16)
    (hP : (VG.Proof.AesGcm.Arm.arg s₀ 3 ++ VG.Proof.AesGcm.Arm.arg s₀ 2).toNat = ct.length) :
    WP isa streamVerify s₀ fun s' => abiPreserved s₀ s' ∧ VG.Proof.AesGcm.Arm.VerPost s₀ a ct s' := by
  have h' : VG.Proof.AesGcm.Arm.finPre 7 6 s₀ := streamVerifyPreArm.fin h
  have L := VG.Proof.AesGcm.Arm.finLay h'
  have hR := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have spf := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have fW := h'.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : VG.Proof.AesGcm.Arm.args s₀ 7 ∈ s₀.rd := h'.1.2
  obtain ⟨hrd, -, -, -, -, -, -, tW, -, -, -, -, -, -, -, fT, -⟩ := h
  have hTr : Covers [⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4), (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat⟩] (s₀.rd ++ s₀.wr) :=
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have dT : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4), (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat⟩ : Region).Disjoint
      ⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 d, k⟩ := fun hd => tW.sub_right (Lay.wSub hd)
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 → (164 ≤ d ∨ d + k ≤ 128) →
      (VG.Proof.AesGcm.Arm.savedR (VG.Proof.AesGcm.Arm.arg s₀ 6)).Disjoint ⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ h₂ => Lay.w_w (by omega) (by decide) h₁
  refine WP.seq (WP.block_append (VG.Proof.AesGcm.Arm.fin1_wp (wi := 6) h' (by decide) (by decide) fun s₁ h1 => ?_))
  obtain ⟨i5, v5⟩ := h1.args.at spf hin 5 (by decide) (show 4 * 5 = 20 from rfl)
  obtain ⟨s₂, run₂, h6₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [.ldrSp .r6 20] s₁ = some s₂ ∧
      s₂.gpr .r6 = BitVec.ofNat 32 (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat ∧ (∀ r, r ≠ .r6 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    refine ⟨_, by arun [i5, v5], ?_, ?_, ?_⟩
    · simp [gpr_setReg, v5]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have he₂ := h1.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide)) k₂.sp k₂.rd k₂.wr
  refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.tagLenOk_ok h6₂ (VG.Proof.AesGcm.Arm.arg s₀ 5).isLt) fun s₃ ⟨hz₃, g₃, k₃⟩ => ?_)
  have k₁₃ := k₂.trans k₃
  have he₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide)) k₃.sp k₃.rd k₃.wr
  have hk₃ := h1.args.of_eq k₁₃.mem k₁₃.sp k₁₃.rd k₁₃.wr
  have sv₃ : VG.Proof.AesGcm.Arm.SavedAt s₃.mem (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀ := k₁₃.mem ▸ h1.saved
  have mid : WP isa (.ite .eq (.block [.mov .r0 (imm 0)]) (.seq recv (.seq (finTag 0) (.seq (.block [.ldrSp .r6 20])
      (cmp 0))))) s₃ fun s' => (∃ k7, Env (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp k7
        (s₀.gpr .r1) s') ∧ VG.Proof.AesGcm.Arm.SavedAt s'.mem (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀ ∧ VG.Proof.AesGcm.Arm.VerPost s₀ a ct s' := by
    refine WP.ite _ (eval_eq' hz₃) (fun ht => ?_) (fun hf => ?_)
    · have hbad : Spec.Gcm.tagLenOk (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat = false := by simpa using ht
      refine WP.of_runBlock ⟨s₃.setReg .r0 (BitVec.ofNat 32 0), by arun [], ⟨_, he₃.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl) rfl rfl rfl⟩, sv₃, fun iv _ _ => ?_⟩
      simp only [hbad, Bool.false_eq_true, false_and, ite_false]
      simp [gpr_setReg]
    · have hok : Spec.Gcm.tagLenOk (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat = true := by simpa using hf
      obtain ⟨t1, t16⟩ := VG.Proof.AesGcm.Arm.tagLenOk_bounds hok
      have h6₃ : s₃.gpr .r6 = BitVec.ofNat 32 (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat := by rw [g₃ _ (by decide), h6₂]
      obtain ⟨i4, v4⟩ := hk₃.at spf hin 4 (by decide) (show 4 * 4 = 16 from rfl)
      refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.recv_ok L he₃ i4 v4 (by rw [hk₃.rd, hk₃.wr]; exact hTr) fT (dT (by decide)) h6₃ t1 t16)
        fun s₄ hh => ?_)
      obtain ⟨hb₄, hf₄, g₄, rd₄, wr₄, sp₄⟩ := hh
      have he₄ := he₃.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide) (by decide) (by decide)
          (by decide)) sp₄ rd₄ wr₄
      have dA : ∀ {d k : Nat}, d + k ≤ 2560 → (VG.Proof.AesGcm.Arm.args s₀ 7).Disjoint ⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 d, k⟩ :=
        fun hd => (h'.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
      have hk₄ := hk₃.frame spf hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dA (by decide)) sp₄ rd₄ wr₄
      have f₀₄ : Frame [VG.Proof.AesGcm.Arm.savedR (VG.Proof.AesGcm.Arm.arg s₀ 6), ⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 256, 16⟩] s₀.mem s₄.mem :=
        (h1.frame.mono (by simp)).trans ((k₁₃.mem ▸ hf₄ : Frame _ s₁.mem s₄.mem).mono (by simp))
      have dc₀₄ : ∀ r ∈ [VG.Proof.AesGcm.Arm.savedR (VG.Proof.AesGcm.Arm.arg s₀ 6), ⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 256, 16⟩],
          (⟨State.addr (s₀.gpr .r0), 256⟩ : Region).Disjoint r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact L.cw'.sub_right (Lay.wSub (by decide))
        · exact L.cw'.sub_right (Lay.wSub (by decide))
      have ds₀₄ : ∀ r ∈ [VG.Proof.AesGcm.Arm.savedR (VG.Proof.AesGcm.Arm.arg s₀ 6), ⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 256, 16⟩],
          (⟨State.addr (s₀.gpr .r2), 80⟩ : Region).Disjoint r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · simpa using L.st_w (a := 0) (n := 80) (d := 128) (k := 36) (by decide) (.inr ⟨by decide, by decide⟩)
        · simpa using L.st_w (a := 0) (n := 80) (d := 256) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
      refine WP.seq (WP.mono (WP.with_rdwr (VG.Proof.AesGcm.Arm.finTag_ok L (na := 7) (by decide) (o := 0) (.inl rfl) he₄ hk₄ spf hin
        (VG.Proof.AesGcm.Arm.fin_argsTag h' (.inl rfl)) (show s₀.gpr .r1 = BitVec.ofNat 32 (s₀.gpr .r1).toNat by simp) hR
        (VG.Proof.AesGcm.Arm.ctxH_keep f₀₄ dc₀₄) ha hP)) fun s₅ hh => ?_)
      obtain ⟨fo, rd₅, wr₅, sp₅⟩ := hh
      obtain ⟨k7₅, he₅⟩ := fo.env
      obtain ⟨j5, w5⟩ := fo.args.at spf hin 5 (by decide) (show 4 * 5 = 20 from rfl)
      obtain ⟨s₆, run₆, h6₆, g₆, k₆⟩ : ∃ s₆, runBlock isa [.ldrSp .r6 20] s₅ = some s₆ ∧
          s₆.gpr .r6 = BitVec.ofNat 32 (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat ∧ (∀ r, r ≠ .r6 → s₆.gpr r = s₅.gpr r) ∧ Keeps s₅ s₆ := by
        refine ⟨_, by arun [j5, w5], ?_, ?_, ?_⟩
        · simp [gpr_setReg, w5]
        · intro r hr; simp [gpr_setReg, hr]
        · exact ⟨rfl, rfl, rfl, rfl⟩
      refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
      have he₆ := he₅.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₆ _ (by decide)) k₆.sp k₆.rd k₆.wr
      refine WP.mono (VG.Proof.AesGcm.Arm.cmp_ok L he₆ (o := 0) (.inl rfl) h6₆ t1 t16) fun s₇ hh => ?_
      obtain ⟨h0₇, hf₇, g₇, rd₇, wr₇, sp₇⟩ := hh
      refine ⟨⟨k7₅, he₆.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₇ _ (by decide) (by decide) (by decide) (by decide)
          (by decide)) sp₇ rd₇ wr₇⟩, ?_, fun iv hs hl => ?_⟩
      · have sv₅ := (sv₃.frame hf₄ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact dW (by decide) (.inl (by decide)))).frame fo.frame
          (VG.Proof.AesGcm.Arm.saved_tagFrame L (.inl rfl))
        have sv₆ : VG.Proof.AesGcm.Arm.SavedAt s₆.mem (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀ := k₆.mem ▸ sv₅
        refine sv₆.frame hf₇ ?_
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact dW (by decide) (.inl (by decide))
      · have ht' : bytesAt s₆.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 0) 16 =
            fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
              (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct := by
          rw [k₆.mem]; exact VG.Proof.AesGcm.Arm.fin_out h' f₀₄ dc₀₄ ds₀₄ fo hs hl
        have hrc : bytesAt s₆.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 256) 16 =
            bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4)) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat ++ zeros (16 - (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat) := by
          rw [k₆.mem, bytesAt_frame fo.frame (fun r hr => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl | rfl | rfl | rfl
              · have := L.st_w (a := 0) (n := 32) (d := 256) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
                simp only [add_ofNat_zero] at this
                exact this.symm
              · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
              · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
              · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
              · exact (L.stk_w (by decide)).symm) (by decide), hb₄, k₁₃.mem,
            bytesAt_frame h1.frame (fun r hr => by
              simp only [List.mem_singleton] at hr; subst hr
              exact dT (d := 128) (k := 36) (by decide)) (by omega)]
        have hX : (bytesAt s₆.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 0) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat ++
              zeros (16 - (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat) = bytesAt s₆.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 256) 16) ↔
            (fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
              (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct).take (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat =
              bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4)) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat := by
          rw [VG.Proof.AesGcm.Arm.bytesAt_take _ _ t16, ht', hrc, List.append_cancel_right_eq]
        simp only [hok, true_and]
        by_cases e : (fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
              (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct).take (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat =
              bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4)) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat
        · simp only [e, ite_true]
          rw [h0₇]; simp only [hX.mpr e, ite_true]
        · simp only [e, ite_false]
          rw [h0₇]; simp only [show ¬ _ from fun x => e (hX.mp x), ite_false]
  refine WP.seq (WP.mono mid fun s₄ hh => ?_)
  obtain ⟨⟨k7, he⟩, sv, vp⟩ := hh
  refine WP.mono (VG.Proof.AesGcm.Arm.restore_ok he.r11 fW (covers_left he.perm.w) sv he.sp) fun s' hh => ⟨hh.1, fun iv hs hl => ?_⟩
  have := vp iv hs hl
  rw [hh.2.2.1]; exact this

theorem streamVerify_wp {s₀ : State} (h : streamVerifyArm.pre s₀) :
    WP isa streamVerify s₀ fun s' => abiPreserved s₀ s' ∧ streamVerifyArm.post s₀ s' := by
  have h₀ := VG.Proof.AesGcm.Arm.ver_run h (a := List.replicate ((VG.Proof.AesGcm.Arm.arg s₀ 0).toNat % 16) 0)
    (ct := List.replicate (VG.Proof.AesGcm.Arm.arg s₀ 3 ++ VG.Proof.AesGcm.Arm.arg s₀ 2).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte =>
      VG.Proof.AesGcm.Arm.arg64 s₀ 0 = BitVec.ofNat 64 i.1.length ∧ (VG.Proof.AesGcm.Arm.arg64 s₀ 2).toNat = i.2.length)
    fun i hi => WP.mono (VG.Proof.AesGcm.Arm.ver_run h (a := i.1) (ct := i.2) (VG.Proof.AesGcm.Arm.low_mod16 hi.1).symm hi.2) fun _ hh => hh.2)
    fun s' hh => ⟨hh.1, fun iv a c hs hl hp => hh.2 ⟨a, c⟩ ⟨hl, hp⟩ iv hs hl⟩

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.Init`. -/
section

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_init`

Untrusted: everything here is checked by Lean. `init` saves our caller's
registers in `scratch` (`W`), expands the key into the context with
`vg_aes_expand_key_scratch`, and computes the hash subkey `CIPH_K(0¹²⁸)` into its
bytes 240–255 with `vg_aes_ctr32` on a zero block, from a zero counter block
at `W + 96` (`init_wp`). The layout lemmas of `Lay` apply with the state
taken to be `W + 16` (which `init` never touches).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt KeyRepr)
open VG.Proof.Cmac (store4)

/-- The number of rounds for a key of `L` bytes, as `init` computes it. -/
theorem roundsOf {L : Nat} (h : L = 16 ∨ L = 24 ∨ L = 32) :
    (BitVec.ofNat 32 L >>> 2) + BitVec.ofNat 32 6 = BitVec.ofNat 32 (Spec.Aes.rounds (L / 4)) := by
  rcases h with rfl | rfl | rfl <;> decide

theorem rounds_ok {L : Nat} (h : L = 16 ∨ L = 24 ∨ L = 32) :
    Spec.Aes.rounds (L / 4) = 10 ∨ Spec.Aes.rounds (L / 4) = 12 ∨ Spec.Aes.rounds (L / 4) = 14 := by
  rcases h with rfl | rfl | rfl <;> decide

/-- The layout, with the state taken to be `W + 16`. -/
theorem initLay {c w sp : BitVec 32} (cw : c.toNat + 256 ≤ 2 ^ 32) (ww : w.toNat + 2560 ≤ 2 ^ 32)
    (sp8 : 8 ≤ sp.toNat) (cW : (⟨State.addr c, 256⟩ : Region).Disjoint ⟨State.addr w, 2560⟩)
    (kc : (below sp).Disjoint ⟨State.addr c, 256⟩) (kw : (below sp).Disjoint ⟨State.addr w, 2560⟩) :
    Lay c (w + BitVec.ofNat 32 16) w sp := by
  have e : State.addr (w + BitVec.ofNat 32 16) = State.addr w + BitVec.ofNat 64 16 := addr_add (by omega)
  have hs : Region.Sub ⟨State.addr w + BitVec.ofNat 64 16, 80⟩ ⟨State.addr w, 2560⟩ := Lay.wSub (by decide)
  refine ⟨cw, ?_, ww, sp8, ?_, cW, ?_, ?_, kc, ?_, kw⟩
  · rw [show (w + BitVec.ofNat 32 16).toNat = w.toNat + 16 by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16) (by decide), Nat.mod_eq_of_lt (by omega)]]
    omega
  · rw [e]; exact cW.sub_right hs
  · rw [e]; simpa using Lay.w_w (w := w) (a := 16) (n := 80) (d := 0) (k := 16) (.inr (by decide)) (by decide)
      (by decide)
  · rw [e]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · rw [e]; exact kw.sub_right hs

/-- The entry: our caller's registers saved, `W` in `r11`, the context in
`r9`, the number of rounds in `r8`, and the working space of the key
expansion in `r3`. -/
theorem initPre_ok {s₀ : State} (hfit : (s₀.gpr .r3).toNat + 2560 ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr (s₀.gpr .r3), 2560⟩] s₀.wr) {Q : State → Prop}
    (k : ∀ s₁, s₁.gpr .r11 = s₀.gpr .r3 → s₁.gpr .r9 = s₀.gpr .r2 →
      s₁.gpr .r8 = (s₀.gpr .r1 >>> 2) + BitVec.ofNat 32 6 → s₁.gpr .r3 = s₀.gpr .r3 + BitVec.ofNat 32 512 →
      s₁.gpr .r0 = s₀.gpr .r0 → s₁.gpr .r1 = s₀.gpr .r1 → s₁.gpr .r2 = s₀.gpr .r2 →
      s₁.rd = s₀.rd → s₁.wr = s₀.wr → s₁.sp = s₀.sp → VG.Proof.AesGcm.Arm.SavedAt s₁.mem (s₀.gpr .r3) s₀ →
      Frame [VG.Proof.AesGcm.Arm.savedR (s₀.gpr .r3)] s₀.mem s₁.mem → Q s₁) :
    WP isa (.block initPre) s₀ Q := by
  unfold initPre
  refine VG.Proof.AesGcm.Arm.save_ok rfl hfit hw fun s' g rd wr sp sv fr => WP.of_runBlock ⟨_, by arun [], ?_⟩
  refine k _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rd wr sp sv fr
  all_goals simp [gpr_setReg, g]

/-- The hash subkey's block and `T` zeroed, and the arguments of
`vg_aes_ctr32` on them. -/
theorem initArgs_ok {c w sp k8 : BitVec 32} (L : Lay c (w + BitVec.ofNat 32 16) w sp) {s : State}
    (h9 : s.gpr .r9 = c) (h11 : s.gpr .r11 = w) (h8 : s.gpr .r8 = k8) (hc : Covers [⟨State.addr c, 256⟩] s.wr)
    (hw : Covers [⟨State.addr w, 2560⟩] s.wr) :
    ∃ s', runBlock isa initArgs s = some s' ∧
      s'.mem = store4 (store4 s.mem (State.addr c + BitVec.ofNat 64 240) 0 0 0 0)
        (State.addr w + BitVec.ofNat 64 96) 0 0 0 0 ∧
      s'.gpr .r0 = c ∧ s'.gpr .r1 = k8 ∧ s'.gpr .r2 = w + BitVec.ofNat 32 96 ∧
      s'.gpr .r3 = c + BitVec.ofNat 32 240 ∧ s'.gpr .r12 = BitVec.ofNat 32 1 ∧
      s'.gpr .lr = w + BitVec.ofNat 32 512 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have c₀ := in_off hc (show 240 + 4 ≤ 256 by decide) (by decide)
  have c₁ := in_off hc (show 244 + 4 ≤ 256 by decide) (by decide)
  have c₂ := in_off hc (show 248 + 4 ≤ 256 by decide) (by decide)
  have c₃ := in_off hc (show 252 + 4 ≤ 256 by decide) (by decide)
  have w₀ := in_off hw (show 96 + 4 ≤ 2560 by decide) (by decide)
  have w₁ := in_off hw (show 100 + 4 ≤ 2560 by decide) (by decide)
  have w₂ := in_off hw (show 104 + 4 ≤ 2560 by decide) (by decide)
  have w₃ := in_off hw (show 108 + 4 ≤ 2560 by decide) (by decide)
  refine ⟨_, by simp only [initArgs]; arun [h9, h11, L.cA, L.wA, c₀, c₁, c₂, c₃, w₀, w₁, w₂, w₃], ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc]; rfl
  · simp [gpr_setReg, h9]
  · simp [gpr_setReg, h8]
  · simp [gpr_setReg, h11]
  · simp [gpr_setReg, h9]
  · simp [gpr_setReg]
  · simp [gpr_setReg, h11]
  · intro r a b d e f i; simp [gpr_setReg, a, b, d, e, f, i]
  all_goals rfl

theorem zero_block (m : Mem) (p : Addr) : blockAt (store4 m p 0 0 0 0) p = 0 := by
  rw [blockAt, Cmac.bytesAt_store4, Cmac.le4_zero]; decide

/-- After the entry, from `s₀`. -/
structure IS1 (s₀ s₁ : State) : Prop where
  r11 : s₁.gpr .r11 = s₀.gpr .r3
  r9 : s₁.gpr .r9 = s₀.gpr .r2
  r8 : s₁.gpr .r8 = (s₀.gpr .r1 >>> 2) + BitVec.ofNat 32 6
  r3 : s₁.gpr .r3 = s₀.gpr .r3 + BitVec.ofNat 32 512
  r0 : s₁.gpr .r0 = s₀.gpr .r0
  r1 : s₁.gpr .r1 = s₀.gpr .r1
  r2 : s₁.gpr .r2 = s₀.gpr .r2
  rd : s₁.rd = s₀.rd
  wr : s₁.wr = s₀.wr
  sp : s₁.sp = s₀.sp
  saved : VG.Proof.AesGcm.Arm.SavedAt s₁.mem (s₀.gpr .r3) s₀
  frame : Frame [VG.Proof.AesGcm.Arm.savedR (s₀.gpr .r3)] s₀.mem s₁.mem

/-- The number of rounds of `init`'s key. -/
abbrev initR (s₀ : State) : Nat := Spec.Aes.rounds ((s₀.gpr .r1).toNat / 4)

theorem is1_wp {s₀ : State} (h : initArm.pre s₀) : WP isa (.block initPre) s₀ (VG.Proof.AesGcm.Arm.IS1 s₀) := by
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, fs, -, -⟩ := h
  exact VG.Proof.AesGcm.Arm.initPre_ok fs (by rw [hwr]; exact covers_of_mem (by simp))
    fun s₁ a b c d e f g h i j k l => ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩

theorem init_kc {s₀ s₁ : State} (h : initArm.pre s₀) (h1 : VG.Proof.AesGcm.Arm.IS1 s₀ s₁) :
    KeyCall s₁ (s₀.gpr .r0) (s₀.gpr .r2) (s₀.gpr .r3 + BitVec.ofNat 32 512) (s₀.gpr .r1).toNat := by
  obtain ⟨hrd, hwr, dkc, dks, dcs, bk, bc, bs, fk, fc, fs, sp8, hlen⟩ := h
  have L := VG.Proof.AesGcm.Arm.initLay fc fs sp8 dcs bc bs
  have hW : Covers [⟨State.addr (s₀.gpr .r3), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have hC : Covers [⟨State.addr (s₀.gpr .r2), 256⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have eS := L.wA (d := 512) (by decide)
  refine ⟨h1.r0, by rw [h1.r1]; simp, h1.r2, h1.r3, hlen, fk, by omega, by rw [L.wN (by decide)]; omega,
    dkc.sub_right (Region.sub_prefix (by decide)), ?_, ?_, ?_, ?_⟩
  · rw [eS]; exact dks.sub_right (Lay.wSub (by decide))
  · rw [eS]; exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
  · rw [h1.rd, h1.wr, hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_singleton_self _))
  · rw [h1.wr, eS]
    exact covers_cons (covers_prefix hC (by decide)) (covers_cons (covers_off hW (by decide) (by decide)) covers_nil)

/-- After the key expansion. -/
def IS2 (s₀ s₂ : State) : Prop :=
  ∃ s₁, VG.Proof.AesGcm.Arm.IS1 s₀ s₁ ∧ KeyPost s₁ (s₀.gpr .r0) (s₀.gpr .r2) (s₀.gpr .r3 + BitVec.ofNat 32 512) (s₀.gpr .r1).toNat s₂

/-- After `initArgs`. -/
def IS3 (s₀ s₃ : State) : Prop := ∃ s₂, VG.Proof.AesGcm.Arm.IS2 s₀ s₂ ∧ runBlock isa initArgs s₂ = some s₃

theorem IS2.g {s₀ s₂ : State} (h : VG.Proof.AesGcm.Arm.IS2 s₀ s₂) : s₂.gpr .r9 = s₀.gpr .r2 ∧ s₂.gpr .r11 = s₀.gpr .r3 ∧
    s₂.gpr .r8 = (s₀.gpr .r1 >>> 2) + BitVec.ofNat 32 6 ∧ s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr ∧ s₂.sp = s₀.sp := by
  obtain ⟨s₁, h1, kp⟩ := h
  exact ⟨by rw [kp.saved .r9 (by decide) (by decide), h1.r9], by rw [kp.saved .r11 (by decide) (by decide), h1.r11],
    by rw [kp.saved .r8 (by decide) (by decide), h1.r8], kp.rd.trans h1.rd, kp.wr.trans h1.wr, kp.sp.trans h1.sp⟩

/-- What `initArgs` leaves. -/
theorem IS3.facts {s₀ s₃ : State} (h : initArm.pre s₀) (h3 : VG.Proof.AesGcm.Arm.IS3 s₀ s₃) :
    ∃ s₂, VG.Proof.AesGcm.Arm.IS2 s₀ s₂ ∧
      s₃.mem = store4 (store4 s₂.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 240) 0 0 0 0)
        (State.addr (s₀.gpr .r3) + BitVec.ofNat 64 96) 0 0 0 0 ∧
      s₃.gpr .r0 = s₀.gpr .r2 ∧ s₃.gpr .r1 = BitVec.ofNat 32 (VG.Proof.AesGcm.Arm.initR s₀) ∧
      s₃.gpr .r2 = s₀.gpr .r3 + BitVec.ofNat 32 96 ∧
      s₃.gpr .r3 = s₀.gpr .r2 + BitVec.ofNat 32 240 ∧ s₃.gpr .r12 = BitVec.ofNat 32 1 ∧
      s₃.gpr .lr = s₀.gpr .r3 + BitVec.ofNat 32 512 ∧ s₃.gpr .r11 = s₀.gpr .r3 ∧
      s₃.rd = s₀.rd ∧ s₃.wr = s₀.wr ∧ s₃.sp = s₀.sp := by
  obtain ⟨s₂, h2, run⟩ := h3
  obtain ⟨-, hwr, -, -, dcs, -, bc, bs, -, fc, fs, sp8, hlen⟩ := h
  have L := VG.Proof.AesGcm.Arm.initLay fc fs sp8 dcs bc bs
  obtain ⟨g9, g11, g8, grd, gwr, gsp⟩ := h2.g
  have hr8 : s₀.gpr .r1 >>> 2 + BitVec.ofNat 32 6 = BitVec.ofNat 32 (VG.Proof.AesGcm.Arm.initR s₀) := by
    have := VG.Proof.AesGcm.Arm.roundsOf hlen; rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  obtain ⟨s₃', run', hm, g0, g1, g2, g3, g12, glr, gg, rd, wr, sp⟩ := VG.Proof.AesGcm.Arm.initArgs_ok L (s := s₂) g9 g11 g8
    (by rw [gwr, hwr]; exact covers_of_mem (by simp)) (by rw [gwr, hwr]; exact covers_of_mem (by simp))
  obtain rfl : s₃' = s₃ := Option.some.inj (run'.symm.trans run)
  exact ⟨s₂, h2, hm, g0, g1.trans hr8, g2, g3, g12, glr,
    by rw [gg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g11],
    rd.trans grd, wr.trans gwr, sp.trans gsp⟩

theorem init_cc {s₀ s₃ : State} (h : initArm.pre s₀) (h3 : VG.Proof.AesGcm.Arm.IS3 s₀ s₃) :
    CtrCall s₃ (s₀.gpr .r2) (s₀.gpr .r3 + BitVec.ofNat 32 96) (s₀.gpr .r2 + BitVec.ofNat 32 240)
      (s₀.gpr .r3 + BitVec.ofNat 32 512) (VG.Proof.AesGcm.Arm.initR s₀) 1 := by
  obtain ⟨s₂, -, -, g0, g1, g2, g3, g12, glr, -, -, wr₃, hk3⟩ := h3.facts h
  obtain ⟨-, hwr, -, -, dcs, -, bc, bs, -, fc, fs, sp8, hlen⟩ := h
  have L := VG.Proof.AesGcm.Arm.initLay fc fs sp8 dcs bc bs
  have hW : Covers [⟨State.addr (s₀.gpr .r3), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have hC : Covers [⟨State.addr (s₀.gpr .r2), 256⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have eS := L.wA (d := 512) (by decide)
  have eT := L.wA (d := 96) (by decide)
  have eH := L.cA (d := 240) (by decide)
  refine ⟨g0, g1, g2, g3, g12, glr, VG.Proof.AesGcm.Arm.rounds_ok hlen, by rw [hk3]; exact sp8,
    by omega, by rw [L.wN (by decide)]; omega, by rw [L.cN (by decide)]; omega, by rw [L.wN (by decide)]; omega,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [eS, eT, eH, hk3]
  · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
  · simpa using Lay.ctx_ctx (c := s₀.gpr .r2) (a := 0) (n := 240) (d := 240) (k := 16) (.inl (by decide))
      (by decide) (by decide)
  · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
  · exact (L.ctx_w (a := 240) (n := 16) (d := 96) (k := 16) (by decide) (by decide)).symm
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact L.kc.sub_right (Region.sub_prefix (by decide))
  · exact L.stk_w (by decide)
  · exact L.stk_ctx (by decide)
  · exact L.stk_w (by decide)
  · rw [wr₃]; exact covers_left (covers_prefix hC (by decide))
  · rw [wr₃]
    exact covers_cons (covers_off hW (by decide) (by decide))
      (covers_cons (covers_off hC (by decide) (by decide)) (covers_cons (covers_off hW (by decide) (by decide))
        covers_nil))

/-- After the call of `vg_aes_ctr32`. -/
def IS4 (s₀ s₄ : State) : Prop :=
  ∃ s₃, VG.Proof.AesGcm.Arm.IS3 s₀ s₃ ∧ CtrPost s₃ (s₀.gpr .r2) (s₀.gpr .r3 + BitVec.ofNat 32 96) (s₀.gpr .r2 + BitVec.ofNat 32 240)
      (s₀.gpr .r3 + BitVec.ofNat 32 512) (VG.Proof.AesGcm.Arm.initR s₀) 1 s₄

theorem init_fin {s₀ s₄ : State} (h : initArm.pre s₀) (h4 : VG.Proof.AesGcm.Arm.IS4 s₀ s₄) :
    WP isa (.block restore) s₄ fun s' => abiPreserved s₀ s' ∧ initArm.post s₀ s' := by
  obtain ⟨s₃, h3, cp⟩ := h4
  obtain ⟨s₂, h2, hm₃, -, -, -, -, -, -, g11, -, wr₃, hk3⟩ := h3.facts h
  obtain ⟨s₁, h1, kp⟩ := h2
  obtain ⟨-, hwr, -, dks, dcs, -, bc, bs, -, fc, fs, sp8, hlen⟩ := h
  have L := VG.Proof.AesGcm.Arm.initLay fc fs sp8 dcs bc bs
  have hR := VG.Proof.AesGcm.Arm.rounds_ok hlen
  have hW : Covers [⟨State.addr (s₀.gpr .r3), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have eS := L.wA (d := 512) (by decide)
  have eT := L.wA (d := 96) (by decide)
  have eH := L.cA (d := 240) (by decide)
  have dSv : ∀ {d k : Nat}, d + k ≤ 2560 → (128 + 36 ≤ d ∨ d + k ≤ 128) →
      (VG.Proof.AesGcm.Arm.savedR (s₀.gpr .r3)).Disjoint ⟨State.addr (s₀.gpr .r3) + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ h₂ => Lay.w_w (by omega) (by decide) h₁
  have dSc : ∀ {d k : Nat}, d + k ≤ 256 →
      (VG.Proof.AesGcm.Arm.savedR (s₀.gpr .r3)).Disjoint ⟨State.addr (s₀.gpr .r2) + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ => (L.ctx_w h₁ (show 128 + 36 ≤ 2560 by decide)).symm
  have cframe := cp.frame
  have cout := cp.out
  simp only [eS, eT, eH, hk3] at cframe cout
  have f₃ : Frame [⟨State.addr (s₀.gpr .r2) + BitVec.ofNat 64 240, 16⟩, ⟨State.addr (s₀.gpr .r3) + BitVec.ofNat 64 96, 16⟩]
      s₂.mem s₃.mem := by
    rw [hm₃]
    exact ((Cmac.frame_store4 _ 0 0 0 0).mono (by simp)).trans ((Cmac.frame_store4 _ 0 0 0 0).mono (by simp))
  have kframe := kp.frame
  rw [eS] at kframe
  have sv₄ : VG.Proof.AesGcm.Arm.SavedAt s₄.mem (s₀.gpr .r3) s₀ := by
    refine ((h1.saved.frame kframe ?_).frame f₃ ?_).frame cframe ?_
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simpa using dSc (d := 0) (k := 240) (by decide)
      · exact dSv (by decide) (.inl (by decide))
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dSc (by decide)
      · exact dSv (by decide) (.inr (by decide))
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact dSv (by decide) (.inr (by decide))
      · exact dSc (by decide)
      · exact dSv (by decide) (.inl (by decide))
      · exact (L.stk_w (show 128 + 36 ≤ 2560 by decide)).symm
  refine WP.mono (VG.Proof.AesGcm.Arm.restore_ok (s₀ := s₀) (by rw [cp.saved _ (by decide) (by decide), g11]) fs
      (by rw [cp.wr, wr₃]; exact covers_left hW) sv₄ (by rw [cp.sp, hk3])) fun s' hh => ⟨hh.1, ?_⟩
  have hm := hh.2.1
  have hRb : 16 * (VG.Proof.AesGcm.Arm.initR s₀ + 1) ≤ 240 := by simp only [VG.Proof.AesGcm.Arm.initR]; rcases hR with h' | h' | h' <;> omega
  have dP : ∀ {d k : Nat}, 240 ≤ d → d + k ≤ 256 →
      (⟨State.addr (s₀.gpr .r2), 16 * (VG.Proof.AesGcm.Arm.initR s₀ + 1)⟩ : Region).Disjoint
        ⟨State.addr (s₀.gpr .r2) + BitVec.ofNat 64 d, k⟩ := fun {d k} h₁ h₂ => by
    simpa using Lay.ctx_ctx (c := s₀.gpr .r2) (a := 0) (n := 16 * (VG.Proof.AesGcm.Arm.initR s₀ + 1))
      (d := d) (k := k) (.inl (by simp only [VG.Proof.AesGcm.Arm.initR] at hRb ⊢; omega)) (by simp only [VG.Proof.AesGcm.Arm.initR] at hRb ⊢; omega) h₂
  have dPw : ∀ {d k : Nat}, d + k ≤ 2560 →
      (⟨State.addr (s₀.gpr .r2), 16 * (VG.Proof.AesGcm.Arm.initR s₀ + 1)⟩ : Region).Disjoint
        ⟨State.addr (s₀.gpr .r3) + BitVec.ofNat 64 d, k⟩ := fun h₁ =>
    (L.cw'.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub h₁)
  have ks₃ : bytesAt s₃.mem (State.addr (s₀.gpr .r2)) (16 * (VG.Proof.AesGcm.Arm.initR s₀ + 1)) =
      Spec.Aes.expandKey (bytesAt s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat) := by
    rw [bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dP (Nat.le_refl _) (by decide)
        · exact dPw (by decide)) (by omega), kp.out,
      bytesAt_frame h1.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact dks.sub_right (Lay.wSub (by decide))) (by omega)]
  simp only [VG.Proof.AesGcm.Arm.initArm, KeyRepr, length_bytesAt, hm]
  refine ⟨?_, ?_⟩
  · rw [bytesAt_frame cframe (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact dPw (by decide)
        · exact dP (Nat.le_refl _) (by decide)
        · exact dPw (by decide)
        · exact (L.kc.sub_right (Region.sub_prefix (by omega))).symm) (by omega), ks₃]
  · rw [blocksAt_one, blocksAt_one, ctr32_single, List.cons.injEq] at cout
    have z₁ : blockAt s₃.mem (State.addr (s₀.gpr .r3) + BitVec.ofNat 64 96) = 0 := by rw [hm₃, VG.Proof.AesGcm.Arm.zero_block]
    have z₂ : blockAt s₃.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 240) = 0 := by
      rw [hm₃, blockAt_frame (Cmac.frame_store4 _ 0 0 0 0) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.ctx_w (by decide) (by decide)), VG.Proof.AesGcm.Arm.zero_block]
    rw [VG.Proof.AesGcm.Arm.ctxH_eq, cout.1, z₁, z₂]
    refine BitVec.zero_xor.trans ?_
    rw [ks₃, Spec.Gcm.aes, length_bytesAt]

theorem is3_run {s₀ s₂ : State} (h : initArm.pre s₀) (h2 : VG.Proof.AesGcm.Arm.IS2 s₀ s₂) : ∃ s₃, runBlock isa initArgs s₂ = some s₃ := by
  obtain ⟨-, hwr, -, -, dcs, -, bc, bs, -, fc, fs, sp8, -⟩ := h
  obtain ⟨g9, g11, -, -, gwr, -⟩ := h2.g
  obtain ⟨s₃, run, -⟩ := VG.Proof.AesGcm.Arm.initArgs_ok (VG.Proof.AesGcm.Arm.initLay fc fs sp8 dcs bc bs) (s := s₂) g9 g11 rfl
    (by rw [gwr, hwr]; exact covers_of_mem (by simp)) (by rw [gwr, hwr]; exact covers_of_mem (by simp))
  exact ⟨s₃, run⟩

theorem init_wp {s₀ : State} (h : initArm.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ initArm.post s₀ s' :=
  WP.seq (WP.mono (VG.Proof.AesGcm.Arm.is1_wp h) fun s₁ h1 => WP.seq (WP.mono (key_call (VG.Proof.AesGcm.Arm.init_kc h h1)) fun s₂ kp =>
    WP.seq (by
      obtain ⟨s₃, run⟩ := VG.Proof.AesGcm.Arm.is3_run h ⟨s₁, h1, kp⟩
      exact WP.of_runBlock ⟨s₃, run, WP.seq (WP.mono (ctr_call (VG.Proof.AesGcm.Arm.init_cc h ⟨s₂, ⟨s₁, h1, kp⟩, run⟩)) fun s₄ cp =>
        VG.Proof.AesGcm.Arm.init_fin h ⟨s₃, ⟨s₂, ⟨s₁, h1, kp⟩, run⟩, cp⟩)⟩)))

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.OneShot`. -/
section

/-!
# AES-GCM on ARMv7: the pieces of `vg_aes_gcm_seal` and `vg_aes_gcm_open`

Untrusted: everything here is checked by Lean. Both keep a streaming state at
`W + 16`: the entry saves our caller's registers (`one1_wp`), `oneAad` writes
`J₀` and absorbs the additional data, padded (`oneAad_ok`), `oneCrypt` runs
counter mode over the data from the first counter block (`oneCrypt_ok`), and
`oneTag o` absorbs the data as ciphertext, padded, then the lengths block,
and writes the tag to `W + o` (`oneTag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph ghashInput fullTag zeros padLen j0 inc32 gctr ghash ghashFrom blocks
  toBytes ofBytes)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock padded)

section
variable {n wi : Nat}

/-- The state, at `W + 16`. -/
abbrev oSt (s₀ : State) (wi : Nat) : BitVec 32 := VG.Proof.AesGcm.Arm.arg s₀ wi + BitVec.ofNat 32 16

theorem oneLay {s₀ : State} (h : VG.Proof.AesGcm.Arm.onePre n wi s₀) : Lay (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp := by
  obtain ⟨-, -, -, dcW, -, -, -, -, -, -, -, bc, -, -, -, bW, fc, -, -, -, fW, sp8, -, -⟩ := h
  exact VG.Proof.AesGcm.Arm.initLay fc fW sp8 dcW bc bW

theorem oSt_addr {s₀ : State} (h : VG.Proof.AesGcm.Arm.onePre n wi s₀) :
    State.addr (VG.Proof.AesGcm.Arm.oSt s₀ wi) = State.addr (VG.Proof.AesGcm.Arm.arg s₀ wi) + BitVec.ofNat 64 16 :=
  addr_add (by have := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega)

/-- A buffer apart from `W` is apart from the state. -/
theorem oSt_disj {s₀ : State} (h : VG.Proof.AesGcm.Arm.onePre n wi s₀) {R : Region} (hR : R.Disjoint ⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ wi), 2560⟩) :
    R.Disjoint ⟨State.addr (VG.Proof.AesGcm.Arm.oSt s₀ wi), 80⟩ := by
  rw [VG.Proof.AesGcm.Arm.oSt_addr h]; exact hR.sub_right (Lay.wSub (by decide))

/-- After the entry, from `s₀`. -/
structure SO1 (n wi : Nat) (s₀ s₁ : State) : Prop where
  env : Env (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp (s₀.gpr .r7) (s₀.gpr .r1) s₁
  r4 : s₁.gpr .r4 = s₀.gpr .r2
  r5 : s₁.gpr .r5 = s₀.gpr .r3
  args : VG.Proof.AesGcm.Arm.ArgsKeep n s₀ s₁
  saved : VG.Proof.AesGcm.Arm.SavedAt s₁.mem (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀
  frame : Frame [VG.Proof.AesGcm.Arm.savedR (VG.Proof.AesGcm.Arm.arg s₀ wi)] s₀.mem s₁.mem

theorem one1_wp {s₀ : State} (h : VG.Proof.AesGcm.Arm.onePre n wi s₀) (hn : wi < n) (hwi : 4 * wi < 4096) {Q : State → Prop}
    (k : ∀ s₁, VG.Proof.AesGcm.Arm.SO1 n wi s₀ s₁ → Q s₁) : WP isa (.block (oneEntry (4 * wi))) s₀ Q := by
  have hst := VG.Proof.AesGcm.Arm.oSt_addr h
  have ww := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨⟨hc, -, -, hin⟩, ⟨-, hw, -⟩, -, -, -, -, -, -, -, -, dWA, -, -, -, -, -, -, -, -, -, fW, -, spf, -⟩ := h
  have hA : ∀ r ∈ [VG.Proof.AesGcm.Arm.savedR (VG.Proof.AesGcm.Arm.arg s₀ wi)], (VG.Proof.AesGcm.Arm.args s₀ n).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (dWA.sub_left (Lay.wSub (by decide))).symm
  have hC : Covers [⟨State.addr (s₀.gpr .r0), 256⟩] (s₀.rd ++ s₀.wr) :=
    covers_of_mem (List.mem_append_left _ hc)
  have hW : Covers [⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ wi), 2560⟩] s₀.wr := covers_of_mem hw
  have hS : Covers [⟨State.addr (VG.Proof.AesGcm.Arm.oSt s₀ wi), 80⟩] s₀.wr := by rw [hst]; exact covers_off hW (by decide) (by decide)
  have ha : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 (4 * wi))) 4 := VG.Proof.AesGcm.Arm.arg_in hn spf hin
  refine VG.Proof.AesGcm.Arm.entry_ok (off := 4 * wi) hwi ha fW hW fun s₁ g12 g rd wr sp sv fr => ?_
  have hk : VG.Proof.AesGcm.Arm.ArgsKeep n s₀ s₁ := (ArgsKeep.refl n s₀).frame spf fr hA sp rd wr
  refine WP.of_runBlock ⟨_, by arun [], ?_⟩
  refine k _ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩, ?_, ?_, ?_, sv, fr⟩
  any_goals (simp [gpr_setReg, g, g12]; done)
  · simp [gpr_setReg, g, g12]; rfl
  · simp [gpr_setReg, g, g12]; rfl
  · exact sp
  · change Covers _ (s₁.rd ++ s₁.wr); rw [rd, wr]; exact hC
  · change Covers _ s₁.wr; rw [wr]; exact hS
  · change Covers _ s₁.wr; rw [wr]; exact hW
  · exact hk.of_eq rfl rfl rfl rfl

end

theorem abs16_sub {st w sp : BitVec 32} : ∀ r ∈ absFrame st w sp 16, ∃ r' ∈ VG.Proof.AesGcm.Arm.j0Frame st w sp, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem t16_sub {st w sp : BitVec 32} : ∀ r ∈ tFrame st w sp 16, ∃ r' ∈ VG.Proof.AesGcm.Arm.j0Frame st w sp, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem abs16_j0Frame {st w sp : BitVec 32} {m m' : Mem} (h : Frame (absFrame st w sp 16) m m') :
    Frame (VG.Proof.AesGcm.Arm.j0Frame st w sp) m m' := h.sub VG.Proof.AesGcm.Arm.abs16_sub

theorem t16_j0Frame {st w sp : BitVec 32} {m m' : Mem} (h : Frame (tFrame st w sp 16) m m') :
    Frame (VG.Proof.AesGcm.Arm.j0Frame st w sp) m m' := h.sub VG.Proof.AesGcm.Arm.t16_sub

section
variable {n wi : Nat}

/-- The stack arguments are apart from what `j0` (and the other pieces) write. -/
theorem one_argsJ0 {s₀ : State} (h : VG.Proof.AesGcm.Arm.onePre n wi s₀) :
    ∀ r ∈ VG.Proof.AesGcm.Arm.j0Frame (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp, (VG.Proof.AesGcm.Arm.args s₀ n).Disjoint r := by
  have hst := VG.Proof.AesGcm.Arm.oSt_addr h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, dWA, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [hst]; exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (VG.Proof.AesGcm.Arm.below_args s₀ spf).symm

/-- A buffer apart from `W` and the stack below `sp` is apart from what `j0` writes. -/
theorem one_dataJ0 {s₀ : State} (h : VG.Proof.AesGcm.Arm.onePre n wi s₀) {R : Region} (hW : R.Disjoint ⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ wi), 2560⟩)
    (hb : (below s₀.sp).Disjoint R) : ∀ r ∈ VG.Proof.AesGcm.Arm.j0Frame (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp, R.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact VG.Proof.AesGcm.Arm.oSt_disj h hW
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hb.symm

/-- After `oneAad`, from `m₁`. -/
structure OA (n wi : Nat) (s₀ : State) (m₁ : Mem) (s : State) : Prop where
  env : ∃ k7, Env (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp k7 (s₀.gpr .r1) s
  args : VG.Proof.AesGcm.Arm.ArgsKeep n s₀ s
  j : blockAt s.mem (State.addr (VG.Proof.AesGcm.Arm.oSt s₀ wi)) =
    j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat)
  cb : blockAt s.mem (State.addr (VG.Proof.AesGcm.Arm.oSt s₀ wi) + BitVec.ofNat 64 48) =
    inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat))
  abs : Absorbed s.mem (State.addr (VG.Proof.AesGcm.Arm.oSt s₀ wi) + BitVec.ofNat 64 16) (State.addr (VG.Proof.AesGcm.Arm.oSt s₀ wi) + BitVec.ofNat 64 32)
    (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
    (bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 0)) (VG.Proof.AesGcm.Arm.arg s₀ 1).toNat ++
      zeros (padLen (bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 0)) (VG.Proof.AesGcm.Arm.arg s₀ 1).toNat).length))
  hH : blockAt s.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0))
  frame : Frame (VG.Proof.AesGcm.Arm.j0Frame (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp) m₁ s.mem

theorem oneAad_ok {s₀ s₁ : State} (h : VG.Proof.AesGcm.Arm.onePre n wi s₀) (hn : 5 ≤ n) (h1 : VG.Proof.AesGcm.Arm.SO1 n wi s₀ s₁) :
    WP isa oneAad s₁ (VG.Proof.AesGcm.Arm.OA n wi s₀ s₁.mem) := by
  have L := VG.Proof.AesGcm.Arm.oneLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : VG.Proof.AesGcm.Arm.args s₀ n ∈ s₀.rd := h.1.2.2.2
  have hp := h
  obtain ⟨hrd, -, -, -, -, dnW, -, daW, -, -, -, -, bn, ba, -, -, -, fn, fa, -, -, -, -, -⟩ := hp
  have hH₁ := VG.Proof.AesGcm.Arm.ctxH_keep h1.frame (VG.Proof.AesGcm.Arm.ctx_saved L)
  have ji : VG.Proof.AesGcm.Arm.J0In (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp (s₀.gpr .r7) (s₀.gpr .r1)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (s₀.gpr .r2) (s₀.gpr .r3).toNat s₁ :=
    ⟨h1.env, hH₁, h1.r4, by rw [h1.r5]; simp, ⟨by
      rw [h1.args.rd, h1.args.wr]; exact covers_of_mem (List.mem_append_left _ hrd.2.1),
      (s₀.gpr .r3).isLt, fn, VG.Proof.AesGcm.Arm.oSt_disj h dnW, dnW, bn⟩⟩
  refine WP.seq (WP.mono (WP.with_rdwr (VG.Proof.AesGcm.Arm.j0_ok L ji)) fun s₂ hh => ?_)
  obtain ⟨jo, rd₂, wr₂, sp₂⟩ := hh
  obtain ⟨k7, he₂⟩ := jo.env
  have hiv : bytesAt s₁.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat =
      bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat :=
    bytesAt_frame h1.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dnW.sub_right (Lay.wSub (by decide))) (by omega)
  rw [hiv] at jo
  have hk₂ := h1.args.frame spf jo.frame (VG.Proof.AesGcm.Arm.one_argsJ0 h) sp₂ rd₂ wr₂
  obtain ⟨a0, v0⟩ := hk₂.at spf hin 0 (by omega) (show 4 * 0 = 0 from rfl)
  obtain ⟨a1, v1⟩ := hk₂.at spf hin 1 (by omega) (show 4 * 1 = 4 from rfl)
  obtain ⟨s₃, run₃, h4₃, h5₃, h6₃, g₃, k₃⟩ : ∃ s₃, runBlock isa [.ldrSp .r4 0, .ldrSp .r5 4, .mov .r6 (imm 0)] s₂ =
      some s₃ ∧ s₃.gpr .r4 = VG.Proof.AesGcm.Arm.arg s₀ 0 ∧ s₃.gpr .r5 = VG.Proof.AesGcm.Arm.arg s₀ 1 ∧ s₃.gpr .r6 = BitVec.ofNat 32 0 ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
    refine ⟨_, by arun [a0, v0, a1, v1], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, v0]
    · simp [gpr_setReg, v1]
    · simp [gpr_setReg]
    · intro r x y z; simp [gpr_setReg, x, y, z]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide) (by decide)) k₃.sp k₃.rd k₃.wr
  have hk₃ := hk₂.of_eq k₃.mem k₃.sp k₃.rd k₃.wr
  have hda : DataOk (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp s₃ (VG.Proof.AesGcm.Arm.arg s₀ 0) (VG.Proof.AesGcm.Arm.arg s₀ 1).toNat :=
    ⟨by rw [hk₃.rd, hk₃.wr]; exact covers_of_mem (List.mem_append_left _ hrd.2.2.1), (VG.Proof.AesGcm.Arm.arg s₀ 1).isLt, fa,
      VG.Proof.AesGcm.Arm.oSt_disj h daW, daW, ba⟩
  have haad : bytesAt s₃.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 0)) (VG.Proof.AesGcm.Arm.arg s₀ 1).toNat =
      bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 0)) (VG.Proof.AesGcm.Arm.arg s₀ 1).toNat := by
    rw [k₃.mem, bytesAt_frame jo.frame (VG.Proof.AesGcm.Arm.one_dataJ0 h daW ba) (by omega),
      bytesAt_frame h1.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact daW.sub_right (Lay.wSub (by decide))) (by omega)]
  have ai : AbsIn (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp k7 (s₀.gpr .r1) 16 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) []
      (VG.Proof.AesGcm.Arm.arg s₀ 0) (VG.Proof.AesGcm.Arm.arg s₀ 1).toNat s₃ :=
    ⟨he₃, h4₃, by rw [h5₃]; simp, by rw [h6₃]; rfl, hda, by rw [k₃.mem]; exact jo.hH⟩
  refine WP.seq (WP.mono (WP.with_rdwr (absorb_ok L (.inr rfl) ai)) fun s₄ hh => ?_)
  obtain ⟨ab, rd₄, wr₄, sp₄⟩ := hh
  rw [haad, List.nil_append] at ab
  have hk₄ := hk₃.frame spf ab.frame (VG.Proof.AesGcm.Arm.disj_sub (VG.Proof.AesGcm.Arm.one_argsJ0 h) VG.Proof.AesGcm.Arm.abs16_sub) sp₄ rd₄ wr₄
  obtain ⟨b1, w1⟩ := hk₄.at spf hin 1 (by omega) (show 4 * 1 = 4 from rfl)
  obtain ⟨s₅, run₅, h6₅, g₅, k₅⟩ : ∃ s₅, runBlock isa [.ldrSp .r6 4, .dp .and .r6 .r6 (imm 15)] s₄ = some s₅ ∧
      s₅.gpr .r6 = BitVec.ofNat 32 ((VG.Proof.AesGcm.Arm.arg s₀ 1).toNat % 16) ∧ (∀ r, r ≠ .r6 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    refine ⟨_, by arun [b1, w1], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, w1, and15]
    · intro r x; simp [gpr_setReg, x]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ := ab.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₅ _ (by decide)) k₅.sp k₅.rd k₅.wr
  have hk₅ := hk₄.of_eq k₅.mem k₅.sp k₅.rd k₅.wr
  have hH₄ : blockAt s₄.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0)) := by
    rw [blockAt_frame ab.frame (ctx_absFrame L (.inr rfl)), k₃.mem]; exact jo.hH
  refine WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl)
    (x := bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 0)) (VG.Proof.AesGcm.Arm.arg s₀ 1).toNat) (H := ctxH s₀.mem (State.addr (s₀.gpr .r0)))
    ⟨he₅, by rw [k₅.mem]; exact hH₄⟩ (by rw [h6₅, length_bytesAt]))) fun s₆ hh => ?_
  obtain ⟨fl, rd₆, wr₆, sp₆⟩ := hh
  rw [k₅.mem] at fl
  have keepA : ∀ {d : Nat}, (d = 0 ∨ d = 48) → ∀ r ∈ absFrame (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp 16,
      (⟨State.addr (VG.Proof.AesGcm.Arm.oSt s₀ wi) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.st_st (by omega) (by omega) (by decide)
    · exact Lay.st_st (by omega) (by omega) (by decide)
    · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
    · exact (L.stk_st (by omega)).symm
  have keepT : ∀ {d : Nat}, (d = 0 ∨ d = 48) → ∀ r ∈ tFrame (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp 16,
      (⟨State.addr (VG.Proof.AesGcm.Arm.oSt s₀ wi) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.st_st (by omega) (by omega) (by decide)
    · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
    · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
    · exact (L.stk_st (by omega)).symm
  have blk : ∀ {d : Nat}, (d = 0 ∨ d = 48) → blockAt s₆.mem (State.addr (VG.Proof.AesGcm.Arm.oSt s₀ wi) + BitVec.ofNat 64 d) =
      blockAt s₂.mem (State.addr (VG.Proof.AesGcm.Arm.oSt s₀ wi) + BitVec.ofNat 64 d) := fun hd => by
    rw [blockAt_frame fl.frame (keepT hd), blockAt_frame ab.frame (keepA hd), k₃.mem]
  refine ⟨⟨k7, fl.env⟩, hk₄.frame spf fl.frame (VG.Proof.AesGcm.Arm.disj_sub (VG.Proof.AesGcm.Arm.one_argsJ0 h) VG.Proof.AesGcm.Arm.t16_sub) (sp₆.trans k₅.sp) (rd₆.trans k₅.rd)
    (wr₆.trans k₅.wr), ?_, ?_, ?_, fl.hH, ?_⟩
  · have := blk (d := 0) (.inl rfl); rw [add_ofNat_zero] at this; rw [this]; exact jo.j0
  · rw [blk (.inr rfl)]; exact jo.cb
  · exact fl.abs (ab.abs (by rw [k₃.mem]; exact Proof.Gcm.absorbed_nil _ jo.y))
  · rw [k₃.mem] at ab
    exact (jo.frame.trans (VG.Proof.AesGcm.Arm.abs16_j0Frame ab.frame)).trans (VG.Proof.AesGcm.Arm.t16_j0Frame fl.frame)

/-- The data, for `crypt` and `absorb`. -/
theorem one_dataOk {s₀ s : State} (h : VG.Proof.AesGcm.Arm.onePre n wi s₀) (hk : VG.Proof.AesGcm.Arm.ArgsKeep n s₀ s) :
    DataOk (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp s (VG.Proof.AesGcm.Arm.arg s₀ 2) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat := by
  have hp := h
  obtain ⟨-, hwr, -, -, -, -, -, -, dDW, -, -, -, -, -, bD, -, -, -, -, fD, -, -, -, -⟩ := hp
  exact ⟨by rw [hk.rd, hk.wr]; exact covers_left (covers_of_mem hwr.1), (VG.Proof.AesGcm.Arm.arg s₀ 3).isLt, fD,
    VG.Proof.AesGcm.Arm.oSt_disj h dDW, dDW, bD⟩

theorem dataArgs_run {s₀ s : State} (hk : VG.Proof.AesGcm.Arm.ArgsKeep n s₀ s) (hf : s₀.sp.toNat + 4 * n ≤ 2 ^ 32)
    (hin : VG.Proof.AesGcm.Arm.args s₀ n ∈ s₀.rd) (hn : 5 ≤ n) :
    ∃ s', runBlock isa dataArgs s = some s' ∧ s'.gpr .r4 = VG.Proof.AesGcm.Arm.arg s₀ 2 ∧ s'.gpr .r5 = VG.Proof.AesGcm.Arm.arg s₀ 3 ∧
      s'.gpr .r6 = BitVec.ofNat 32 0 ∧ (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain ⟨a2, v2⟩ := hk.at hf hin 2 (by omega) (show 4 * 2 = 8 from rfl)
  obtain ⟨a3, v3⟩ := hk.at hf hin 3 (by omega) (show 4 * 3 = 12 from rfl)
  refine ⟨_, by simp only [dataArgs]; arun [a2, v2, a3, v3], ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, v2]
  · simp [gpr_setReg, v3]
  · simp [gpr_setReg]
  · intro r x y z; simp [gpr_setReg, x, y, z]
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- After `oneCrypt`, from `m₀`. -/
structure OC (n wi : Nat) (s₀ : State) (k7 : BitVec 32) (icb : Block) (m₀ : Mem) (s : State) : Prop where
  env : Env (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp k7 (s₀.gpr .r1) s
  args : VG.Proof.AesGcm.Arm.ArgsKeep n s₀ s
  out : bytesAt s.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat =
    gctr (ciphOf m₀ (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat) icb (bytesAt m₀ (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat)
  frame : Frame (crFrame (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp (VG.Proof.AesGcm.Arm.arg s₀ 2) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat) m₀ s.mem

theorem oneCrypt_ok {s₀ s : State} (h : VG.Proof.AesGcm.Arm.onePre n wi s₀) (hn : 5 ≤ n) {k7 : BitVec 32}
    (he : Env (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp k7 (s₀.gpr .r1) s) (hk : VG.Proof.AesGcm.Arm.ArgsKeep n s₀ s) {icb : Block}
    (hcb : blockAt s.mem (State.addr (VG.Proof.AesGcm.Arm.oSt s₀ wi) + BitVec.ofNat 64 48) = icb) :
    WP isa oneCrypt s (VG.Proof.AesGcm.Arm.OC n wi s₀ k7 icb s.mem) := by
  have L := VG.Proof.AesGcm.Arm.oneLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : VG.Proof.AesGcm.Arm.args s₀ n ∈ s₀.rd := h.1.2.2.2
  have dcD := h.2.2.1
  have hwr := h.2.1
  obtain ⟨s₁, run₁, h4, h5, h6, g₁, k₁⟩ := VG.Proof.AesGcm.Arm.dataArgs_run hk spf hin hn
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  have hk₁ := hk.of_eq k₁.mem k₁.sp k₁.rd k₁.wr
  have ci : CrIn (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp k7 (s₀.gpr .r1) (s₀.gpr .r1).toNat icb 0 (VG.Proof.AesGcm.Arm.arg s₀ 2)
      (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat s₁ :=
    ⟨he₁, h4, by rw [h5]; simp, by rw [h6], by rw [he₁.r8]; simp, hR,
      ⟨VG.Proof.AesGcm.Arm.one_dataOk h hk₁, by rw [hk₁.wr]; exact covers_of_mem hwr.1, dcD⟩⟩
  refine WP.mono (WP.with_rdwr (crypt_ok L ci)) fun s₂ hh => ?_
  obtain ⟨co, rd₂, wr₂, sp₂⟩ := hh
  have hA : ∀ r ∈ crFrame (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp (VG.Proof.AesGcm.Arm.arg s₀ 2) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat, (VG.Proof.AesGcm.Arm.args s₀ n).Disjoint r := by
    have hst := VG.Proof.AesGcm.Arm.oSt_addr h
    obtain ⟨-, -, -, -, -, -, -, -, -, dDA, dWA, -⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact dDA.symm
    · rw [hst, add_ofNat_assoc]; exact (dWA.sub_left (Lay.wSub (by decide))).symm
    · exact (dWA.sub_left (Lay.wSub (by decide))).symm
    · exact (VG.Proof.AesGcm.Arm.below_args s₀ spf).symm
  rw [k₁.mem] at co
  have c0 := Proof.Gcm.ctr_zero s.mem _ (State.addr (VG.Proof.AesGcm.Arm.oSt s₀ wi) + BitVec.ofNat 64 64)
    (ciphOf s.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat) hcb
  exact ⟨co.env, hk₁.frame spf (k₁.mem ▸ co.frame) hA sp₂ rd₂ wr₂, by rw [co.out c0, Proof.Gcm.gctr_eq],
    co.frame⟩

end

theorem padded_eq (a c : List Byte) :
    (a ++ zeros (padLen a.length) ++ c) ++ zeros (padLen (a ++ zeros (padLen a.length) ++ c).length) = padded a c := by
  by_cases hc : c = []
  · subst hc
    have h0 : padLen (a ++ zeros (padLen a.length) ++ []).length = 0 := by
      apply Proof.Gcm.padLen_of_mod
      simp only [List.append_nil, List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
    rw [h0]; simp [padded, Proof.Gcm.ghashInput_nil, zeros]
  · simp only [padded, Proof.Gcm.ghashInput_of_ne hc]

/-- The regions `oneTag o` writes. -/
abbrev otFrame (st w sp : BitVec 32) (o : Nat) : List Region :=
  [⟨State.addr st, 48⟩, ⟨State.addr w + BitVec.ofNat 64 96, 16⟩, ⟨State.addr w + BitVec.ofNat 64 o, 16⟩,
    ⟨State.addr w + BitVec.ofNat 64 512, 2048⟩, below sp]

theorem abs_otSub {st w sp : BitVec 32} {o : Nat} : ∀ r ∈ absFrame st w sp 16, ∃ r' ∈ VG.Proof.AesGcm.Arm.otFrame st w sp o, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 512, 2048⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem t_otSub {st w sp : BitVec 32} {o : Nat} : ∀ r ∈ tFrame st w sp 16, ∃ r' ∈ VG.Proof.AesGcm.Arm.otFrame st w sp o, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 512, 2048⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem tag_otSub {st w sp : BitVec 32} {o : Nat} : ∀ r ∈ VG.Proof.AesGcm.Arm.tagFrame st w sp o, ∃ r' ∈ VG.Proof.AesGcm.Arm.otFrame st w sp o, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

section
variable {n wi : Nat}

/-- After `oneTag o`, from `m₀`, for the tag of `a` and the bytes at `data`. -/
structure OT (n wi : Nat) (s₀ : State) (o : Nat) (a : List Byte) (J : Block) (m₀ : Mem) (s : State) : Prop where
  env : ∃ k7, Env (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp k7 (s₀.gpr .r1) s
  args : VG.Proof.AesGcm.Arm.ArgsKeep n s₀ s
  out : bytesAt s.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ wi) + BitVec.ofNat 64 o) 16 =
    toBytes (ghashFrom (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (ghash (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (blocks (padded a (bytesAt m₀ (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat))))
      [ofBytes (lensBlock a.length (bytesAt m₀ (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat).length)] ^^^
      ciphOf m₀ (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat J)
  frame : Frame (VG.Proof.AesGcm.Arm.otFrame (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp o) m₀ s.mem

theorem one_argsOt {s₀ : State} (h : VG.Proof.AesGcm.Arm.onePre n wi s₀) {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ VG.Proof.AesGcm.Arm.otFrame (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp o, (VG.Proof.AesGcm.Arm.args s₀ n).Disjoint r := by
  have hst := VG.Proof.AesGcm.Arm.oSt_addr h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, dWA, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [hst]; exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by omega))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (VG.Proof.AesGcm.Arm.below_args s₀ spf).symm

theorem oneTag_ok {s₀ s : State} (h : VG.Proof.AesGcm.Arm.onePre n wi s₀) (hn : 5 ≤ n) {o : Nat} (ho : o = 0 ∨ o = 112) {k7 : BitVec 32}
    (he : Env (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp k7 (s₀.gpr .r1) s) (hk : VG.Proof.AesGcm.Arm.ArgsKeep n s₀ s)
    (hH : blockAt s.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0)))
    {a : List Byte} (hl : (VG.Proof.AesGcm.Arm.arg s₀ 1).toNat = a.length)
    (hab : Absorbed s.mem (State.addr (VG.Proof.AesGcm.Arm.oSt s₀ wi) + BitVec.ofNat 64 16) (State.addr (VG.Proof.AesGcm.Arm.oSt s₀ wi) + BitVec.ofNat 64 32)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (a ++ zeros (padLen a.length))) :
    WP isa (oneTag o) s (VG.Proof.AesGcm.Arm.OT n wi s₀ o a (blockAt s.mem (State.addr (VG.Proof.AesGcm.Arm.oSt s₀ wi))) s.mem) := by
  have L := VG.Proof.AesGcm.Arm.oneLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : VG.Proof.AesGcm.Arm.args s₀ n ∈ s₀.rd := h.1.2.2.2
  have hA := VG.Proof.AesGcm.Arm.one_argsOt h ho
  have dC : ∀ r ∈ VG.Proof.AesGcm.Arm.otFrame (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp o, (⟨State.addr (s₀.gpr .r0), 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.cs.sub_right (Region.sub_prefix (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by omega))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.kc.symm
  have dJ : ∀ r ∈ absFrame (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp 16 ++ tFrame (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp 16,
      (⟨State.addr (VG.Proof.AesGcm.Arm.oSt s₀ wi), 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    have e1 : ∀ {d k : Nat}, 16 ≤ d → d + k ≤ 80 →
        (⟨State.addr (VG.Proof.AesGcm.Arm.oSt s₀ wi), 16⟩ : Region).Disjoint ⟨State.addr (VG.Proof.AesGcm.Arm.oSt s₀ wi) + BitVec.ofNat 64 d, k⟩ := fun h1 h2 => by
      have := Lay.st_st (st := VG.Proof.AesGcm.Arm.oSt s₀ wi) (a := 0) (n := 16) (.inl h1) (by decide) h2
      rwa [add_ofNat_zero] at this
    have e2 : ∀ {d k : Nat}, 96 ≤ d → d + k ≤ 2560 →
        (⟨State.addr (VG.Proof.AesGcm.Arm.oSt s₀ wi), 16⟩ : Region).Disjoint ⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ wi) + BitVec.ofNat 64 d, k⟩ := fun h1 h2 => by
      have := L.st_w (a := 0) (n := 16) (by decide) (.inr ⟨h1, h2⟩)
      rwa [add_ofNat_zero] at this
    have e3 : (⟨State.addr (VG.Proof.AesGcm.Arm.oSt s₀ wi), 16⟩ : Region).Disjoint (below s₀.sp) := by
      have := (L.stk_st (a := 0) (n := 16) (by decide)).symm
      rwa [add_ofNat_zero] at this
    rcases hr with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
    · exact e1 (by decide) (by decide)
    · exact e1 (by decide) (by decide)
    · exact e2 (by decide) (by decide)
    · exact e3
    · exact e1 (by decide) (by decide)
    · exact e2 (by decide) (by decide)
    · exact e2 (by decide) (by decide)
    · exact e3
  have hx : (a ++ zeros (padLen a.length)).length % 16 = 0 := by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  obtain ⟨s₁, run₁, h4, h5, h6, g₁, k₁⟩ := VG.Proof.AesGcm.Arm.dataArgs_run hk spf hin hn
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  have hk₁ := hk.of_eq k₁.mem k₁.sp k₁.rd k₁.wr
  have ai : AbsIn (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp k7 (s₀.gpr .r1) 16 (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (a ++ zeros (padLen a.length)) (VG.Proof.AesGcm.Arm.arg s₀ 2) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat s₁ :=
    ⟨he₁, h4, by rw [h5]; simp, by rw [h6, hx], VG.Proof.AesGcm.Arm.one_dataOk h hk₁, by rw [k₁.mem]; exact hH⟩
  refine WP.seq (WP.mono (WP.with_rdwr (absorb_ok L (.inr rfl) ai)) fun s₂ hh => ?_)
  obtain ⟨ab, rd₂, wr₂, sp₂⟩ := hh
  rw [k₁.mem] at ab
  have hk₂ := hk₁.frame spf (k₁.mem ▸ ab.frame) (VG.Proof.AesGcm.Arm.disj_sub hA VG.Proof.AesGcm.Arm.abs_otSub) sp₂ rd₂ wr₂
  obtain ⟨b3, w3⟩ := hk₂.at spf hin 3 (by omega) (show 4 * 3 = 12 from rfl)
  obtain ⟨s₃, run₃, h6₃, g₃, k₃⟩ : ∃ s₃, runBlock isa [.ldrSp .r6 12, .dp .and .r6 .r6 (imm 15)] s₂ = some s₃ ∧
      s₃.gpr .r6 = BitVec.ofNat 32 ((VG.Proof.AesGcm.Arm.arg s₀ 3).toNat % 16) ∧ (∀ r, r ≠ .r6 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
    refine ⟨_, by arun [b3, w3], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, w3, and15]
    · intro r x; simp [gpr_setReg, x]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ := ab.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide)) k₃.sp k₃.rd k₃.wr
  have hk₃ := hk₂.of_eq k₃.mem k₃.sp k₃.rd k₃.wr
  have hH₂ : blockAt s₂.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0)) := by
    rw [blockAt_frame ab.frame (ctx_absFrame L (.inr rfl))]; exact hH
  let ct := bytesAt s.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat
  have hlx : ((a ++ zeros (padLen a.length)) ++ ct).length % 16 = (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat % 16 := by
    simp only [List.length_append, Proof.Gcm.length_zeros, ct, length_bytesAt] at hx ⊢; omega
  refine WP.seq (WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl)
    (x := (a ++ zeros (padLen a.length)) ++ ct) (H := ctxH s₀.mem (State.addr (s₀.gpr .r0)))
    ⟨he₃, by rw [k₃.mem]; exact hH₂⟩ (by rw [h6₃, hlx]))) fun s₄ hh => ?_)
  obtain ⟨fl, rd₄, wr₄, sp₄⟩ := hh
  rw [k₃.mem] at fl
  have hk₄ := hk₂.frame spf fl.frame (VG.Proof.AesGcm.Arm.disj_sub hA VG.Proof.AesGcm.Arm.t_otSub) (sp₄.trans k₃.sp) (rd₄.trans k₃.rd) (wr₄.trans k₃.wr)
  obtain ⟨c1, x1⟩ := hk₄.at spf hin 1 (by omega) (show 4 * 1 = 4 from rfl)
  obtain ⟨c3, x3⟩ := hk₄.at spf hin 3 (by omega) (show 4 * 3 = 12 from rfl)
  obtain ⟨s₅, run₅, h4₅, h5₅, h6₅, h7₅, g₅, k₅⟩ : ∃ s₅, runBlock isa [.ldrSp .r4 4, .mov .r5 (imm 0), .ldrSp .r6 12,
      .mov .r7 (imm 0)] s₄ = some s₅ ∧ s₅.gpr .r4 = VG.Proof.AesGcm.Arm.arg s₀ 1 ∧ s₅.gpr .r5 = 0 ∧ s₅.gpr .r6 = VG.Proof.AesGcm.Arm.arg s₀ 3 ∧
      s₅.gpr .r7 = 0 ∧ (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    refine ⟨_, by arun [c1, x1, c3, x3], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, x1]
    · simp [gpr_setReg]
    · simp [gpr_setReg, x3]
    · simp [gpr_setReg]
    · intro r x y z q; simp [gpr_setReg, x, y, z, q]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ := fl.env.set7 h7₅ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₅ _ (by decide) (by decide) (by decide) (by decide))
    k₅.sp k₅.rd k₅.wr
  have hk₅ := hk₄.of_eq k₅.mem k₅.sp k₅.rd k₅.wr
  refine WP.mono (WP.with_rdwr (VG.Proof.AesGcm.Arm.tag_ok L ho he₅ (show s₀.gpr .r1 = BitVec.ofNat 32 (s₀.gpr .r1).toNat by simp) hR
    (H := ctxH s₀.mem (State.addr (s₀.gpr .r0))) (by rw [k₅.mem]; exact fl.hH) rfl)) fun s₆ hh => ?_
  obtain ⟨tg, rd₆, wr₆, sp₆⟩ := hh
  rw [h4₅, h5₅, h6₅, h7₅, k₅.mem] at tg
  have f₄ : Frame (absFrame (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp 16 ++ tFrame (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp 16) s.mem s₄.mem :=
    (ab.frame.mono (fun r hr => List.mem_append_left _ hr)).trans
      ((k₃.mem ▸ fl.frame : Frame _ s₂.mem s₄.mem).mono (fun r hr => List.mem_append_right _ hr))
  refine ⟨⟨_, tg.env⟩, hk₄.frame spf tg.frame (VG.Proof.AesGcm.Arm.disj_sub hA VG.Proof.AesGcm.Arm.tag_otSub) (sp₆.trans k₅.sp) (rd₆.trans k₅.rd)
    (wr₆.trans k₅.wr), ?_, ?_⟩
  · rw [tg.out]
    have hw := (fl.abs (ab.abs hab)).whole_eq (by
      simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _)
    rw [VG.Proof.AesGcm.Arm.padded_eq] at hw
    rw [hw, ciph_frame f₄ (VG.Proof.AesGcm.Arm.disj_sub dC (fun r hr => by
        simp only [List.mem_append] at hr
        rcases hr with hr | hr
        · exact VG.Proof.AesGcm.Arm.abs_otSub r hr
        · exact VG.Proof.AesGcm.Arm.t_otSub r hr)) hR,
      blockAt_frame f₄ dJ]
    have z0 : (0 : BitVec 32).toNat = 0 := rfl
    have l1 : ((0 : BitVec 32) ++ VG.Proof.AesGcm.Arm.arg s₀ 1).toNat = a.length := by
      rw [Proof.Gcm.toNat_append, ← hl, z0, Nat.zero_mul, Nat.zero_add]
    have l3 : ((0 : BitVec 32) ++ VG.Proof.AesGcm.Arm.arg s₀ 3).toNat = ct.length := by
      rw [Proof.Gcm.toNat_append, length_bytesAt, z0, Nat.zero_mul, Nat.zero_add]
    rw [l1, l3]
  · refine (f₄.sub fun r hr => ?_).trans (tg.frame.sub VG.Proof.AesGcm.Arm.tag_otSub)
    simp only [List.mem_append] at hr
    rcases hr with hr | hr
    · exact VG.Proof.AesGcm.Arm.abs_otSub r hr
    · exact VG.Proof.AesGcm.Arm.t_otSub r hr

end

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.Seal`. -/
section

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_seal`

Untrusted: everything here is checked by Lean. `seal` keeps a streaming
state at `W + 16`: `J₀` and the additional data (`oneAad`), the data
encrypted in place (`oneCrypt`), and the tag of the ciphertext into `W`
(`oneTag 0`), copied to `tag` (`tagOut`) (`seal_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph ghashInput fullTag zeros padLen j0 inc32 gctr encryptWith toBytes)
open VG.Proof.Gcm (Absorbed)

section
variable {n wi : Nat}

theorem one_dataW {s₀ s : State} (h : VG.Proof.AesGcm.Arm.onePre n wi s₀) (hk : VG.Proof.AesGcm.Arm.ArgsKeep n s₀ s) (k7 k8 : BitVec 32) :
    DataW (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp k7 k8 s (VG.Proof.AesGcm.Arm.arg s₀ 2) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat :=
  ⟨VG.Proof.AesGcm.Arm.one_dataOk h hk, by rw [hk.wr]; exact covers_of_mem h.2.1.1, h.2.2.1⟩

theorem saved_otFrame {s₀ : State} (h : VG.Proof.AesGcm.Arm.onePre n wi s₀) {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ VG.Proof.AesGcm.Arm.otFrame (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp o, (VG.Proof.AesGcm.Arm.savedR (VG.Proof.AesGcm.Arm.arg s₀ wi)).Disjoint r := by
  have L := VG.Proof.AesGcm.Arm.oneLay h
  have hst := VG.Proof.AesGcm.Arm.oSt_addr h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [hst]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inr (by omega)) (by decide) (by omega)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

/-- What `seal`'s pieces leave, from the entry on. -/
theorem seal_mid {s₀ s₁ s₂ s₃ : State} (h : VG.Proof.AesGcm.Arm.onePre n wi s₀) (h1 : VG.Proof.AesGcm.Arm.SO1 n wi s₀ s₁) (oa : VG.Proof.AesGcm.Arm.OA n wi s₀ s₁.mem s₂)
    {k7 : BitVec 32} (oc : VG.Proof.AesGcm.Arm.OC n wi s₀ k7 (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat))) s₂.mem s₃) :
    blockAt s₃.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0)) ∧
    Absorbed s₃.mem (State.addr (VG.Proof.AesGcm.Arm.oSt s₀ wi) + BitVec.ofNat 64 16) (State.addr (VG.Proof.AesGcm.Arm.oSt s₀ wi) + BitVec.ofNat 64 32)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 0)) (VG.Proof.AesGcm.Arm.arg s₀ 1).toNat ++
        zeros (padLen (bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 0)) (VG.Proof.AesGcm.Arm.arg s₀ 1).toNat).length)) ∧
    blockAt s₃.mem (State.addr (VG.Proof.AesGcm.Arm.oSt s₀ wi)) =
      j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat) ∧
    ciphOf s₃.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
      ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat ∧
    bytesAt s₃.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat =
      gctr (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
        (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
          (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat)))
        (bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat) ∧
    VG.Proof.AesGcm.Arm.SavedAt s₃.mem (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀ := by
  have L := VG.Proof.AesGcm.Arm.oneLay h
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hd := VG.Proof.AesGcm.Arm.one_dataW h oa.args 0 0
  have dCr := ctx_crFrame L hd
  have dc₂ : ∀ r ∈ [VG.Proof.AesGcm.Arm.savedR (VG.Proof.AesGcm.Arm.arg s₀ wi)] ++ VG.Proof.AesGcm.Arm.j0Frame (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp,
      (⟨State.addr (s₀.gpr .r0), 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | hr
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.cs
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.kc.symm
  have f₂ : Frame ([VG.Proof.AesGcm.Arm.savedR (VG.Proof.AesGcm.Arm.arg s₀ wi)] ++ VG.Proof.AesGcm.Arm.j0Frame (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp) s₀.mem s₂.mem :=
    (h1.frame.mono fun r hr => List.mem_append_left _ hr).trans (oa.frame.mono fun r hr => List.mem_append_right _ hr)
  have hc₂ := VG.Proof.AesGcm.Arm.ciph_keep f₂ dc₂ hR
  have hD₂ : bytesAt s₂.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat =
      bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat := by
    have hp := h
    obtain ⟨-, -, -, -, -, -, -, -, dDW, -, -, -, -, -, bD, -⟩ := hp
    exact bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with rfl | hr
      · exact dDW.sub_right (Lay.wSub (by decide))
      · exact VG.Proof.AesGcm.Arm.one_dataJ0 h dDW bD r hr) (by have := hd.ok.lt; omega)
  have hb := Nat.mod_lt (bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 0)) (VG.Proof.AesGcm.Arm.arg s₀ 1).toNat ++
    zeros (padLen (bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 0)) (VG.Proof.AesGcm.Arm.arg s₀ 1).toNat).length)).length (show 16 > 0 by decide)
  refine ⟨?_, (oa.abs.congr (blockAt_frame oc.frame (VG.Proof.AesGcm.Arm.stp_crFrame L hd (by decide)))
      (bytesAt_frame oc.frame (VG.Proof.AesGcm.Arm.stp_crFrame L hd (by omega)) (by omega))), ?_,
    by rw [ciph_frame oc.frame dCr hR, hc₂], by rw [oc.out, hc₂, hD₂],
    (h1.saved.frame oa.frame (VG.Proof.AesGcm.Arm.saved_j0Frame L)).frame oc.frame (VG.Proof.AesGcm.Arm.saved_crFrame L hd)⟩
  · rw [blockAt_frame oc.frame (fun r hr => (dCr r hr).sub_left (Lay.ctxSub (by decide)))]; exact oa.hH
  · rw [blockAt_frame oc.frame (by simpa using VG.Proof.AesGcm.Arm.stp_crFrame L hd (d := 0) (k := 16) (by decide))]; exact oa.j

end

theorem seal_wp {s₀ : State} (h : sealArm.pre s₀) :
    WP isa «seal» s₀ fun s' => abiPreserved s₀ s' ∧ sealArm.post s₀ s' := by
  have h' : VG.Proof.AesGcm.Arm.onePre 6 5 s₀ := sealPreArm.one h
  have L := VG.Proof.AesGcm.Arm.oneLay h'
  have fW := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : VG.Proof.AesGcm.Arm.args s₀ 6 ∈ s₀.rd := h'.1.2.2.2
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, dT, -, -, tW, -, -, -, -, -, -, -, -, -, -, -, -, fT, -⟩ := h
  have dTW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4), 16⟩ : Region).Disjoint
      ⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 5) + BitVec.ofNat 64 d, k⟩ := fun hd => tW.sub_right (Lay.wSub hd)
  refine WP.seq (VG.Proof.AesGcm.Arm.one1_wp (wi := 5) h' (by decide) (by decide) fun s₁ h1 =>
    WP.seq (WP.mono (VG.Proof.AesGcm.Arm.oneAad_ok h' (by decide) h1) fun s₂ oa => ?_))
  obtain ⟨k7, he₂⟩ := oa.env
  refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.oneCrypt_ok h' (by decide) he₂ oa.args oa.cb) fun s₃ oc => ?_)
  have he₃ := oc.env
  obtain ⟨hH₃, hab₃, hj₃, hc₃, hD₃, sv₃⟩ := VG.Proof.AesGcm.Arm.seal_mid h' h1 oa oc
  refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.oneTag_ok h' (by decide) (o := 0) (.inl rfl) he₃ oc.args hH₃ (length_bytesAt _ _ _).symm hab₃)
    fun s₄ ot => ?_)
  obtain ⟨k7'', he₄⟩ := ot.env
  obtain ⟨i4, v4⟩ := ot.args.at spf hin 4 (by decide) (show 4 * 4 = 16 from rfl)
  obtain ⟨s₅, run₅, hb₅, hf₅, g₅, rd₅, wr₅, sp₅⟩ := VG.Proof.AesGcm.Arm.tagOut_ok L he₄ i4 v4
    (by rw [ot.args.wr, hwr]; exact covers_of_mem (by simp)) fT (by simpa using dTW (d := 0) (k := 16) (by decide))
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₅ _ (by decide) (by decide)) sp₅ rd₅ wr₅
  have sv₅ := (sv₃.frame ot.frame (VG.Proof.AesGcm.Arm.saved_otFrame h' (.inl rfl))).frame hf₅ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (dTW (by decide)).symm)
  refine WP.mono (VG.Proof.AesGcm.Arm.restore_ok he₅.r11 fW (covers_left he₅.perm.w) sv₅ he₅.sp) fun s' hh => ⟨hh.1, ?_⟩
  have hm := hh.2.1
  have hpre := h'
  obtain ⟨-, -, -, -, -, -, -, -, dDW, -, -, -, -, -, bD, -⟩ := hpre
  have hD₄ : bytesAt s₄.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat =
      bytesAt s₃.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat := by
    refine bytesAt_frame ot.frame (fun r hr => ?_) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [VG.Proof.AesGcm.Arm.oSt_addr h']; exact dDW.sub_right (Lay.wSub (by decide))
    · exact dDW.sub_right (Lay.wSub (by decide))
    · exact dDW.sub_right (Lay.wSub (by decide))
    · exact dDW.sub_right (Lay.wSub (by decide))
    · exact bD.symm
  have hD₅ : bytesAt s₅.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat =
      bytesAt s₄.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat :=
    bytesAt_frame hf₅ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dT) (by omega)
  have ho := ot.out
  rw [hc₃, hj₃, add_ofNat_zero, ← Proof.Gcm.fullTag_eq] at ho
  simp only [VG.Proof.AesGcm.Arm.sealArm, encryptWith, hm, hD₅, hD₄, hD₃, hb₅, ho]
  refine Prod.ext rfl ?_
  exact List.take_of_length_le (by
    rw [Spec.Gcm.fullTag, Proof.Gcm.length_gctr, Cmac.toBytes_length])

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.Open`. -/
section

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_open`

Untrusted: everything here is checked by Lean. `open` checks the tag length;
if it is allowed, it computes the tag of the ciphertext into `W + 112`
(`oneAad`, `oneTag 112`), copies the received tag (at `tag`) to `W + 256`, compares
the first `tag_len` bytes of each, and decrypts the data in place only if
they are equal; `r0` is the result (`open_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph ghashInput fullTag zeros padLen j0 inc32 gctr decryptWith openResult toBytes)
open VG.Proof.Gcm (Absorbed)

theorem SO1.keep {n wi : Nat} {s₀ s₁ s₂ : State} (h1 : VG.Proof.AesGcm.Arm.SO1 n wi s₀ s₁)
    (hg : ∀ r, r ≠ .r0 → r ≠ .r6 → s₂.gpr r = s₁.gpr r) (hk : Keeps s₁ s₂) : VG.Proof.AesGcm.Arm.SO1 n wi s₀ s₂ :=
  ⟨h1.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hk.sp hk.rd hk.wr,
    by rw [hg _ (by decide) (by decide)]; exact h1.r4, by rw [hg _ (by decide) (by decide)]; exact h1.r5,
    h1.args.of_eq hk.mem hk.sp hk.rd hk.wr, hk.mem ▸ h1.saved, hk.mem ▸ h1.frame⟩

/-- What `open` promises, given the result `r0` and the data. -/
def OpenPost (s₀ s : State) : Prop :=
  match VG.Proof.AesGcm.Arm.openRes s₀ with
  | some pt => s.gpr .r0 = 1 ∧ bytesAt s.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat = pt
  | none => s.gpr .r0 = 0 ∧
      bytesAt s.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat = bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat

theorem openPost_none {s₀ s : State} (h : VG.Proof.AesGcm.Arm.openRes s₀ = none) (h0 : s.gpr .r0 = 0)
    (hd : bytesAt s.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat = bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat) :
    VG.Proof.AesGcm.Arm.OpenPost s₀ s := by
  unfold VG.Proof.AesGcm.Arm.OpenPost; rw [h]; exact ⟨h0, hd⟩

theorem openPost_some {s₀ s : State} {pt : List Byte} (h : VG.Proof.AesGcm.Arm.openRes s₀ = some pt) (h0 : s.gpr .r0 = 1)
    (hd : bytesAt s.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat = pt) : VG.Proof.AesGcm.Arm.OpenPost s₀ s := by
  unfold VG.Proof.AesGcm.Arm.OpenPost; rw [h]; exact ⟨h0, hd⟩

/-- The code of `open` once the tag length is known to be allowed. -/
abbrev openGood : Prog isa :=
  .seq oneAad (.seq (oneTag uO) (.seq (.block [.ldrSp .r6 20]) (.seq recv (.seq (cmp uO)
    (.seq (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)]) (.seq (.ite .eq (.block []) oneCrypt)
      (.block [.mov .r0 (.reg .r7)])))))))

/-- Whether the computed tag, cut to the tag length, is the received one. -/
abbrev openTagOk (s₀ : State) : Prop :=
  (fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat) (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat)
      (bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 0)) (VG.Proof.AesGcm.Arm.arg s₀ 1).toNat)
      (bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat)).take (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat =
    bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4)) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat

/-- After the tags are compared, with the result in `r7` and `Z`. -/
structure OpenMid (s₀ s : State) : Prop where
  env : Env (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ 6) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp (s.gpr .r7) (s₀.gpr .r1) s
  args : VG.Proof.AesGcm.Arm.ArgsKeep 7 s₀ s
  saved : VG.Proof.AesGcm.Arm.SavedAt s.mem (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀
  dat : bytesAt s.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat = bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat
  ciph : ciphOf s.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
    ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat
  cb : blockAt s.mem (State.addr (VG.Proof.AesGcm.Arm.oSt s₀ 6) + BitVec.ofNat 64 48) =
    inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat))
  r7 : s.gpr .r7 = if VG.Proof.AesGcm.Arm.openTagOk s₀ then 1 else 0
  z : s.z = decide (¬ VG.Proof.AesGcm.Arm.openTagOk s₀)

/-- `open` up to the comparison of the tags, followed by any `T`. -/
theorem open_head {s₀ s₂ : State} (ho : VG.Proof.AesGcm.Arm.openPreArm s₀) (h2 : VG.Proof.AesGcm.Arm.SO1 7 6 s₀ s₂)
    (hok : Spec.Gcm.tagLenOk (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat = true) {T : Prog isa} {Q : State → Prop}
    (k : ∀ s₈, VG.Proof.AesGcm.Arm.OpenMid s₀ s₈ → WP isa T s₈ Q) :
    WP isa (.seq oneAad (.seq (oneTag uO) (.seq (.block [.ldrSp .r6 20]) (.seq recv (.seq (cmp uO)
      (.seq (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)]) T)))))) s₂ Q := by
  have h : VG.Proof.AesGcm.Arm.onePre 7 6 s₀ := openPreArm.one ho
  obtain ⟨hrd, -, -, -, -, -, -, -, -, -, -, tW, -, -, -, -, -, bT, -, -, -, -, -, fT, -⟩ := ho
  have dTW : ∀ {d k : Nat}, d + k ≤ 2560 → (⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4), (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat⟩ : Region).Disjoint
      ⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 d, k⟩ := fun hd => tW.sub_right (Lay.wSub hd)
  have L := VG.Proof.AesGcm.Arm.oneLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hR := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : VG.Proof.AesGcm.Arm.args s₀ 7 ∈ s₀.rd := h.1.2.2.2
  obtain ⟨t1, t16⟩ := VG.Proof.AesGcm.Arm.tagLenOk_bounds hok
  have dW : ∀ {d k : Nat}, d + k ≤ 2560 → (164 ≤ d ∨ d + k ≤ 128) →
      (VG.Proof.AesGcm.Arm.savedR (VG.Proof.AesGcm.Arm.arg s₀ 6)).Disjoint ⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ h₂ => Lay.w_w (by omega) (by decide) h₁
  refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.oneAad_ok h (by decide) h2) fun s₃ oa => ?_)
  obtain ⟨k7, he₃⟩ := oa.env
  refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.oneTag_ok h (by decide) (o := 112) (.inr rfl) he₃ oa.args oa.hH (length_bytesAt _ _ _).symm
    oa.abs) fun s₄ ot => ?_)
  obtain ⟨k7₄, he₄⟩ := ot.env
  obtain ⟨j5, w5⟩ := ot.args.at spf hin 5 (by decide) (show 4 * 5 = 20 from rfl)
  obtain ⟨s₅, run₅, h6₅, g₅, k₅⟩ : ∃ s₅, runBlock isa [.ldrSp .r6 20] s₄ = some s₅ ∧
      s₅.gpr .r6 = BitVec.ofNat 32 (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat ∧ (∀ r, r ≠ .r6 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    refine ⟨_, by arun [j5, w5], ?_, ?_, ?_⟩
    · simp [gpr_setReg, w5]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₅ _ (by decide)) k₅.sp k₅.rd k₅.wr
  have hk₅ := ot.args.of_eq k₅.mem k₅.sp k₅.rd k₅.wr
  obtain ⟨i4, v4⟩ := hk₅.at spf hin 4 (by decide) (show 4 * 4 = 16 from rfl)
  refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.recv_ok L he₅ i4 v4
    (by rw [hk₅.rd, hk₅.wr]; exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))) fT
    (dTW (by decide)) h6₅ t1 t16) fun s₆ hh => ?_)
  obtain ⟨hb₆, hf₆, g₆, rd₆, wr₆, sp₆⟩ := hh
  have he₆ := he₅.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₆ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)) sp₆ rd₆ wr₆
  have h6₆ : s₆.gpr .r6 = BitVec.ofNat 32 (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat := by
    rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), h6₅]
  refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.cmp_ok L he₆ (o := 112) (.inr rfl) h6₆ t1 t16) fun s₇ hh => ?_)
  obtain ⟨h0₇, hf₇, g₇, rd₇, wr₇, sp₇⟩ := hh
  have he₇ := he₆.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₇ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)) sp₇ rd₇ wr₇
  -- what the pieces leave
  let rs : List Region := [VG.Proof.AesGcm.Arm.savedR (VG.Proof.AesGcm.Arm.arg s₀ 6)] ++ VG.Proof.AesGcm.Arm.j0Frame (VG.Proof.AesGcm.Arm.oSt s₀ 6) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp ++
    VG.Proof.AesGcm.Arm.otFrame (VG.Proof.AesGcm.Arm.oSt s₀ 6) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp 112 ++
    [⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 256, 16⟩, ⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 240, 16⟩]
  have F₇ : Frame rs s₀.mem s₇.mem := by
    have e₂ : Frame [VG.Proof.AesGcm.Arm.savedR (VG.Proof.AesGcm.Arm.arg s₀ 6)] s₀.mem s₂.mem := h2.frame
    refine ((((e₂.mono ?_).trans (oa.frame.mono ?_)).trans (ot.frame.mono ?_)).trans
      ((k₅.mem ▸ hf₆ : Frame _ s₄.mem s₆.mem).mono ?_)).trans (hf₇.mono ?_)
    all_goals intro r hr; simp only [rs, List.mem_append]
    · exact .inl (.inl (.inl hr))
    · exact .inl (.inl (.inr hr))
    · exact .inl (.inr hr)
    · simp only [List.mem_singleton] at hr; exact .inr (by simp [hr])
    · simp only [List.mem_singleton] at hr; exact .inr (by simp [hr])
  have hp := h
  obtain ⟨-, -, dcD, dcW, -, -, -, -, dDW, -, -, bc, -, -, bD, bW, -⟩ := hp
  have dC : ∀ r ∈ rs, (⟨State.addr (s₀.gpr .r0), 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [rs, List.mem_append] at hr
    rcases hr with ((hr | hr) | hr) | hr
    · simp only [List.mem_singleton] at hr; subst hr; exact L.cw'.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.cs
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.kc.symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact L.cs.sub_right (Region.sub_prefix (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.kc.symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
  have dD : ∀ r ∈ rs, (⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2), (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat⟩ : Region).Disjoint r := by
    intro r hr
    simp only [rs, List.mem_append] at hr
    rcases hr with ((hr | hr) | hr) | hr
    · simp only [List.mem_singleton] at hr; subst hr; exact dDW.sub_right (Lay.wSub (by decide))
    · exact VG.Proof.AesGcm.Arm.one_dataJ0 h dDW bD r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [VG.Proof.AesGcm.Arm.oSt_addr h]; exact dDW.sub_right (Lay.wSub (by decide))
      · exact dDW.sub_right (Lay.wSub (by decide))
      · exact dDW.sub_right (Lay.wSub (by decide))
      · exact dDW.sub_right (Lay.wSub (by decide))
      · exact bD.symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dDW.sub_right (Lay.wSub (by decide))
      · exact dDW.sub_right (Lay.wSub (by decide))
  let ciph := ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat
  let H := ctxH s₀.mem (State.addr (s₀.gpr .r0))
  let iv := bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat
  let aad := bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 0)) (VG.Proof.AesGcm.Arm.arg s₀ 1).toNat
  let dat := bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat
  let tl := (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat
  let tag₀ := bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4)) tl
  have F₃ : Frame ([VG.Proof.AesGcm.Arm.savedR (VG.Proof.AesGcm.Arm.arg s₀ 6)] ++ VG.Proof.AesGcm.Arm.j0Frame (VG.Proof.AesGcm.Arm.oSt s₀ 6) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp) s₀.mem s₃.mem :=
    (h2.frame.mono fun r hr => List.mem_append_left _ hr).trans (oa.frame.mono fun r hr => List.mem_append_right _ hr)
  have sub₃ : ∀ r ∈ [VG.Proof.AesGcm.Arm.savedR (VG.Proof.AesGcm.Arm.arg s₀ 6)] ++ VG.Proof.AesGcm.Arm.j0Frame (VG.Proof.AesGcm.Arm.oSt s₀ 6) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp, r ∈ rs := fun r hr => by
    simp only [rs, List.mem_append] at hr ⊢; exact .inl (.inl hr)
  have hD₃ : bytesAt s₃.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat = dat :=
    bytesAt_frame F₃ (fun r hr => dD r (sub₃ r hr)) (by omega)
  have hT₄ : bytesAt s₄.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 112) 16 = fullTag ciph H iv aad dat := by
    rw [ot.out, hD₃, VG.Proof.AesGcm.Arm.ciph_keep F₃ (fun r hr => dC r (sub₃ r hr)) hR, oa.j, ← Proof.Gcm.fullTag_eq]
  have F₄ : Frame ([VG.Proof.AesGcm.Arm.savedR (VG.Proof.AesGcm.Arm.arg s₀ 6)] ++ VG.Proof.AesGcm.Arm.j0Frame (VG.Proof.AesGcm.Arm.oSt s₀ 6) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp ++ VG.Proof.AesGcm.Arm.otFrame (VG.Proof.AesGcm.Arm.oSt s₀ 6) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp 112)
      s₀.mem s₄.mem :=
    (F₃.mono fun r hr => List.mem_append_left _ hr).trans (ot.frame.mono fun r hr => List.mem_append_right _ hr)
  have hR₀ : bytesAt s₄.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4)) tl = tag₀ := by
    refine bytesAt_frame F₄ (fun r hr => ?_) (by omega)
    have hst := VG.Proof.AesGcm.Arm.oSt_addr h
    have z : ∀ {d k : Nat}, d + k ≤ 2560 → 16 ≤ d →
        (⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 4), tl⟩ : Region).Disjoint ⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 d, k⟩ :=
      fun h₁ _ => dTW h₁
    simp only [List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · simp only [List.mem_singleton] at hr; subst hr; exact z (by decide) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hst]; exact z (by decide) (by decide)
      · exact z (by decide) (by decide)
      · exact z (by decide) (by decide)
      · exact bT.symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [hst]; exact z (by decide) (by decide)
      · exact z (by decide) (by decide)
      · exact z (by decide) (by decide)
      · exact z (by decide) (by decide)
      · exact bT.symm
  have hX : (bytesAt s₆.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 112) tl ++ zeros (16 - tl) =
      bytesAt s₆.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 256) 16) ↔ (fullTag ciph H iv aad dat).take tl = tag₀ := by
    rw [hb₆, k₅.mem, hR₀, bytesAt_frame hf₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega)) (by omega) (by decide))
        (by omega), k₅.mem, VG.Proof.AesGcm.Arm.bytesAt_take _ _ t16, hT₄, List.append_cancel_right_eq]
  let X : Prop := bytesAt s₆.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 112) tl ++ zeros (16 - tl) =
      bytesAt s₆.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 256) 16
  obtain ⟨s₈, run₈, h7₈, hz₈, g₈, k₈⟩ : ∃ s₈, runBlock isa [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)] s₇ = some s₈ ∧
      s₈.gpr .r7 = s₇.gpr .r0 ∧ s₈.z = decide ((s₇.gpr .r0).toNat = 0) ∧ (∀ r, r ≠ .r7 → s₈.gpr r = s₇.gpr r) ∧
      Keeps s₇ s₈ := by
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · simp only [z_subFlags, gpr_setReg, reduceCtorEq, ite_false]; exact VG.Proof.AesGcm.Arm.z_sub0 _
    · intro r hr; simp only [gpr_subFlags, gpr_setReg, hr, ite_false]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₈, run₈, ?_⟩)
  have he₈ := he₇.set7 h7₈ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₈ _ (by decide)) k₈.sp k₈.rd k₈.wr
  have dA6 : ∀ {d : Nat}, d + 16 ≤ 2560 → ∀ r ∈ [(⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 d, 16⟩ : Region)],
      (VG.Proof.AesGcm.Arm.args s₀ 7).Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (h.2.2.2.2.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
  have hk₈ : VG.Proof.AesGcm.Arm.ArgsKeep 7 s₀ s₈ :=
    ((((ot.args.of_eq k₅.mem k₅.sp k₅.rd k₅.wr).frame spf hf₆ (dA6 (by decide)) sp₆ rd₆ wr₆).frame spf hf₇
      (dA6 (by decide)) sp₇ rd₇ wr₇).of_eq k₈.mem k₈.sp k₈.rd k₈.wr)
  have F₈ : Frame rs s₀.mem s₈.mem := by rw [k₈.mem]; exact F₇
  have hdat₈ : bytesAt s₈.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat = dat := bytesAt_frame F₈ dD (by omega)
  have hc₈ : ciphOf s₈.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat = ciph := VG.Proof.AesGcm.Arm.ciph_keep F₈ dC hR
  have hcb₈ : blockAt s₈.mem (State.addr (VG.Proof.AesGcm.Arm.oSt s₀ 6) + BitVec.ofNat 64 48) = inc32 (j0 H iv) := by
    have F₃₈ : Frame (VG.Proof.AesGcm.Arm.otFrame (VG.Proof.AesGcm.Arm.oSt s₀ 6) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp 112 ++
        [⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 256, 16⟩, ⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 240, 16⟩])
        s₃.mem s₈.mem := by
      rw [k₈.mem]
      refine ((ot.frame.mono fun r hr => List.mem_append_left _ hr).trans
        ((k₅.mem ▸ hf₆ : Frame _ s₄.mem s₆.mem).mono fun r hr => ?_)).trans (hf₇.mono fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; simp [hr]
      · simp only [List.mem_singleton] at hr; simp [hr]
    rw [blockAt_frame F₃₈ (fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
      · have := Lay.st_st (st := VG.Proof.AesGcm.Arm.oSt s₀ 6) (a := 48) (n := 16) (d := 0) (k := 48) (.inr (by decide)) (by decide)
          (by decide)
        rwa [add_ofNat_zero] at this
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact (L.stk_st (by decide)).symm
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩))]
    exact oa.cb
  have F₂₈ : Frame (VG.Proof.AesGcm.Arm.j0Frame (VG.Proof.AesGcm.Arm.oSt s₀ 6) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp ++ VG.Proof.AesGcm.Arm.otFrame (VG.Proof.AesGcm.Arm.oSt s₀ 6) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp 112 ++
      [⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 256, 16⟩, ⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 240, 16⟩])
      s₂.mem s₈.mem := by
    rw [k₈.mem]
    refine (((oa.frame.mono ?_).trans (ot.frame.mono ?_)).trans
      ((k₅.mem ▸ hf₆ : Frame _ s₄.mem s₆.mem).mono ?_)).trans (hf₇.mono ?_)
    all_goals intro r hr; simp only [List.mem_append]
    · exact .inl (.inl hr)
    · exact .inl (.inr hr)
    · simp only [List.mem_singleton] at hr; exact .inr (by simp [hr])
    · simp only [List.mem_singleton] at hr; exact .inr (by simp [hr])
  have sv₈ : VG.Proof.AesGcm.Arm.SavedAt s₈.mem (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀ := by
    refine h2.saved.frame F₂₈ fun r hr => ?_
    simp only [List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact VG.Proof.AesGcm.Arm.saved_j0Frame L r hr
    · exact VG.Proof.AesGcm.Arm.saved_otFrame h (.inr rfl) r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dW (by decide) (.inl (by decide))
      · exact dW (by decide) (.inl (by decide))
  have hX0 : (s₇.gpr .r0).toNat = 0 ↔ ¬X := by
    rw [h0₇]
    split
    · next hx => exact ⟨fun e => absurd e (by decide), fun e => absurd hx e⟩
    · next hx => exact ⟨fun _ => hx, fun _ => rfl⟩
  refine k s₈ ⟨by rw [h7₈]; exact he₈, hk₈, sv₈, hdat₈, hc₈, hcb₈, ?_, ?_⟩
  · rw [h7₈, h0₇]; exact ite_congr (propext hX) (fun _ => rfl) (fun _ => rfl)
  · rw [hz₈]; exact decide_eq_decide.mpr (hX0.trans (not_congr hX))

theorem open_good {s₀ s₂ : State} (ho : VG.Proof.AesGcm.Arm.openPreArm s₀) (h2 : VG.Proof.AesGcm.Arm.SO1 7 6 s₀ s₂)
    (hok : Spec.Gcm.tagLenOk (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat = true) :
    WP isa VG.Proof.AesGcm.Arm.openGood s₂ fun s => (∃ k7, Env (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ 6) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s) ∧
      VG.Proof.AesGcm.Arm.SavedAt s.mem (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀ ∧ VG.Proof.AesGcm.Arm.OpenPost s₀ s := by
  have h : VG.Proof.AesGcm.Arm.onePre 7 6 s₀ := openPreArm.one ho
  have L := VG.Proof.AesGcm.Arm.oneLay h
  refine VG.Proof.AesGcm.Arm.open_head ho h2 hok fun s₈ om => ?_
  -- the data decrypted only if the tags are equal
  have mid : WP isa (.ite .eq (.block []) oneCrypt) s₈ fun s₉ =>
      Env (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ 6) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp (s₈.gpr .r7) (s₀.gpr .r1) s₉ ∧ VG.Proof.AesGcm.Arm.SavedAt s₉.mem (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀ ∧
      (VG.Proof.AesGcm.Arm.openTagOk s₀ → bytesAt s₉.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat =
        gctr (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
          (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat)))
          (bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat)) ∧
      (¬VG.Proof.AesGcm.Arm.openTagOk s₀ → bytesAt s₉.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat =
        bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat) := by
    refine WP.ite _ (eval_eq' om.z) (fun ht => ?_) (fun hf => ?_)
    · have hx : ¬VG.Proof.AesGcm.Arm.openTagOk s₀ := of_decide_eq_true ht
      exact WP.block_nil ⟨om.env, om.saved, fun x => absurd x hx, fun _ => om.dat⟩
    · have hx : VG.Proof.AesGcm.Arm.openTagOk s₀ := Classical.not_not.mp (of_decide_eq_false hf)
      refine WP.mono (VG.Proof.AesGcm.Arm.oneCrypt_ok h (by decide) om.env om.args om.cb) fun s₉ oc => ?_
      exact ⟨oc.env, om.saved.frame oc.frame (VG.Proof.AesGcm.Arm.saved_crFrame L (VG.Proof.AesGcm.Arm.one_dataW h om.args 0 0)),
        fun _ => by rw [oc.out, om.ciph, om.dat], fun x => absurd hx x⟩
  refine WP.seq (WP.mono mid fun s₉ hh => ?_)
  obtain ⟨he₉, sv₉, hd₁, hd₂⟩ := hh
  refine WP.of_runBlock ⟨s₉.setReg .r0 (s₉.gpr .r7), by arun [], ⟨_, he₉.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl) rfl rfl rfl⟩, sv₉, ?_⟩
  have hres : VG.Proof.AesGcm.Arm.openRes s₀ = if VG.Proof.AesGcm.Arm.openTagOk s₀ then
      some (gctr (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat)
        (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat)))
        (bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2)) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat)) else none := by
    simp only [VG.Proof.AesGcm.Arm.openRes, openResult, hok, ite_true, decryptWith]
  have r0 : (s₉.setReg .r0 (s₉.gpr .r7)).gpr .r0 = if VG.Proof.AesGcm.Arm.openTagOk s₀ then 1 else 0 := by
    rw [gpr_setReg_self, he₉.r7, om.r7]
  by_cases e : VG.Proof.AesGcm.Arm.openTagOk s₀
  · exact VG.Proof.AesGcm.Arm.openPost_some (hres.trans (ite_eq_left_of_eq_true _ _ (eq_true e)))
      (r0.trans (ite_eq_left_of_eq_true _ _ (eq_true e))) (hd₁ e)
  · exact VG.Proof.AesGcm.Arm.openPost_none (hres.trans (ite_eq_right_of_eq_false _ _ (eq_false e)))
      (r0.trans (ite_eq_right_of_eq_false _ _ (eq_false e))) (hd₂ e)

theorem open_wp {s₀ : State} (h : openArm.pre s₀) :
    WP isa «open» s₀ fun s' => abiPreserved s₀ s' ∧ openArm.post s₀ s' := by
  have h' : VG.Proof.AesGcm.Arm.onePre 7 6 s₀ := openPreArm.one h
  have L := VG.Proof.AesGcm.Arm.oneLay h'
  have fW := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : VG.Proof.AesGcm.Arm.args s₀ 7 ∈ s₀.rd := h'.1.2.2.2
  refine WP.seq (WP.block_append (VG.Proof.AesGcm.Arm.one1_wp (wi := 6) h' (by decide) (by decide) fun s₁ h1 => ?_))
  obtain ⟨i5, v5⟩ := h1.args.at spf hin 5 (by decide) (show 4 * 5 = 20 from rfl)
  obtain ⟨s₂, run₂, h6₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [.ldrSp .r6 20] s₁ = some s₂ ∧
      s₂.gpr .r6 = BitVec.ofNat 32 (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat ∧ (∀ r, r ≠ .r6 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    refine ⟨_, by arun [i5, v5], ?_, ?_, ?_⟩
    · simp [gpr_setReg, v5]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.tagLenOk_ok h6₂ (VG.Proof.AesGcm.Arm.arg s₀ 5).isLt) fun s₃ ⟨hz₃, g₃, k₃⟩ => ?_)
  have h3 : VG.Proof.AesGcm.Arm.SO1 7 6 s₀ s₃ := (h1.keep (fun r a b => g₂ r b) k₂).keep (fun r a b => g₃ r a) k₃
  have mid : WP isa (.ite .eq (.block [.mov .r0 (imm 0)]) VG.Proof.AesGcm.Arm.openGood) s₃ fun s =>
      (∃ k7, Env (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ 6) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s) ∧
      VG.Proof.AesGcm.Arm.SavedAt s.mem (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀ ∧ VG.Proof.AesGcm.Arm.OpenPost s₀ s := by
    refine WP.ite _ (eval_eq' hz₃) (fun ht => ?_) (fun hf => VG.Proof.AesGcm.Arm.open_good h h3 (by simpa using hf))
    have hbad : Spec.Gcm.tagLenOk (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat = false := by simpa using ht
    refine WP.of_runBlock ⟨s₃.setReg .r0 (BitVec.ofNat 32 0), by arun [], ⟨_, h3.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl) rfl rfl rfl⟩, h3.saved, ?_⟩
    refine VG.Proof.AesGcm.Arm.openPost_none (by simp only [VG.Proof.AesGcm.Arm.openRes, openResult, hbad]; rfl) (by simp [gpr_setReg]) ?_
    show bytesAt s₃.mem _ _ = _
    exact bytesAt_frame h3.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact h'.2.2.2.2.2.2.2.2.1.sub_right (Lay.wSub (by decide))) (by omega)
  refine WP.seq (WP.mono mid fun s₄ hh => ?_)
  obtain ⟨⟨k7, he⟩, sv, op⟩ := hh
  refine WP.mono (VG.Proof.AesGcm.Arm.restore_ok he.r11 fW (covers_left he.perm.w) sv he.sp) fun s' hh => ⟨hh.1, ?_⟩
  have e : VG.Proof.AesGcm.Arm.OpenPost s₀ s' := by
    unfold VG.Proof.AesGcm.Arm.OpenPost at op ⊢; rw [hh.2.1, hh.2.2.1]; exact op
  exact e

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.CTBase`. -/
section

/-!
# AES-GCM on ARMv7: constant time, the combinators

Untrusted: everything here is checked by Lean. `CT I c`: two runs of `c` from
states that both satisfy `I` leak the same. The invariants `I` fix what is
public (pointers, lengths, rounds) as parameters and leave the secrets
(memory, the values the state represents) existential, so that the
correctness lemmas, applied to each run, give the invariant of the next
piece (`CT.seq`). Branches are on flags the invariants fix (`CT.ite`);
blocks are checked by the taint analysis from registers the invariants fix
(`CT.taint`, and `CT.argTaint` for blocks that read stack arguments); the
calls are constant time by their own proofs, with the same arguments in both
runs (`CT.gh`, `CT.ctr`).
-/

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Impl.AesGcm.Arm

/-- Both runs satisfy `I`. -/
abbrev Both (I : State → Prop) : State → State → Prop := fun s₁ s₂ => I s₁ ∧ I s₂

/-- Two runs from states satisfying `I` leak the same. -/
abbrev CT (I : State → Prop) (c : Prog isa) : Prop := RelCT isa (VG.Proof.AesGcm.Arm.Both I) c fun _ _ => True

namespace CT

theorem mono {I J : State → Prop} {c : Prog isa} (h : VG.Proof.AesGcm.Arm.CT I c) (hi : ∀ s, J s → I s) : VG.Proof.AesGcm.Arm.CT J c :=
  RelCT.mono h (fun _ _ hh => ⟨hi _ hh.1, hi _ hh.2⟩) fun _ _ _ => trivial

theorem seq {I J : State → Prop} {c₁ c₂ : Prog isa} (h₁ : VG.Proof.AesGcm.Arm.CT I c₁) (w : ∀ s, I s → WP isa c₁ s J)
    (h₂ : VG.Proof.AesGcm.Arm.CT J c₂) : VG.Proof.AesGcm.Arm.CT I (.seq c₁ c₂) :=
  (rel_wp (F := I) (F' := I) h₁ w w).seq h₂

theorem ite {I : State → Prop} {t e : Prog isa} (b : Bool) (hz : ∀ s, I s → s.z = b)
    (ht : b = true → VG.Proof.AesGcm.Arm.CT I t) (he : b = false → VG.Proof.AesGcm.Arm.CT I e) : VG.Proof.AesGcm.Arm.CT I (.ite .eq t e) := by
  have ev : ∀ s, I s → isa.eval .eq s = some b := fun s hs => eval_eq' (hz s hs)
  refine RelCT.ite (fun _ _ h => by rw [ev _ h.1, ev _ h.2]) ?_ ?_
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hp, hc⟩ e₁ e₂
    rw [ev _ hp.1] at hc
    exact ht (Option.some.inj hc) _ _ _ _ _ _ hp e₁ e₂
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hp, hc⟩ e₁ e₂
    rw [ev _ hp.1] at hc
    exact he (Option.some.inj hc) _ _ _ _ _ _ hp e₁ e₂

theorem taint {I : State → Prop} {c : Prog isa} (rs : List Reg)
    (hp : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) {h : Taint.Hint VG.Arm.Taint.T}
    (hc : (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs rs) c h).isSome = true) : VG.Proof.AesGcm.Arm.CT I c :=
  RelCT.taint (A := VG.Arm.taint) _ (fun _ _ hh => Taint.agree_ofRegs (hp _ _ hh.1 hh.2)) hc

/-- A block, with the stack arguments: `n` bytes of them, the same in both runs and apart
from the writable regions. -/
theorem argTaint {I : State → Prop} {c : Prog isa} (rs : List Reg) (n : Nat)
    (hp : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hsp : ∀ s₁ s₂, I s₁ → I s₂ → s₁.sp = s₂.sp)
    (hw : ∀ s, I s → s.sp.toNat + n ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, n⟩ r)
    (hm : ∀ s₁ s₂, I s₁ → I s₂ → ∀ k < n, s₁.mem (VG.Arm.Taint.argByte s₁ k) = s₂.mem (VG.Arm.Taint.argByte s₂ k))
    {h : Taint.Hint VG.Arm.Taint.T}
    (hc : (VG.Taint.check VG.Arm.taint (VG.Arm.argTaint rs n) c h).isSome = true) : VG.Proof.AesGcm.Arm.CT I c :=
  RelCT.taint (A := VG.Arm.taint) _ (fun _ _ hh => agree_argTaint (hp _ _ hh.1 hh.2) (hsp _ _ hh.1 hh.2)
    (hw _ hh.1) (hw _ hh.2) (hm _ _ hh.1 hh.2)) hc

theorem skip {I : State → Prop} : VG.Proof.AesGcm.Arm.CT I (.block []) :=
  VG.Proof.AesGcm.Arm.CT.taint [] (fun _ _ _ _ _ h => by simp at h) (h := .block []) rfl

theorem gh {I : State → Prop}
    (h : ∀ s₁ s₂, I s₁ → I s₂ → ∃ H Y D S : BitVec 32, ∃ n : Nat,
      GhCall s₁ H Y D S n ∧ GhCall s₂ H Y D S n ∧ s₁.sp = s₂.sp) : VG.Proof.AesGcm.Arm.CT I ghFrame :=
  gh_rel fun _ _ hh => h _ _ hh.1 hh.2

theorem ctr {I : State → Prop}
    (h : ∀ s₁ s₂, I s₁ → I s₂ → ∃ K C D S : BitVec 32, ∃ R n : Nat,
      CtrCall s₁ K C D S R n ∧ CtrCall s₂ K C D S R n ∧ s₁.sp = s₂.sp) : VG.Proof.AesGcm.Arm.CT I ctrFrame :=
  ctr_rel fun _ _ hh => h _ _ hh.1 hh.2

end CT

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.CTAbsorb`. -/
section

/-!
# AES-GCM on ARMv7: `ghash1`, `absorb`, `flush` and `lens` are constant time

Untrusted: everything here is checked by Lean. The invariants fix the
context, the state, `W`, the stack pointer, the data's address and length and
the number of bytes absorbed so far modulo 16, and leave the rest
existential.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

theorem Env.pin {c st w sp a b a' b' : BitVec 32} {s₁ s₂ : State} (h₁ : Env c st w sp a b s₁)
    (h₂ : Env c st w sp a' b' s₂) {r : Reg} (hr : r = .r9 ∨ r = .r10 ∨ r = .r11) : s₁.gpr r = s₂.gpr r := by
  rcases hr with rfl | rfl | rfl
  · rw [h₁.r9, h₂.r9]
  · rw [h₁.r10, h₂.r10]
  · rw [h₁.r11, h₂.r11]

/-- Before `ghash1 yo b o`, for the block at `P`. -/
structure GhIn (c st w sp : BitVec 32) (b : Reg) (o : Nat) (P : BitVec 32) (s : State) : Prop where
  env : ∃ k7 k8, Env c st w sp k7 k8 s
  hP : s.gpr b + BitVec.ofNat 32 o = P
  hpr : Covers [⟨State.addr P, 16⟩] (s.rd ++ s.wr)

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp)
include L

theorem ghash1_ct {yo : Nat} (hyo : yo = 0 ∨ yo = 16) {b : Reg} {o : Nat}
    (hbo : (b = .r10 ∧ o = 32) ∨ (b = .r11 ∧ o = 96)) {P : BitVec 32} (hfit : P.toNat + 16 ≤ 2 ^ 32)
    (hpy : (⟨State.addr st + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨State.addr P, 16⟩)
    (hpw : (⟨State.addr P, 16⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 512, 256⟩)
    (hpk : (below sp).Disjoint ⟨State.addr P, 16⟩) :
    VG.Proof.AesGcm.Arm.CT (VG.Proof.AesGcm.Arm.GhIn c st w sp b o P) (ghash1 yo b o) := by
  have hb : b = .r10 ∨ b = .r11 := by rcases hbo with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have he : encodable (BitVec.ofNat 32 o) = true := by rcases hbo with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  have hey : encodable (BitVec.ofNat 32 yo) = true := by rcases hyo with rfl | rfl <;> decide
  let J : State → Prop := fun s => GhCall s (c + BitVec.ofNat 32 240) (st + BitVec.ofNat 32 yo) P
    (w + BitVec.ofNat 32 512) 1 ∧ s.sp = sp
  refine CT.seq (J := J) ?_ (fun s ⟨⟨k7, k8, hs⟩, hP, hpr⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r9, .r10, .r11])
        (.block [addI .r0 .r9 240, addI .r1 .r10 yo, addI .r2 b o, .mov .r3 (imm 1), addI .r12 .r11 scrO]) h).isSome =
        true := by
      rcases hyo with rfl | rfl <;> rcases hbo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨_, by taint_decide⟩
    exact CT.taint [.r9, .r10, .r11] (fun s₁ s₂ ⟨⟨_, _, h₁⟩, _, _⟩ ⟨⟨_, _, h₂⟩, _, _⟩ r hr => h₁.pin h₂ (by simpa using hr))
      hc
  · obtain ⟨s₁, run₁, h0, h1, h2, h3, h12, hkeep, hk⟩ := ghArgs_ok hs yo b o hb hey he
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    have he₁ : Env c st w sp k7 k8 s₁ := hs.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hkeep _ (by decide) (by decide) (by decide) (by decide)
        (by decide)) hk.sp hk.rd hk.wr
    exact ⟨ghCall_mk L hyo he₁ h0 h1 (by rw [h2, hP]) h3 h12 (by omega) (by simpa using hpy) (by simpa using hpw)
      (by simpa using hpk) (by rw [hk.rd, hk.wr]; simpa using hpr), he₁.sp⟩
  · exact CT.gh fun s₁ s₂ h₁ h₂ => ⟨_, _, _, _, _, h₁.1, h₂.1, h₁.2.trans h₂.2.symm⟩

end

/-- Before `absorb yo`: `q` bytes in the buffer. -/
def AbsI (c st w sp : BitVec 32) (yo : Nat) (D : BitVec 32) (n q : Nat) (s : State) : Prop :=
  ∃ k7 k8 H x, x.length % 16 = q ∧ AbsIn c st w sp k7 k8 yo H x D n s

/-- Part of the way, `j` bytes absorbed. -/
def MidI (c st w sp : BitVec 32) (yo : Nat) (D : BitVec 32) (n q j : Nat) (s : State) : Prop :=
  ∃ k7 k8 H x m₀, x.length % 16 = q ∧ AbsMid c st w sp k7 k8 yo H x D n m₀ j s

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

theorem absorbHead_ct {D : BitVec 32} {n q : Nat} (hn : n ≠ 0) (hq : q ≠ 0) :
    VG.Proof.AesGcm.Arm.CT (VG.Proof.AesGcm.Arm.AbsI c st w sp yo D n q) (absorbHead yo) := by
  let J : State → Prop := fun s => ∃ k7 k8 H x m₀ k, x.length % 16 = q ∧ HeadMid c st w sp k7 k8 yo H x D n m₀ k s
  refine CT.seq (J := J) ?_ (fun s ⟨k7, k8, H, x, hx, hs⟩ => WP.mono (headPre_ok L hyo hs hn (by omega))
    fun s' ⟨k, hm⟩ => ⟨k7, k8, H, x, s.mem, k, hx, hm⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5, .r6, .r10]) headPre h).isSome =
        true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, x₁, hx₁, h₁⟩ ⟨_, _, _, x₂, hx₂, h₂⟩ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.r4, h₂.r4]
    · rw [h₁.r5, h₂.r5]
    · rw [h₁.r6, h₂.r6, hx₁, hx₂]
    · exact h₁.env.pin h₂.env (by simp)
  · refine CT.ite (decide (q + min (16 - q) n = 16)) (fun s ⟨_, _, _, _, _, _, hx, hm⟩ => by
      rw [hm.z, hm.kmin, hx]) (fun _ => ?_) (fun _ => CT.skip)
    have eB := L.stA (d := 32) (by decide)
    have hf : (st + BitVec.ofNat 32 32).toNat + 16 ≤ 2 ^ 32 := by rw [L.stN (by decide)]; have := L.sw; omega
    refine (VG.Proof.AesGcm.Arm.ghash1_ct L hyo (.inl ⟨rfl, rfl⟩) (P := st + BitVec.ofNat 32 32) hf ?_ ?_ ?_).mono
      fun s ⟨k7, k8, _, _, _, _, _, hm⟩ => ⟨⟨k7, k8, hm.env⟩, by rw [hm.env.r10], ?_⟩
    · rw [eB]; exact Lay.st_st (.inl (by omega)) (by omega) (by decide)
    · rw [eB]; exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
    · rw [eB]; exact L.stk_st (by decide)
    · rw [eB]; exact covers_left (hm.env.perm.stC (by decide))

theorem absorbFill_ct {D : BitVec 32} {n q : Nat} (hn : n ≠ 0) (hq : q < 16) :
    VG.Proof.AesGcm.Arm.CT (VG.Proof.AesGcm.Arm.AbsI c st w sp yo D n q) (absorbFill yo) := by
  refine CT.seq (J := fun s => VG.Proof.AesGcm.Arm.AbsI c st w sp yo D n q s ∧ s.z = decide (q = 0)) ?_
    (fun s ⟨k7, k8, H, x, hx, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r6]) (.block [.cmp .r6 (imm 0)]) h).isSome =
        true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, x₁, hx₁, h₁⟩ ⟨_, _, _, x₂, hx₂, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r6, h₂.r6, hx₁, hx₂]) hc
  · obtain ⟨s₂, run₂, hz₂, hg₂, hm₂, hrd₂, hwr₂, hsp₂⟩ := cmp0_ok s .r6 hs.r6 (by omega)
    exact WP.of_runBlock ⟨s₂, run₂, ⟨k7, k8, H, x, hx, hs.keep hg₂ ⟨hm₂, hrd₂, hwr₂, hsp₂⟩⟩, by rw [hz₂, hx]⟩
  · exact CT.ite (decide (q = 0)) (fun s h => h.2) (fun _ => CT.skip) fun hb =>
      (VG.Proof.AesGcm.Arm.absorbHead_ct L hyo hn (by simpa using hb)).mono fun s h => h.1

theorem absorbWhole_ct {D : BitVec 32} {n q j : Nat} : VG.Proof.AesGcm.Arm.CT (VG.Proof.AesGcm.Arm.MidI c st w sp yo D n q j) (absorbWhole yo) := by
  let nb := (n - j) / 16
  let J₁ : State → Prop := fun s => ∃ k7 k8, Env c st w sp k7 k8 s ∧ DataOk st w sp s D n ∧ j ≤ n ∧
    s.gpr .r2 = D + BitVec.ofNat 32 j ∧ s.gpr .r3 = BitVec.ofNat 32 nb ∧ s.z = decide (nb = 0)
  refine CT.seq (J := J₁) ?_ (fun s ⟨k7, k8, H, x, m₀, hx, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5]) (.block splitWhole) h).isSome =
        true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, _, h₂⟩ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.r4, h₂.r4]
    · rw [h₁.r5, h₂.r5]
  · obtain ⟨s₁, run₁, h2, h3, -, -, hz, hg₁, hk₁⟩ := split_ok hs.le hs.data.lt32 hs.r4 hs.r5
    refine WP.of_runBlock ⟨s₁, run₁, k7, k8, hs.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) hk₁.sp hk₁.rd hk₁.wr, hs.data.of_eq hk₁.rd hk₁.wr, hs.le, h2, h3, hz⟩
  · refine CT.ite (decide (nb = 0)) (fun s h => by obtain ⟨_, _, _, _, _, _, _, hz⟩ := h; exact hz)
      (fun _ => CT.skip) fun hb => ?_
    have h0 : nb ≠ 0 := by simpa using hb
    let J₂ : State → Prop := fun s => ∃ k7 k8, Env c st w sp k7 k8 s ∧ DataOk st w sp s D n ∧ j ≤ n ∧
      s.gpr .r0 = c + BitVec.ofNat 32 240 ∧ s.gpr .r1 = st + BitVec.ofNat 32 yo ∧
      s.gpr .r2 = D + BitVec.ofNat 32 j ∧ s.gpr .r3 = BitVec.ofNat 32 nb ∧ s.gpr .r12 = w + BitVec.ofNat 32 512
    refine CT.seq (J := J₂) ?_ (fun s ⟨k7, k8, he, hd, hj, h2, h3, _⟩ => ?_) ?_
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r9, .r10, .r11])
          (.block [addI .r0 .r9 240, addI .r1 .r10 yo, addI .r12 .r11 scrO]) h).isSome = true := by
        rcases hyo with rfl | rfl <;> exact ⟨_, by taint_decide⟩
      exact CT.taint _ (fun s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => h₁.pin h₂ (by simpa using hr)) hc
    · have h9 := he.r9; have h10 := he.r10; have h11 := he.r11
      have ey : encodable (BitVec.ofNat 32 yo) = true := by rcases hyo with rfl | rfl <;> decide
      refine WP.of_runBlock ⟨((s.setReg .r0 (s.gpr .r9 + BitVec.ofNat 32 240)).setReg .r1
        (s.gpr .r10 + BitVec.ofNat 32 yo)).setReg .r12 (s.gpr .r11 + BitVec.ofNat 32 512), by arun [ey], k7, k8, he.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hd.of_eq rfl rfl, hj, ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, h9]
      · simp [gpr_setReg, h10]
      · simp [gpr_setReg, h2]
      · simp [gpr_setReg, h3]
      · simp [gpr_setReg, h11]
    · refine CT.gh fun s₁ s₂ ⟨_, _, he₁, hd₁, hj₁, a0, a1, a2, a3, a12⟩ ⟨_, _, he₂, hd₂, hj₂, b0, b1, b2, b3, b12⟩ => ?_
      have hdj₁ := hd₁.sub (j := j) (k := 16 * nb) (by omega) (by omega)
      have hdj₂ := hd₂.sub (j := j) (k := 16 * nb) (by omega) (by omega)
      exact ⟨_, _, _, _, _, ghCall_mk L hyo he₁ a0 a1 a2 a3 a12 (by have := hdj₁.fit; omega)
        (hdj₁.st.sub_right (Lay.stSub (by omega))).symm (hdj₁.w.sub_right (Lay.wSub (by decide))) hdj₁.stk hdj₁.rd,
        ghCall_mk L hyo he₂ b0 b1 b2 b3 b12 (by have := hdj₂.fit; omega)
        (hdj₂.st.sub_right (Lay.stSub (by omega))).symm (hdj₂.w.sub_right (Lay.wSub (by decide))) hdj₂.stk hdj₂.rd,
        he₁.sp.trans he₂.sp.symm⟩

omit L hyo in
theorem absorbTail_ct {D : BitVec 32} {n q j : Nat} : VG.Proof.AesGcm.Arm.CT (VG.Proof.AesGcm.Arm.MidI c st w sp yo D n q j) absorbTail := by
  obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5, .r10]) absorbTail h).isSome =
      true := ⟨_, by taint_decide⟩
  refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, _, h₂⟩ r hr => ?_) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h₁.r4, h₂.r4]
  · rw [h₁.r5, h₂.r5]
  · exact h₁.env.pin h₂.env (by simp)

theorem absorb_ct {D : BitVec 32} {n q : Nat} (hq : q < 16) : VG.Proof.AesGcm.Arm.CT (VG.Proof.AesGcm.Arm.AbsI c st w sp yo D n q) (absorb yo) := by
  refine CT.seq (J := fun s => VG.Proof.AesGcm.Arm.AbsI c st w sp yo D n q s ∧ s.z = decide (n = 0)) ?_
    (fun s ⟨k7, k8, H, x, hx, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5]) (.block [.cmp .r5 (imm 0)]) h).isSome =
        true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r5, h₂.r5]) hc
  · obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r5 hs.r5 hs.data.lt32
    exact WP.of_runBlock ⟨s₁, run₁, ⟨k7, k8, H, x, hx, hs.keep hg₁ ⟨hm₁, hrd₁, hwr₁, hsp₁⟩⟩, hz⟩
  refine CT.ite (decide (n = 0)) (fun s h => h.2) (fun _ => CT.skip) fun hb => ?_
  have h0 : n ≠ 0 := by simpa using hb
  let j₁ := if q = 0 then 0 else min (16 - q) n
  refine CT.seq (J := VG.Proof.AesGcm.Arm.MidI c st w sp yo D n q j₁) ((VG.Proof.AesGcm.Arm.absorbFill_ct L hyo h0 hq).mono fun s h => h.1)
    (fun s ⟨⟨k7, k8, H, x, hx, hs⟩, _⟩ => WP.mono (absorbFill_ok L hyo hs h0) fun s' ⟨j, hj, hm⟩ =>
      ⟨k7, k8, H, x, s.mem, hx, by rw [hj, hx] at hm; exact hm⟩) ?_
  refine CT.seq (J := VG.Proof.AesGcm.Arm.MidI c st w sp yo D n q (j₁ + 16 * ((n - j₁) / 16))) (VG.Proof.AesGcm.Arm.absorbWhole_ct L hyo)
    (fun s ⟨k7, k8, H, x, m₀, hx, hs⟩ => WP.mono (whole_ok L hyo hs (hs.data_eq hyo)) fun s' ⟨j, hj, hm, _⟩ =>
      ⟨k7, k8, H, x, m₀, hx, by rw [hj] at hm; exact hm⟩) VG.Proof.AesGcm.Arm.absorbTail_ct

/-- `ghash1 yo .r11 96`, of `T`. -/
theorem ghT_ct : VG.Proof.AesGcm.Arm.CT (VG.Proof.AesGcm.Arm.GhIn c st w sp .r11 96 (w + BitVec.ofNat 32 96)) (ghash1 yo .r11 tO) := by
  have eT := L.wA (d := 96) (by decide)
  have hf : (w + BitVec.ofNat 32 96).toNat + 16 ≤ 2 ^ 32 := by rw [L.wN (by decide)]; have := L.ww; omega
  refine VG.Proof.AesGcm.Arm.ghash1_ct L hyo (.inr ⟨rfl, rfl⟩) hf ?_ ?_ ?_
  · rw [eT]; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · rw [eT]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · rw [eT]; exact L.stk_w (by decide)

omit hyo in
theorem ghIn_T {s : State} {k7 k8 : BitVec 32} (he : Env c st w sp k7 k8 s) :
    VG.Proof.AesGcm.Arm.GhIn c st w sp .r11 96 (w + BitVec.ofNat 32 96) s :=
  ⟨⟨k7, k8, he⟩, by rw [he.r11], by rw [L.wA (d := 96) (by decide)]; exact covers_left (he.perm.wC (by decide))⟩

/-- Before `flush yo`: `q` buffered bytes. -/
theorem flush_ct {q : Nat} (hq : q < 16) :
    VG.Proof.AesGcm.Arm.CT (fun s => ∃ k7 k8, Env c st w sp k7 k8 s ∧ s.gpr .r6 = BitVec.ofNat 32 q) (flush yo) := by
  refine CT.seq (J := fun s => (∃ k7 k8, Env c st w sp k7 k8 s ∧ s.gpr .r6 = BitVec.ofNat 32 q) ∧
    s.z = decide (q = 0)) ?_ (fun s ⟨k7, k8, he, h6⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r6]) (.block [.cmp .r6 (imm 0)]) h).isSome =
        true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) hc
  · obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r6 h6 (by omega)
    exact WP.of_runBlock ⟨s₁, run₁, ⟨k7, k8, he.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁, by rw [hg₁, h6]⟩, hz⟩
  refine CT.ite (decide (q = 0)) (fun s h => h.2) (fun _ => CT.skip) fun hb => ?_
  have h0 : q ≠ 0 := by simpa using hb
  refine CT.seq (J := VG.Proof.AesGcm.Arm.GhIn c st w sp .r11 96 (w + BitVec.ofNat 32 96)) ?_ (fun s ⟨⟨k7, k8, he, h6⟩, _⟩ =>
    WP.mono (flushCopy_ok L hyo (H := blockAt s.mem (State.addr c + BitVec.ofNat 64 240)) ⟨he, rfl⟩ h6 hq h0)
      fun s' hm => VG.Proof.AesGcm.Arm.ghIn_T L hm.env) (VG.Proof.AesGcm.Arm.ghT_ct L hyo)
  obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r6, .r10, .r11])
      (.seq (.block flushPre) copyLoop) h).isSome = true := ⟨_, by taint_decide⟩
  refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, h₁, a₁⟩, _⟩ ⟨⟨_, _, h₂, a₂⟩, _⟩ r hr => ?_) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a₁, a₂]
  · exact h₁.pin h₂ (by simp)
  · exact h₁.pin h₂ (by simp)

/-- `lens yo`: the lengths are not needed, only `W`. -/
theorem lens_ct : VG.Proof.AesGcm.Arm.CT (fun s => ∃ k7 k8, Env c st w sp k7 k8 s) (lens yo) := by
  refine CT.seq (J := VG.Proof.AesGcm.Arm.GhIn c st w sp .r11 96 (w + BitVec.ofNat 32 96)) ?_ (fun s ⟨k7, k8, he⟩ =>
    WP.mono (lensStore_ok L he) fun s' ⟨_, hg, hrd, hwr, hsp⟩ => VG.Proof.AesGcm.Arm.ghIn_T L (k7 := k7) (k8 := k8)
      (he.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide)) hsp hrd hwr)) (VG.Proof.AesGcm.Arm.ghT_ct L hyo)
  obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r11])
      (.block (be64Store .r4 .r5 tO ++ be64Store .r6 .r7 (tO + 8))) h).isSome = true := ⟨_, by taint_decide⟩
  exact CT.taint _ (fun s₁ s₂ ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr => h₁.pin h₂ (by simp at hr; simp [hr])) hc

end

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.CTCrypt`. -/
section

/-!
# AES-GCM on ARMv7: `crypt` and `tag` are constant time

Untrusted: everything here is checked by Lean. The invariants fix the
context, the state, `W`, the stack pointer, the number of rounds (in `r8`),
the data's address and length, and the length of the text so far modulo 16.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- Before `crypt`. -/
def CrI (c st w sp k8 : BitVec 32) (R : Nat) (D : BitVec 32) (n q : Nat) (s : State) : Prop :=
  ∃ k7 icb P, P % 16 = q ∧ CrIn c st w sp k7 k8 R icb P D n s

/-- Part of the way: `j` bytes done. -/
def CrM (c st w sp k8 : BitVec 32) (R : Nat) (D : BitVec 32) (n q j : Nat) (s : State) : Prop :=
  ∃ k7 icb P m₀, P % 16 = q ∧ CrMid c st w sp k7 k8 R icb P D n m₀ j s

theorem pin8 {c st w sp a b a' b' : BitVec 32} {s₁ s₂ : State} (h₁ : Env c st w sp a b s₁)
    (h₂ : Env c st w sp a' b' s₂) {R : Nat} (e₁ : s₁.gpr .r8 = BitVec.ofNat 32 R) (e₂ : s₂.gpr .r8 = BitVec.ofNat 32 R)
    {r : Reg} (hr : r = .r8 ∨ r = .r9 ∨ r = .r10 ∨ r = .r11) : s₁.gpr r = s₂.gpr r := by
  rcases hr with rfl | hr
  · rw [e₁, e₂]
  · exact h₁.pin h₂ hr

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp)
include L

theorem cryptWhole_ct {k8 : BitVec 32} {R : Nat} {D : BitVec 32} {n q j : Nat} :
    VG.Proof.AesGcm.Arm.CT (VG.Proof.AesGcm.Arm.CrM c st w sp k8 R D n q j) cryptWhole := by
  let nb := (n - j) / 16
  let J₁ : State → Prop := fun s => ∃ k7, Env c st w sp k7 k8 s ∧ DataW c st w sp k7 k8 s D n ∧ j ≤ n ∧
    s.gpr .r8 = BitVec.ofNat 32 R ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧
    s.gpr .r3 = D + BitVec.ofNat 32 j ∧ s.gpr .r12 = BitVec.ofNat 32 nb ∧ s.z = decide (nb = 0)
  refine CT.seq (J := J₁) ?_ (fun s ⟨k7, icb, P, m₀, hP, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5]) (.block splitCtr) h).isSome =
        true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, h₂⟩ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.r4, h₂.r4]
    · rw [h₁.r5, h₂.r5]
  · obtain ⟨s₁, run₁, h3, h12, -, -, hz, hg₁, hk₁⟩ := splitCtr_ok hs.le hs.data.ok.lt32 hs.r4 hs.r5
    refine WP.of_runBlock ⟨s₁, run₁, k7, hs.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) hk₁.sp hk₁.rd hk₁.wr, hs.data.of_eq hk₁.rd hk₁.wr, hs.le,
      by rw [hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hs.r8], hs.rounds,
      h3, h12, hz⟩
  · refine CT.ite (decide (nb = 0)) (fun s h => by obtain ⟨_, _, _, _, _, _, _, _, hz⟩ := h; exact hz)
      (fun _ => CT.skip) fun hb => ?_
    have h0 : nb ≠ 0 := by simpa using hb
    let J₂ : State → Prop := fun s => ∃ k7, Env c st w sp k7 k8 s ∧ DataW c st w sp k7 k8 s D n ∧ j ≤ n ∧
      (R = 10 ∨ R = 12 ∨ R = 14) ∧ s.gpr .r0 = c ∧ s.gpr .r1 = BitVec.ofNat 32 R ∧
      s.gpr .r2 = st + BitVec.ofNat 32 48 ∧ s.gpr .r3 = D + BitVec.ofNat 32 j ∧
      s.gpr .r12 = BitVec.ofNat 32 nb ∧ s.gpr .lr = w + BitVec.ofNat 32 512
    refine CT.seq (J := J₂) ?_ (fun s ⟨k7, he, hd, hj, h8, hR, h3, h12, _⟩ => ?_) ?_
    · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r8, .r9, .r10, .r11])
          (.block [.mov .r0 (.reg .r9), .mov .r1 (.reg .r8), addI .r2 .r10 48, addI .lr .r11 scrO]) h).isSome =
          true := ⟨_, by taint_decide⟩
      exact CT.taint _ (fun s₁ s₂ ⟨_, h₁, _, _, e₁, _⟩ ⟨_, h₂, _, _, e₂, _⟩ r hr => VG.Proof.AesGcm.Arm.pin8 h₁ h₂ e₁ e₂ (by simpa using hr)) hc
    · obtain ⟨s₂, run₂, h0', h1', h2', hlr', hg₂, hk₂⟩ := wholeArgs_ok he
      refine WP.of_runBlock ⟨s₂, run₂, k7, he.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide) (by decide))
        hk₂.sp hk₂.rd hk₂.wr, hd.of_eq hk₂.rd hk₂.wr, hj, hR, h0', by rw [h1', h8], h2',
        by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h3],
        by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h12], hlr'⟩
    · refine CT.ctr fun s₁ s₂ ⟨_, he₁, hd₁, hj₁, hR, a0, a1, a2, a3, a12, alr⟩
        ⟨_, he₂, hd₂, _, _, b0, b1, b2, b3, b12, blr⟩ => ?_
      exact ⟨_, _, _, _, _, _, ctrWhole_mk L he₁ a0 a1 a2 a3 a12 alr hR (hd₁.sub (by omega) (by omega)),
        ctrWhole_mk L he₂ b0 b1 b2 b3 b12 blr hR (hd₂.sub (by omega) (by omega)), he₁.sp.trans he₂.sp.symm⟩

theorem cryptTail_ct {k8 : BitVec 32} {R : Nat} {D : BitVec 32} {n q j : Nat} :
    VG.Proof.AesGcm.Arm.CT (VG.Proof.AesGcm.Arm.CrM c st w sp k8 R D n q j) cryptTail := by
  refine CT.seq (J := fun s => VG.Proof.AesGcm.Arm.CrM c st w sp k8 R D n q j s ∧ s.z = decide (n - j = 0)) ?_
    (fun s ⟨k7, icb, P, m₀, hP, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5]) (.block [.cmp .r5 (imm 0)]) h).isSome =
        true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r5, h₂.r5]) hc
  · obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r5 hs.r5 (by have := hs.data.ok.lt32; omega)
    refine WP.of_runBlock ⟨s₁, run₁, ⟨k7, icb, P, m₀, hP, ?_⟩, hz⟩
    exact ⟨hs.env.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁, hs.le, by rw [hg₁, hs.r4], by rw [hg₁, hs.r5],
      by rw [hg₁, hs.r8], hs.rounds, hs.data.of_eq hrd₁ hwr₁, fun h => by rw [hm₁]; exact hs.ctr h,
      fun h => by rw [hm₁]; exact hs.done h, by rw [hm₁]; exact hs.rest, hs.whole, by rw [hm₁]; exact hs.frame⟩
  refine CT.ite (decide (n - j = 0)) (fun s h => h.2) (fun _ => CT.skip) fun _ => ?_
  let J₁ : State → Prop := fun s => ∃ k7, Env c st w sp k7 k8 s ∧ (R = 10 ∨ R = 12 ∨ R = 14) ∧ s.gpr .r0 = c ∧
    s.gpr .r1 = BitVec.ofNat 32 R ∧ s.gpr .r2 = st + BitVec.ofNat 32 48 ∧ s.gpr .r3 = st + BitVec.ofNat 32 64 ∧
    s.gpr .r12 = BitVec.ofNat 32 1 ∧ s.gpr .lr = w + BitVec.ofNat 32 512
  let J₂ : State → Prop := fun s => ∃ k7 icb P m₀ s₀, TailKs c st w sp k7 k8 R icb P D n m₀ j s₀ s
  refine CT.seq (J := J₂) (CT.seq (J := J₁) ?_ (fun s ⟨⟨k7, icb, P, m₀, hP, hs⟩, _⟩ => ?_) ?_)
    (fun s ⟨⟨k7, icb, P, m₀, hP, hs⟩, _⟩ => WP.mono (tailKs_ok L hs (hs.ciph L)) fun s' h => ⟨k7, icb, P, m₀, s, h⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r8, .r9, .r10, .r11]) (.block tailArgs)
        h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, _, _, h₁⟩, _⟩ ⟨⟨_, _, _, _, _, h₂⟩, _⟩ r hr =>
      VG.Proof.AesGcm.Arm.pin8 h₁.env h₂.env h₁.r8 h₂.r8 (by simpa using hr)) hc
  · obtain ⟨s₂, run₂, -, h0, h1, h2, h3, h12, hlr, hg₂, hrd₂, hwr₂, hsp₂⟩ := tailArgs_ok L hs.env
    exact WP.of_runBlock ⟨s₂, run₂, k7, hs.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        exact hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hsp₂ hrd₂ hwr₂,
      hs.rounds, h0, by rw [h1, hs.r8], h2, h3, h12, hlr⟩
  · exact CT.ctr fun s₁ s₂ ⟨_, he₁, hR, a0, a1, a2, a3, a12, alr⟩ ⟨_, he₂, _, b0, b1, b2, b3, b12, blr⟩ =>
      ⟨_, _, _, _, _, _, ctrTail_mk L he₁ a0 a1 a2 a3 a12 alr hR, ctrTail_mk L he₂ b0 b1 b2 b3 b12 blr hR,
        he₁.sp.trans he₂.sp.symm⟩
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5, .r10])
        (.seq (.block [addI .r1 .r10 64, .mov .r2 (.reg .r4), .mov .r3 (.reg .r5)]) xorLoop) h).isSome = true :=
      ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, h₂⟩ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.r4, h₂.r4]
    · rw [h₁.r5, h₂.r5]
    · exact h₁.env.pin h₂.env (by simp)

theorem crypt_ct {k8 : BitVec 32} {R : Nat} {D : BitVec 32} {n q : Nat} :
    VG.Proof.AesGcm.Arm.CT (VG.Proof.AesGcm.Arm.CrI c st w sp k8 R D n q) crypt := by
  refine CT.seq (J := fun s => VG.Proof.AesGcm.Arm.CrI c st w sp k8 R D n q s ∧ s.z = decide (n = 0)) ?_
    (fun s ⟨k7, icb, P, hP, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5]) (.block [.cmp .r5 (imm 0)]) h).isSome =
        true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r5, h₂.r5]) hc
  · obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r5 hs.r5 hs.data.ok.lt32
    exact WP.of_runBlock ⟨s₁, run₁, ⟨k7, icb, P, hP, hs.keep hg₁ ⟨hm₁, hrd₁, hwr₁, hsp₁⟩⟩, hz⟩
  refine CT.ite (decide (n = 0)) (fun s h => h.2) (fun _ => CT.skip) fun hb => ?_
  have h0 : n ≠ 0 := by simpa using hb
  let j₁ := if q = 0 then 0 else min (16 - q) n
  refine CT.seq (J := VG.Proof.AesGcm.Arm.CrM c st w sp k8 R D n q j₁) ?_
    (fun s ⟨⟨k7, icb, P, hP, hs⟩, _⟩ => WP.mono (cryptFill_ok L hs h0) fun s' ⟨j, hj, hm⟩ =>
      ⟨k7, icb, P, s.mem, hP, by rw [hj, hP] at hm; exact hm⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r5, .r6, .r10]) cryptFill h).isSome =
        true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, hP₁, h₁⟩, _⟩ ⟨⟨_, _, _, hP₂, h₂⟩, _⟩ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.r4, h₂.r4]
    · rw [h₁.r5, h₂.r5]
    · rw [h₁.r6, h₂.r6, hP₁, hP₂]
    · exact h₁.env.pin h₂.env (by simp)
  refine CT.seq (J := VG.Proof.AesGcm.Arm.CrM c st w sp k8 R D n q (j₁ + 16 * ((n - j₁) / 16))) (VG.Proof.AesGcm.Arm.cryptWhole_ct L)
    (fun s ⟨k7, icb, P, m₀, hP, hs⟩ => WP.mono (cryptWhole_ok L hs (hs.ciph L)) fun s' ⟨j, hj, hm, _⟩ =>
      ⟨k7, icb, P, m₀, hP, by rw [hj] at hm; exact hm⟩) (VG.Proof.AesGcm.Arm.cryptTail_ct L)

/-- `tag o`, from an environment with the number of rounds in `r8`. -/
theorem tag_ct {o R : Nat} (ho : o = 0 ∨ o = 112) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    VG.Proof.AesGcm.Arm.CT (fun s => ∃ k7, Env c st w sp k7 (BitVec.ofNat 32 R) s) (tag o) := by
  refine CT.seq (J := fun s => ∃ k7, Env c st w sp k7 (BitVec.ofNat 32 R) s)
    ((VG.Proof.AesGcm.Arm.lens_ct L (yo := 16) (.inr rfl)).mono fun s ⟨k7, he⟩ => ⟨k7, _, he⟩)
    (fun s ⟨k7, he⟩ => WP.mono (lens_ok L (yo := 16) (.inr rfl) (H := blockAt s.mem (State.addr c + BitVec.ofNat 64 240))
      he rfl) fun s' h => ⟨k7, h.1⟩) ?_
  let J : State → Prop := fun s => ∃ k7, Env c st w sp k7 (BitVec.ofNat 32 R) s ∧ s.gpr .r0 = c ∧
    s.gpr .r1 = BitVec.ofNat 32 R ∧ s.gpr .r2 = st ∧ s.gpr .r3 = w + BitVec.ofNat 32 o ∧
    s.gpr .r12 = BitVec.ofNat 32 1 ∧ s.gpr .lr = w + BitVec.ofNat 32 512
  refine CT.seq (J := J) ?_ (fun s ⟨k7, he⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r8, .r9, .r10, .r11]) (.block (tagArgs o))
        h).isSome = true := by rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ r hr => VG.Proof.AesGcm.Arm.pin8 h₁ h₂ h₁.r8 h₂.r8 (by simpa using hr)) hc
  · obtain ⟨s₂, run₂, -, h0, h1, h2, h3, h12, hlr, hg₂, hrd₂, hwr₂, hsp₂⟩ := VG.Proof.AesGcm.Arm.tagArgs_ok L ho he
    exact WP.of_runBlock ⟨s₂, run₂, k7, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        exact hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hsp₂ hrd₂ hwr₂,
      h0, h1, h2, h3, h12, hlr⟩
  · exact CT.ctr fun s₁ s₂ ⟨_, he₁, a0, a1, a2, a3, a12, alr⟩ ⟨_, he₂, b0, b1, b2, b3, b12, blr⟩ =>
      ⟨_, _, _, _, _, _, VG.Proof.AesGcm.Arm.ctrTag_mk L ho he₁ a0 a1 a2 a3 a12 alr hR, VG.Proof.AesGcm.Arm.ctrTag_mk L ho he₂ b0 b1 b2 b3 b12 blr hR,
        he₁.sp.trans he₂.sp.symm⟩

end

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.CTJ0`. -/
section

/-!
# AES-GCM on ARMv7: `j0` is constant time

Untrusted: everything here is checked by Lean. The invariant fixes the
context, the state, `W`, the stack pointer and the nonce's address and
length.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- Before `j0`. -/
def J0I (c st w sp : BitVec 32) (Np : BitVec 32) (n : Nat) (s : State) : Prop :=
  ∃ k7 k8 H, VG.Proof.AesGcm.Arm.J0In c st w sp k7 k8 H Np n s

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp)
include L

theorem j0hash_ct {Np : BitVec 32} {n : Nat} (hlt : n < 2 ^ 32) : VG.Proof.AesGcm.Arm.CT (VG.Proof.AesGcm.Arm.J0I c st w sp Np n) j0hash := by
  -- the accumulator zeroed, then the nonce absorbed
  let A : State → Prop := fun s => ∃ k8 H, AbsIn c st w sp (BitVec.ofNat 32 n) k8 0 H [] Np n s ∧
    blockAt s.mem (State.addr st + BitVec.ofNat 64 0) = 0
  refine CT.seq (J := A) ?_ (fun s ⟨k7, k8, H, hs⟩ => WP.mono (VG.Proof.AesGcm.Arm.j0zero_ok L hs)
    fun s' h => ⟨k8, H, h.1, h.2.1⟩) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5, .r10]) (.block [.mov .r0 (imm 0),
        .str .r0 .r10 0, .str .r0 .r10 4, .str .r0 .r10 8, .str .r0 .r10 12, .mov .r7 (.reg .r5), .mov .r6 (imm 0)])
        h).isSome = true := ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.r5, h₂.r5]
    · exact h₁.env.pin h₂.env (by simp)
  let E : State → Prop := fun s => ∃ k8, Env c st w sp (BitVec.ofNat 32 n) k8 s
  refine CT.seq (J := E) ((VG.Proof.AesGcm.Arm.absorb_ct L (.inl rfl) (by decide)).mono fun s ⟨k8, H, hs, _⟩ => ⟨_, k8, H, [], rfl, hs⟩)
    (fun s ⟨k8, H, hs, _⟩ => WP.mono (absorb_ok L (.inl rfl) hs) fun s' h => ⟨k8, h.env⟩) ?_
  -- the length of the nonce modulo 16
  let F : State → Prop := fun s => ∃ k7 k8, Env c st w sp k7 k8 s ∧ s.gpr .r6 = BitVec.ofNat 32 (n % 16) ∧
    s.gpr .r7 = BitVec.ofNat 32 n
  refine CT.seq (J := F) ?_ (fun s ⟨k8, he⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r7]) (.block [.dp .and .r6 .r7 (imm 15)])
        h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r7, h₂.r7]) hc
  · have hand := and15 (BitVec.ofNat 32 n)
    rw [toNat32 hlt] at hand
    refine WP.of_runBlock ⟨s.setReg .r6 (s.gpr .r7 &&& BitVec.ofNat 32 15), by arun [], _, k8, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, he.r7, hand]
    · simp [gpr_setReg, he.r7]
  let G : State → Prop := fun s => ∃ k7 k8, Env c st w sp k7 k8 s
  refine CT.seq (J := G) ((VG.Proof.AesGcm.Arm.flush_ct L (yo := 0) (.inl rfl) (q := n % 16) (Nat.mod_lt _ (by decide))).mono
    fun s ⟨k7, k8, he, h6, _⟩ => ⟨k7, k8, he, h6⟩) (fun s ⟨k7, k8, he, h6, _⟩ => WP.mono
      (flush_ok L (yo := 0) (.inl rfl) (x := List.replicate n 0) (H := blockAt s.mem (State.addr c + BitVec.ofNat 64 240))
        ⟨he, rfl⟩ (by rw [h6]; simp)) fun s' h => ⟨k7, k8, h.env⟩) ?_
  refine CT.seq (J := G) ?_ (fun s ⟨k7, k8, he⟩ => ?_) ((VG.Proof.AesGcm.Arm.lens_ct L (.inl rfl)).mono fun s h => h)
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs []) (.block [.mov .r4 (imm 0), .mov .r5 (imm 0),
        .mov .r6 (.reg .r7), .mov .r7 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun _ _ _ _ r hr => by simp at hr) hc
  · exact WP.of_runBlock ⟨(((s.setReg .r4 (BitVec.ofNat 32 0)).setReg .r5 (BitVec.ofNat 32 0)).setReg .r6
      (s.gpr .r7)).setReg .r7 (BitVec.ofNat 32 0), by arun [], _, k8, he.set7 (k7' := 0) (by simp [gpr_setReg]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl⟩

theorem j0_ct {Np : BitVec 32} {n : Nat} (hlt : n < 2 ^ 32) : VG.Proof.AesGcm.Arm.CT (VG.Proof.AesGcm.Arm.J0I c st w sp Np n) j0 := by
  refine CT.seq (J := fun s => VG.Proof.AesGcm.Arm.J0I c st w sp Np n s ∧ s.z = decide (n = 12)) ?_ (fun s ⟨k7, k8, H, hs⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r5]) (.block [.cmp .r5 (imm 12)])
        h).isSome = true := ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r5, h₂.r5]) hc
  · obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmpk_ok s .r5 hs.r5 hlt (k := 12) (by decide) (by decide)
    exact WP.of_runBlock ⟨s₁, run₁, ⟨k7, k8, H, ⟨hs.env.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁,
      by rw [hm₁]; exact hs.hH, by rw [hg₁]; exact hs.r4, by rw [hg₁]; exact hs.r5, hs.data.of_eq hrd₁ hwr₁⟩⟩, hz⟩
  let M : State → Prop := fun s => ∃ k7 k8, Env c st w sp k7 k8 s
  refine CT.seq (J := M) ?_ (fun s ⟨⟨k7, k8, H, hs⟩, hz⟩ => ?_) ?_
  · refine CT.ite (decide (n = 12)) (fun s h => h.2) (fun hb => ?_) (fun _ => (VG.Proof.AesGcm.Arm.j0hash_ct L hlt).mono fun s h => h.1)
    obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r10]) (.block j012) h).isSome = true :=
      ⟨_, by taint_decide⟩
    refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, h₁⟩, _⟩ ⟨⟨_, _, _, h₂⟩, _⟩ r hr => ?_) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.r4, h₂.r4]
    · exact h₁.env.pin h₂.env (by simp)
  · refine WP.ite (decide (n = 12)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
    · have h12 : n = 12 := by simpa using ht
      subst h12
      exact WP.mono (VG.Proof.AesGcm.Arm.j012_ok L hs) fun s' h => h.env.elim fun k7 he => ⟨k7, k8, he⟩
    · exact WP.mono (VG.Proof.AesGcm.Arm.j0hash_ok L hs (by simpa using hf)) fun s' h => h.env.elim fun k7 he => ⟨k7, k8, he⟩
  · obtain ⟨_, hc⟩ : ∃ h, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r10]) (.block initState) h).isSome = true :=
      ⟨_, by taint_decide⟩
    exact CT.taint _ (fun s₁ s₂ ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr => h₁.pin h₂ (by simp at hr; simp [hr])) hc

end

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.CTFn`. -/
section

/-!
# AES-GCM on ARMv7: constant time of the functions, the tools

Untrusted: everything here is checked by Lean. The functions relate two runs
from initial states `s₀` and `s₀'` with the same public data (`F`, `F'`
describe each run from its initial state); the pieces' `CT` lemmas apply
with the public data of `s₀` (`rel_of_ct`); blocks that read stack
arguments are checked with them public (`rel_argTaint`), from `ArgsKeep`.
-/

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Impl.AesGcm.Arm

theorem rel_of_ct {I F F' : State → Prop} {c : Prog isa} (h : VG.Proof.AesGcm.Arm.CT I c) (h₁ : ∀ s, F s → I s)
    (h₂ : ∀ s, F' s → I s) : RelCT isa (fun a b => F a ∧ F' b) c fun _ _ => True :=
  RelCT.mono h (fun _ _ hh => ⟨h₁ _ hh.1, h₂ _ hh.2⟩) fun _ _ _ => trivial

/-- The stack arguments, as public in the taint analysis, from two runs that keep them. -/
theorem ArgsKeep.agree {n : Nat} {s₀ s₀' s s' : State} (hk : VG.Proof.AesGcm.Arm.ArgsKeep n s₀ s) (hk' : VG.Proof.AesGcm.Arm.ArgsKeep n s₀' s')
    (hsp : s₀.sp = s₀'.sp) (hf : s₀.sp.toNat + 4 * n ≤ 2 ^ 32) (ha : ∀ i < n, stackArg s₀ i = stackArg s₀' i)
    (hw : ∀ r ∈ s₀.wr, (VG.Proof.AesGcm.Arm.args s₀ n).Disjoint r) (hw' : ∀ r ∈ s₀'.wr, (VG.Proof.AesGcm.Arm.args s₀' n).Disjoint r)
    {rs : List Reg} (hr : ∀ r ∈ rs, s.gpr r = s'.gpr r) :
    VG.Arm.Taint.Agree (VG.Arm.argTaint rs (4 * n)) s s' := by
  have e : ∀ {t₀ t : State}, VG.Proof.AesGcm.Arm.ArgsKeep n t₀ t → (∀ r ∈ t₀.wr, (VG.Proof.AesGcm.Arm.args t₀ n).Disjoint r) →
      t.sp.toNat + 4 * n ≤ 2 ^ 32 → t.sp.toNat + 4 * n ≤ 2 ^ 32 ∧
        ∀ r ∈ t.wr, Region.Disjoint ⟨State.addr t.sp, 4 * n⟩ r := fun {t₀ t} k w f => by
    refine ⟨f, fun r hr => ?_⟩
    rw [k.wr] at hr
    have := w r hr
    simp only [VG.Proof.AesGcm.Arm.args, VG.Proof.AesGcm.Arm.argAddr_zero] at this
    rwa [← k.sp] at this
  have f : s.sp.toNat + 4 * n ≤ 2 ^ 32 := by rw [hk.sp]; exact hf
  have f' : s'.sp.toNat + 4 * n ≤ 2 ^ 32 := by rw [hk'.sp, ← hsp]; exact hf
  have hsp' : s.sp = s'.sp := by rw [hk.sp, hk'.sp, hsp]
  exact agree_argTaint hr hsp' (e hk hw f) (e hk' hw' f')
    (argMem_of hsp' f fun i hi => by rw [hk.arg i hi, hk'.arg i hi, ha i hi])

theorem ArgsKeep.weaken {n m : Nat} {s₀ s : State} (h : VG.Proof.AesGcm.Arm.ArgsKeep n s₀ s) (hm : m ≤ n) : VG.Proof.AesGcm.Arm.ArgsKeep m s₀ s :=
  ⟨h.sp, h.rd, h.wr, fun i hi => h.arg i (by omega)⟩

theorem args_sub (s : State) {m n : Nat} (hm : m ≤ n) : Region.Sub (VG.Proof.AesGcm.Arm.args s m) (VG.Proof.AesGcm.Arm.args s n) :=
  Region.sub_prefix (by omega)

theorem rel_ite {F F' : State → Prop} {t e : Prog isa} (b : Bool) (hz : ∀ s, F s → s.z = b)
    (hz' : ∀ s, F' s → s.z = b) (ht : b = true → RelCT isa (fun a b => F a ∧ F' b) t fun _ _ => True)
    (he : b = false → RelCT isa (fun a b => F a ∧ F' b) e fun _ _ => True) :
    RelCT isa (fun a b => F a ∧ F' b) (.ite .eq t e) fun _ _ => True := by
  refine RelCT.ite (fun _ _ h => by rw [eval_eq' (hz _ h.1), eval_eq' (hz' _ h.2)]) ?_ ?_
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hp, hc⟩ e₁ e₂
    rw [eval_eq' (hz _ hp.1)] at hc
    exact ht (Option.some.inj hc) _ _ _ _ _ _ hp e₁ e₂
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hp, hc⟩ e₁ e₂
    rw [eval_eq' (hz _ hp.1)] at hc
    exact he (Option.some.inj hc) _ _ _ _ _ _ hp e₁ e₂

theorem rel_skip {F F' : State → Prop} : RelCT isa (fun a b => F a ∧ F' b) (.block []) fun _ _ => True :=
  VG.Proof.AesGcm.Arm.rel_of_ct (I := fun _ => True) CT.skip (fun _ _ => trivial) (fun _ _ => trivial)

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.CTText`. -/
section

/-!
# AES-GCM on ARMv7: `textAbsorb` is constant time

Untrusted: everything here is checked by Lean. Two runs from initial states
`s₀` and `s₀'` with the same stack arguments: the blocks read them as
public, and `flush` and `absorb` are constant time by `flush_ct` and
`absorb_ct`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)

/-- What `textAbsorb` needs, in a run from `s₀`. -/
def TA (s₀ : State) (c st w sp : BitVec 32) (s : State) : Prop :=
  ∃ k7 k8, Env c st w sp k7 k8 s ∧ VG.Proof.AesGcm.Arm.ArgsKeep 7 s₀ s ∧ DataOk st w sp s (VG.Proof.AesGcm.Arm.arg s₀ 4) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp)
include L

/-- `flush 16`, for one run, kept to what `textAbsorb` needs. -/
theorem ta_flush {s₀ s : State} (h : VG.Proof.AesGcm.Arm.TA s₀ c st w sp s) {q : Nat} (hq : q < 16) (h6 : s.gpr .r6 = BitVec.ofNat 32 q)
    (hf : s₀.sp.toNat + 4 * 7 ≤ 2 ^ 32) (hA : ∀ r ∈ VG.Proof.AesGcm.Arm.taFrame st w sp, (VG.Proof.AesGcm.Arm.args s₀ 7).Disjoint r) :
    WP isa (flush 16) s (VG.Proof.AesGcm.Arm.TA s₀ c st w sp) := by
  obtain ⟨k7, k8, he, hk, hd⟩ := h
  refine WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl) (x := List.replicate q 0)
    (H := blockAt s.mem (State.addr c + BitVec.ofNat 64 240)) ⟨he, rfl⟩ (by simp [h6, Nat.mod_eq_of_lt hq])))
    fun s' ⟨fl, rd, wr, sp'⟩ => ⟨k7, k8, fl.env, hk.frame hf fl.frame (fun r hr => hA r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp)) sp' rd wr, hd.of_eq rd wr⟩

theorem textAbsorb_rel {s₀ s₀' : State} (hf : s₀.sp.toNat + 4 * 7 ≤ 2 ^ 32) (hsp : s₀.sp = s₀'.sp)
    (ha : ∀ i < 7, VG.Proof.AesGcm.Arm.arg s₀ i = VG.Proof.AesGcm.Arm.arg s₀' i) (hw : ∀ r ∈ s₀.wr, (VG.Proof.AesGcm.Arm.args s₀ 7).Disjoint r)
    (hw' : ∀ r ∈ s₀'.wr, (VG.Proof.AesGcm.Arm.args s₀' 7).Disjoint r) (hin : VG.Proof.AesGcm.Arm.args s₀ 7 ∈ s₀.rd) (hin' : VG.Proof.AesGcm.Arm.args s₀' 7 ∈ s₀'.rd)
    (hA : ∀ r ∈ VG.Proof.AesGcm.Arm.taFrame st w sp, (VG.Proof.AesGcm.Arm.args s₀ 7).Disjoint r) (hA' : ∀ r ∈ VG.Proof.AesGcm.Arm.taFrame st w sp, (VG.Proof.AesGcm.Arm.args s₀' 7).Disjoint r) :
    RelCT isa (fun a b => VG.Proof.AesGcm.Arm.TA s₀ c st w sp a ∧ VG.Proof.AesGcm.Arm.TA s₀' c st w sp b) textAbsorb fun _ _ => True := by
  have hf' : s₀'.sp.toNat + 4 * 7 ≤ 2 ^ 32 := by rw [← hsp]; exact hf
  have ag : ∀ {s s'}, VG.Proof.AesGcm.Arm.ArgsKeep 7 s₀ s → VG.Proof.AesGcm.Arm.ArgsKeep 7 s₀' s' →
      VG.Arm.Taint.Agree (VG.Arm.argTaint [] (4 * 7)) s s' := fun k k' =>
    k.agree k' hsp hf ha hw hw' (by simp)
  -- the length of the data
  let G₁ : State → State → Prop := fun t₀ s => VG.Proof.AesGcm.Arm.TA t₀ c st w sp s ∧ s.z = decide ((VG.Proof.AesGcm.Arm.arg t₀ 5).toNat = 0)
  have run₁ : ∀ {t₀ s : State}, VG.Proof.AesGcm.Arm.TA t₀ c st w sp s → t₀.sp.toNat + 4 * 7 ≤ 2 ^ 32 → VG.Proof.AesGcm.Arm.args t₀ 7 ∈ t₀.rd →
      WP isa (.block [.ldrSp .r5 20, .cmp .r5 (imm 0)]) s (G₁ t₀) := fun {t₀ s} ⟨k7, k8, he, hk, hd⟩ f i => by
    obtain ⟨i5, v5⟩ := hk.at f i 5 (by decide) (show 4 * 5 = 20 from rfl)
    refine WP.of_runBlock ⟨_, by arun [i5, v5], ?_⟩
    refine ⟨⟨k7, k8, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl,
      hd.of_eq rfl rfl⟩, ?_⟩
    simp only [z_subFlags, gpr_setReg, ite_true, v5]; exact VG.Proof.AesGcm.Arm.z_sub0 _
  have a := rel_agree (F := VG.Proof.AesGcm.Arm.TA s₀ c st w sp) (F' := VG.Proof.AesGcm.Arm.TA s₀' c st w sp) (G := G₁ s₀) (G' := G₁ s₀')
    (VG.Arm.argTaint [] (4 * 7)) (c := .block [.ldrSp .r5 20, .cmp .r5 (imm 0)])
    (fun s s' ⟨_, _, _, k, _⟩ ⟨_, _, _, k', _⟩ => ag k k') ⟨_, by taint_decide⟩
    (fun s h => run₁ h hf hin) (fun s h => run₁ h hf' hin')
  refine a.seq (VG.Proof.AesGcm.Arm.rel_ite (decide ((VG.Proof.AesGcm.Arm.arg s₀ 5).toNat = 0)) (fun s h => h.2) (fun s h => by rw [h.2, ha 5 (by decide)])
    (fun _ => VG.Proof.AesGcm.Arm.rel_skip) fun _ => ?_)
  -- whether there is text so far
  let G₂ : State → State → Prop := fun t₀ s => VG.Proof.AesGcm.Arm.TA t₀ c st w sp s ∧ s.z = decide ((VG.Proof.AesGcm.Arm.arg t₀ 3 ++ VG.Proof.AesGcm.Arm.arg t₀ 2).toNat = 0)
  have run₂ : ∀ {t₀ s : State}, G₁ t₀ s → t₀.sp.toNat + 4 * 7 ≤ 2 ^ 32 → VG.Proof.AesGcm.Arm.args t₀ 7 ∈ t₀.rd →
      WP isa (.block tlenZero) s (G₂ t₀) := fun {t₀ s} ⟨⟨k7, k8, he, hk, hd⟩, _⟩ f i => by
    obtain ⟨i2, v2⟩ := hk.at f i 2 (by decide) (show 4 * 2 = 8 from rfl)
    obtain ⟨i3, v3⟩ := hk.at f i 3 (by decide) (show 4 * 3 = 12 from rfl)
    refine WP.of_runBlock ⟨_, by simp only [tlenZero]; arun [i2, v2, i3, v3], ?_⟩
    refine ⟨⟨k7, k8, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_subFlags]) rfl rfl rfl,
      hk.of_eq rfl rfl rfl rfl, hd.of_eq rfl rfl⟩, ?_⟩
    simp only [z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, v2, v3]
    rw [VG.Proof.AesGcm.Arm.z_sub0]
    exact decide_eq_decide.mpr (VG.Proof.AesGcm.Arm.or_zero_iff _ _)
  have b := rel_agree (F := G₁ s₀) (F' := G₁ s₀') (G := G₂ s₀) (G' := G₂ s₀')
    (VG.Arm.argTaint [] (4 * 7)) (c := .block tlenZero)
    (fun s s' ⟨⟨_, _, _, k, _⟩, _⟩ ⟨⟨_, _, _, k', _⟩, _⟩ => ag k k') ⟨_, by taint_decide⟩
    (fun s h => run₂ h hf hin) (fun s h => run₂ h hf' hin')
  refine b.seq ?_
  -- the additional data padded, before the first text
  have ff : ∀ {t₀ : State}, t₀.sp.toNat + 4 * 7 ≤ 2 ^ 32 → VG.Proof.AesGcm.Arm.args t₀ 7 ∈ t₀.rd →
      (∀ r ∈ VG.Proof.AesGcm.Arm.taFrame st w sp, (VG.Proof.AesGcm.Arm.args t₀ 7).Disjoint r) →
      ∀ s, G₂ t₀ s → WP isa (.ite .eq firstFlush (.block [])) s (VG.Proof.AesGcm.Arm.TA t₀ c st w sp) := fun {t₀} f i hA₀ s ⟨hs, hz⟩ => by
    refine WP.ite _ (eval_eq' hz) (fun _ => ?_) (fun _ => WP.block_nil hs)
    obtain ⟨k7, k8, he, hk, hd⟩ := hs
    obtain ⟨i0, v0⟩ := hk.at f i 0 (by decide) (show 4 * 0 = 0 from rfl)
    refine WP.seq (WP.of_runBlock ⟨_, by arun [i0, v0], ?_⟩)
    refine VG.Proof.AesGcm.Arm.ta_flush L ⟨k7, k8, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl,
      hd.of_eq rfl rfl⟩ (q := (VG.Proof.AesGcm.Arm.arg t₀ 0).toNat % 16) (Nat.mod_lt _ (by decide)) ?_ f hA₀
    simp only [gpr_setReg, ite_true, v0, and15]
  have cF : RelCT isa (fun a b => G₂ s₀ a ∧ G₂ s₀' b) (.ite .eq firstFlush (.block [])) fun _ _ => True := by
    refine VG.Proof.AesGcm.Arm.rel_ite (decide ((VG.Proof.AesGcm.Arm.arg s₀ 3 ++ VG.Proof.AesGcm.Arm.arg s₀ 2).toNat = 0)) (fun s h => h.2)
      (fun s h => by rw [h.2, ha 3 (by decide), ha 2 (by decide)]) (fun _ => ?_) (fun _ => VG.Proof.AesGcm.Arm.rel_skip)
    let G₃ : State → State → Prop := fun t₀ s => VG.Proof.AesGcm.Arm.TA t₀ c st w sp s ∧ s.gpr .r6 = BitVec.ofNat 32 ((VG.Proof.AesGcm.Arm.arg t₀ 0).toNat % 16)
    have run₃ : ∀ {t₀ s : State}, G₂ t₀ s → t₀.sp.toNat + 4 * 7 ≤ 2 ^ 32 → VG.Proof.AesGcm.Arm.args t₀ 7 ∈ t₀.rd →
        WP isa (.block [.ldrSp .r6 0, .dp .and .r6 .r6 (imm 15)]) s (G₃ t₀) := fun {t₀ s} ⟨⟨k7, k8, he, hk, hd⟩, _⟩ f i => by
      obtain ⟨i0, v0⟩ := hk.at f i 0 (by decide) (show 4 * 0 = 0 from rfl)
      refine WP.of_runBlock ⟨_, by arun [i0, v0], ?_⟩
      refine ⟨⟨k7, k8, he.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl,
        hd.of_eq rfl rfl⟩, ?_⟩
      simp only [gpr_setReg, ite_true, v0, and15]
    have c₁ := rel_agree (F := G₂ s₀) (F' := G₂ s₀') (G := G₃ s₀) (G' := G₃ s₀')
      (VG.Arm.argTaint [] (4 * 7)) (c := .block [.ldrSp .r6 0, .dp .and .r6 .r6 (imm 15)])
      (fun s s' ⟨⟨_, _, _, k, _⟩, _⟩ ⟨⟨_, _, _, k', _⟩, _⟩ => ag k k') ⟨_, by taint_decide⟩
      (fun s h => run₃ h hf hin) (fun s h => run₃ h hf' hin')
    exact c₁.seq (VG.Proof.AesGcm.Arm.rel_of_ct (VG.Proof.AesGcm.Arm.flush_ct L (yo := 16) (.inr rfl) (q := (VG.Proof.AesGcm.Arm.arg s₀ 0).toNat % 16) (Nat.mod_lt _ (by decide)))
      (fun s ⟨⟨k7, k8, he, _⟩, h6⟩ => ⟨k7, k8, he, h6⟩)
      (fun s ⟨⟨k7, k8, he, _⟩, h6⟩ => ⟨k7, k8, he, by rw [h6, ha 0 (by decide)]⟩))
  refine (rel_wp cF (ff hf hin hA) (ff hf' hin' hA')).seq ?_
  -- the arguments of `absorb`
  let G₄ : State → State → Prop := fun t₀ s => VG.Proof.AesGcm.Arm.TA t₀ c st w sp s ∧ s.gpr .r4 = VG.Proof.AesGcm.Arm.arg t₀ 4 ∧ s.gpr .r5 = VG.Proof.AesGcm.Arm.arg t₀ 5 ∧
    s.gpr .r6 = BitVec.ofNat 32 ((VG.Proof.AesGcm.Arm.arg t₀ 2).toNat % 16)
  have run₄ : ∀ {t₀ s : State}, VG.Proof.AesGcm.Arm.TA t₀ c st w sp s → t₀.sp.toNat + 4 * 7 ≤ 2 ^ 32 → VG.Proof.AesGcm.Arm.args t₀ 7 ∈ t₀.rd →
      WP isa (.block textArgs) s (G₄ t₀) := fun {t₀ s} ⟨k7, k8, he, hk, hd⟩ f i => by
    obtain ⟨s', run, h4, h5, h6, hg, hK⟩ := VG.Proof.AesGcm.Arm.textArgs_run hk f i
    exact WP.of_runBlock ⟨s', run, ⟨k7, k8, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide) (by decide)) hK.sp hK.rd hK.wr,
      hk.of_eq hK.mem hK.sp hK.rd hK.wr, hd.of_eq hK.rd hK.wr⟩, h4, h5, h6⟩
  have d := rel_agree (F := VG.Proof.AesGcm.Arm.TA s₀ c st w sp) (F' := VG.Proof.AesGcm.Arm.TA s₀' c st w sp) (G := G₄ s₀) (G' := G₄ s₀')
    (VG.Arm.argTaint [] (4 * 7)) (c := .block textArgs)
    (fun s s' ⟨_, _, _, k, _⟩ ⟨_, _, _, k', _⟩ => ag k k') ⟨_, by taint_decide⟩
    (fun s h => run₄ h hf hin) (fun s h => run₄ h hf' hin')
  refine d.seq (VG.Proof.AesGcm.Arm.rel_of_ct (VG.Proof.AesGcm.Arm.absorb_ct L (yo := 16) (.inr rfl) (D := VG.Proof.AesGcm.Arm.arg s₀ 4) (n := (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat)
    (q := (VG.Proof.AesGcm.Arm.arg s₀ 2).toNat % 16) (Nat.mod_lt _ (by decide))) ?_ ?_)
  · intro s ⟨⟨k7, k8, he, _, hd⟩, h4, h5, h6⟩
    exact ⟨k7, k8, blockAt s.mem (State.addr c + BitVec.ofNat 64 240), List.replicate ((VG.Proof.AesGcm.Arm.arg s₀ 2).toNat % 16) 0,
      by simp, ⟨he, h4, by rw [h5]; simp, by rw [h6]; simp, hd, rfl⟩⟩
  · intro s ⟨⟨k7, k8, he, _, hd⟩, h4, h5, h6⟩
    rw [← ha 4 (by decide), ← ha 5 (by decide)] at hd
    exact ⟨k7, k8, blockAt s.mem (State.addr c + BitVec.ofNat 64 240), List.replicate ((VG.Proof.AesGcm.Arm.arg s₀ 2).toNat % 16) 0,
      by simp, ⟨he, by rw [h4, ha 4 (by decide)], by rw [h5, ha 5 (by decide)]; simp,
        by rw [h6, ha 2 (by decide)]; simp, hd, rfl⟩⟩

end

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.CTCryptFn`. -/
section

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt` are constant time

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Impl.AesGcm.Arm
open VG.Spec.Gcm (Block blockAt)

theorem sc_pubs {s₀ s₀' : State} (hq : VG.Proof.AesGcm.Arm.streamCryptPub s₀ s₀') : s₀.sp = s₀'.sp ∧ s₀.gpr .r0 = s₀'.gpr .r0 ∧
    s₀.gpr .r1 = s₀'.gpr .r1 ∧ s₀.gpr .r2 = s₀'.gpr .r2 ∧ ∀ i < 7, VG.Proof.AesGcm.Arm.arg s₀ i = VG.Proof.AesGcm.Arm.arg s₀' i := hq

/-- The stack arguments are apart from the writable regions. -/
theorem sc_hw {t : State} (ht : VG.Proof.AesGcm.Arm.streamCryptPre t) : ∀ r ∈ t.wr, (VG.Proof.AesGcm.Arm.args t 7).Disjoint r := by
  obtain ⟨-, hwr, -, -, -, -, -, dsA, -, dDA, dWA, -⟩ := ht
  intro r hr
  rw [hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact dsA.symm
  · exact dDA.symm
  · exact dWA.symm

/-- After the entry of `encrypt` (or the arguments of `crypt`). -/
def EC1 (s₀ : State) (s : State) : Prop :=
  ∃ k7, Env (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s ∧ VG.Proof.AesGcm.Arm.ArgsKeep 7 s₀ s ∧
    s.gpr .r4 = VG.Proof.AesGcm.Arm.arg s₀ 4 ∧ s.gpr .r5 = VG.Proof.AesGcm.Arm.arg s₀ 5 ∧ s.gpr .r6 = BitVec.ofNat 32 ((VG.Proof.AesGcm.Arm.arg s₀ 2).toNat % 16)

/-- Two runs' pieces agree on everything public. -/
theorem ec1_crI {s₀ s : State} (h : VG.Proof.AesGcm.Arm.streamCryptPre s₀) (he : VG.Proof.AesGcm.Arm.EC1 s₀ s) :
    VG.Proof.AesGcm.Arm.CrI (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp (s₀.gpr .r1) (s₀.gpr .r1).toNat (VG.Proof.AesGcm.Arm.arg s₀ 4) (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat
      ((VG.Proof.AesGcm.Arm.arg s₀ 2).toNat % 16) s := by
  obtain ⟨k7, he, hk, h4, h5, h6⟩ := he
  exact ⟨k7, 0, (VG.Proof.AesGcm.Arm.arg s₀ 3 ++ VG.Proof.AesGcm.Arm.arg s₀ 2).toNat, (VG.Proof.AesGcm.Arm.lowTo_mod16 rfl).symm, VG.Proof.AesGcm.Arm.sc_crIn h he hk h4 h5 h6 0 rfl⟩

theorem ec1_crypt {s₀ s : State} (h : VG.Proof.AesGcm.Arm.streamCryptPre s₀) (he : VG.Proof.AesGcm.Arm.EC1 s₀ s) :
    WP isa crypt s (fun s' => VG.Proof.AesGcm.Arm.TA s₀ (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp s' ∧
      ∃ k7, Env (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s') := by
  have L := VG.Proof.AesGcm.Arm.scLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨k7, icb, P, -, ci⟩ := VG.Proof.AesGcm.Arm.ec1_crI h he
  obtain ⟨_, _, hk, _⟩ := he
  refine WP.mono (WP.with_rdwr (crypt_ok L ci)) fun s' ⟨co, rd, wr, sp⟩ => ?_
  have hk' := hk.frame spf co.frame (VG.Proof.AesGcm.Arm.sc_argsCr h) sp rd wr
  exact ⟨⟨_, _, co.env, hk', (VG.Proof.AesGcm.Arm.sc_dataW (k7 := k7) h hk').ok⟩, _, co.env⟩

theorem streamEncrypt_rel {s₀ s₀' : State} (h0 : VG.Proof.AesGcm.Arm.streamCryptPre s₀) (h0' : VG.Proof.AesGcm.Arm.streamCryptPre s₀')
    (hq : VG.Proof.AesGcm.Arm.streamCryptPub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') streamEncrypt fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, qa⟩ := VG.Proof.AesGcm.Arm.sc_pubs hq
  have L := VG.Proof.AesGcm.Arm.scLay h0
  have spf := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : ∀ {t : State}, VG.Proof.AesGcm.Arm.streamCryptPre t → VG.Proof.AesGcm.Arm.args t 7 ∈ t.rd := fun {t} ht => by rw [ht.1]; simp
  have e1 : ∀ {t : State}, VG.Proof.AesGcm.Arm.streamCryptPre t → WP isa (.block (cryptEntry ++ textArgs)) t (VG.Proof.AesGcm.Arm.EC1 t) := fun {t} ht => by
    have spf := ht.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    refine WP.block_append (VG.Proof.AesGcm.Arm.sc1_wp ht fun s₁ h1 => ?_)
    obtain ⟨s', run, h4, h5, h6, hg, hK⟩ := VG.Proof.AesGcm.Arm.textArgs_run h1.args spf (hin ht)
    exact WP.of_runBlock ⟨s', run, _, h1.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide) (by decide)) hK.sp hK.rd hK.wr,
      h1.args.of_eq hK.mem hK.sp hK.rd hK.wr, h4, h5, h6⟩
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := VG.Proof.AesGcm.Arm.EC1 s₀) (G' := VG.Proof.AesGcm.Arm.EC1 s₀')
    (VG.Arm.argTaint [.r0, .r1, .r2] (4 * 7)) (c := .block (cryptEntry ++ textArgs))
    (fun s s' e e' => by
      subst e e'
      refine (ArgsKeep.refl 7 s).agree (ArgsKeep.refl 7 s') q₀ spf qa (VG.Proof.AesGcm.Arm.sc_hw h0) (VG.Proof.AesGcm.Arm.sc_hw h0')
        fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> with_reducible assumption) ⟨_, by taint_decide⟩
    (fun s e => by rw [e]; exact e1 h0) (fun s e => by rw [e]; exact e1 h0')
  let G₂ : State → Prop := fun s => VG.Proof.AesGcm.Arm.TA s₀ (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp s
  let G₂' : State → Prop := fun s => VG.Proof.AesGcm.Arm.TA s₀' (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp s
  have b := rel_wp (F := VG.Proof.AesGcm.Arm.EC1 s₀) (F' := VG.Proof.AesGcm.Arm.EC1 s₀') (G := G₂) (G' := G₂')
    (VG.Proof.AesGcm.Arm.rel_of_ct (VG.Proof.AesGcm.Arm.crypt_ct L) (fun s he => VG.Proof.AesGcm.Arm.ec1_crI h0 he) (fun s he => by
      have := VG.Proof.AesGcm.Arm.ec1_crI h0' he
      rwa [← q₁, ← q₂, ← q₃, ← q₀, ← qa 2 (by decide), ← qa 4 (by decide), ← qa 5 (by decide),
        ← qa 6 (by decide)] at this))
    (fun s he => WP.mono (VG.Proof.AesGcm.Arm.ec1_crypt h0 he) fun _ h => h.1)
    (fun s he => WP.mono (VG.Proof.AesGcm.Arm.ec1_crypt h0' he) fun _ h => by
      have := h.1; rwa [← q₁, ← q₃, ← q₀, ← qa 6 (by decide)] at this)
  have c := VG.Proof.AesGcm.Arm.textAbsorb_rel L spf q₀ qa (VG.Proof.AesGcm.Arm.sc_hw h0) (VG.Proof.AesGcm.Arm.sc_hw h0') (hin h0) (hin h0')
    (VG.Proof.AesGcm.Arm.sc_argsTa h0) (by
      have := VG.Proof.AesGcm.Arm.sc_argsTa h0'; rwa [← q₃, ← qa 6 (by decide), ← q₀] at this)
  let G₃ : State → Prop := fun s => ∃ k7 k8, Env (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp k7 k8 s
  have ta : ∀ {t₀ : State}, VG.Proof.AesGcm.Arm.streamCryptPre t₀ → t₀.sp = s₀.sp → VG.Proof.AesGcm.Arm.arg t₀ 6 = VG.Proof.AesGcm.Arm.arg s₀ 6 →
      t₀.gpr .r0 = s₀.gpr .r0 → t₀.gpr .r2 = s₀.gpr .r2 → ∀ s, VG.Proof.AesGcm.Arm.TA t₀ (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp s →
      WP isa textAbsorb s G₃ := fun {t₀} ht e0 e6 er0 er2 s ⟨k7, k8, he, hk, hd⟩ => by
    have Lt := VG.Proof.AesGcm.Arm.scLay ht
    rw [e0, e6, er0, er2] at Lt
    have spf := ht.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hA := VG.Proof.AesGcm.Arm.sc_argsTa ht
    rw [e0, e6, er2] at hA
    exact WP.mono (VG.Proof.AesGcm.Arm.textAbsorb_ok Lt (a := List.replicate ((VG.Proof.AesGcm.Arm.arg t₀ 0).toNat % 16) 0)
      (ct := List.replicate (VG.Proof.AesGcm.Arm.arg t₀ 3 ++ VG.Proof.AesGcm.Arm.arg t₀ 2).toNat 0) he hk spf (hin ht) hA rfl hd (by simp) (by simp))
      fun s' h => ⟨_, _, h.env⟩
  have d := rel_wp (F := G₂) (F' := G₂') (G := G₃) (G' := G₃) c
    (ta h0 rfl rfl rfl rfl) (ta h0' q₀.symm (qa 6 (by decide)).symm q₁.symm q₃.symm)
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have e := RelCT.taint (A := VG.Arm.taint) (P := fun s₁ s₂ => G₃ s₁ ∧ G₃ s₂) (c := .block restore) (Taint.ofRegs [.r11])
    (fun s₁ s₂ ⟨⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r11, h₂.r11]) hB
  exact a.seq (b.seq (d.seq e))

theorem streamDecrypt_rel {s₀ s₀' : State} (h0 : VG.Proof.AesGcm.Arm.streamCryptPre s₀) (h0' : VG.Proof.AesGcm.Arm.streamCryptPre s₀')
    (hq : VG.Proof.AesGcm.Arm.streamCryptPub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') streamDecrypt fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, qa⟩ := VG.Proof.AesGcm.Arm.sc_pubs hq
  have L := VG.Proof.AesGcm.Arm.scLay h0
  have spf := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : ∀ {t : State}, VG.Proof.AesGcm.Arm.streamCryptPre t → VG.Proof.AesGcm.Arm.args t 7 ∈ t.rd := fun {t} ht => by rw [ht.1]; simp
  let G₁ : State → Prop := fun s => VG.Proof.AesGcm.Arm.TA s₀ (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp s ∧
    ∃ k7, Env (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s
  let G₁' : State → Prop := fun s => VG.Proof.AesGcm.Arm.TA s₀' (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp s ∧
    ∃ k7, Env (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s
  have e1 : ∀ {t : State}, VG.Proof.AesGcm.Arm.streamCryptPre t → t.sp = s₀.sp → VG.Proof.AesGcm.Arm.arg t 6 = VG.Proof.AesGcm.Arm.arg s₀ 6 → t.gpr .r0 = s₀.gpr .r0 →
      t.gpr .r1 = s₀.gpr .r1 → t.gpr .r2 = s₀.gpr .r2 →
      WP isa (.block cryptEntry) t fun s => VG.Proof.AesGcm.Arm.TA t (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp s ∧
        ∃ k7, Env (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s :=
    fun {t} ht e0 e6 er0 er1 er2 => VG.Proof.AesGcm.Arm.sc1_wp ht fun s₁ h1 => by
      have he := h1.env
      rw [e0, e6, er0, er1, er2] at he
      have hd := (VG.Proof.AesGcm.Arm.sc_dataW (k7 := t.gpr .r7) ht h1.args).ok
      rw [e0, e6, er2] at hd
      exact ⟨⟨_, _, he, h1.args, hd⟩, _, he⟩
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := G₁) (G' := G₁')
    (VG.Arm.argTaint [.r0, .r1, .r2] (4 * 7)) (c := .block cryptEntry)
    (fun s s' e e' => by
      subst e e'
      refine (ArgsKeep.refl 7 s).agree (ArgsKeep.refl 7 s') q₀ spf qa (VG.Proof.AesGcm.Arm.sc_hw h0) (VG.Proof.AesGcm.Arm.sc_hw h0') fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> with_reducible assumption) ⟨_, by taint_decide⟩
    (fun s e => by rw [e]; exact e1 h0 rfl rfl rfl rfl rfl)
    (fun s e => by rw [e]; exact e1 h0' q₀.symm (qa 6 (by decide)).symm q₁.symm q₂.symm q₃.symm)
  have c := VG.Proof.AesGcm.Arm.textAbsorb_rel L spf q₀ qa (VG.Proof.AesGcm.Arm.sc_hw h0) (VG.Proof.AesGcm.Arm.sc_hw h0') (hin h0) (hin h0')
    (VG.Proof.AesGcm.Arm.sc_argsTa h0) (by
      have := VG.Proof.AesGcm.Arm.sc_argsTa h0'; rwa [← q₃, ← qa 6 (by decide), ← q₀] at this)
  let G₂ : State → State → Prop := fun t₀ s =>
    ∃ k7, Env (t₀.gpr .r0) (t₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg t₀ 6) t₀.sp k7 (t₀.gpr .r1) s ∧ VG.Proof.AesGcm.Arm.ArgsKeep 7 t₀ s
  have ta : ∀ {t₀ : State}, VG.Proof.AesGcm.Arm.streamCryptPre t₀ → t₀.sp = s₀.sp → VG.Proof.AesGcm.Arm.arg t₀ 6 = VG.Proof.AesGcm.Arm.arg s₀ 6 →
      t₀.gpr .r0 = s₀.gpr .r0 → t₀.gpr .r1 = s₀.gpr .r1 → t₀.gpr .r2 = s₀.gpr .r2 → ∀ s,
      (VG.Proof.AesGcm.Arm.TA t₀ (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp s ∧
        ∃ k7, Env (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp k7 (s₀.gpr .r1) s) →
      WP isa textAbsorb s (G₂ t₀) := fun {t₀} ht e0 e6 er0 er1 er2 s ⟨⟨_, _, _, hk, hd⟩, k7, he⟩ => by
    have Lt := VG.Proof.AesGcm.Arm.scLay ht
    rw [e0, e6, er0, er2] at Lt
    have spf := ht.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hA := VG.Proof.AesGcm.Arm.sc_argsTa ht
    rw [e0, e6, er2] at hA
    refine WP.mono (VG.Proof.AesGcm.Arm.textAbsorb_ok Lt (a := List.replicate ((VG.Proof.AesGcm.Arm.arg t₀ 0).toNat % 16) 0)
      (ct := List.replicate (VG.Proof.AesGcm.Arm.arg t₀ 3 ++ VG.Proof.AesGcm.Arm.arg t₀ 2).toNat 0) he hk spf (hin ht) hA rfl hd (by simp) (by simp))
      fun s' h => ⟨k7, ?_, h.args⟩
    have := h.env
    rwa [← e0, ← e6, ← er0, ← er1, ← er2] at this
  have d := rel_wp (F := G₁) (F' := G₁') (G := G₂ s₀) (G' := G₂ s₀') (c.mono (fun _ _ h => ⟨h.1.1, h.2.1⟩)
    fun _ _ h => h) (ta h0 rfl rfl rfl rfl rfl) (ta h0' q₀.symm (qa 6 (by decide)).symm q₁.symm q₂.symm q₃.symm)
  -- the arguments of `crypt`
  have e3 : ∀ {t₀ : State}, VG.Proof.AesGcm.Arm.streamCryptPre t₀ → ∀ s, G₂ t₀ s → WP isa (.block textArgs) s (VG.Proof.AesGcm.Arm.EC1 t₀) :=
    fun {t₀} ht s ⟨k7, he, hk⟩ => by
      have spf := ht.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      obtain ⟨s', run, h4, h5, h6, hg, hK⟩ := VG.Proof.AesGcm.Arm.textArgs_run hk spf (hin ht)
      exact WP.of_runBlock ⟨s', run, _, he.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide) (by decide)) hK.sp hK.rd hK.wr,
        hk.of_eq hK.mem hK.sp hK.rd hK.wr, h4, h5, h6⟩
  have f := rel_agree (F := G₂ s₀) (F' := G₂ s₀') (VG.Arm.argTaint [] (4 * 7)) (c := .block textArgs)
    (fun s s' ⟨_, _, k⟩ ⟨_, _, k'⟩ => k.agree k' q₀ spf qa (VG.Proof.AesGcm.Arm.sc_hw h0) (VG.Proof.AesGcm.Arm.sc_hw h0') (by simp)) ⟨_, by taint_decide⟩
    (e3 h0) (e3 h0')
  let G₃ : State → Prop := fun s => ∃ k7 k8, Env (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp k7 k8 s
  have g := rel_wp (F := VG.Proof.AesGcm.Arm.EC1 s₀) (F' := VG.Proof.AesGcm.Arm.EC1 s₀') (G := G₃) (G' := G₃)
    (VG.Proof.AesGcm.Arm.rel_of_ct (VG.Proof.AesGcm.Arm.crypt_ct L) (fun s he => VG.Proof.AesGcm.Arm.ec1_crI h0 he) (fun s he => by
      have := VG.Proof.AesGcm.Arm.ec1_crI h0' he
      rwa [← q₁, ← q₂, ← q₃, ← q₀, ← qa 2 (by decide), ← qa 4 (by decide), ← qa 5 (by decide),
        ← qa 6 (by decide)] at this))
    (fun s he => WP.mono (VG.Proof.AesGcm.Arm.ec1_crypt h0 he) fun _ h => h.2.elim fun k7 he => ⟨k7, _, he⟩)
    (fun s he => WP.mono (VG.Proof.AesGcm.Arm.ec1_crypt h0' he) fun _ h => h.2.elim fun k7 he => by
      rw [← q₁, ← q₃, ← q₀, ← qa 6 (by decide)] at he; exact ⟨k7, _, he⟩)
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have e := RelCT.taint (A := VG.Arm.taint) (P := fun s₁ s₂ => G₃ s₁ ∧ G₃ s₂) (c := .block restore) (Taint.ofRegs [.r11])
    (fun s₁ s₂ ⟨⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.r11, h₂.r11]) hB
  exact a.seq (d.seq (f.seq (g.seq e)))

theorem streamEncrypt_ct : ConstantTime isa streamEncryptArm.pre streamEncryptArm.pub streamEncrypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.AesGcm.Arm.streamEncrypt_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem streamDecrypt_ct : ConstantTime isa streamDecryptArm.pre streamDecryptArm.pub streamDecrypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.AesGcm.Arm.streamDecrypt_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.CTFin`. -/
section

/-!
# AES-GCM on ARMv7: `finTag`, `vg_aes_gcm_stream_finish` and `vg_aes_gcm_stream_verify` are constant time

Untrusted: everything here is checked by Lean. `finish` copies the tag to
`tag` through a pointer read from the stack (`tagOut_wp`); `verify` compares
the tags without a branch: only the tag length decides which code runs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Gcm (Block blockAt)

/-- What `finTag` needs, in a run from `s₀`. -/
def FT (na : Nat) (s₀ : State) (c st w sp : BitVec 32) (R : Nat) (s : State) : Prop :=
  ∃ k7, Env c st w sp k7 (BitVec.ofNat 32 R) s ∧ VG.Proof.AesGcm.Arm.ArgsKeep na s₀ s

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp)
include L

theorem finTag_rel {na : Nat} (hna : 4 ≤ na) {o R : Nat} (ho : o = 0 ∨ o = 112) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {s₀ s₀' : State} (hf : s₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hsp : s₀.sp = s₀'.sp)
    (ha : ∀ i < na, VG.Proof.AesGcm.Arm.arg s₀ i = VG.Proof.AesGcm.Arm.arg s₀' i) (hw : ∀ r ∈ s₀.wr, (VG.Proof.AesGcm.Arm.args s₀ na).Disjoint r)
    (hw' : ∀ r ∈ s₀'.wr, (VG.Proof.AesGcm.Arm.args s₀' na).Disjoint r) (hin : VG.Proof.AesGcm.Arm.args s₀ na ∈ s₀.rd) (hin' : VG.Proof.AesGcm.Arm.args s₀' na ∈ s₀'.rd)
    (hA : ∀ r ∈ VG.Proof.AesGcm.Arm.tagFrame st w sp o, (VG.Proof.AesGcm.Arm.args s₀ na).Disjoint r) (hA' : ∀ r ∈ VG.Proof.AesGcm.Arm.tagFrame st w sp o, (VG.Proof.AesGcm.Arm.args s₀' na).Disjoint r) :
    RelCT isa (fun a b => VG.Proof.AesGcm.Arm.FT na s₀ c st w sp R a ∧ VG.Proof.AesGcm.Arm.FT na s₀' c st w sp R b) (finTag o) fun _ _ => True := by
  have hf' : s₀'.sp.toNat + 4 * na ≤ 2 ^ 32 := by rw [← hsp]; exact hf
  have ag : ∀ {s s'}, VG.Proof.AesGcm.Arm.ArgsKeep na s₀ s → VG.Proof.AesGcm.Arm.ArgsKeep na s₀' s' →
      VG.Arm.Taint.Agree (VG.Arm.argTaint [] (4 * 4)) s s' := fun k k' =>
    (k.weaken hna).agree (k'.weaken hna) hsp (by omega) (fun i hi => ha i (by omega))
      (fun r hr => (hw r hr).sub_left (VG.Proof.AesGcm.Arm.args_sub _ hna)) (fun r hr => (hw' r hr).sub_left (VG.Proof.AesGcm.Arm.args_sub _ hna)) (by simp)
  have keep : ∀ {s s' : State} {k7 : BitVec 32} (rs : List Reg), Env c st w sp k7 (BitVec.ofNat 32 R) s →
      (∀ r, r ∉ rs → s'.gpr r = s.gpr r) → (∀ r ∈ [Reg.r7, .r8, .r9, .r10, .r11], r ∉ rs) → Keeps s s' →
      Env c st w sp k7 (BitVec.ofNat 32 R) s' := fun rs he hg hn hK =>
    he.keep (fun r hr => hg r (hn r hr)) hK.sp hK.rd hK.wr
  -- whether there is text
  let GA : State → State → Prop := fun t₀ s => VG.Proof.AesGcm.Arm.FT na t₀ c st w sp R s ∧
    s.z = decide ((VG.Proof.AesGcm.Arm.arg t₀ 3 ++ VG.Proof.AesGcm.Arm.arg t₀ 2).toNat = 0)
  have runA : ∀ {t₀ s : State}, VG.Proof.AesGcm.Arm.FT na t₀ c st w sp R s → t₀.sp.toNat + 4 * na ≤ 2 ^ 32 → VG.Proof.AesGcm.Arm.args t₀ na ∈ t₀.rd →
      WP isa (.block tlenZero) s (GA t₀) := fun {t₀ s} ⟨k7, he, hk⟩ f i => by
    obtain ⟨i2, v2⟩ := hk.at f i 2 (by omega) (show 4 * 2 = 8 from rfl)
    obtain ⟨i3, v3⟩ := hk.at f i 3 (by omega) (show 4 * 3 = 12 from rfl)
    refine WP.of_runBlock ⟨_, by simp only [tlenZero]; arun [i2, v2, i3, v3], ?_⟩
    refine ⟨⟨k7, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_subFlags]) rfl rfl rfl,
      hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
    simp only [z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, v2, v3]
    rw [VG.Proof.AesGcm.Arm.z_sub0]
    exact decide_eq_decide.mpr (VG.Proof.AesGcm.Arm.or_zero_iff _ _)
  have a := rel_agree (F := VG.Proof.AesGcm.Arm.FT na s₀ c st w sp R) (F' := VG.Proof.AesGcm.Arm.FT na s₀' c st w sp R) (G := GA s₀) (G' := GA s₀')
    (VG.Arm.argTaint [] (4 * 4)) (c := .block tlenZero)
    (fun s s' ⟨_, _, k⟩ ⟨_, _, k'⟩ => ag k k') ⟨_, by taint_decide⟩
    (fun s h => runA h hf hin) (fun s h => runA h hf' hin')
  refine a.seq ?_
  -- the buffered bytes' length
  let v : State → BitVec 32 := fun t₀ => if (VG.Proof.AesGcm.Arm.arg t₀ 3 ++ VG.Proof.AesGcm.Arm.arg t₀ 2).toNat = 0 then VG.Proof.AesGcm.Arm.arg t₀ 0 else VG.Proof.AesGcm.Arm.arg t₀ 2
  let GB : State → State → Prop := fun t₀ s => VG.Proof.AesGcm.Arm.FT na t₀ c st w sp R s ∧ s.gpr .r6 = v t₀
  have runB : ∀ {t₀ s : State}, GA t₀ s → t₀.sp.toNat + 4 * na ≤ 2 ^ 32 → VG.Proof.AesGcm.Arm.args t₀ na ∈ t₀.rd →
      WP isa (.ite .eq (.block [.ldrSp .r6 0]) (.block [.ldrSp .r6 8])) s (GB t₀) :=
    fun {t₀ s} ⟨⟨k7, he, hk⟩, hz⟩ f i => by
    refine WP.ite _ (eval_eq' hz) (fun ht => ?_) (fun hf₀ => ?_)
    · obtain ⟨i0, v0⟩ := hk.at f i 0 (by omega) (show 4 * 0 = 0 from rfl)
      refine WP.of_runBlock ⟨_, by arun [i0, v0], ?_⟩
      refine ⟨⟨k7, he.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
      have : (VG.Proof.AesGcm.Arm.arg t₀ 3 ++ VG.Proof.AesGcm.Arm.arg t₀ 2).toNat = 0 := by simpa using ht
      simp [gpr_setReg, v0, v, this]
    · obtain ⟨i2, v2⟩ := hk.at f i 2 (by omega) (show 4 * 2 = 8 from rfl)
      refine WP.of_runBlock ⟨_, by arun [i2, v2], ?_⟩
      refine ⟨⟨k7, he.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
      have : (VG.Proof.AesGcm.Arm.arg t₀ 3 ++ VG.Proof.AesGcm.Arm.arg t₀ 2).toNat ≠ 0 := by simpa using hf₀
      simp [gpr_setReg, v2, v, this]
  have b : RelCT isa (fun a b => GA s₀ a ∧ GA s₀' b) (.ite .eq (.block [.ldrSp .r6 0]) (.block [.ldrSp .r6 8]))
      fun _ _ => True := by
    refine VG.Proof.AesGcm.Arm.rel_ite (decide ((VG.Proof.AesGcm.Arm.arg s₀ 3 ++ VG.Proof.AesGcm.Arm.arg s₀ 2).toNat = 0)) (fun s h => h.2)
      (fun s h => by rw [h.2, ha 3 (by omega), ha 2 (by omega)]) (fun _ => ?_) (fun _ => ?_)
    · obtain ⟨_, hc⟩ : ∃ h, (taint.check (VG.Arm.argTaint [] (4 * 4)) (.block [.ldrSp .r6 0]) h).isSome = true :=
        ⟨_, by taint_decide⟩
      exact RelCT.taint (A := VG.Arm.taint) (VG.Arm.argTaint [] (4 * 4)) (fun s s' h =>
        ag h.1.1.choose_spec.2 h.2.1.choose_spec.2) hc
    · obtain ⟨_, hc⟩ : ∃ h, (taint.check (VG.Arm.argTaint [] (4 * 4)) (.block [.ldrSp .r6 8]) h).isSome = true :=
        ⟨_, by taint_decide⟩
      exact RelCT.taint (A := VG.Arm.taint) (VG.Arm.argTaint [] (4 * 4)) (fun s s' h =>
        ag h.1.1.choose_spec.2 h.2.1.choose_spec.2) hc
  refine (rel_wp b (fun s h => runB h hf hin) (fun s h => runB h hf' hin')).seq ?_
  have hv : v s₀' = v s₀ := by simp only [v, ha 0 (by omega), ha 2 (by omega), ha 3 (by omega)]
  -- modulo 16
  let GC : State → State → Prop := fun t₀ s => VG.Proof.AesGcm.Arm.FT na t₀ c st w sp R s ∧
    s.gpr .r6 = BitVec.ofNat 32 ((v s₀).toNat % 16)
  have runC : ∀ {t₀ s : State}, v t₀ = v s₀ → GB t₀ s → WP isa (.block [.dp .and .r6 .r6 (imm 15)]) s (GC t₀) :=
    fun {t₀ s} e ⟨⟨k7, he, hk⟩, h6⟩ => by
    refine WP.of_runBlock ⟨_, by arun [], ?_⟩
    refine ⟨⟨k7, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
    simp only [gpr_setReg, ite_true, h6, and15, e]
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.r6]) (.block [.dp .and .r6 .r6 (imm 15)]) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have cC := rel_wp (F := GB s₀) (F' := GB s₀') (G := GC s₀) (G' := GC s₀')
    (RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs [.r6]) (fun s s' h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2, hv]) hC)
    (fun s h => runC rfl h) (fun s h => runC hv h)
  refine cC.seq ?_
  -- the buffered bytes padded
  have runF : ∀ {t₀ s : State}, t₀.sp.toNat + 4 * na ≤ 2 ^ 32 → (∀ r ∈ VG.Proof.AesGcm.Arm.tagFrame st w sp o, (VG.Proof.AesGcm.Arm.args t₀ na).Disjoint r) →
      GC t₀ s → WP isa (flush 16) s (VG.Proof.AesGcm.Arm.FT na t₀ c st w sp R) := fun {t₀ s} f hA₀ ⟨⟨k7, he, hk⟩, h6⟩ => by
    have hq := Nat.mod_lt (v s₀).toNat (show 16 > 0 by decide)
    refine WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl) (x := List.replicate ((v s₀).toNat % 16) 0)
      (H := blockAt s.mem (State.addr c + BitVec.ofNat 64 240)) ⟨he, rfl⟩ (by simp [h6, Nat.mod_eq_of_lt hq])))
      fun s' ⟨fl, rd, wr, sp'⟩ => ⟨k7, fl.env, hk.frame f fl.frame (VG.Proof.AesGcm.Arm.disj_sub hA₀ VG.Proof.AesGcm.Arm.tFrame_sub) sp' rd wr⟩
  have cF := rel_wp (F := GC s₀) (F' := GC s₀') (G := VG.Proof.AesGcm.Arm.FT na s₀ c st w sp R) (G' := VG.Proof.AesGcm.Arm.FT na s₀' c st w sp R)
    (VG.Proof.AesGcm.Arm.rel_of_ct (VG.Proof.AesGcm.Arm.flush_ct L (yo := 16) (.inr rfl) (q := (v s₀).toNat % 16) (Nat.mod_lt _ (by decide)))
      (fun s ⟨⟨k7, he, _⟩, h6⟩ => ⟨k7, _, he, h6⟩) (fun s ⟨⟨k7, he, _⟩, h6⟩ => ⟨k7, _, he, h6⟩))
    (fun s h => runF hf hA h) (fun s h => runF hf' hA' h)
  refine cF.seq ?_
  -- the lengths
  have runD : ∀ {t₀ s : State}, t₀.sp.toNat + 4 * na ≤ 2 ^ 32 → VG.Proof.AesGcm.Arm.args t₀ na ∈ t₀.rd → VG.Proof.AesGcm.Arm.FT na t₀ c st w sp R s →
      WP isa (.block [.ldrSp .r4 0, .ldrSp .r5 4, .ldrSp .r6 8, .ldrSp .r7 12]) s (VG.Proof.AesGcm.Arm.FT na t₀ c st w sp R) :=
    fun {t₀ s} f i ⟨k7, he, hk⟩ => by
    obtain ⟨j0, w0⟩ := hk.at f i 0 (by omega) (show 4 * 0 = 0 from rfl)
    obtain ⟨j1, w1⟩ := hk.at f i 1 (by omega) (show 4 * 1 = 4 from rfl)
    obtain ⟨j2, w2⟩ := hk.at f i 2 (by omega) (show 4 * 2 = 8 from rfl)
    obtain ⟨j3, w3⟩ := hk.at f i 3 (by omega) (show 4 * 3 = 12 from rfl)
    refine WP.of_runBlock ⟨_, by arun [j0, w0, j1, w1, j2, w2, j3, w3], ?_⟩
    exact ⟨_, he.set7 (k7' := VG.Proof.AesGcm.Arm.arg t₀ 3) (by simp [gpr_setReg, w3]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩
  have cD := rel_agree (F := VG.Proof.AesGcm.Arm.FT na s₀ c st w sp R) (F' := VG.Proof.AesGcm.Arm.FT na s₀' c st w sp R) (G := VG.Proof.AesGcm.Arm.FT na s₀ c st w sp R)
    (G' := VG.Proof.AesGcm.Arm.FT na s₀' c st w sp R) (VG.Arm.argTaint [] (4 * 4))
    (c := .block [.ldrSp .r4 0, .ldrSp .r5 4, .ldrSp .r6 8, .ldrSp .r7 12])
    (fun s s' ⟨_, _, k⟩ ⟨_, _, k'⟩ => ag k k') ⟨_, by taint_decide⟩
    (fun s h => runD hf hin h) (fun s h => runD hf' hin' h)
  exact cD.seq (VG.Proof.AesGcm.Arm.rel_of_ct (VG.Proof.AesGcm.Arm.tag_ct L ho hR) (fun s ⟨k7, he, _⟩ => ⟨k7, he⟩) (fun s ⟨k7, he, _⟩ => ⟨k7, he⟩))

end

/-- `tagOut` in a run from `t₀`, with the tag at its stack argument 4: what follows needs only `r11`. -/
theorem tagOut_wp {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp) {n : Nat} (hn : 5 ≤ n) {t₀ s : State}
    (he : Env c st w sp k7 k8 s) (hk : VG.Proof.AesGcm.Arm.ArgsKeep n t₀ s) (hf : t₀.sp.toNat + 4 * n ≤ 2 ^ 32)
    (hin : VG.Proof.AesGcm.Arm.args t₀ n ∈ t₀.rd) (hTw : (⟨State.addr (VG.Proof.AesGcm.Arm.arg t₀ 4), 16⟩ : Region) ∈ t₀.wr)
    (hTf : (VG.Proof.AesGcm.Arm.arg t₀ 4).toNat + 16 ≤ 2 ^ 32) (hTd : (⟨State.addr (VG.Proof.AesGcm.Arm.arg t₀ 4), 16⟩ : Region).Disjoint ⟨State.addr w, 16⟩) :
    WP isa (.block tagOut) s fun s' => s'.gpr .r11 = w := by
  obtain ⟨i4, v4⟩ := hk.at hf hin 4 (by omega) (show 4 * 4 = 16 from rfl)
  obtain ⟨s', run, -, -, g, -⟩ := VG.Proof.AesGcm.Arm.tagOut_ok L he i4 v4 (by rw [hk.wr]; exact covers_of_mem hTw) hTf hTd
  exact WP.of_runBlock ⟨s', run, by rw [g _ (by decide) (by decide), he.r11]⟩

theorem fin_hw {n wi : Nat} {t : State} (ht : VG.Proof.AesGcm.Arm.finPre n wi t) : ∀ r ∈ t.wr, (VG.Proof.AesGcm.Arm.args t n).Disjoint r := ht.2.1.2.2

theorem fin_entry_agree {n wi : Nat} {s₀ s₀' : State} (h0 : VG.Proof.AesGcm.Arm.finPre n wi s₀) (h0' : VG.Proof.AesGcm.Arm.finPre n wi s₀')
    (hq : VG.Proof.AesGcm.Arm.finPub n s₀ s₀') :
    ∀ s s', s = s₀ → s' = s₀' → VG.Arm.Taint.Agree (VG.Arm.argTaint [.r0, .r1, .r2] (4 * n)) s s' := by
  obtain ⟨q₀, q₁, q₂, q₃, qa⟩ := hq
  intro s s' e e'
  subst e e'
  refine (ArgsKeep.refl n s).agree (ArgsKeep.refl n s') q₀ h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 qa (VG.Proof.AesGcm.Arm.fin_hw h0) (VG.Proof.AesGcm.Arm.fin_hw h0')
    fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> with_reducible assumption

theorem streamFinish_rel {s₀ s₀' : State} (h0 : streamFinishArm.pre s₀) (h0' : streamFinishArm.pre s₀')
    (hq : streamFinishArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') streamFinish fun _ _ => True := by
  have h0₆ : VG.Proof.AesGcm.Arm.finPre 6 5 s₀ := streamFinishPreArm.fin h0
  have h0₆' : VG.Proof.AesGcm.Arm.finPre 6 5 s₀' := streamFinishPreArm.fin h0'
  obtain ⟨q₀, q₁, q₂, q₃, qa⟩ := id hq
  have L := VG.Proof.AesGcm.Arm.finLay h0₆
  have hR := h0₆.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have spf := h0₆.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf' := h0₆'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := VG.Proof.AesGcm.Arm.SF1 6 5 s₀) (G' := VG.Proof.AesGcm.Arm.SF1 6 5 s₀')
    (VG.Arm.argTaint [.r0, .r1, .r2] (4 * 6)) (c := .block (finEntry 20)) (VG.Proof.AesGcm.Arm.fin_entry_agree h0₆ h0₆' hq) ⟨_, by taint_decide⟩
    (fun s e => by rw [e]; exact VG.Proof.AesGcm.Arm.fin1_wp h0₆ (by decide) (by decide) fun _ h => h)
    (fun s e => by rw [e]; exact VG.Proof.AesGcm.Arm.fin1_wp h0₆' (by decide) (by decide) fun _ h => h)
  let G : State → State → Prop := fun t₀ s =>
    (∃ k7 k8, Env (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 5) s₀.sp k7 k8 s) ∧ VG.Proof.AesGcm.Arm.ArgsKeep 6 t₀ s
  have tg : ∀ {t₀ : State}, VG.Proof.AesGcm.Arm.finPre 6 5 t₀ → t₀.sp = s₀.sp → VG.Proof.AesGcm.Arm.arg t₀ 5 = VG.Proof.AesGcm.Arm.arg s₀ 5 → t₀.gpr .r0 = s₀.gpr .r0 →
      t₀.gpr .r2 = s₀.gpr .r2 → ∀ s, VG.Proof.AesGcm.Arm.SF1 6 5 t₀ s → WP isa (finTag 0) s (G t₀) := fun {t₀} ht e0 e4 er0 er2 s h1 =>
    WP.mono (VG.Proof.AesGcm.Arm.fin_tag ht (by decide) h1 (.inl rfl) (a := List.replicate ((VG.Proof.AesGcm.Arm.arg t₀ 0).toNat % 16) 0)
      (ct := List.replicate (VG.Proof.AesGcm.Arm.arg t₀ 3 ++ VG.Proof.AesGcm.Arm.arg t₀ 2).toNat 0) (by simp) (by simp)) fun s' h => by
      obtain ⟨k7, he⟩ := h.env
      rw [e0, e4, er0, er2] at he
      exact ⟨⟨k7, _, he⟩, h.args⟩
  have e1 : BitVec.ofNat 32 (s₀.gpr .r1).toNat = s₀.gpr .r1 := by simp
  have b := rel_wp (F := VG.Proof.AesGcm.Arm.SF1 6 5 s₀) (F' := VG.Proof.AesGcm.Arm.SF1 6 5 s₀') (G := G s₀) (G' := G s₀')
    (VG.Proof.AesGcm.Arm.finTag_rel L (na := 6) (by decide) (o := 0) (.inl rfl) hR spf q₀ qa (VG.Proof.AesGcm.Arm.fin_hw h0₆) (VG.Proof.AesGcm.Arm.fin_hw h0₆')
      h0₆.1.2 h0₆'.1.2 (VG.Proof.AesGcm.Arm.fin_argsTag h0₆ (.inl rfl))
      (by have := VG.Proof.AesGcm.Arm.fin_argsTag h0₆' (o := 0) (.inl rfl); rwa [← q₃, ← qa 5 (by decide), ← q₀] at this) |>.mono
      (fun s s' ⟨h₁, h₂⟩ => ⟨⟨_, by rw [e1]; exact h₁.env, h₁.args⟩, ⟨_, by
        have := h₂.env; rw [← q₁, ← q₂, ← q₃, ← qa 5 (by decide), ← q₀] at this; rw [e1]; exact this, h₂.args⟩⟩)
      fun _ _ h => h)
    (tg h0₆ rfl rfl rfl rfl) (tg h0₆' q₀.symm (qa 5 (by decide)).symm q₁.symm q₃.symm)
  -- the tag copied out
  let W : State → Prop := fun s => s.gpr .r11 = VG.Proof.AesGcm.Arm.arg s₀ 5
  obtain ⟨hrd, hwr, -, -, -, -, -, -, tW, -, -, -, -, -, -, -, -, fT, -⟩ := h0
  obtain ⟨-, hwr', -, -, -, -, -, -, tW', -, -, -, -, -, -, -, -, fT', -⟩ := h0'
  have c := rel_agree (F := G s₀) (F' := G s₀') (G := W) (G' := W) (VG.Arm.argTaint [.r11] (4 * 6)) (c := .block tagOut)
    (fun s s' ⟨⟨_, _, he⟩, hk⟩ ⟨⟨_, _, he'⟩, hk'⟩ => hk.agree hk' q₀ spf qa (VG.Proof.AesGcm.Arm.fin_hw h0₆) (VG.Proof.AesGcm.Arm.fin_hw h0₆') fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [he.r11, he'.r11]) ⟨_, by taint_decide⟩
    (fun s ⟨⟨_, _, he⟩, hk⟩ => VG.Proof.AesGcm.Arm.tagOut_wp L (by decide) he hk spf h0₆.1.2 (by rw [hwr]; simp) fT
      (tW.sub_right (Region.sub_prefix (by decide))))
    (fun s ⟨⟨_, _, he⟩, hk⟩ => VG.Proof.AesGcm.Arm.tagOut_wp L (by decide) he hk spf' h0₆'.1.2 (by rw [hwr']; simp) fT'
      (by rw [qa 5 (by decide)]; exact tW'.sub_right (Region.sub_prefix (by decide))))
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have d := RelCT.taint (A := VG.Arm.taint) (P := fun s₁ s₂ => W s₁ ∧ W s₂) (c := .block restore) (Taint.ofRegs [.r11])
    (fun s₁ s₂ ⟨h₁, h₂⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) hB
  exact a.seq (b.seq (c.seq d))

theorem streamFinish_ct : ConstantTime isa streamFinishArm.pre streamFinishArm.pub streamFinish :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.AesGcm.Arm.streamFinish_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.CTVerify`. -/
section

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_stream_verify` is constant time

Untrusted: everything here is checked by Lean. Only the (public) tag length
decides which code runs: the tags are compared without a branch.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm

/-- `rel_ite`, with a postcondition. -/
theorem rel_iteQ {F F' : State → Prop} {Q : State → State → Prop} {t e : Prog isa} (b : Bool)
    (hz : ∀ s, F s → s.z = b) (hz' : ∀ s, F' s → s.z = b)
    (ht : b = true → RelCT isa (fun a b => F a ∧ F' b) t Q)
    (he : b = false → RelCT isa (fun a b => F a ∧ F' b) e Q) :
    RelCT isa (fun a b => F a ∧ F' b) (.ite .eq t e) Q := by
  refine RelCT.ite (fun _ _ h => by rw [eval_eq' (hz _ h.1), eval_eq' (hz' _ h.2)]) ?_ ?_
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hp, hc⟩ e₁ e₂
    rw [eval_eq' (hz _ hp.1)] at hc
    exact ht (Option.some.inj hc) _ _ _ _ _ _ hp e₁ e₂
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨hp, hc⟩ e₁ e₂
    rw [eval_eq' (hz _ hp.1)] at hc
    exact he (Option.some.inj hc) _ _ _ _ _ _ hp e₁ e₂

/-- `finTag`'s state with the tag length in `r6`. -/
def P6 (c st w sp : BitVec 32) (R tl : Nat) (t₀ s : State) : Prop :=
  VG.Proof.AesGcm.Arm.FT 7 t₀ c st w sp R s ∧ s.gpr .r6 = BitVec.ofNat 32 tl

/-- After the comparison: `r0` is 1 or 0. -/
def P7 (c st w sp : BitVec 32) (R : Nat) (t₀ s : State) : Prop :=
  VG.Proof.AesGcm.Arm.FT 7 t₀ c st w sp R s ∧ ∃ b : Bool, s.gpr .r0 = if b then 1 else 0

theorem ite_bool {p : Prop} [Decidable p] {x : BitVec 32} (h : x = if p then 1 else 0) :
    ∃ b : Bool, x = if b then 1 else 0 :=
  ⟨decide p, by rw [h]; simp only [decide_eq_true_eq]⟩

section
variable {c st w sp : BitVec 32} {R tl : Nat} {t₀ : State}

theorem ld6_wp {s : State} (hf : t₀.sp.toNat + 4 * 7 ≤ 2 ^ 32) (hin : VG.Proof.AesGcm.Arm.args t₀ 7 ∈ t₀.rd)
    (h5 : (VG.Proof.AesGcm.Arm.arg t₀ 5).toNat = tl) (h : VG.Proof.AesGcm.Arm.FT 7 t₀ c st w sp R s) :
    WP isa (.block [.ldrSp .r6 20]) s (VG.Proof.AesGcm.Arm.P6 c st w sp R tl t₀) := by
  subst h5
  obtain ⟨k7, he, hk⟩ := h
  obtain ⟨i5, v5⟩ := hk.at hf hin 5 (by decide) (show 4 * 5 = 20 from rfl)
  refine WP.of_runBlock ⟨_, by arun [i5, v5], ?_⟩
  refine ⟨⟨k7, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
  simp [gpr_setReg, v5]

theorem tlo_wp {s : State} (htl : tl < 2 ^ 32) (h : VG.Proof.AesGcm.Arm.P6 c st w sp R tl t₀ s) :
    WP isa tagLenOk s fun s' => VG.Proof.AesGcm.Arm.P6 c st w sp R tl t₀ s' ∧ s'.z = !Spec.Gcm.tagLenOk tl := by
  obtain ⟨⟨k7, he, hk⟩, h6⟩ := h
  refine WP.mono (VG.Proof.AesGcm.Arm.tagLenOk_ok h6 htl) fun s' ⟨hz, g, k⟩ => ⟨⟨⟨k7, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g _ (by decide)) k.sp k.rd k.wr,
    hk.of_eq k.mem k.sp k.rd k.wr⟩, by rw [g _ (by decide), h6]⟩, hz⟩

theorem mov0_wp {s : State} (h : s.gpr .r11 = w) :
    WP isa (.block [.mov .r0 (imm 0)]) s fun s' => s'.gpr .r11 = w :=
  WP.of_runBlock ⟨_, by arun [], by simp [gpr_setReg, h]⟩

variable (L : Lay c st w sp)
include L

theorem recv_wp {s : State} (hf : t₀.sp.toNat + 4 * 7 ≤ 2 ^ 32) (hin : VG.Proof.AesGcm.Arm.args t₀ 7 ∈ t₀.rd)
    (hD : (VG.Proof.AesGcm.Arm.args t₀ 7).Disjoint ⟨State.addr w + BitVec.ofNat 64 256, 16⟩)
    (hTr : (⟨State.addr (VG.Proof.AesGcm.Arm.arg t₀ 4), tl⟩ : Region) ∈ t₀.rd) (hTf : (VG.Proof.AesGcm.Arm.arg t₀ 4).toNat + tl ≤ 2 ^ 32)
    (hTd : (⟨State.addr (VG.Proof.AesGcm.Arm.arg t₀ 4), tl⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 256, 16⟩)
    (h1 : 1 ≤ tl) (h16 : tl ≤ 16) (h : VG.Proof.AesGcm.Arm.P6 c st w sp R tl t₀ s) : WP isa recv s (VG.Proof.AesGcm.Arm.P6 c st w sp R tl t₀) := by
  obtain ⟨⟨k7, he, hk⟩, h6⟩ := h
  obtain ⟨i4, v4⟩ := hk.at hf hin 4 (by decide) (show 4 * 4 = 16 from rfl)
  refine WP.mono (VG.Proof.AesGcm.Arm.recv_ok L he i4 v4 (by rw [hk.rd, hk.wr]; exact covers_of_mem (List.mem_append_left _ hTr)) hTf hTd
    h6 h1 h16) fun s' ⟨_, hf₄, g₄, rd₄, wr₄, sp₄⟩ => ?_
  refine ⟨⟨k7, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide) (by decide) (by decide)
        (by decide)) sp₄ rd₄ wr₄,
    hk.frame hf hf₄ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hD) sp₄ rd₄ wr₄⟩, ?_⟩
  rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), h6]

theorem ft_wp {s : State} (hf : t₀.sp.toNat + 4 * 7 ≤ 2 ^ 32) (hin : VG.Proof.AesGcm.Arm.args t₀ 7 ∈ t₀.rd)
    (hA : ∀ r ∈ VG.Proof.AesGcm.Arm.tagFrame st w sp 0, (VG.Proof.AesGcm.Arm.args t₀ 7).Disjoint r) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (h : VG.Proof.AesGcm.Arm.FT 7 t₀ c st w sp R s) : WP isa (finTag 0) s (VG.Proof.AesGcm.Arm.FT 7 t₀ c st w sp R) := by
  obtain ⟨k7, he, hk⟩ := h
  exact WP.mono (VG.Proof.AesGcm.Arm.finTag_ok L (by decide) (.inl rfl) he hk hf hin hA rfl hR rfl
    (a := List.replicate ((VG.Proof.AesGcm.Arm.arg t₀ 0).toNat % 16) 0) (ct := List.replicate (VG.Proof.AesGcm.Arm.arg t₀ 3 ++ VG.Proof.AesGcm.Arm.arg t₀ 2).toNat 0)
    (by simp) (by simp)) fun s' h => ⟨h.env.choose, h.env.choose_spec, h.args⟩

theorem cmp_wp {s : State} (hf : t₀.sp.toNat + 4 * 7 ≤ 2 ^ 32) {o : Nat} (ho : o = 0 ∨ o = 112)
    (hD : (VG.Proof.AesGcm.Arm.args t₀ 7).Disjoint ⟨State.addr w + BitVec.ofNat 64 240, 16⟩) (h1 : 1 ≤ tl) (h16 : tl ≤ 16)
    (h : VG.Proof.AesGcm.Arm.P6 c st w sp R tl t₀ s) : WP isa (cmp o) s (VG.Proof.AesGcm.Arm.P7 c st w sp R t₀) := by
  obtain ⟨⟨k7, he, hk⟩, h6⟩ := h
  refine WP.mono (VG.Proof.AesGcm.Arm.cmp_ok L he ho h6 h1 h16) fun s' ⟨h0, hf₇, g₇, rd₇, wr₇, sp₇⟩ => ?_
  refine ⟨⟨k7, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₇ _ (by decide) (by decide) (by decide) (by decide)
        (by decide)) sp₇ rd₇ wr₇,
    hk.frame hf hf₇ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hD) sp₇ rd₇ wr₇⟩,
    VG.Proof.AesGcm.Arm.ite_bool h0⟩

end

theorem streamVerify_rel {s₀ s₀' : State} (h0 : streamVerifyArm.pre s₀) (h0' : streamVerifyArm.pre s₀')
    (hq : streamVerifyArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') streamVerify fun _ _ => True := by
  have h0₇ : VG.Proof.AesGcm.Arm.finPre 7 6 s₀ := streamVerifyPreArm.fin h0
  have h0₇' : VG.Proof.AesGcm.Arm.finPre 7 6 s₀' := streamVerifyPreArm.fin h0'
  obtain ⟨q₀, q₁, q₂, q₃, qa⟩ := id hq
  have L := VG.Proof.AesGcm.Arm.finLay h0₇
  have hR := h0₇.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have spf := h0₇.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf' := h0₇'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : VG.Proof.AesGcm.Arm.args s₀ 7 ∈ s₀.rd := h0₇.1.2
  have hin' : VG.Proof.AesGcm.Arm.args s₀' 7 ∈ s₀'.rd := h0₇'.1.2
  obtain ⟨hrd, -, -, -, -, -, -, tW, -, -, -, -, -, -, -, fT, -⟩ := h0
  obtain ⟨hrd', -, -, -, -, -, -, tW', -, -, -, -, -, -, -, fT', -⟩ := h0'
  have hA := VG.Proof.AesGcm.Arm.fin_argsTag h0₇ (o := 0) (.inl rfl)
  have hA' : ∀ r ∈ VG.Proof.AesGcm.Arm.tagFrame (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp 0, (VG.Proof.AesGcm.Arm.args s₀' 7).Disjoint r := by
    have := VG.Proof.AesGcm.Arm.fin_argsTag h0₇' (o := 0) (.inl rfl); rwa [← q₃, ← qa 6 (by decide), ← q₀] at this
  have hD : ∀ {d k : Nat}, d + k ≤ 2560 →
      (VG.Proof.AesGcm.Arm.args s₀ 7).Disjoint ⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 d, k⟩ :=
    fun hd => (h0₇.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
  have hD' : ∀ {d k : Nat}, d + k ≤ 2560 →
      (VG.Proof.AesGcm.Arm.args s₀' 7).Disjoint ⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 d, k⟩ := fun hd => by
    rw [qa 6 (by decide)]; exact (h0₇'.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
  have h5' : (VG.Proof.AesGcm.Arm.arg s₀' 5).toNat = (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat := by rw [qa 5 (by decide)]
  have e1 : BitVec.ofNat 32 (s₀.gpr .r1).toNat = s₀.gpr .r1 := by simp
  -- shorthands for the public data
  let P6₀ := VG.Proof.AesGcm.Arm.P6 (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp (s₀.gpr .r1).toNat (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat
  let FT₀ := fun t₀ => VG.Proof.AesGcm.Arm.FT 7 t₀ (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp (s₀.gpr .r1).toNat
  let P7₀ := VG.Proof.AesGcm.Arm.P7 (s₀.gpr .r0) (s₀.gpr .r2) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp (s₀.gpr .r1).toNat
  let P3 : State → State → Prop := fun t₀ s => P6₀ t₀ s ∧ s.z = !Spec.Gcm.tagLenOk (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat
  let W : State → Prop := fun s => s.gpr .r11 = VG.Proof.AesGcm.Arm.arg s₀ 6
  have r11 : ∀ {t₀ s}, FT₀ t₀ s → s.gpr .r11 = VG.Proof.AesGcm.Arm.arg s₀ 6 := fun h => h.choose_spec.1.r11
  -- the entry, and the tag length
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := P6₀ s₀) (G' := P6₀ s₀')
    (VG.Arm.argTaint [.r0, .r1, .r2] (4 * 7)) (c := .block (finEntry 24 ++ [.ldrSp .r6 20]))
    (VG.Proof.AesGcm.Arm.fin_entry_agree h0₇ h0₇' hq) ⟨_, by taint_decide⟩
    (fun s e => by
      rw [e]
      exact WP.block_append (VG.Proof.AesGcm.Arm.fin1_wp h0₇ (by decide) (by decide) fun s₁ h1 =>
        VG.Proof.AesGcm.Arm.ld6_wp spf hin rfl ⟨_, by rw [e1]; exact h1.env, h1.args⟩))
    (fun s e => by
      rw [e]
      exact WP.block_append (VG.Proof.AesGcm.Arm.fin1_wp h0₇' (by decide) (by decide) fun s₁ h1 =>
        VG.Proof.AesGcm.Arm.ld6_wp spf' hin' h5' ⟨_, by
          have := h1.env; rw [← q₁, ← q₂, ← q₃, ← qa 6 (by decide), ← q₀] at this; rw [e1]; exact this, h1.args⟩))
  -- whether the length is allowed
  obtain ⟨_, hT⟩ : ∃ h, (taint.check (Taint.ofRegs [.r6]) tagLenOk h).isSome = true := ⟨_, by taint_decide⟩
  have b := rel_wp (F := P6₀ s₀) (F' := P6₀ s₀') (G := P3 s₀) (G' := P3 s₀')
    (RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs [.r6]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2]) hT)
    (fun s h => VG.Proof.AesGcm.Arm.tlo_wp (VG.Proof.AesGcm.Arm.arg s₀ 5).isLt h) (fun s h => VG.Proof.AesGcm.Arm.tlo_wp (VG.Proof.AesGcm.Arm.arg s₀ 5).isLt h)
  -- the branches
  have mid : RelCT isa (fun a b => P3 s₀ a ∧ P3 s₀' b)
      (.ite .eq (.block [.mov .r0 (imm 0)]) (.seq recv (.seq (finTag 0) (.seq (.block [.ldrSp .r6 20])
        (cmp 0))))) fun a b => W a ∧ W b := by
    refine VG.Proof.AesGcm.Arm.rel_iteQ (!Spec.Gcm.tagLenOk (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat) (fun s h => h.2) (fun s h => h.2) (fun _ => ?_)
      (fun hb => ?_)
    · obtain ⟨_, hc⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block [.mov .r0 (imm 0)]) h).isSome = true :=
        ⟨_, by taint_decide⟩
      exact rel_wp (F := P3 s₀) (F' := P3 s₀') (G := W) (G' := W)
        (RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs []) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
          simp at hr) hc)
        (fun s h => VG.Proof.AesGcm.Arm.mov0_wp (r11 h.1.1)) (fun s h => VG.Proof.AesGcm.Arm.mov0_wp (r11 h.1.1))
    · have hok : Spec.Gcm.tagLenOk (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat = true := by simpa using hb
      obtain ⟨t1, t16⟩ := VG.Proof.AesGcm.Arm.tagLenOk_bounds hok
      have x1 := rel_agree (F := P3 s₀) (F' := P3 s₀') (G := P6₀ s₀) (G' := P6₀ s₀')
        (VG.Arm.argTaint [.r6, .r11] (4 * 7)) (c := recv)
        (fun s s' h h' => h.1.1.choose_spec.2.agree h'.1.1.choose_spec.2 q₀ spf qa (VG.Proof.AesGcm.Arm.fin_hw h0₇) (VG.Proof.AesGcm.Arm.fin_hw h0₇')
          fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · rw [h.1.2, h'.1.2]
            · rw [r11 h.1.1, r11 h'.1.1]) ⟨_, by taint_decide⟩
        (fun s h => VG.Proof.AesGcm.Arm.recv_wp L spf hin (hD (by decide)) (by rw [hrd]; simp) fT
          (tW.sub_right (Lay.wSub (by decide))) t1 t16 h.1)
        (fun s h => VG.Proof.AesGcm.Arm.recv_wp L spf' hin' (hD' (by decide)) (by rw [hrd', h5']; simp)
          (by rw [← h5']; exact fT') (by rw [← h5', qa 6 (by decide)]; exact tW'.sub_right (Lay.wSub (by decide)))
          t1 t16 h.1)
      have x2 := rel_wp (F := P6₀ s₀) (F' := P6₀ s₀') (G := FT₀ s₀) (G' := FT₀ s₀')
        (VG.Proof.AesGcm.Arm.finTag_rel L (na := 7) (by decide) (o := 0) (.inl rfl) hR spf q₀ qa (VG.Proof.AesGcm.Arm.fin_hw h0₇) (VG.Proof.AesGcm.Arm.fin_hw h0₇') hin hin'
          hA hA' |>.mono (fun s s' h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)
        (fun s h => VG.Proof.AesGcm.Arm.ft_wp L spf hin hA hR h.1) (fun s h => VG.Proof.AesGcm.Arm.ft_wp L spf' hin' hA' hR h.1)
      have x3 := rel_agree (F := FT₀ s₀) (F' := FT₀ s₀') (G := P6₀ s₀) (G' := P6₀ s₀')
        (VG.Arm.argTaint [] (4 * 7)) (c := .block [.ldrSp .r6 20])
        (fun s s' h h' => h.choose_spec.2.agree h'.choose_spec.2 q₀ spf qa (VG.Proof.AesGcm.Arm.fin_hw h0₇) (VG.Proof.AesGcm.Arm.fin_hw h0₇') (rs := [])
          (by simp)) ⟨_, by taint_decide⟩
        (fun s h => VG.Proof.AesGcm.Arm.ld6_wp spf hin rfl h) (fun s h => VG.Proof.AesGcm.Arm.ld6_wp spf' hin' h5' h)
      obtain ⟨_, c4⟩ : ∃ h, (taint.check (Taint.ofRegs [.r6, .r11]) (cmp 0) h).isSome = true :=
        ⟨_, by taint_decide⟩
      have x4 := rel_wp (F := P6₀ s₀) (F' := P6₀ s₀') (G := W) (G' := W)
        (RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs [.r6, .r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [h.1.2, h.2.2]
          · rw [r11 h.1.1, r11 h.2.1]) c4)
        (fun s h => WP.mono (VG.Proof.AesGcm.Arm.cmp_wp L spf (.inl rfl) (hD (by decide)) t1 t16 h) fun _ h => r11 h.1)
        (fun s h => WP.mono (VG.Proof.AesGcm.Arm.cmp_wp L spf' (.inl rfl) (hD' (by decide)) t1 t16 h) fun _ h => r11 h.1)
      exact x1.seq (x2.seq (x3.seq x4))
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have d := RelCT.taint (A := VG.Arm.taint) (P := fun s₁ s₂ => W s₁ ∧ W s₂) (c := .block restore) (Taint.ofRegs [.r11])
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1, h.2]) hB
  exact a.seq (b.seq (mid.seq d))

theorem streamVerify_ct : ConstantTime isa streamVerifyArm.pre streamVerifyArm.pub streamVerify :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.AesGcm.Arm.streamVerify_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.CTOne`. -/
section

/-!
# AES-GCM on ARMv7: the pieces of `seal` and `open` are constant time

Untrusted: everything here is checked by Lean. Each piece is related across
two runs from `s₀` and `s₀'` with the same public data (`onePub`), from
what it needs in each run, to what the next piece needs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Gcm (Block blockAt)

/-- A relation of two runs of `c` carries what a further `R` reaches from them. -/
theorem rel_ghost {F F' G G' Z Z' : State → Prop} {c R : Prog isa}
    (h : RelCT isa (fun a b => F a ∧ F' b) c fun a b => G a ∧ G' b) :
    RelCT isa (fun a b => (F a ∧ WP isa (.seq c R) a Z) ∧ (F' b ∧ WP isa (.seq c R) b Z')) c
      fun a b => (G a ∧ WP isa R a Z) ∧ (G' b ∧ WP isa R b Z') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, hg, hg'⟩ := h _ _ _ _ _ _ ⟨hp.1.1, hp.2.1⟩ e₁ e₂
  obtain ⟨u₁, x₁, f₁, w₁⟩ := WP.seq_iff.mp hp.1.2
  obtain ⟨u₂, x₂, f₂, w₂⟩ := WP.seq_iff.mp hp.2.2
  obtain ⟨-, rfl⟩ := Exec.det f₁ e₁
  obtain ⟨-, rfl⟩ := Exec.det f₂ e₂
  exact ⟨ht, ⟨hg, w₁⟩, ⟨hg', w₂⟩⟩

theorem wp_nil {s : State} {Q : State → Prop} (h : WP isa (.block []) s Q) : Q s := by
  obtain ⟨t, s', e, hq⟩ := h
  rw [Exec.block_iff] at e
  simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, -⟩ := e
  exact hq

/-- The stack arguments are apart from what the code writes. -/
theorem one_hw {n wi : Nat} {t : State} (ht : VG.Proof.AesGcm.Arm.onePre n wi t) : ∀ r ∈ t.wr, (VG.Proof.AesGcm.Arm.args t n).Disjoint r := ht.2.1.2.2

/-- A block reading stack arguments below 20 is constant time in two runs that keep them. -/
theorem argsR {na : Nat} (hna : 5 ≤ na) {t₀ t₀' : State} (hsp : t₀.sp = t₀'.sp)
    (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (ha : ∀ i < na, VG.Proof.AesGcm.Arm.arg t₀ i = VG.Proof.AesGcm.Arm.arg t₀' i)
    (hw : ∀ r ∈ t₀.wr, (VG.Proof.AesGcm.Arm.args t₀ na).Disjoint r) (hw' : ∀ r ∈ t₀'.wr, (VG.Proof.AesGcm.Arm.args t₀' na).Disjoint r)
    {b : List Instr} (hb : ∃ hc, (taint.check (VG.Arm.argTaint [] (4 * 5)) (.block b) hc).isSome = true)
    {P P' : State → Prop} (hP : ∀ s, P s → VG.Proof.AesGcm.Arm.ArgsKeep na t₀ s) (hP' : ∀ s, P' s → VG.Proof.AesGcm.Arm.ArgsKeep na t₀' s) :
    RelCT isa (fun a b => P a ∧ P' b) (.block b) fun _ _ => True := by
  obtain ⟨_, hc⟩ := hb
  exact RelCT.taint (A := VG.Arm.taint) (VG.Arm.argTaint [] (4 * 5)) (fun s s' h =>
    ((hP _ h.1).weaken hna).agree ((hP' _ h.2).weaken hna) hsp (by omega) (fun i hi => ha i (by omega))
      (fun r hr => (hw r hr).sub_left (VG.Proof.AesGcm.Arm.args_sub _ hna)) (fun r hr => (hw' r hr).sub_left (VG.Proof.AesGcm.Arm.args_sub _ hna))
      (by simp)) hc

/-! ## Each run -/

section
variable {na wi : Nat} {t₀ : State} {c w sp : BitVec 32} {R : Nat}

theorem so1_FT {s : State} (h1 : VG.Proof.AesGcm.Arm.SO1 na wi t₀ s) (ec : t₀.gpr .r0 = c) (ew : VG.Proof.AesGcm.Arm.arg t₀ wi = w) (esp : t₀.sp = sp)
    (eR : (t₀.gpr .r1).toNat = R) : VG.Proof.AesGcm.Arm.FT na t₀ c (w + BitVec.ofNat 32 16) w sp R s := by
  subst ec ew esp eR
  exact ⟨_, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact h1.env, h1.args⟩

theorem j0_wpI (h : VG.Proof.AesGcm.Arm.onePre na wi t₀) (ec : t₀.gpr .r0 = c) (ew : VG.Proof.AesGcm.Arm.arg t₀ wi = w) (esp : t₀.sp = sp) {s : State}
    (hs : VG.Proof.AesGcm.Arm.FT na t₀ c (w + BitVec.ofNat 32 16) w sp R s) (h4 : s.gpr .r4 = t₀.gpr .r2)
    (h5 : s.gpr .r5 = t₀.gpr .r3) :
    VG.Proof.AesGcm.Arm.J0I c (w + BitVec.ofNat 32 16) w sp (t₀.gpr .r2) (t₀.gpr .r3).toNat s ∧
      WP isa j0 s (VG.Proof.AesGcm.Arm.FT na t₀ c (w + BitVec.ofNat 32 16) w sp R) := by
  subst ec ew esp
  have L := VG.Proof.AesGcm.Arm.oneLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨k7, he, hk⟩ := hs
  have hp := h
  obtain ⟨hrd, -, -, -, -, dnW, -, -, -, -, -, -, bn, -, -, -, -, fn, -⟩ := hp
  have ji : VG.Proof.AesGcm.Arm.J0In (t₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt t₀ wi) (VG.Proof.AesGcm.Arm.arg t₀ wi) t₀.sp k7 (BitVec.ofNat 32 R)
      (blockAt s.mem (State.addr (t₀.gpr .r0) + BitVec.ofNat 64 240)) (t₀.gpr .r2) (t₀.gpr .r3).toNat s :=
    ⟨he, rfl, h4, by rw [h5]; simp, ⟨by rw [hk.rd, hk.wr]; exact covers_of_mem (List.mem_append_left _ hrd.2.1),
      (t₀.gpr .r3).isLt, fn, VG.Proof.AesGcm.Arm.oSt_disj h dnW, dnW, bn⟩⟩
  exact ⟨⟨_, _, _, ji⟩, WP.mono (WP.with_rdwr (VG.Proof.AesGcm.Arm.j0_ok L ji)) fun s' ⟨jo, rd', wr', sp'⟩ =>
    ⟨jo.env.choose, jo.env.choose_spec, hk.frame spf jo.frame (VG.Proof.AesGcm.Arm.one_argsJ0 h) sp' rd' wr'⟩⟩

variable {st : BitVec 32}

theorem b1_wpI (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hin : VG.Proof.AesGcm.Arm.args t₀ na ∈ t₀.rd) (hn : 5 ≤ na) {s : State}
    (hs : VG.Proof.AesGcm.Arm.FT na t₀ c st w sp R s) :
    WP isa (.block [.ldrSp .r4 0, .ldrSp .r5 4, .mov .r6 (imm 0)]) s fun s' => VG.Proof.AesGcm.Arm.FT na t₀ c st w sp R s' ∧
      s'.gpr .r4 = VG.Proof.AesGcm.Arm.arg t₀ 0 ∧ s'.gpr .r5 = VG.Proof.AesGcm.Arm.arg t₀ 1 ∧ s'.gpr .r6 = BitVec.ofNat 32 0 := by
  obtain ⟨k7, he, hk⟩ := hs
  obtain ⟨a0, v0⟩ := hk.at hf hin 0 (by omega) (show 4 * 0 = 0 from rfl)
  obtain ⟨a1, v1⟩ := hk.at hf hin 1 (by omega) (show 4 * 1 = 4 from rfl)
  refine WP.of_runBlock ⟨_, by arun [a0, v0, a1, v1], ?_⟩
  refine ⟨⟨k7, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩,
    ?_, ?_, ?_⟩
  · simp [gpr_setReg, v0]
  · simp [gpr_setReg, v1]
  · simp [gpr_setReg]

theorem b2_wpI (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hin : VG.Proof.AesGcm.Arm.args t₀ na ∈ t₀.rd) (hn : 5 ≤ na) {s : State}
    (hs : VG.Proof.AesGcm.Arm.FT na t₀ c st w sp R s) :
    WP isa (.block [.ldrSp .r6 4, .dp .and .r6 .r6 (imm 15)]) s fun s' => VG.Proof.AesGcm.Arm.FT na t₀ c st w sp R s' ∧
      s'.gpr .r6 = BitVec.ofNat 32 ((VG.Proof.AesGcm.Arm.arg t₀ 1).toNat % 16) := by
  obtain ⟨k7, he, hk⟩ := hs
  obtain ⟨b1, w1⟩ := hk.at hf hin 1 (by omega) (show 4 * 1 = 4 from rfl)
  refine WP.of_runBlock ⟨_, by arun [b1, w1], ?_⟩
  refine ⟨⟨k7, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
  simp only [gpr_setReg, ite_true, w1, and15]

theorem b3_wpI (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hin : VG.Proof.AesGcm.Arm.args t₀ na ∈ t₀.rd) (hn : 5 ≤ na) {s : State}
    (hs : VG.Proof.AesGcm.Arm.FT na t₀ c st w sp R s) :
    WP isa (.block [.ldrSp .r6 12, .dp .and .r6 .r6 (imm 15)]) s fun s' => VG.Proof.AesGcm.Arm.FT na t₀ c st w sp R s' ∧
      s'.gpr .r6 = BitVec.ofNat 32 ((VG.Proof.AesGcm.Arm.arg t₀ 3).toNat % 16) := by
  obtain ⟨k7, he, hk⟩ := hs
  obtain ⟨b3, w3⟩ := hk.at hf hin 3 (by omega) (show 4 * 3 = 12 from rfl)
  refine WP.of_runBlock ⟨_, by arun [b3, w3], ?_⟩
  refine ⟨⟨k7, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩, ?_⟩
  simp only [gpr_setReg, ite_true, w3, and15]

theorem b4_wpI (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hin : VG.Proof.AesGcm.Arm.args t₀ na ∈ t₀.rd) (hn : 5 ≤ na) {s : State}
    (hs : VG.Proof.AesGcm.Arm.FT na t₀ c st w sp R s) :
    WP isa (.block [.ldrSp .r4 4, .mov .r5 (imm 0), .ldrSp .r6 12, .mov .r7 (imm 0)]) s
      (VG.Proof.AesGcm.Arm.FT na t₀ c st w sp R) := by
  obtain ⟨k7, he, hk⟩ := hs
  obtain ⟨j1, w1⟩ := hk.at hf hin 1 (by omega) (show 4 * 1 = 4 from rfl)
  obtain ⟨j3, w3⟩ := hk.at hf hin 3 (by omega) (show 4 * 3 = 12 from rfl)
  refine WP.of_runBlock ⟨_, by arun [j1, w1, j3, w3], ?_⟩
  exact ⟨_, he.set7 (k7' := BitVec.ofNat 32 0) (by simp [gpr_setReg]) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩

theorem da_wpI (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hin : VG.Proof.AesGcm.Arm.args t₀ na ∈ t₀.rd) (hn : 5 ≤ na) {s : State}
    (hs : VG.Proof.AesGcm.Arm.FT na t₀ c st w sp R s) :
    WP isa (.block dataArgs) s fun s' => VG.Proof.AesGcm.Arm.FT na t₀ c st w sp R s' ∧
      s'.gpr .r4 = VG.Proof.AesGcm.Arm.arg t₀ 2 ∧ s'.gpr .r5 = VG.Proof.AesGcm.Arm.arg t₀ 3 ∧ s'.gpr .r6 = BitVec.ofNat 32 0 := by
  obtain ⟨k7, he, hk⟩ := hs
  obtain ⟨s', run, h4, h5, h6, g, k⟩ := VG.Proof.AesGcm.Arm.dataArgs_run hk hf hin hn
  exact WP.of_runBlock ⟨s', run, ⟨k7, he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g _ (by decide) (by decide) (by decide)) k.sp k.rd k.wr,
    hk.of_eq k.mem k.sp k.rd k.wr⟩, h4, h5, h6⟩

variable (L : Lay c st w sp)
include L

theorem abs_wpI (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hJ : ∀ r ∈ VG.Proof.AesGcm.Arm.j0Frame st w sp, (VG.Proof.AesGcm.Arm.args t₀ na).Disjoint r)
    {D : BitVec 32} {n : Nat} (hd : DataOk st w sp t₀ D n) {s : State} (hs : VG.Proof.AesGcm.Arm.FT na t₀ c st w sp R s)
    (h4 : s.gpr .r4 = D) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) (h6 : s.gpr .r6 = BitVec.ofNat 32 0) :
    VG.Proof.AesGcm.Arm.AbsI c st w sp 16 D n 0 s ∧ WP isa (absorb 16) s (VG.Proof.AesGcm.Arm.FT na t₀ c st w sp R) := by
  obtain ⟨k7, he, hk⟩ := hs
  have ai : AbsIn c st w sp k7 (BitVec.ofNat 32 R) 16 (blockAt s.mem (State.addr c + BitVec.ofNat 64 240)) []
      D n s := ⟨he, h4, h5, by rw [h6]; rfl, hd.of_eq hk.rd hk.wr, rfl⟩
  exact ⟨⟨_, _, _, _, rfl, ai⟩, WP.mono (WP.with_rdwr (absorb_ok L (.inr rfl) ai)) fun s' ⟨ab, rd', wr', sp'⟩ =>
    ⟨k7, ab.env, hk.frame hf ab.frame (VG.Proof.AesGcm.Arm.disj_sub hJ VG.Proof.AesGcm.Arm.abs16_sub) sp' rd' wr'⟩⟩

theorem fl_wpI (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) (hJ : ∀ r ∈ VG.Proof.AesGcm.Arm.j0Frame st w sp, (VG.Proof.AesGcm.Arm.args t₀ na).Disjoint r)
    {q : Nat} (hq : q < 16) {s : State} (hs : VG.Proof.AesGcm.Arm.FT na t₀ c st w sp R s) (h6 : s.gpr .r6 = BitVec.ofNat 32 q) :
    WP isa (flush 16) s (VG.Proof.AesGcm.Arm.FT na t₀ c st w sp R) := by
  obtain ⟨k7, he, hk⟩ := hs
  exact WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl) (x := List.replicate q 0)
    (H := blockAt s.mem (State.addr c + BitVec.ofNat 64 240)) ⟨he, rfl⟩ (by simp [h6, Nat.mod_eq_of_lt hq])))
    fun s' ⟨fl, rd', wr', sp'⟩ => ⟨k7, fl.env, hk.frame hf fl.frame (VG.Proof.AesGcm.Arm.disj_sub hJ VG.Proof.AesGcm.Arm.t16_sub) sp' rd' wr'⟩

theorem cr_wpI (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) {D : BitVec 32} {n : Nat} (hd : DataOk st w sp t₀ D n)
    (hwD : Covers [⟨State.addr D, n⟩] t₀.wr) (hcD : (⟨State.addr c, 256⟩ : Region).Disjoint ⟨State.addr D, n⟩)
    (hA : ∀ r ∈ crFrame st w sp D n, (VG.Proof.AesGcm.Arm.args t₀ na).Disjoint r) (hR : R = 10 ∨ R = 12 ∨ R = 14) {s : State}
    (hs : VG.Proof.AesGcm.Arm.FT na t₀ c st w sp R s) (h4 : s.gpr .r4 = D) (h5 : s.gpr .r5 = BitVec.ofNat 32 n)
    (h6 : s.gpr .r6 = BitVec.ofNat 32 0) :
    VG.Proof.AesGcm.Arm.CrI c st w sp (BitVec.ofNat 32 R) R D n 0 s ∧ WP isa crypt s (VG.Proof.AesGcm.Arm.FT na t₀ c st w sp R) := by
  obtain ⟨k7, he, hk⟩ := hs
  have ci : CrIn c st w sp k7 (BitVec.ofNat 32 R) R (blockAt s.mem (State.addr st + BitVec.ofNat 64 48)) 0 D n s :=
    ⟨he, h4, h5, by rw [h6], he.r8, hR, ⟨hd.of_eq hk.rd hk.wr, by rw [hk.wr]; exact hwD, hcD⟩⟩
  exact ⟨⟨_, _, _, rfl, ci⟩, WP.mono (WP.with_rdwr (crypt_ok L ci)) fun s' ⟨co, rd', wr', sp'⟩ =>
    ⟨k7, co.env, hk.frame hf co.frame hA sp' rd' wr'⟩⟩

theorem tg_wpI (hf : t₀.sp.toNat + 4 * na ≤ 2 ^ 32) {o : Nat} (ho : o = 0 ∨ o = 112)
    (hT : ∀ r ∈ VG.Proof.AesGcm.Arm.tagFrame st w sp o, (VG.Proof.AesGcm.Arm.args t₀ na).Disjoint r) (hR : R = 10 ∨ R = 12 ∨ R = 14) {s : State}
    (hs : VG.Proof.AesGcm.Arm.FT na t₀ c st w sp R s) : WP isa (tag o) s (VG.Proof.AesGcm.Arm.FT na t₀ c st w sp R) := by
  obtain ⟨k7, he, hk⟩ := hs
  exact WP.mono (WP.with_rdwr (VG.Proof.AesGcm.Arm.tag_ok L ho he rfl hR rfl rfl)) fun s' ⟨tg, rd', wr', sp'⟩ =>
    ⟨k7, tg.env, hk.frame hf tg.frame hT sp' rd' wr'⟩

end

/-! ## Both runs -/

theorem one_aadOk {n wi : Nat} {t : State} (h : VG.Proof.AesGcm.Arm.onePre n wi t) :
    DataOk (VG.Proof.AesGcm.Arm.oSt t wi) (VG.Proof.AesGcm.Arm.arg t wi) t.sp t (VG.Proof.AesGcm.Arm.arg t 0) (VG.Proof.AesGcm.Arm.arg t 1).toNat := by
  have hp := h
  obtain ⟨hrd, -, -, -, -, -, -, daW, -, -, -, -, -, ba, -, -, -, -, fa, -⟩ := hp
  exact ⟨covers_of_mem (List.mem_append_left _ hrd.2.2.1), (VG.Proof.AesGcm.Arm.arg t 1).isLt, fa, VG.Proof.AesGcm.Arm.oSt_disj h daW, daW, ba⟩

theorem one_argsCr {n wi : Nat} {t : State} (h : VG.Proof.AesGcm.Arm.onePre n wi t) :
    ∀ r ∈ crFrame (VG.Proof.AesGcm.Arm.oSt t wi) (VG.Proof.AesGcm.Arm.arg t wi) t.sp (VG.Proof.AesGcm.Arm.arg t 2) (VG.Proof.AesGcm.Arm.arg t 3).toNat, (VG.Proof.AesGcm.Arm.args t n).Disjoint r := by
  have hst := VG.Proof.AesGcm.Arm.oSt_addr h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, dDA, dWA, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact dDA.symm
  · rw [hst, add_ofNat_assoc]; exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (VG.Proof.AesGcm.Arm.below_args t spf).symm

/-- A run's state, with the public data of `s₀` and the stack arguments of `t₀`. -/
abbrev OF (na wi : Nat) (s₀ t₀ s : State) : Prop :=
  VG.Proof.AesGcm.Arm.FT na t₀ (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp (s₀.gpr .r1).toNat s

section
variable {na wi : Nat} {s₀ s₀' : State} (h0 : VG.Proof.AesGcm.Arm.onePre na wi s₀) (h0' : VG.Proof.AesGcm.Arm.onePre na wi s₀') (hq : VG.Proof.AesGcm.Arm.onePub na s₀ s₀')
  (hn : 5 ≤ na) (hwi : wi < na)
include h0 h0' hq hn hwi

theorem oneAad_rel :
    RelCT isa (fun a b => VG.Proof.AesGcm.Arm.SO1 na wi s₀ a ∧ VG.Proof.AesGcm.Arm.SO1 na wi s₀' b) oneAad fun a b => VG.Proof.AesGcm.Arm.OF na wi s₀ s₀ a ∧ VG.Proof.AesGcm.Arm.OF na wi s₀ s₀' b := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := hq
  have L := VG.Proof.AesGcm.Arm.oneLay h0
  have spf := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf' := h0'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : VG.Proof.AesGcm.Arm.args s₀ na ∈ s₀.rd := h0.1.2.2.2
  have hin' : VG.Proof.AesGcm.Arm.args s₀' na ∈ s₀'.rd := h0'.1.2.2.2
  have e4 : VG.Proof.AesGcm.Arm.arg s₀' wi = VG.Proof.AesGcm.Arm.arg s₀ wi := (qa wi hwi).symm
  have est : VG.Proof.AesGcm.Arm.oSt s₀' wi = VG.Proof.AesGcm.Arm.oSt s₀ wi := by show VG.Proof.AesGcm.Arm.arg s₀' wi + _ = VG.Proof.AesGcm.Arm.arg s₀ wi + _; rw [e4]
  have hJ := VG.Proof.AesGcm.Arm.one_argsJ0 h0
  have hJ' : ∀ r ∈ VG.Proof.AesGcm.Arm.j0Frame (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp, (VG.Proof.AesGcm.Arm.args s₀' na).Disjoint r := by
    have := VG.Proof.AesGcm.Arm.one_argsJ0 h0'; rwa [est, e4, ← q₀] at this
  have so : ∀ s, VG.Proof.AesGcm.Arm.SO1 na wi s₀ s → VG.Proof.AesGcm.Arm.OF na wi s₀ s₀ s := fun s h1 => VG.Proof.AesGcm.Arm.so1_FT h1 rfl rfl rfl rfl
  have so' : ∀ s, VG.Proof.AesGcm.Arm.SO1 na wi s₀' s → VG.Proof.AesGcm.Arm.OF na wi s₀ s₀' s := fun s h1 => VG.Proof.AesGcm.Arm.so1_FT h1 q₁.symm e4 q₀.symm (by rw [q₂])
  -- `J₀`
  have x1 := rel_wp (F := VG.Proof.AesGcm.Arm.SO1 na wi s₀) (F' := VG.Proof.AesGcm.Arm.SO1 na wi s₀') (G := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀) (G' := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀')
    (VG.Proof.AesGcm.Arm.rel_of_ct (VG.Proof.AesGcm.Arm.j0_ct L (Np := s₀.gpr .r2) (n := (s₀.gpr .r3).toNat) (s₀.gpr .r3).isLt)
      (fun s h1 => (VG.Proof.AesGcm.Arm.j0_wpI h0 rfl rfl rfl (so s h1) h1.r4 h1.r5).1)
      (fun s h1 => by
        have := (VG.Proof.AesGcm.Arm.j0_wpI h0' q₁.symm e4 q₀.symm (so' s h1) h1.r4 h1.r5).1
        rwa [← q₃, ← q₄] at this))
    (fun s h1 => (VG.Proof.AesGcm.Arm.j0_wpI h0 rfl rfl rfl (so s h1) h1.r4 h1.r5).2)
    (fun s h1 => (VG.Proof.AesGcm.Arm.j0_wpI h0' q₁.symm e4 q₀.symm (so' s h1) h1.r4 h1.r5).2)
  -- the additional data's arguments
  let B1 : State → State → Prop := fun t₀ s => VG.Proof.AesGcm.Arm.OF na wi s₀ t₀ s ∧ s.gpr .r4 = VG.Proof.AesGcm.Arm.arg s₀ 0 ∧
    s.gpr .r5 = VG.Proof.AesGcm.Arm.arg s₀ 1 ∧ s.gpr .r6 = BitVec.ofNat 32 0
  have x2 := rel_wp (F := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀) (F' := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀') (G := B1 s₀) (G' := B1 s₀')
    (VG.Proof.AesGcm.Arm.argsR hn q₀ spf qa (VG.Proof.AesGcm.Arm.one_hw h0) (VG.Proof.AesGcm.Arm.one_hw h0') ⟨_, by taint_decide⟩ (fun s h => h.choose_spec.2)
      (fun s h => h.choose_spec.2))
    (fun s h => VG.Proof.AesGcm.Arm.b1_wpI spf hin hn h)
    (fun s h => WP.mono (VG.Proof.AesGcm.Arm.b1_wpI spf' hin' hn h) fun s' ⟨y₁, y₂, y₃, y₄⟩ =>
      ⟨y₁, by rw [y₂, qa 0 (by omega)], by rw [y₃, qa 1 (by omega)], y₄⟩)
  -- absorbed
  have hda := VG.Proof.AesGcm.Arm.one_aadOk h0
  have hda' : DataOk (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp s₀' (VG.Proof.AesGcm.Arm.arg s₀ 0) (VG.Proof.AesGcm.Arm.arg s₀ 1).toNat := by
    have := VG.Proof.AesGcm.Arm.one_aadOk h0'; rwa [est, e4, ← q₀, ← qa 0 (by omega), ← qa 1 (by omega)] at this
  have x3 := rel_wp (F := B1 s₀) (F' := B1 s₀') (G := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀) (G' := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀')
    (VG.Proof.AesGcm.Arm.rel_of_ct (VG.Proof.AesGcm.Arm.absorb_ct L (yo := 16) (.inr rfl) (D := VG.Proof.AesGcm.Arm.arg s₀ 0) (n := (VG.Proof.AesGcm.Arm.arg s₀ 1).toNat) (q := 0) (by decide))
      (fun s h => (VG.Proof.AesGcm.Arm.abs_wpI L spf hJ hda h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).1)
      (fun s h => (VG.Proof.AesGcm.Arm.abs_wpI L spf' hJ' hda' h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).1))
    (fun s h => (VG.Proof.AesGcm.Arm.abs_wpI L spf hJ hda h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).2)
    (fun s h => (VG.Proof.AesGcm.Arm.abs_wpI L spf' hJ' hda' h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).2)
  -- padded
  let B2 : State → State → Prop := fun t₀ s => VG.Proof.AesGcm.Arm.OF na wi s₀ t₀ s ∧
    s.gpr .r6 = BitVec.ofNat 32 ((VG.Proof.AesGcm.Arm.arg s₀ 1).toNat % 16)
  have x4 := rel_wp (F := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀) (F' := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀') (G := B2 s₀) (G' := B2 s₀')
    (VG.Proof.AesGcm.Arm.argsR hn q₀ spf qa (VG.Proof.AesGcm.Arm.one_hw h0) (VG.Proof.AesGcm.Arm.one_hw h0') ⟨_, by taint_decide⟩ (fun s h => h.choose_spec.2)
      (fun s h => h.choose_spec.2))
    (fun s h => VG.Proof.AesGcm.Arm.b2_wpI spf hin hn h)
    (fun s h => WP.mono (VG.Proof.AesGcm.Arm.b2_wpI spf' hin' hn h) fun s' ⟨y₁, y₂⟩ => ⟨y₁, by rw [y₂, qa 1 (by omega)]⟩)
  have x5 := rel_wp (F := B2 s₀) (F' := B2 s₀') (G := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀) (G' := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀')
    (VG.Proof.AesGcm.Arm.rel_of_ct (VG.Proof.AesGcm.Arm.flush_ct L (yo := 16) (.inr rfl) (q := (VG.Proof.AesGcm.Arm.arg s₀ 1).toNat % 16) (Nat.mod_lt _ (by decide)))
      (fun s ⟨⟨k7, he, _⟩, h6⟩ => ⟨k7, _, he, h6⟩) (fun s ⟨⟨k7, he, _⟩, h6⟩ => ⟨k7, _, he, h6⟩))
    (fun s h => VG.Proof.AesGcm.Arm.fl_wpI L spf hJ (Nat.mod_lt _ (by decide)) h.1 h.2)
    (fun s h => VG.Proof.AesGcm.Arm.fl_wpI L spf' hJ' (Nat.mod_lt _ (by decide)) h.1 h.2)
  exact x1.seq (x2.seq (x3.seq (x4.seq x5)))

theorem oneCrypt_rel :
    RelCT isa (fun a b => VG.Proof.AesGcm.Arm.OF na wi s₀ s₀ a ∧ VG.Proof.AesGcm.Arm.OF na wi s₀ s₀' b) oneCrypt fun a b => VG.Proof.AesGcm.Arm.OF na wi s₀ s₀ a ∧ VG.Proof.AesGcm.Arm.OF na wi s₀ s₀' b := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := hq
  have L := VG.Proof.AesGcm.Arm.oneLay h0
  have spf := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf' := h0'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hR : VG.Proof.AesGcm.Arm.roundsOk s₀ := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : VG.Proof.AesGcm.Arm.args s₀ na ∈ s₀.rd := h0.1.2.2.2
  have hin' : VG.Proof.AesGcm.Arm.args s₀' na ∈ s₀'.rd := h0'.1.2.2.2
  have e4 : VG.Proof.AesGcm.Arm.arg s₀' wi = VG.Proof.AesGcm.Arm.arg s₀ wi := (qa wi hwi).symm
  have est : VG.Proof.AesGcm.Arm.oSt s₀' wi = VG.Proof.AesGcm.Arm.oSt s₀ wi := by show VG.Proof.AesGcm.Arm.arg s₀' wi + _ = VG.Proof.AesGcm.Arm.arg s₀ wi + _; rw [e4]
  let D1 : State → State → Prop := fun t₀ s => VG.Proof.AesGcm.Arm.OF na wi s₀ t₀ s ∧ s.gpr .r4 = VG.Proof.AesGcm.Arm.arg s₀ 2 ∧
    s.gpr .r5 = VG.Proof.AesGcm.Arm.arg s₀ 3 ∧ s.gpr .r6 = BitVec.ofNat 32 0
  have x1 := rel_wp (F := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀) (F' := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀') (G := D1 s₀) (G' := D1 s₀')
    (VG.Proof.AesGcm.Arm.argsR hn q₀ spf qa (VG.Proof.AesGcm.Arm.one_hw h0) (VG.Proof.AesGcm.Arm.one_hw h0') ⟨_, by taint_decide⟩ (fun s h => h.choose_spec.2)
      (fun s h => h.choose_spec.2))
    (fun s h => VG.Proof.AesGcm.Arm.da_wpI spf hin hn h)
    (fun s h => WP.mono (VG.Proof.AesGcm.Arm.da_wpI spf' hin' hn h) fun s' ⟨y₁, y₂, y₃, y₄⟩ =>
      ⟨y₁, by rw [y₂, qa 2 (by omega)], by rw [y₃, qa 3 (by omega)], y₄⟩)
  have hd := VG.Proof.AesGcm.Arm.one_dataOk h0 (ArgsKeep.refl na s₀)
  have hd' : DataOk (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp s₀' (VG.Proof.AesGcm.Arm.arg s₀ 2) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat := by
    have := VG.Proof.AesGcm.Arm.one_dataOk h0' (ArgsKeep.refl na s₀'); rwa [est, e4, ← q₀, ← qa 2 (by omega), ← qa 3 (by omega)] at this
  have hwD : Covers [⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2), (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat⟩] s₀.wr := by
    exact covers_of_mem h0.2.1.1
  have hwD' : Covers [⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2), (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat⟩] s₀'.wr := by
    rw [qa 2 (by omega), qa 3 (by omega)]; exact covers_of_mem h0'.2.1.1
  have hcD' : (⟨State.addr (s₀.gpr .r0), 256⟩ : Region).Disjoint ⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2), (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat⟩ := by
    rw [q₁, qa 2 (by omega), qa 3 (by omega)]; exact h0'.2.2.1
  have hA := VG.Proof.AesGcm.Arm.one_argsCr h0
  have hA' : ∀ r ∈ crFrame (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp (VG.Proof.AesGcm.Arm.arg s₀ 2) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat, (VG.Proof.AesGcm.Arm.args s₀' na).Disjoint r := by
    have := VG.Proof.AesGcm.Arm.one_argsCr h0'; rwa [est, e4, ← q₀, ← qa 2 (by omega), ← qa 3 (by omega)] at this
  have x2 := rel_wp (F := D1 s₀) (F' := D1 s₀') (G := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀) (G' := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀')
    (VG.Proof.AesGcm.Arm.rel_of_ct (VG.Proof.AesGcm.Arm.crypt_ct L (k8 := BitVec.ofNat 32 (s₀.gpr .r1).toNat) (R := (s₀.gpr .r1).toNat) (D := VG.Proof.AesGcm.Arm.arg s₀ 2)
        (n := (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat) (q := 0))
      (fun s h => (VG.Proof.AesGcm.Arm.cr_wpI L spf hd hwD h0.2.2.1 hA hR h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).1)
      (fun s h => (VG.Proof.AesGcm.Arm.cr_wpI L spf' hd' hwD' hcD' hA' hR h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).1))
    (fun s h => (VG.Proof.AesGcm.Arm.cr_wpI L spf hd hwD h0.2.2.1 hA hR h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).2)
    (fun s h => (VG.Proof.AesGcm.Arm.cr_wpI L spf' hd' hwD' hcD' hA' hR h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).2)
  exact x1.seq x2

theorem oneTag_rel {o : Nat} (ho : o = 0 ∨ o = 112) :
    RelCT isa (fun a b => VG.Proof.AesGcm.Arm.OF na wi s₀ s₀ a ∧ VG.Proof.AesGcm.Arm.OF na wi s₀ s₀' b) (oneTag o)
      fun a b => VG.Proof.AesGcm.Arm.OF na wi s₀ s₀ a ∧ VG.Proof.AesGcm.Arm.OF na wi s₀ s₀' b := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := hq
  have L := VG.Proof.AesGcm.Arm.oneLay h0
  have spf := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf' := h0'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hR : VG.Proof.AesGcm.Arm.roundsOk s₀ := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : VG.Proof.AesGcm.Arm.args s₀ na ∈ s₀.rd := h0.1.2.2.2
  have hin' : VG.Proof.AesGcm.Arm.args s₀' na ∈ s₀'.rd := h0'.1.2.2.2
  have e4 : VG.Proof.AesGcm.Arm.arg s₀' wi = VG.Proof.AesGcm.Arm.arg s₀ wi := (qa wi hwi).symm
  have est : VG.Proof.AesGcm.Arm.oSt s₀' wi = VG.Proof.AesGcm.Arm.oSt s₀ wi := by show VG.Proof.AesGcm.Arm.arg s₀' wi + _ = VG.Proof.AesGcm.Arm.arg s₀ wi + _; rw [e4]
  have hJ := VG.Proof.AesGcm.Arm.one_argsJ0 h0
  have hJ' : ∀ r ∈ VG.Proof.AesGcm.Arm.j0Frame (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp, (VG.Proof.AesGcm.Arm.args s₀' na).Disjoint r := by
    have := VG.Proof.AesGcm.Arm.one_argsJ0 h0'; rwa [est, e4, ← q₀] at this
  have hT := VG.Proof.AesGcm.Arm.disj_sub (VG.Proof.AesGcm.Arm.one_argsOt h0 ho) VG.Proof.AesGcm.Arm.tag_otSub
  have hT' : ∀ r ∈ VG.Proof.AesGcm.Arm.tagFrame (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp o, (VG.Proof.AesGcm.Arm.args s₀' na).Disjoint r := by
    have := VG.Proof.AesGcm.Arm.disj_sub (VG.Proof.AesGcm.Arm.one_argsOt h0' ho) VG.Proof.AesGcm.Arm.tag_otSub; rwa [est, e4, ← q₀] at this
  have ag : RelCT isa (fun a b => VG.Proof.AesGcm.Arm.OF na wi s₀ s₀ a ∧ VG.Proof.AesGcm.Arm.OF na wi s₀ s₀' b) (.block dataArgs) fun _ _ => True :=
    VG.Proof.AesGcm.Arm.argsR hn q₀ spf qa (VG.Proof.AesGcm.Arm.one_hw h0) (VG.Proof.AesGcm.Arm.one_hw h0') ⟨_, by taint_decide⟩ (fun s h => h.choose_spec.2)
      (fun s h => h.choose_spec.2)
  let D1 : State → State → Prop := fun t₀ s => VG.Proof.AesGcm.Arm.OF na wi s₀ t₀ s ∧ s.gpr .r4 = VG.Proof.AesGcm.Arm.arg s₀ 2 ∧
    s.gpr .r5 = VG.Proof.AesGcm.Arm.arg s₀ 3 ∧ s.gpr .r6 = BitVec.ofNat 32 0
  have x1 := rel_wp (F := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀) (F' := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀') (G := D1 s₀) (G' := D1 s₀') ag
    (fun s h => VG.Proof.AesGcm.Arm.da_wpI spf hin hn h)
    (fun s h => WP.mono (VG.Proof.AesGcm.Arm.da_wpI spf' hin' hn h) fun s' ⟨y₁, y₂, y₃, y₄⟩ =>
      ⟨y₁, by rw [y₂, qa 2 (by omega)], by rw [y₃, qa 3 (by omega)], y₄⟩)
  have hd := VG.Proof.AesGcm.Arm.one_dataOk h0 (ArgsKeep.refl na s₀)
  have hd' : DataOk (VG.Proof.AesGcm.Arm.oSt s₀ wi) (VG.Proof.AesGcm.Arm.arg s₀ wi) s₀.sp s₀' (VG.Proof.AesGcm.Arm.arg s₀ 2) (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat := by
    have := VG.Proof.AesGcm.Arm.one_dataOk h0' (ArgsKeep.refl na s₀'); rwa [est, e4, ← q₀, ← qa 2 (by omega), ← qa 3 (by omega)] at this
  have x2 := rel_wp (F := D1 s₀) (F' := D1 s₀') (G := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀) (G' := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀')
    (VG.Proof.AesGcm.Arm.rel_of_ct (VG.Proof.AesGcm.Arm.absorb_ct L (yo := 16) (.inr rfl) (D := VG.Proof.AesGcm.Arm.arg s₀ 2) (n := (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat) (q := 0) (by decide))
      (fun s h => (VG.Proof.AesGcm.Arm.abs_wpI L spf hJ hd h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).1)
      (fun s h => (VG.Proof.AesGcm.Arm.abs_wpI L spf' hJ' hd' h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).1))
    (fun s h => (VG.Proof.AesGcm.Arm.abs_wpI L spf hJ hd h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).2)
    (fun s h => (VG.Proof.AesGcm.Arm.abs_wpI L spf' hJ' hd' h.1 h.2.1 (by rw [h.2.2.1]; simp) h.2.2.2).2)
  let B3 : State → State → Prop := fun t₀ s => VG.Proof.AesGcm.Arm.OF na wi s₀ t₀ s ∧
    s.gpr .r6 = BitVec.ofNat 32 ((VG.Proof.AesGcm.Arm.arg s₀ 3).toNat % 16)
  have x3 := rel_wp (F := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀) (F' := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀') (G := B3 s₀) (G' := B3 s₀')
    (VG.Proof.AesGcm.Arm.argsR hn q₀ spf qa (VG.Proof.AesGcm.Arm.one_hw h0) (VG.Proof.AesGcm.Arm.one_hw h0') ⟨_, by taint_decide⟩ (fun s h => h.choose_spec.2)
      (fun s h => h.choose_spec.2))
    (fun s h => VG.Proof.AesGcm.Arm.b3_wpI spf hin hn h)
    (fun s h => WP.mono (VG.Proof.AesGcm.Arm.b3_wpI spf' hin' hn h) fun s' ⟨y₁, y₂⟩ => ⟨y₁, by rw [y₂, qa 3 (by omega)]⟩)
  have x4 := rel_wp (F := B3 s₀) (F' := B3 s₀') (G := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀) (G' := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀')
    (VG.Proof.AesGcm.Arm.rel_of_ct (VG.Proof.AesGcm.Arm.flush_ct L (yo := 16) (.inr rfl) (q := (VG.Proof.AesGcm.Arm.arg s₀ 3).toNat % 16) (Nat.mod_lt _ (by decide)))
      (fun s ⟨⟨k7, he, _⟩, h6⟩ => ⟨k7, _, he, h6⟩) (fun s ⟨⟨k7, he, _⟩, h6⟩ => ⟨k7, _, he, h6⟩))
    (fun s h => VG.Proof.AesGcm.Arm.fl_wpI L spf hJ (Nat.mod_lt _ (by decide)) h.1 h.2)
    (fun s h => VG.Proof.AesGcm.Arm.fl_wpI L spf' hJ' (Nat.mod_lt _ (by decide)) h.1 h.2)
  have x5 := rel_wp (F := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀) (F' := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀') (G := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀) (G' := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀')
    (VG.Proof.AesGcm.Arm.argsR hn q₀ spf qa (VG.Proof.AesGcm.Arm.one_hw h0) (VG.Proof.AesGcm.Arm.one_hw h0') ⟨_, by taint_decide⟩ (fun s h => h.choose_spec.2)
      (fun s h => h.choose_spec.2))
    (fun s h => VG.Proof.AesGcm.Arm.b4_wpI spf hin hn h) (fun s h => VG.Proof.AesGcm.Arm.b4_wpI spf' hin' hn h)
  have x6 := rel_wp (F := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀) (F' := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀') (G := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀) (G' := VG.Proof.AesGcm.Arm.OF na wi s₀ s₀')
    (VG.Proof.AesGcm.Arm.rel_of_ct (VG.Proof.AesGcm.Arm.tag_ct L ho hR) (fun s ⟨k7, he, _⟩ => ⟨k7, he⟩) (fun s ⟨k7, he, _⟩ => ⟨k7, he⟩))
    (fun s h => VG.Proof.AesGcm.Arm.tg_wpI L spf ho hT hR h) (fun s h => VG.Proof.AesGcm.Arm.tg_wpI L spf' ho hT' hR h)
  exact x1.seq (x2.seq (x3.seq (x4.seq (x5.seq x6))))

end

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.CTOpen`. -/
section

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_seal` and `vg_aes_gcm_open` are constant time

Untrusted: everything here is checked by Lean. `open` decrypts only if the
tags are equal, which its contract makes public: the comparison, done
without a branch, is related across the runs by what each run computes
(`rel_ghost`, `open_head`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm

theorem one_entry_agree {n wi : Nat} {rs : List Reg} (hrs : ∀ r ∈ rs, r = .r0 ∨ r = .r1 ∨ r = .r2 ∨ r = .r3)
    {s₀ s₀' : State} (h0 : VG.Proof.AesGcm.Arm.onePre n wi s₀) (h0' : VG.Proof.AesGcm.Arm.onePre n wi s₀') (hq : VG.Proof.AesGcm.Arm.onePub n s₀ s₀') :
    ∀ s s', s = s₀ → s' = s₀' → VG.Arm.Taint.Agree (VG.Arm.argTaint rs (4 * n)) s s' := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := hq
  intro s s' e e'
  subst e e'
  refine (ArgsKeep.refl n s).agree (ArgsKeep.refl n s') q₀
    h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 qa (VG.Proof.AesGcm.Arm.one_hw h0) (VG.Proof.AesGcm.Arm.one_hw h0') fun r hr => ?_
  rcases hrs r hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem seal_rel {s₀ s₀' : State} (h0 : sealArm.pre s₀) (h0' : sealArm.pre s₀') (hq : sealArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') «seal» fun _ _ => True := by
  have h6 : VG.Proof.AesGcm.Arm.onePre 6 5 s₀ := sealPreArm.one h0
  have h6' : VG.Proof.AesGcm.Arm.onePre 6 5 s₀' := sealPreArm.one h0'
  have hq6 : VG.Proof.AesGcm.Arm.onePub 6 s₀ s₀' := hq
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := id hq6
  have L := VG.Proof.AesGcm.Arm.oneLay h6
  have spf := h6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf' := h6'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, -, -, -, tW, -, -, -, -, -, -, -, -, -, -, -, -, fT, -⟩ := h0
  obtain ⟨-, hwr', -, -, -, -, -, -, -, -, -, -, -, -, tW', -, -, -, -, -, -, -, -, -, -, -, -, fT', -⟩ := h0'
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := VG.Proof.AesGcm.Arm.SO1 6 5 s₀) (G' := VG.Proof.AesGcm.Arm.SO1 6 5 s₀')
    (VG.Arm.argTaint [.r0, .r1, .r2, .r3] (4 * 6)) (c := .block (oneEntry 20))
    (VG.Proof.AesGcm.Arm.one_entry_agree (by simp) h6 h6' hq6) ⟨_, by taint_decide⟩
    (fun s e => by rw [e]; exact VG.Proof.AesGcm.Arm.one1_wp h6 (by decide) (by decide) fun _ h => h)
    (fun s e => by rw [e]; exact VG.Proof.AesGcm.Arm.one1_wp h6' (by decide) (by decide) fun _ h => h)
  -- the tag copied out
  let W : State → Prop := fun s => s.gpr .r11 = VG.Proof.AesGcm.Arm.arg s₀ 5
  have c := rel_agree (F := VG.Proof.AesGcm.Arm.OF 6 5 s₀ s₀) (F' := VG.Proof.AesGcm.Arm.OF 6 5 s₀ s₀') (G := W) (G' := W) (VG.Arm.argTaint [.r11] (4 * 6))
    (c := .block tagOut)
    (fun s s' ⟨_, he, hk⟩ ⟨_, he', hk'⟩ => hk.agree hk' q₀ spf qa (VG.Proof.AesGcm.Arm.one_hw h6) (VG.Proof.AesGcm.Arm.one_hw h6') fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [he.r11, he'.r11]) ⟨_, by taint_decide⟩
    (fun s ⟨_, he, hk⟩ => VG.Proof.AesGcm.Arm.tagOut_wp L (by decide) he hk spf h6.1.2.2.2 (by rw [hwr]; simp) fT
      (tW.sub_right (Region.sub_prefix (by decide))))
    (fun s ⟨_, he, hk⟩ => VG.Proof.AesGcm.Arm.tagOut_wp L (by decide) he hk spf' h6'.1.2.2.2 (by rw [hwr']; simp) fT'
      (by rw [qa 5 (by decide)]; exact tW'.sub_right (Region.sub_prefix (by decide))))
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have d := RelCT.taint (A := VG.Arm.taint) (P := fun s₁ s₂ => W s₁ ∧ W s₂) (c := .block restore)
    (Taint.ofRegs [.r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1, h.2]) hB
  exact a.seq ((VG.Proof.AesGcm.Arm.oneAad_rel h6 h6' hq6 (by decide) (by decide)).seq ((VG.Proof.AesGcm.Arm.oneCrypt_rel h6 h6' hq6 (by decide) (by decide)).seq
    ((VG.Proof.AesGcm.Arm.oneTag_rel h6 h6' hq6 (by decide) (by decide) (.inl rfl)).seq (c.seq d))))

theorem seal_ct : ConstantTime isa sealArm.pre sealArm.pub «seal» :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.AesGcm.Arm.seal_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `open` -/

theorem openRes_isSome {t : State} (hok : Spec.Gcm.tagLenOk (VG.Proof.AesGcm.Arm.arg t 5).toNat = true) :
    (VG.Proof.AesGcm.Arm.openRes t).isSome = decide (VG.Proof.AesGcm.Arm.openTagOk t) := by
  have e : VG.Proof.AesGcm.Arm.openRes t = if VG.Proof.AesGcm.Arm.openTagOk t then
      some (Spec.Gcm.gctr (Spec.Gcm.ctxCiph t.mem (State.addr (t.gpr .r0)) (t.gpr .r1).toNat)
        (Spec.Gcm.inc32 (Spec.Gcm.j0 (Spec.Gcm.ctxH t.mem (State.addr (t.gpr .r0)))
          (Spec.Aes.bytesAt t.mem (State.addr (t.gpr .r2)) (t.gpr .r3).toNat)))
        (Spec.Aes.bytesAt t.mem (State.addr (VG.Proof.AesGcm.Arm.arg t 2)) (VG.Proof.AesGcm.Arm.arg t 3).toNat)) else none := by
    simp only [VG.Proof.AesGcm.Arm.openRes, Spec.Gcm.openResult, hok, ite_true, Spec.Gcm.decryptWith]
  rw [e]
  by_cases h : VG.Proof.AesGcm.Arm.openTagOk t
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), decide_eq_true h]; rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), decide_eq_false h]; rfl

theorem open1_wp {t₀ : State} (h : VG.Proof.AesGcm.Arm.onePre 7 6 t₀) :
    WP isa (.block (oneEntry 24 ++ ([.ldrSp .r6 20] : List Instr))) t₀ fun s =>
      VG.Proof.AesGcm.Arm.SO1 7 6 t₀ s ∧ s.gpr .r6 = BitVec.ofNat 32 (VG.Proof.AesGcm.Arm.arg t₀ 5).toNat := by
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : VG.Proof.AesGcm.Arm.args t₀ 7 ∈ t₀.rd := h.1.2.2.2
  refine WP.block_append (VG.Proof.AesGcm.Arm.one1_wp h (by decide) (by decide) fun s₁ h1 => ?_)
  obtain ⟨i5, v5⟩ := h1.args.at spf hin 5 (by decide) (show 4 * 5 = 20 from rfl)
  refine WP.of_runBlock ⟨_, by arun [i5, v5], ?_⟩
  exact ⟨h1.keep (fun r _ b => by simp [gpr_setReg, b]) ⟨rfl, rfl, rfl, rfl⟩, by simp [gpr_setReg, v5]⟩

section
variable {c st w sp : BitVec 32} {R : Nat} {t₀ : State}

theorem blk_wp {s : State} (h : VG.Proof.AesGcm.Arm.P7 c st w sp R t₀ s) :
    WP isa (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)]) s (VG.Proof.AesGcm.Arm.FT 7 t₀ c st w sp R) := by
  obtain ⟨⟨k7, he, hk⟩, -⟩ := h
  refine WP.of_runBlock ⟨_, by arun [], ?_⟩
  exact ⟨_, he.set7 rfl (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [gpr_subFlags, gpr_setReg]) rfl rfl rfl, hk.of_eq rfl rfl rfl rfl⟩

theorem mov07_wp {s : State} (h : s.gpr .r11 = w) :
    WP isa (.block [.mov .r0 (.reg .r7)]) s fun s' => s'.gpr .r11 = w :=
  WP.of_runBlock ⟨_, by arun [], by simp [gpr_setReg, h]⟩

end

theorem open_rel {s₀ s₀' : State} (h0 : openArm.pre s₀) (h0' : openArm.pre s₀') (hq : openArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') «open» fun _ _ => True := by
  have h6 : VG.Proof.AesGcm.Arm.onePre 7 6 s₀ := openPreArm.one h0
  have h6' : VG.Proof.AesGcm.Arm.onePre 7 6 s₀' := openPreArm.one h0'
  have hq6 : VG.Proof.AesGcm.Arm.onePub 7 s₀ s₀' := hq.1
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := id hq6
  have L := VG.Proof.AesGcm.Arm.oneLay h6
  have spf := h6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf' := h6'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hR : VG.Proof.AesGcm.Arm.roundsOk s₀ := h6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : VG.Proof.AesGcm.Arm.args s₀ 7 ∈ s₀.rd := h6.1.2.2.2
  have hin' : VG.Proof.AesGcm.Arm.args s₀' 7 ∈ s₀'.rd := h6'.1.2.2.2
  have e4 : VG.Proof.AesGcm.Arm.arg s₀' 6 = VG.Proof.AesGcm.Arm.arg s₀ 6 := (qa 6 (by decide)).symm
  have hrd := h0.1
  have hrd' := h0'.1
  have tW := h0.2.2.2.2.2.2.2.2.2.2.2.1
  have tW' := h0'.2.2.2.2.2.2.2.2.2.2.2.1
  have fT := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have fT' := h0'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h5' : (VG.Proof.AesGcm.Arm.arg s₀' 5).toNat = (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat := by rw [qa 5 (by decide)]
  let W : State → Prop := fun s => s.gpr .r11 = VG.Proof.AesGcm.Arm.arg s₀ 6
  have r11 : ∀ {t₀ s : State}, VG.Proof.AesGcm.Arm.OF 7 6 s₀ t₀ s → W s := fun h => h.choose_spec.1.r11
  -- the entry, and the tag length
  let G1 : State → State → Prop := fun t₀ s => VG.Proof.AesGcm.Arm.SO1 7 6 t₀ s ∧ s.gpr .r6 = BitVec.ofNat 32 (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := G1 s₀) (G' := G1 s₀')
    (VG.Arm.argTaint [.r0, .r1, .r2, .r3] (4 * 7)) (c := .block (oneEntry 24 ++ [.ldrSp .r6 20]))
    (VG.Proof.AesGcm.Arm.one_entry_agree (by simp) h6 h6' hq6) ⟨_, by taint_decide⟩
    (fun s e => by rw [e]; exact VG.Proof.AesGcm.Arm.open1_wp h6)
    (fun s e => by rw [e]; exact WP.mono (VG.Proof.AesGcm.Arm.open1_wp h6') fun s' ⟨y₁, y₂⟩ => ⟨y₁, by rw [y₂, h5']⟩)
  let G2 : State → State → Prop := fun t₀ s => VG.Proof.AesGcm.Arm.SO1 7 6 t₀ s ∧ s.z = !Spec.Gcm.tagLenOk (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat
  have tl : ∀ {t₀ s : State}, G1 t₀ s → WP isa tagLenOk s (G2 t₀) := fun {t₀ s} ⟨h1, h6r⟩ =>
    WP.mono (VG.Proof.AesGcm.Arm.tagLenOk_ok h6r (VG.Proof.AesGcm.Arm.arg s₀ 5).isLt) fun s' ⟨hz, g, k⟩ => ⟨h1.keep (fun r a _ => g r a) k, hz⟩
  obtain ⟨_, hT⟩ : ∃ h, (taint.check (Taint.ofRegs [.r6]) tagLenOk h).isSome = true := ⟨_, by taint_decide⟩
  have b := rel_wp (F := G1 s₀) (F' := G1 s₀') (G := G2 s₀) (G' := G2 s₀')
    (RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs [.r6]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2]) hT)
    (fun s h => tl h) (fun s h => tl h)
  -- the branches
  let rest6 : Prog isa := .seq (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)]) (.block [])
  let rest5 : Prog isa := .seq (cmp uO) rest6
  let rest4 : Prog isa := .seq recv rest5
  let rest3 : Prog isa := .seq (.block [.ldrSp .r6 20]) rest4
  let rest2 : Prog isa := .seq (oneTag uO) rest3
  let Z : State → State → Prop := fun t₀ s => s.z = decide (¬VG.Proof.AesGcm.Arm.openTagOk t₀)
  have mid : RelCT isa (fun a b => G2 s₀ a ∧ G2 s₀' b)
      (.ite .eq (.block [.mov .r0 (imm 0)]) VG.Proof.AesGcm.Arm.openGood) fun a b => W a ∧ W b := by
    refine VG.Proof.AesGcm.Arm.rel_iteQ (!Spec.Gcm.tagLenOk (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat) (fun s h => h.2) (fun s h => h.2) (fun _ => ?_)
      (fun hb => ?_)
    · obtain ⟨_, hc⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block [.mov .r0 (imm 0)]) h).isSome = true :=
        ⟨_, by taint_decide⟩
      exact rel_wp (F := G2 s₀) (F' := G2 s₀') (G := W) (G' := W)
        (RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs []) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
          simp at hr) hc)
        (fun s h => VG.Proof.AesGcm.Arm.mov0_wp h.1.env.r11) (fun s h => VG.Proof.AesGcm.Arm.mov0_wp (by rw [h.1.env.r11, e4]))
    · have hok : Spec.Gcm.tagLenOk (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat = true := by simpa using hb
      have hok' : Spec.Gcm.tagLenOk (VG.Proof.AesGcm.Arm.arg s₀' 5).toNat = true := by rw [h5']; exact hok
      obtain ⟨t1, t16⟩ := VG.Proof.AesGcm.Arm.tagLenOk_bounds hok
      have eZ : decide (¬VG.Proof.AesGcm.Arm.openTagOk s₀') = decide (¬VG.Proof.AesGcm.Arm.openTagOk s₀) := by
        rw [decide_not, decide_not, ← VG.Proof.AesGcm.Arm.openRes_isSome hok, ← VG.Proof.AesGcm.Arm.openRes_isSome hok', hq.2 hR]
      -- what each run reaches: whether the tags are equal
      have pfx : ∀ {t₀ s : State}, VG.Proof.AesGcm.Arm.openPreArm t₀ → Spec.Gcm.tagLenOk (VG.Proof.AesGcm.Arm.arg t₀ 5).toNat = true → VG.Proof.AesGcm.Arm.SO1 7 6 t₀ s →
          WP isa (.seq oneAad rest2) s (Z t₀) := fun ht hk h2 =>
        VG.Proof.AesGcm.Arm.open_head ht h2 hk (T := .block []) fun s₈ om => WP.block_nil om.z
      have y1 := VG.Proof.AesGcm.Arm.rel_ghost (R := rest2) (Z := Z s₀) (Z' := Z s₀') (VG.Proof.AesGcm.Arm.oneAad_rel h6 h6' hq6 (by decide) (by decide))
      have y2 := VG.Proof.AesGcm.Arm.rel_ghost (R := rest3) (Z := Z s₀) (Z' := Z s₀')
        (VG.Proof.AesGcm.Arm.oneTag_rel h6 h6' hq6 (by decide) (by decide) (o := uO) (.inr rfl))
      have y3 := VG.Proof.AesGcm.Arm.rel_ghost (R := rest4) (Z := Z s₀) (Z' := Z s₀')
        (rel_agree (F := VG.Proof.AesGcm.Arm.OF 7 6 s₀ s₀) (F' := VG.Proof.AesGcm.Arm.OF 7 6 s₀ s₀')
          (G := VG.Proof.AesGcm.Arm.P6 (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ 6) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp (s₀.gpr .r1).toNat (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat s₀)
          (G' := VG.Proof.AesGcm.Arm.P6 (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ 6) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp (s₀.gpr .r1).toNat (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat s₀')
          (VG.Arm.argTaint [] (4 * 7)) (c := .block [.ldrSp .r6 20])
          (fun s s' h h' => h.choose_spec.2.agree h'.choose_spec.2 q₀ spf qa (VG.Proof.AesGcm.Arm.one_hw h6) (VG.Proof.AesGcm.Arm.one_hw h6') (rs := [])
            (by simp)) ⟨_, by taint_decide⟩
          (fun s h => VG.Proof.AesGcm.Arm.ld6_wp spf hin rfl h) (fun s h => VG.Proof.AesGcm.Arm.ld6_wp spf' hin' h5' h))
      have hD : ∀ {d k : Nat}, d + k ≤ 2560 →
          (VG.Proof.AesGcm.Arm.args s₀ 7).Disjoint ⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 d, k⟩ :=
        fun hd => (h6.2.2.2.2.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
      have hD' : ∀ {d k : Nat}, d + k ≤ 2560 →
          (VG.Proof.AesGcm.Arm.args s₀' 7).Disjoint ⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 6) + BitVec.ofNat 64 d, k⟩ := fun hd => by
        rw [← e4]; exact (h6'.2.2.2.2.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
      have y4 := VG.Proof.AesGcm.Arm.rel_ghost (R := rest5) (Z := Z s₀) (Z' := Z s₀')
        (rel_agree
          (F := VG.Proof.AesGcm.Arm.P6 (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ 6) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp (s₀.gpr .r1).toNat (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat s₀)
          (F' := VG.Proof.AesGcm.Arm.P6 (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ 6) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp (s₀.gpr .r1).toNat (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat s₀')
          (G := VG.Proof.AesGcm.Arm.P6 (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ 6) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp (s₀.gpr .r1).toNat (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat s₀)
          (G' := VG.Proof.AesGcm.Arm.P6 (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ 6) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp (s₀.gpr .r1).toNat (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat s₀')
          (VG.Arm.argTaint [.r6, .r11] (4 * 7)) (c := recv)
          (fun s s' h h' => h.1.choose_spec.2.agree h'.1.choose_spec.2 q₀ spf qa (VG.Proof.AesGcm.Arm.one_hw h6) (VG.Proof.AesGcm.Arm.one_hw h6')
            fun r hr => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl
              · rw [h.2, h'.2]
              · rw [r11 h.1, r11 h'.1]) ⟨_, by taint_decide⟩
          (fun s h => VG.Proof.AesGcm.Arm.recv_wp L spf hin (hD (by decide)) (by rw [hrd]; simp) fT
            (tW.sub_right (Lay.wSub (by decide))) t1 t16 h)
          (fun s h => VG.Proof.AesGcm.Arm.recv_wp L spf' hin' (hD' (by decide)) (by rw [hrd', h5']; simp)
            (by rw [← h5']; exact fT') (by rw [← h5', ← e4]; exact tW'.sub_right (Lay.wSub (by decide)))
            t1 t16 h))
      obtain ⟨_, c5⟩ : ∃ h, (taint.check (Taint.ofRegs [.r6, .r11]) (cmp uO) h).isSome = true :=
        ⟨_, by taint_decide⟩
      have y5 := VG.Proof.AesGcm.Arm.rel_ghost (R := rest6) (Z := Z s₀) (Z' := Z s₀')
        (rel_wp
          (F := VG.Proof.AesGcm.Arm.P6 (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ 6) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp (s₀.gpr .r1).toNat (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat s₀)
          (F' := VG.Proof.AesGcm.Arm.P6 (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ 6) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp (s₀.gpr .r1).toNat (VG.Proof.AesGcm.Arm.arg s₀ 5).toNat s₀')
          (G := VG.Proof.AesGcm.Arm.P7 (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ 6) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp (s₀.gpr .r1).toNat s₀)
          (G' := VG.Proof.AesGcm.Arm.P7 (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ 6) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp (s₀.gpr .r1).toNat s₀')
          (RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs [.r6, .r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · rw [h.1.2, h.2.2]
            · rw [r11 h.1.1, r11 h.2.1]) c5)
          (fun s h => VG.Proof.AesGcm.Arm.cmp_wp L spf (.inr rfl) (hD (by decide)) t1 t16 h)
          (fun s h => VG.Proof.AesGcm.Arm.cmp_wp L spf' (.inr rfl) (hD' (by decide)) t1 t16 h))
      obtain ⟨_, c6⟩ : ∃ h, (taint.check (Taint.ofRegs [])
          (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩
      have y6 := VG.Proof.AesGcm.Arm.rel_ghost (R := .block []) (Z := Z s₀) (Z' := Z s₀')
        (rel_wp (F := VG.Proof.AesGcm.Arm.P7 (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ 6) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp (s₀.gpr .r1).toNat s₀)
          (F' := VG.Proof.AesGcm.Arm.P7 (s₀.gpr .r0) (VG.Proof.AesGcm.Arm.oSt s₀ 6) (VG.Proof.AesGcm.Arm.arg s₀ 6) s₀.sp (s₀.gpr .r1).toNat s₀')
          (G := VG.Proof.AesGcm.Arm.OF 7 6 s₀ s₀) (G' := VG.Proof.AesGcm.Arm.OF 7 6 s₀ s₀')
          (RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs []) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
            simp at hr) c6)
          (fun s h => VG.Proof.AesGcm.Arm.blk_wp h) (fun s h => VG.Proof.AesGcm.Arm.blk_wp h))
      -- the data decrypted only if the tags are equal, which is public
      have y7 : RelCT isa (fun a b => (VG.Proof.AesGcm.Arm.OF 7 6 s₀ s₀ a ∧ WP isa (.block []) a (Z s₀)) ∧
          (VG.Proof.AesGcm.Arm.OF 7 6 s₀ s₀' b ∧ WP isa (.block []) b (Z s₀'))) (.ite .eq (.block []) oneCrypt) fun a b => W a ∧ W b :=
        VG.Proof.AesGcm.Arm.rel_iteQ (decide (¬VG.Proof.AesGcm.Arm.openTagOk s₀)) (fun s h => VG.Proof.AesGcm.Arm.wp_nil h.2) (fun s h => (VG.Proof.AesGcm.Arm.wp_nil h.2).trans eZ)
          (fun _ => RelCT.block_nil fun x y h => ⟨r11 h.1.1, r11 h.2.1⟩)
          (fun _ => (VG.Proof.AesGcm.Arm.oneCrypt_rel h6 h6' hq6 (by decide) (by decide)).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩)
            fun _ _ h => ⟨r11 h.1, r11 h.2⟩)
      obtain ⟨_, c8⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block [.mov .r0 (.reg .r7)]) h).isSome = true :=
        ⟨_, by taint_decide⟩
      have y8 := rel_wp (F := W) (F' := W) (G := W) (G' := W)
        (RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs [.r11]) (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [h.1, h.2]) c8)
        (fun s h => VG.Proof.AesGcm.Arm.mov07_wp h) (fun s h => VG.Proof.AesGcm.Arm.mov07_wp h)
      refine RelCT.mono (y1.seq (y2.seq (y3.seq (y4.seq (y5.seq (y6.seq (y7.seq y8))))))) (fun s s' h => ?_)
        fun _ _ h => h
      exact ⟨⟨h.1.1, pfx h0 hok h.1.1⟩, ⟨h.2.1, pfx h0' hok' h.2.1⟩⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have d := RelCT.taint (A := VG.Arm.taint) (P := fun s₁ s₂ => W s₁ ∧ W s₂) (c := .block restore) (Taint.ofRegs [.r11])
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1, h.2]) hB
  exact a.seq (b.seq (mid.seq d))

theorem open_ct : ConstantTime isa openArm.pre openArm.pub «open» :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.AesGcm.Arm.open_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.StreamInit`. -/
section

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_stream_init`

Untrusted: everything here is checked by Lean. `stream_init` saves our
caller's registers in `scratch` (`W`) and writes the state's `J₀`, its zero
accumulator and its first counter block with `j0` (`streamInit_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH)

/-- The layout of `stream_init`. -/
theorem siLay {s₀ : State} (h : streamInitArm.pre s₀) :
    Lay (s₀.gpr .r0) (s₀.gpr .r3) (VG.Proof.AesGcm.Arm.arg s₀ 0) s₀.sp := by
  obtain ⟨-, -, dcs, dcW, -, -, dsW, -, -, bc, -, bs, bW, fc, -, fs, fW, sp8, -⟩ := h
  exact Lay.of fc fs fW sp8 dcs dcW dsW bc bs bW

/-- After the entry, from `s₀`. -/
structure SI1 (s₀ s₁ : State) : Prop where
  env : Env (s₀.gpr .r0) (s₀.gpr .r3) (VG.Proof.AesGcm.Arm.arg s₀ 0) s₀.sp (s₀.gpr .r7) (s₀.gpr .r8) s₁
  r4 : s₁.gpr .r4 = s₀.gpr .r1
  r5 : s₁.gpr .r5 = s₀.gpr .r2
  rd : s₁.rd = s₀.rd
  wr : s₁.wr = s₀.wr
  saved : VG.Proof.AesGcm.Arm.SavedAt s₁.mem (VG.Proof.AesGcm.Arm.arg s₀ 0) s₀
  frame : Frame [VG.Proof.AesGcm.Arm.savedR (VG.Proof.AesGcm.Arm.arg s₀ 0)] s₀.mem s₁.mem

theorem si1_wp {s₀ : State} (h : streamInitArm.pre s₀) : WP isa (.block streamInitPre) s₀ (VG.Proof.AesGcm.Arm.SI1 s₀) := by
  have hp := h
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fW, -, spf⟩ := hp
  have hC : Covers [⟨State.addr (s₀.gpr .r0), 256⟩] (s₀.rd ++ s₀.wr) := by
    rw [hrd]; exact covers_of_mem (by simp)
  have hS : Covers [⟨State.addr (s₀.gpr .r3), 80⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have hW : Covers [⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 0), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have ha := VG.Proof.AesGcm.Arm.arg_in (s := s₀) (n := 1) (i := 0) (by decide) spf (by rw [hrd]; simp)
  refine VG.Proof.AesGcm.Arm.entry_ok (off := 0) (by decide) ha fW hW fun s₁ g12 g rd wr sp sv fr => WP.of_runBlock ⟨_, by arun [], ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩, ?_, ?_, ?_, ?_, sv, fr⟩
  any_goals (simp [gpr_setReg, g, g12]; done)
  · simp [gpr_setReg, g, g12, VG.Proof.AesGcm.Arm.stackArg_zero]
  · exact sp
  · change Covers _ (s₁.rd ++ s₁.wr); rw [rd, wr]; exact hC
  · change Covers _ s₁.wr; rw [wr]; exact hS
  · change Covers _ s₁.wr; rw [wr]; exact hW
  · exact rd
  · exact wr

theorem si_j0In {s₀ s₁ : State} (h : streamInitArm.pre s₀) (h1 : VG.Proof.AesGcm.Arm.SI1 s₀ s₁) :
    VG.Proof.AesGcm.Arm.J0In (s₀.gpr .r0) (s₀.gpr .r3) (VG.Proof.AesGcm.Arm.arg s₀ 0) s₀.sp (s₀.gpr .r7) (s₀.gpr .r8) (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (s₀.gpr .r1) (s₀.gpr .r2).toNat s₁ := by
  have L := VG.Proof.AesGcm.Arm.siLay h
  obtain ⟨hrd, -, -, -, dns, dnW, -, -, -, -, bn, -, -, -, fn, -, -, -, -⟩ := h
  refine ⟨h1.env, ?_, h1.r4, by rw [h1.r5]; simp, ⟨?_, (s₀.gpr .r2).isLt, fn, dns, dnW, bn⟩⟩
  · rw [VG.Proof.AesGcm.Arm.ctxH_eq, blockAt_frame h1.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.ctx_w (a := 240) (n := 16) (show 240 + 16 ≤ 256 by decide) (show 128 + 36 ≤ 2560 by decide))]
  · rw [h1.rd, h1.wr, hrd]; exact covers_of_mem (by simp)

/-- After `j0`. -/
def SI2 (s₀ s₂ : State) : Prop :=
  ∃ s₁, VG.Proof.AesGcm.Arm.SI1 s₀ s₁ ∧ VG.Proof.AesGcm.Arm.J0Out (s₀.gpr .r0) (s₀.gpr .r3) (VG.Proof.AesGcm.Arm.arg s₀ 0) s₀.sp (s₀.gpr .r8)
    (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₁.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat) s₁.mem s₂

theorem si_fin {s₀ s₂ : State} (h : streamInitArm.pre s₀) (h2 : VG.Proof.AesGcm.Arm.SI2 s₀ s₂) :
    WP isa (.block restore) s₂ fun s' => abiPreserved s₀ s' ∧ streamInitArm.post s₀ s' := by
  have L := VG.Proof.AesGcm.Arm.siLay h
  obtain ⟨s₁, h1, ho⟩ := h2
  obtain ⟨k7, he⟩ := ho.env
  obtain ⟨-, -, -, -, -, dnW, -, -, -, -, -, -, -, -, fn, -, fW, -, -⟩ := h
  refine WP.mono (VG.Proof.AesGcm.Arm.restore_ok he.r11 fW (covers_left he.perm.w) (h1.saved.frame ho.frame (VG.Proof.AesGcm.Arm.saved_j0Frame L)) he.sp)
    fun s' hh => ⟨hh.1, fun ciph => ?_⟩
  have hm := hh.2.1
  have hiv : bytesAt s₁.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat =
      bytesAt s₀.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat :=
    bytesAt_frame h1.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dnW.sub_right (Lay.wSub (by decide))) (by omega)
  have hj := ho.j0; have hy := ho.y; have hcb := ho.cb
  rw [hiv] at hj hcb
  rw [Proof.Gcm.streamRepr_iff, hm, VG.Proof.AesGcm.Arm.ofNat_lit, VG.Proof.AesGcm.Arm.ofNat_lit, VG.Proof.AesGcm.Arm.ofNat_lit, VG.Proof.AesGcm.Arm.ofNat_lit]
  exact ⟨hj, Proof.Gcm.absorbed_nil _ hy, Proof.Gcm.ctr_zero _ _ _ _ hcb⟩

theorem streamInit_wp {s₀ : State} (h : streamInitArm.pre s₀) :
    WP isa streamInit s₀ fun s' => abiPreserved s₀ s' ∧ streamInitArm.post s₀ s' :=
  WP.seq (WP.mono (VG.Proof.AesGcm.Arm.si1_wp h) fun s₁ h1 => WP.seq (WP.mono (VG.Proof.AesGcm.Arm.j0_ok (VG.Proof.AesGcm.Arm.siLay h) (VG.Proof.AesGcm.Arm.si_j0In h h1)) fun _ ho =>
    VG.Proof.AesGcm.Arm.si_fin h ⟨s₁, h1, ho⟩))

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.StreamAad`. -/
section

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_stream_aad`

Untrusted: everything here is checked by Lean. `stream_aad` saves our
caller's registers in `scratch` (`W`) and absorbs the additional data into
GHASH with `absorb` (`streamAad_wp`), with `len(A) mod 16` from the low
word of `aad_len`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ctxH)

theorem saLay {s₀ : State} (h : streamAadArm.pre s₀) :
    Lay (s₀.gpr .r0) (s₀.gpr .r1) (VG.Proof.AesGcm.Arm.arg s₀ 2) s₀.sp := by
  obtain ⟨-, -, dcs, dcW, -, -, dsW, -, -, bc, -, bs, bW, fc, fs, -, fW, sp8, -⟩ := h
  exact Lay.of fc fs fW sp8 dcs dcW dsW bc bs bW

/-- After the entry, from `s₀`. -/
structure SA1 (s₀ s₁ : State) : Prop where
  env : Env (s₀.gpr .r0) (s₀.gpr .r1) (VG.Proof.AesGcm.Arm.arg s₀ 2) s₀.sp (s₀.gpr .r7) (s₀.gpr .r8) s₁
  r4 : s₁.gpr .r4 = VG.Proof.AesGcm.Arm.arg s₀ 0
  r5 : s₁.gpr .r5 = VG.Proof.AesGcm.Arm.arg s₀ 1
  r6 : s₁.gpr .r6 = BitVec.ofNat 32 ((s₀.gpr .r2).toNat % 16)
  rd : s₁.rd = s₀.rd
  wr : s₁.wr = s₀.wr
  saved : VG.Proof.AesGcm.Arm.SavedAt s₁.mem (VG.Proof.AesGcm.Arm.arg s₀ 2) s₀
  frame : Frame [VG.Proof.AesGcm.Arm.savedR (VG.Proof.AesGcm.Arm.arg s₀ 2)] s₀.mem s₁.mem

theorem sa1_wp {s₀ : State} (h : streamAadArm.pre s₀) : WP isa (.block streamAadPre) s₀ (VG.Proof.AesGcm.Arm.SA1 s₀) := by
  have hp := h
  obtain ⟨hrd, hwr, -, -, -, -, -, -, dWA, -, -, -, -, -, -, -, fW, -, spf⟩ := hp
  have hC : Covers [⟨State.addr (s₀.gpr .r0), 256⟩] (s₀.rd ++ s₀.wr) := by
    rw [hrd]; exact covers_of_mem (by simp)
  have hS : Covers [⟨State.addr (s₀.gpr .r1), 80⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have hW : Covers [⟨State.addr (VG.Proof.AesGcm.Arm.arg s₀ 2), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have ha : ∀ i < 3, InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 (4 * i))) 4 :=
    fun i hi => VG.Proof.AesGcm.Arm.arg_in (n := 3) hi spf (by rw [hrd]; simp)
  have hA : ∀ r ∈ [VG.Proof.AesGcm.Arm.savedR (VG.Proof.AesGcm.Arm.arg s₀ 2)], (VG.Proof.AesGcm.Arm.args s₀ 3).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (dWA.sub_left (Lay.wSub (by decide))).symm
  refine VG.Proof.AesGcm.Arm.entry_ok (off := 8) (by decide) (ha 2 (by decide)) fW hW fun s₁ g12 g rd wr sp sv fr => ?_
  have a₀ := ha 0 (by decide); have a₁ := ha 1 (by decide)
  rw [← rd, ← wr, ← sp] at a₀ a₁
  have e₀ := VG.Proof.AesGcm.Arm.arg_frame (s' := s₁) sp spf fr hA (i := 0) (by decide)
  have e₁ := VG.Proof.AesGcm.Arm.arg_frame (s' := s₁) sp spf fr hA (i := 1) (by decide)
  rw [VG.Proof.AesGcm.Arm.stackArg_zero] at e₀
  simp only [VG.Proof.AesGcm.Arm.stackArg_eq, Nat.mul_one] at e₁ a₁
  simp only [Nat.mul_zero] at a₀
  have hand := and15 (s₀.gpr .r2)
  refine WP.of_runBlock ⟨_, by arun [a₀, a₁], ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩, ?_, ?_, ?_, ?_, ?_, sv, fr⟩
  any_goals (simp [gpr_setReg, g, g12, hand]; done)
  · simp [gpr_setReg, g, g12]; rfl
  · exact sp
  · change Covers _ (s₁.rd ++ s₁.wr); rw [rd, wr]; exact hC
  · change Covers _ s₁.wr; rw [wr]; exact hS
  · change Covers _ s₁.wr; rw [wr]; exact hW
  · simp [gpr_setReg, e₀]
  · simp [gpr_setReg, e₁, stackArg]; rfl
  · exact rd
  · exact wr

theorem sa_absIn {s₀ s₁ : State} (h : streamAadArm.pre s₀) (h1 : VG.Proof.AesGcm.Arm.SA1 s₀ s₁) {x : List Byte}
    (hx : x.length % 16 = (s₀.gpr .r2).toNat % 16) :
    AbsIn (s₀.gpr .r0) (s₀.gpr .r1) (VG.Proof.AesGcm.Arm.arg s₀ 2) s₀.sp (s₀.gpr .r7) (s₀.gpr .r8) 16
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) x (VG.Proof.AesGcm.Arm.arg s₀ 0) (VG.Proof.AesGcm.Arm.arg s₀ 1).toNat s₁ := by
  have L := VG.Proof.AesGcm.Arm.saLay h
  obtain ⟨hrd, -, -, -, dDs, dDW, -, -, -, -, bD, -, -, -, -, fD, -, -, -⟩ := h
  refine ⟨h1.env, h1.r4, by rw [h1.r5]; simp, by rw [h1.r6, hx], ⟨?_, (VG.Proof.AesGcm.Arm.arg s₀ 1).isLt, fD, dDs, dDW, bD⟩, ?_⟩
  · rw [h1.rd, h1.wr, hrd]; exact covers_of_mem (by simp)
  · rw [VG.Proof.AesGcm.Arm.ctxH_eq, blockAt_frame h1.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.ctx_w (a := 240) (n := 16) (show 240 + 16 ≤ 256 by decide) (show 128 + 36 ≤ 2560 by decide))]

/-- After `absorb`. -/
def SA2 (s₀ : State) (x : List Byte) (s₂ : State) : Prop :=
  ∃ s₁, VG.Proof.AesGcm.Arm.SA1 s₀ s₁ ∧ AbsOut (s₀.gpr .r0) (s₀.gpr .r1) (VG.Proof.AesGcm.Arm.arg s₀ 2) s₀.sp (s₀.gpr .r7) (s₀.gpr .r8) 16
    (ctxH s₀.mem (State.addr (s₀.gpr .r0))) x (x ++ bytesAt s₁.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 0)) (VG.Proof.AesGcm.Arm.arg s₀ 1).toNat) s₁.mem s₂

theorem sa_fin {s₀ s₂ : State} (h : streamAadArm.pre s₀) {x : List Byte} (h2 : VG.Proof.AesGcm.Arm.SA2 s₀ x s₂) :
    WP isa (.block restore) s₂ fun s' => abiPreserved s₀ s' ∧ ∀ ciph iv,
      StreamRepr s₀.mem (State.addr (s₀.gpr .r1)) ciph (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv x [] →
      StreamRepr s'.mem (State.addr (s₀.gpr .r1)) ciph (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv
        (x ++ bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 0)) (VG.Proof.AesGcm.Arm.arg s₀ 1).toNat) [] := by
  have L := VG.Proof.AesGcm.Arm.saLay h
  obtain ⟨s₁, h1, ho⟩ := h2
  have he := ho.env
  obtain ⟨-, -, -, -, -, dDW, dsW, -, -, -, -, -, -, -, -, fD, fW, -, -⟩ := h
  refine WP.mono (VG.Proof.AesGcm.Arm.restore_ok he.r11 fW (covers_left he.perm.w) (h1.saved.frame ho.frame (VG.Proof.AesGcm.Arm.saved_absFrame L (.inr rfl)))
    he.sp) fun s' hh => ⟨hh.1, fun ciph iv hs => ?_⟩
  have hm := hh.2.1
  have hd : bytesAt s₁.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 0)) (VG.Proof.AesGcm.Arm.arg s₀ 1).toNat =
      bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 0)) (VG.Proof.AesGcm.Arm.arg s₀ 1).toNat :=
    bytesAt_frame h1.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dDW.sub_right (Lay.wSub (by decide))) (by omega)
  have hab := ho.abs
  rw [hd] at hab
  have dS : ∀ {d : Nat}, d + 16 ≤ 80 → ∀ r ∈ [VG.Proof.AesGcm.Arm.savedR (VG.Proof.AesGcm.Arm.arg s₀ 2)],
      (⟨State.addr (s₀.gpr .r1) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact L.st_w hd (.inr ⟨by decide, by decide⟩)
  have dA : ∀ {d : Nat}, (d = 0 ∨ d = 48 ∨ d = 64) → ∀ r ∈ absFrame (s₀.gpr .r1) (VG.Proof.AesGcm.Arm.arg s₀ 2) s₀.sp 16,
      (⟨State.addr (s₀.gpr .r1) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.st_st (by omega) (by omega) (by decide)
    · exact Lay.st_st (by omega) (by omega) (by decide)
    · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
    · exact (L.stk_st (by omega)).symm
  have keep : ∀ {d : Nat}, (d = 0 ∨ d = 48 ∨ d = 64) →
      blockAt s'.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 d) =
        blockAt s₀.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 d) := fun hd => by
    rw [hm, blockAt_frame ho.frame (dA hd), blockAt_frame h1.frame (dS (by omega))]
  rw [Proof.Gcm.streamRepr_iff] at hs ⊢
  obtain ⟨hj, ha, hc⟩ := hs
  simp only [VG.Proof.AesGcm.Arm.ofNat_lit] at hj ha hc ⊢
  refine ⟨by simpa using (keep (d := 0) (.inl rfl)).trans (by simpa using hj), ?_, ?_⟩
  · rw [hm]
    refine hab (ha.congr ?_ ?_)
    · rw [blockAt_frame h1.frame (dS (by decide))]
    · rw [bytesAt_frame h1.frame (fun r hr => (dS (d := 32) (by decide) r hr).sub_left
        (Region.sub_prefix (by have := Nat.mod_lt (Spec.Gcm.ghashInput x []).length (show 16 > 0 by decide); omega)))
        (by have := Nat.mod_lt (Spec.Gcm.ghashInput x []).length (show 16 > 0 by decide); omega)]
  · exact hc.congr (keep (.inr (.inl rfl))) (keep (.inr (.inr rfl)))

theorem sa_run {s₀ : State} (h : streamAadArm.pre s₀) {x : List Byte} (hx : x.length % 16 = (s₀.gpr .r2).toNat % 16) :
    WP isa streamAad s₀ fun s' => abiPreserved s₀ s' ∧ ∀ ciph iv,
      StreamRepr s₀.mem (State.addr (s₀.gpr .r1)) ciph (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv x [] →
      StreamRepr s'.mem (State.addr (s₀.gpr .r1)) ciph (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv
        (x ++ bytesAt s₀.mem (State.addr (VG.Proof.AesGcm.Arm.arg s₀ 0)) (VG.Proof.AesGcm.Arm.arg s₀ 1).toNat) [] :=
  WP.seq (WP.mono (VG.Proof.AesGcm.Arm.sa1_wp h) fun s₁ h1 => WP.seq (WP.mono (absorb_ok (VG.Proof.AesGcm.Arm.saLay h) (.inr rfl) (VG.Proof.AesGcm.Arm.sa_absIn h h1 hx))
    fun _ ho => VG.Proof.AesGcm.Arm.sa_fin h ⟨s₁, h1, ho⟩))

theorem streamAad_wp {s₀ : State} (h : streamAadArm.pre s₀) :
    WP isa streamAad s₀ fun s' => abiPreserved s₀ s' ∧ streamAadArm.post s₀ s' := by
  have h₀ := VG.Proof.AesGcm.Arm.sa_run h (x := List.replicate ((s₀.gpr .r2).toNat % 16) 0) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : (Block → Block) × List Byte × List Byte =>
      StreamRepr s₀.mem (State.addr (s₀.gpr .r1)) i.1 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) i.2.1 i.2.2 [] ∧
        (s₀.gpr .r3 ++ s₀.gpr .r2) = BitVec.ofNat 64 i.2.2.length)
    fun i hi => WP.mono (VG.Proof.AesGcm.Arm.sa_run h (x := i.2.2) (VG.Proof.AesGcm.Arm.low_mod16 hi.2).symm) fun _ hh => hh.2 i.1 i.2.1 hi.1)
    fun s' hh => ⟨hh.1, fun ciph iv a hs hl => hh.2 ⟨ciph, iv, a⟩ ⟨hs, hl⟩⟩

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.CTStream`. -/
section

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_stream_init` and `vg_aes_gcm_stream_aad` are constant time

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Impl.AesGcm.Arm

theorem streamInit_rel {s₀ s₀' : State} (h0 : streamInitArm.pre s₀) (h0' : streamInitArm.pre s₀')
    (hq : streamInitArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') streamInit fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, q₅⟩ := hq
  have L := VG.Proof.AesGcm.Arm.siLay h0
  have spf := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hw : ∀ {t : State}, streamInitArm.pre t → ∀ r ∈ t.wr, (VG.Proof.AesGcm.Arm.args t 1).Disjoint r := fun {t} ht r hr => by
    obtain ⟨-, hwr, -, -, -, -, -, dsA, dWA, -⟩ := ht
    rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dsA.symm
    · exact dWA.symm
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (VG.Arm.argTaint [.r0, .r1, .r2, .r3] (4 * 1)) (.block streamInitPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := VG.Proof.AesGcm.Arm.SI1 s₀) (G' := VG.Proof.AesGcm.Arm.SI1 s₀')
    (VG.Arm.argTaint [.r0, .r1, .r2, .r3] (4 * 1)) (c := .block streamInitPre)
    (fun s s' e e' => by
      subst e e'
      refine (ArgsKeep.refl 1 s).agree (ArgsKeep.refl 1 s') q₀ spf (fun i hi => by
        obtain rfl : i = 0 := by omega
        exact q₅) (hw h0) (hw h0') fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) ⟨_, hA⟩
    (fun s e => by rw [e]; exact VG.Proof.AesGcm.Arm.si1_wp h0) (fun s e => by rw [e]; exact VG.Proof.AesGcm.Arm.si1_wp h0')
  have hlt := (s₀.gpr .r2).isLt
  have b := rel_wp (F := VG.Proof.AesGcm.Arm.SI1 s₀) (F' := VG.Proof.AesGcm.Arm.SI1 s₀') (G := VG.Proof.AesGcm.Arm.SI2 s₀) (G' := VG.Proof.AesGcm.Arm.SI2 s₀')
    (VG.Proof.AesGcm.Arm.rel_of_ct (VG.Proof.AesGcm.Arm.j0_ct L (Np := s₀.gpr .r1) (n := (s₀.gpr .r2).toNat) hlt) (fun s h1 => ⟨_, _, _, VG.Proof.AesGcm.Arm.si_j0In h0 h1⟩)
      (fun s h1 => by
        have := VG.Proof.AesGcm.Arm.si_j0In h0' h1
        rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₀] at this
        exact ⟨_, _, _, this⟩))
    (fun s h1 => WP.mono (VG.Proof.AesGcm.Arm.j0_ok (VG.Proof.AesGcm.Arm.siLay h0) (VG.Proof.AesGcm.Arm.si_j0In h0 h1)) fun s' ho => ⟨s, h1, ho⟩)
    (fun s h1 => WP.mono (VG.Proof.AesGcm.Arm.j0_ok (VG.Proof.AesGcm.Arm.siLay h0') (VG.Proof.AesGcm.Arm.si_j0In h0' h1)) fun s' ho => ⟨s, h1, ho⟩)
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have c := RelCT.taint (A := VG.Arm.taint) (P := fun s₁ s₂ => VG.Proof.AesGcm.Arm.SI2 s₀ s₁ ∧ VG.Proof.AesGcm.Arm.SI2 s₀' s₂) (c := .block restore)
    (Taint.ofRegs [.r11]) (fun s₁ s₂ ⟨⟨_, _, h₁⟩, ⟨_, _, h₂⟩⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨_, e₁⟩ := h₁.env; obtain ⟨_, e₂⟩ := h₂.env
      rw [e₁.r11, e₂.r11, q₅]) hB
  exact a.seq (b.seq c)

theorem streamInit_ct : ConstantTime isa streamInitArm.pre streamInitArm.pub streamInit :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.AesGcm.Arm.streamInit_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem streamAad_rel {s₀ s₀' : State} (h0 : streamAadArm.pre s₀) (h0' : streamAadArm.pre s₀')
    (hq : streamAadArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') streamAad fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := hq
  have L := VG.Proof.AesGcm.Arm.saLay h0
  have spf := h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hw : ∀ {t : State}, streamAadArm.pre t → ∀ r ∈ t.wr, (VG.Proof.AesGcm.Arm.args t 3).Disjoint r := fun {t} ht r hr => by
    obtain ⟨-, hwr, -, -, -, -, -, dsA, dWA, -⟩ := ht
    rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dsA.symm
    · exact dWA.symm
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (VG.Arm.argTaint [.r0, .r1, .r2, .r3] (4 * 3)) (.block streamAadPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := VG.Proof.AesGcm.Arm.SA1 s₀) (G' := VG.Proof.AesGcm.Arm.SA1 s₀')
    (VG.Arm.argTaint [.r0, .r1, .r2, .r3] (4 * 3)) (c := .block streamAadPre)
    (fun s s' e e' => by
      subst e e'
      refine (ArgsKeep.refl 3 s).agree (ArgsKeep.refl 3 s') q₀ spf (fun i hi => by
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
        · exact q₅
        · exact q₆
        · exact q₇) (hw h0) (hw h0') fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) ⟨_, hA⟩
    (fun s e => by rw [e]; exact VG.Proof.AesGcm.Arm.sa1_wp h0) (fun s e => by rw [e]; exact VG.Proof.AesGcm.Arm.sa1_wp h0')
  have b := rel_wp (F := VG.Proof.AesGcm.Arm.SA1 s₀) (F' := VG.Proof.AesGcm.Arm.SA1 s₀') (G := fun s => ∃ x, VG.Proof.AesGcm.Arm.SA2 s₀ x s) (G' := fun s => ∃ x, VG.Proof.AesGcm.Arm.SA2 s₀' x s)
    (VG.Proof.AesGcm.Arm.rel_of_ct (VG.Proof.AesGcm.Arm.absorb_ct L (yo := 16) (.inr rfl) (D := VG.Proof.AesGcm.Arm.arg s₀ 0) (n := (VG.Proof.AesGcm.Arm.arg s₀ 1).toNat)
      (q := (s₀.gpr .r2).toNat % 16) (Nat.mod_lt _ (by decide)))
      (fun s h1 => ⟨_, _, _, _, by simp, VG.Proof.AesGcm.Arm.sa_absIn h0 h1 (x := List.replicate ((s₀.gpr .r2).toNat % 16) 0) (by simp)⟩)
      (fun s h1 => by
        have := VG.Proof.AesGcm.Arm.sa_absIn h0' h1 (x := List.replicate ((s₀'.gpr .r2).toNat % 16) 0) (by simp)
        rw [← q₁, ← q₂, ← q₃, ← q₅, ← q₆, ← q₇, ← q₀] at this
        exact ⟨_, _, _, _, by simp, this⟩))
    (fun s h1 => WP.mono (absorb_ok L (.inr rfl) (VG.Proof.AesGcm.Arm.sa_absIn h0 h1 (x := List.replicate ((s₀.gpr .r2).toNat % 16) 0)
      (by simp))) fun s' ho => ⟨_, s, h1, ho⟩)
    (fun s h1 => WP.mono (absorb_ok (VG.Proof.AesGcm.Arm.saLay h0') (.inr rfl) (VG.Proof.AesGcm.Arm.sa_absIn h0' h1
      (x := List.replicate ((s₀'.gpr .r2).toNat % 16) 0) (by simp))) fun s' ho => ⟨_, s, h1, ho⟩)
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true := ⟨_, by taint_decide⟩
  have c := RelCT.taint (A := VG.Arm.taint) (P := fun s₁ s₂ => (∃ x, VG.Proof.AesGcm.Arm.SA2 s₀ x s₁) ∧ ∃ x, VG.Proof.AesGcm.Arm.SA2 s₀' x s₂)
    (c := .block restore) (Taint.ofRegs [.r11]) (fun s₁ s₂ ⟨⟨_, _, _, h₁⟩, ⟨_, _, _, h₂⟩⟩ =>
      Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h₁.env.r11, h₂.env.r11, q₇]) hB
  exact a.seq (b.seq c)

theorem streamAad_ct : ConstantTime isa streamAadArm.pre streamAadArm.pub streamAad :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.AesGcm.Arm.streamAad_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.InitCT`. -/
section

/-!
# AES-GCM on ARMv7: `vg_aes_gcm_init` is constant time

Untrusted: everything here is checked by Lean. The blocks are checked by the
taint analysis, from the registers the correctness proof pins (the
arguments, then `r8`, `r9` and `r11`); the calls of `vg_aes_expand_key_scratch` and
`vg_aes_ctr32` are constant time by their own proofs (`key_rel`, `ctr_rel`),
with the same arguments in both runs.
-/

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Impl.AesGcm.Arm

theorem IS4.r11 {s₀ s₄ : State} (h : initArm.pre s₀) (h4 : VG.Proof.AesGcm.Arm.IS4 s₀ s₄) : s₄.gpr .r11 = s₀.gpr .r3 := by
  obtain ⟨s₃, h3, cp⟩ := h4
  obtain ⟨-, -, -, -, -, -, -, -, -, g11, -⟩ := h3.facts h
  rw [cp.saved _ (by decide) (by decide), g11]

theorem init_rel {s₀ s₀' : State} (h0 : initArm.pre s₀) (h0' : initArm.pre s₀') (hq : initArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') init fun _ _ => True := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄⟩ := hq
  have eR : VG.Proof.AesGcm.Arm.initR s₀' = VG.Proof.AesGcm.Arm.initR s₀ := by simp only [VG.Proof.AesGcm.Arm.initR, q₂]
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := VG.Proof.AesGcm.Arm.IS1 s₀) (G' := VG.Proof.AesGcm.Arm.IS1 s₀') (c := .block initPre)
    (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun s s' e e' => by
      subst e e'
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) ⟨_, by taint_decide⟩
    (fun s e => by rw [e]; exact VG.Proof.AesGcm.Arm.is1_wp h0) (fun s e => by rw [e]; exact VG.Proof.AesGcm.Arm.is1_wp h0')
  have b := rel_wp (F := VG.Proof.AesGcm.Arm.IS1 s₀) (F' := VG.Proof.AesGcm.Arm.IS1 s₀') (G := VG.Proof.AesGcm.Arm.IS2 s₀) (G' := VG.Proof.AesGcm.Arm.IS2 s₀')
    (key_rel fun s₁ s₂ h => ⟨_, _, _, _, VG.Proof.AesGcm.Arm.init_kc h0 h.1, by have := VG.Proof.AesGcm.Arm.init_kc h0' h.2; rwa [← q₁, ← q₂, ← q₃, ← q₄] at this⟩)
    (fun s₁ h1 => WP.mono (key_call (VG.Proof.AesGcm.Arm.init_kc h0 h1)) fun s₂ kp => ⟨s₁, h1, kp⟩)
    (fun s₁ h1 => WP.mono (key_call (VG.Proof.AesGcm.Arm.init_kc h0' h1)) fun s₂ kp => ⟨s₁, h1, kp⟩)
  have c := rel_agree (F := VG.Proof.AesGcm.Arm.IS2 s₀) (F' := VG.Proof.AesGcm.Arm.IS2 s₀') (G := VG.Proof.AesGcm.Arm.IS3 s₀) (G' := VG.Proof.AesGcm.Arm.IS3 s₀') (c := .block initArgs)
    (Taint.ofRegs [.r8, .r9, .r11])
    (fun s s' e e' => by
      obtain ⟨g9, g11, g8, -⟩ := e.g
      obtain ⟨g9', g11', g8', -⟩ := e'.g
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [g8, g8', q₂]
      · rw [g9, g9', q₃]
      · rw [g11, g11', q₄]) ⟨_, by taint_decide⟩
    (fun s e => by obtain ⟨s₃, run⟩ := VG.Proof.AesGcm.Arm.is3_run h0 e; exact WP.of_runBlock ⟨s₃, run, s, e, run⟩)
    (fun s e => by obtain ⟨s₃, run⟩ := VG.Proof.AesGcm.Arm.is3_run h0' e; exact WP.of_runBlock ⟨s₃, run, s, e, run⟩)
  have d := rel_wp (F := VG.Proof.AesGcm.Arm.IS3 s₀) (F' := VG.Proof.AesGcm.Arm.IS3 s₀') (G := VG.Proof.AesGcm.Arm.IS4 s₀) (G' := VG.Proof.AesGcm.Arm.IS4 s₀')
    (ctr_rel fun s₁ s₂ h => ⟨_, _, _, _, _, _, VG.Proof.AesGcm.Arm.init_cc h0 h.1,
      by have := VG.Proof.AesGcm.Arm.init_cc h0' h.2; rwa [← q₃, ← q₄, eR] at this,
      by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, e⟩ := h.1.facts h0
         obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, e'⟩ := h.2.facts h0'
         rw [e, e', q₀]⟩)
    (fun s₃ h3 => WP.mono (ctr_call (VG.Proof.AesGcm.Arm.init_cc h0 h3)) fun s₄ cp => ⟨s₃, h3, cp⟩)
    (fun s₃ h3 => WP.mono (ctr_call (VG.Proof.AesGcm.Arm.init_cc h0' h3)) fun s₄ cp => ⟨s₃, h3, cp⟩)
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r11]) (.block restore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have e := RelCT.taint (A := VG.Arm.taint) (P := fun s₁ s₂ => VG.Proof.AesGcm.Arm.IS4 s₀ s₁ ∧ VG.Proof.AesGcm.Arm.IS4 s₀' s₂) (c := .block restore) (Taint.ofRegs [.r11])
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.r11 h0, h.2.r11 h0', q₄]) hB
  exact a.seq (b.seq (c.seq (d.seq e)))

theorem init_ct : ConstantTime isa initArm.pre initArm.pub init :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.AesGcm.Arm.init_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.Verified`. -/
section

/-!
# AES-GCM on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, a state satisfying each precondition, and the shared contracts of
`Spec/Gcm/Contract.lean` with the working space as a last argument
(`Proof/AesGcm/Scratch.lean`), with 8 bytes of stack: each call of
`vg_aes_ctr32` or `vg_ghash` pushes two words.
-/

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Impl.AesGcm.Arm

/-- A state with the given registers, the stack pointer at `0x8000`, memory
of zeros (so stack arguments of 0) and the given regions. -/
def mkSat (g : Reg → BitVec 32) (rd wr : List Region) : State where
  gpr := g
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := rd
  wr := wr

/-- A state satisfying `vg_aes_gcm_init`'s precondition. -/
def initSat : State :=
  VG.Proof.AesGcm.Arm.mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 16 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0)
    [⟨0x1000, 16⟩] [⟨0x2000, 256⟩, ⟨0x3000, 2560⟩]

theorem init_verified : Verified Arm.target init (Proof.AesGcm.initScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => VG.Proof.AesGcm.Arm.init_wp hs) VG.Proof.AesGcm.Arm.init_ct (by
    sig_implies [Proof.AesGcm.initScratchContract, Proof.AesGcm.initScratchSig, Spec.Gcm.initPre, Spec.Gcm.initPost, VG.Proof.AesGcm.Arm.initArm, VG.Proof.AesGcm.Arm.bel, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [initSat, mkSat] using VG.Proof.AesGcm.Arm.initSat)

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition (with no nonce). -/
def siSat : State :=
  VG.Proof.AesGcm.Arm.mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0 | .r3 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x8000, 4⟩] [⟨0x3000, 80⟩, ⟨0, 2560⟩]

theorem streamInit_verified :
    Verified Arm.target streamInit (Proof.AesGcm.streamInitScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => VG.Proof.AesGcm.Arm.streamInit_wp hs) VG.Proof.AesGcm.Arm.streamInit_ct (by
    sig_implies [Proof.AesGcm.streamInitScratchContract, Proof.AesGcm.streamInitScratchSig, Spec.Gcm.streamInitPost, VG.Proof.AesGcm.Arm.streamInitArm, VG.Proof.AesGcm.Arm.bel, VG.Proof.AesGcm.Arm.arg, VG.Proof.AesGcm.Arm.args, VG.Proof.AesGcm.Arm.arg64,
      VG.Proof.AesGcm.Arm.roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [siSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.AesGcm.Arm.siSat)

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition (with no data). -/
def saSat : State :=
  VG.Proof.AesGcm.Arm.mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0, 0⟩, ⟨0x8000, 12⟩] [⟨0x3000, 80⟩, ⟨0, 2560⟩]

theorem streamAad_verified :
    Verified Arm.target streamAad (Proof.AesGcm.streamAadScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => VG.Proof.AesGcm.Arm.streamAad_wp hs) VG.Proof.AesGcm.Arm.streamAad_ct (by
    sig_implies [Proof.AesGcm.streamAadScratchContract, Proof.AesGcm.streamAadScratchSig, Spec.Gcm.streamAadPost, VG.Proof.AesGcm.Arm.streamAadArm, VG.Proof.AesGcm.Arm.bel, VG.Proof.AesGcm.Arm.arg, VG.Proof.AesGcm.Arm.args, VG.Proof.AesGcm.Arm.arg64,
      VG.Proof.AesGcm.Arm.roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [saSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.AesGcm.Arm.saSat)

/-- A state satisfying the precondition of `vg_aes_gcm_stream_encrypt` and `_decrypt` (with no
data, and `scratch` at 0). -/
def scSat : State :=
  VG.Proof.AesGcm.Arm.mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x8000, 28⟩] [⟨0x3000, 80⟩, ⟨0, 0⟩, ⟨0, 2560⟩]

theorem streamEncrypt_verified :
    Verified Arm.target streamEncrypt (Proof.AesGcm.streamEncryptScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => VG.Proof.AesGcm.Arm.streamEncrypt_wp hs) VG.Proof.AesGcm.Arm.streamEncrypt_ct (by
    sig_implies [Proof.AesGcm.streamEncryptScratchContract, Proof.AesGcm.streamCryptScratchSig, Spec.Gcm.streamTextPre, Spec.Gcm.streamEncryptPost, Spec.Gcm.streamDecryptPost, VG.Proof.AesGcm.Arm.streamEncryptArm, VG.Proof.AesGcm.Arm.streamCryptPre,
      VG.Proof.AesGcm.Arm.streamCryptPub, VG.Proof.AesGcm.Arm.bel, VG.Proof.AesGcm.Arm.arg, VG.Proof.AesGcm.Arm.args, VG.Proof.AesGcm.Arm.arg64, VG.Proof.AesGcm.Arm.roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
      [scSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.AesGcm.Arm.scSat)

theorem streamDecrypt_verified :
    Verified Arm.target streamDecrypt (Proof.AesGcm.streamDecryptScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => VG.Proof.AesGcm.Arm.streamDecrypt_wp hs) VG.Proof.AesGcm.Arm.streamDecrypt_ct (by
    sig_implies [Proof.AesGcm.streamDecryptScratchContract, Proof.AesGcm.streamCryptScratchSig, Spec.Gcm.streamTextPre, Spec.Gcm.streamEncryptPost, Spec.Gcm.streamDecryptPost, VG.Proof.AesGcm.Arm.streamDecryptArm, VG.Proof.AesGcm.Arm.streamCryptPre,
      VG.Proof.AesGcm.Arm.streamCryptPub, VG.Proof.AesGcm.Arm.bel, VG.Proof.AesGcm.Arm.arg, VG.Proof.AesGcm.Arm.args, VG.Proof.AesGcm.Arm.arg64, VG.Proof.AesGcm.Arm.roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
      [scSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.AesGcm.Arm.scSat)

/-- `mkSat`, with the stack argument 4 (at `0x8010`) `0x4000`. -/
def mkSat4 (g : Reg → BitVec 32) (rd wr : List Region) : State :=
  { VG.Proof.AesGcm.Arm.mkSat g rd wr with mem := fun a => if a = 0x8011 then 0x40 else 0 }

/-- A state satisfying `vg_aes_gcm_stream_finish`'s precondition (with `tag` at `0x4000` and `work`
at 0). -/
def fSat : State :=
  VG.Proof.AesGcm.Arm.mkSat4 (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x8000, 24⟩] [⟨0x3000, 80⟩, ⟨0x4000, 16⟩, ⟨0, 2560⟩]

theorem streamFinish_verified :
    Verified Arm.target streamFinish (Proof.AesGcm.streamFinishScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => VG.Proof.AesGcm.Arm.streamFinish_wp hs) VG.Proof.AesGcm.Arm.streamFinish_ct (by
    sig_implies [Proof.AesGcm.streamFinishScratchContract, Proof.AesGcm.streamFinishScratchSig,
      Spec.Gcm.streamFinishPre, Spec.Gcm.streamFinishPost, VG.Proof.AesGcm.Arm.streamFinishArm, VG.Proof.AesGcm.Arm.streamFinishPreArm, VG.Proof.AesGcm.Arm.finPub, VG.Proof.AesGcm.Arm.bel, VG.Proof.AesGcm.Arm.arg,
      VG.Proof.AesGcm.Arm.args, VG.Proof.AesGcm.Arm.arg64, VG.Proof.AesGcm.Arm.roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [fSat, mkSat4, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.AesGcm.Arm.fSat)

/-- A state satisfying `vg_aes_gcm_stream_verify`'s precondition (with no tag, and `work` at 0). -/
def vSat : State :=
  VG.Proof.AesGcm.Arm.mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0, 0⟩, ⟨0x8000, 28⟩] [⟨0x3000, 80⟩, ⟨0, 2560⟩]

/-- The postconditions match; the result is the low word of `r1:r0`. -/
theorem streamVerify_verified :
    Verified Arm.target streamVerify (Proof.AesGcm.streamVerifyScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => VG.Proof.AesGcm.Arm.streamVerify_wp hs) VG.Proof.AesGcm.Arm.streamVerify_ct
    { pre := by
        sig_implies_pre [Proof.AesGcm.streamVerifyScratchContract, Proof.AesGcm.streamVerifyScratchSig,
          Spec.Gcm.streamVerifyPre, VG.Proof.AesGcm.Arm.streamVerifyArm, VG.Proof.AesGcm.Arm.streamVerifyPreArm, VG.Proof.AesGcm.Arm.finPub, VG.Proof.AesGcm.Arm.bel, VG.Proof.AesGcm.Arm.arg, VG.Proof.AesGcm.Arm.args, VG.Proof.AesGcm.Arm.arg64, VG.Proof.AesGcm.Arm.roundsOk,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Proof.AesGcm.streamVerifyScratchContract, Proof.AesGcm.streamVerifyScratchSig,
          Spec.Gcm.streamVerifyPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [VG.Proof.AesGcm.Arm.streamVerifyArm, Arm.State.addr] at h
        have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        intro _ iv a c hs ha hc
        rw [e]
        exact h iv a c hs ha hc
      pub := by
        sig_implies_pub [Proof.AesGcm.streamVerifyScratchContract, Proof.AesGcm.streamVerifyScratchSig,
          VG.Proof.AesGcm.Arm.streamVerifyArm, VG.Proof.AesGcm.Arm.streamVerifyPreArm, VG.Proof.AesGcm.Arm.finPub, VG.Proof.AesGcm.Arm.bel, VG.Proof.AesGcm.Arm.arg, VG.Proof.AesGcm.Arm.args, VG.Proof.AesGcm.Arm.arg64, VG.Proof.AesGcm.Arm.roundsOk, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := by
        sig_implies_sat [Proof.AesGcm.streamVerifyScratchContract, Proof.AesGcm.streamVerifyScratchSig,
          Spec.Gcm.streamVerifyPre, VG.Proof.AesGcm.Arm.streamVerifyArm, VG.Proof.AesGcm.Arm.streamVerifyPreArm, VG.Proof.AesGcm.Arm.finPub, VG.Proof.AesGcm.Arm.bel, VG.Proof.AesGcm.Arm.arg, VG.Proof.AesGcm.Arm.args, VG.Proof.AesGcm.Arm.arg64, VG.Proof.AesGcm.Arm.roundsOk,
          Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
          [vSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.AesGcm.Arm.vSat }

/-- A state satisfying `vg_aes_gcm_seal`'s precondition (with no nonce, additional data or
data, `tag` at `0x4000` and `work` at 0). -/
def oSat : State :=
  VG.Proof.AesGcm.Arm.mkSat4 (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0x8000, 24⟩] [⟨0, 0⟩, ⟨0x4000, 16⟩, ⟨0, 2560⟩]

theorem seal_verified : Verified Arm.target «seal» (Proof.AesGcm.sealScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => VG.Proof.AesGcm.Arm.seal_wp hs) VG.Proof.AesGcm.Arm.seal_ct (by
    sig_implies [Proof.AesGcm.sealScratchContract, Proof.AesGcm.sealScratchSig, Spec.Gcm.sealPre,
      Spec.Gcm.sealPost, VG.Proof.AesGcm.Arm.sealArm, VG.Proof.AesGcm.Arm.sealPreArm, VG.Proof.AesGcm.Arm.onePub, VG.Proof.AesGcm.Arm.bel, VG.Proof.AesGcm.Arm.arg, VG.Proof.AesGcm.Arm.args, VG.Proof.AesGcm.Arm.arg64, VG.Proof.AesGcm.Arm.roundsOk, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [oSat, mkSat4, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.AesGcm.Arm.oSat)

/-- A state satisfying `vg_aes_gcm_open`'s precondition (with no nonce, additional data, data
or tag, and `work` at 0). -/
def opSat : State :=
  VG.Proof.AesGcm.Arm.mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x8000, 28⟩] [⟨0, 0⟩, ⟨0, 2560⟩]

/-- The leak `open` may have: whether it succeeds. -/
theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The postconditions match on `openResult`; the result is the low word of
`r1:r0`; and `open`'s public data include its leak, whether it succeeds (for
`rounds` of 10, 12 or 14). -/
theorem open_verified : Verified Arm.target «open» (Proof.AesGcm.openScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => VG.Proof.AesGcm.Arm.open_wp hs) VG.Proof.AesGcm.Arm.open_ct
    { pre := by
        sig_implies_pre [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre, VG.Proof.AesGcm.Arm.openArm,
          VG.Proof.AesGcm.Arm.openPreArm, VG.Proof.AesGcm.Arm.onePub, VG.Proof.AesGcm.Arm.bel, VG.Proof.AesGcm.Arm.arg, VG.Proof.AesGcm.Arm.args, VG.Proof.AesGcm.Arm.arg64, VG.Proof.AesGcm.Arm.roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify,
          Arm.Loc.val, Arm.State.addr]
      post := by
        intro s s' _ h
        sig_eval [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPost, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
        simp only [VG.Proof.AesGcm.Arm.openArm, Arm.State.addr] at h
        have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        intro _
        rw [e]
        exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openLeak, VG.Proof.AesGcm.Arm.openArm,
          VG.Proof.AesGcm.Arm.openPreArm, VG.Proof.AesGcm.Arm.onePub, VG.Proof.AesGcm.Arm.bel, VG.Proof.AesGcm.Arm.arg, VG.Proof.AesGcm.Arm.args, VG.Proof.AesGcm.Arm.arg64, VG.Proof.AesGcm.Arm.roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify,
          Arm.Loc.val, Arm.State.addr] at h
        obtain ⟨hsp, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6⟩ := h
        refine ⟨⟨hsp, h0, h1, h2, h3, fun i hi => ?_⟩, fun hr => VG.Proof.AesGcm.Arm.leak_bool ?_⟩
        · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega) with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact a0
          · exact a1
          · exact a2
          · exact a3
          · exact a4
          · exact a5
          · exact a6
        · have e₁ : ¬((s₁.gpr .r1).toNat = 10 ∨ (s₁.gpr .r1).toNat = 12 ∨ (s₁.gpr .r1).toNat = 14) ↔ False :=
            ⟨fun x => x hr, False.elim⟩
          have e₂ : ¬((s₂.gpr .r1).toNat = 10 ∨ (s₂.gpr .r1).toNat = 12 ∨ (s₂.gpr .r1).toNat = 14) ↔ False :=
            ⟨fun x => x (h1 ▸ hr), False.elim⟩
          simp only [e₁, e₂, ↓reduceIte] at hl
          exact hl
      sat := by
        sig_implies_sat [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre, VG.Proof.AesGcm.Arm.openArm,
          VG.Proof.AesGcm.Arm.openPreArm, VG.Proof.AesGcm.Arm.onePub, VG.Proof.AesGcm.Arm.bel, VG.Proof.AesGcm.Arm.arg, VG.Proof.AesGcm.Arm.args, VG.Proof.AesGcm.Arm.arg64, VG.Proof.AesGcm.Arm.roundsOk, Arm.abi, Arm.argRegs, Arm.reduceClassify,
          Arm.Loc.val, Arm.State.addr]
          [opSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.AesGcm.Arm.opSat }

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.Frame`. -/
section

/-!
# AES-GCM on ARMv7, with its working space on the stack

Each function runs its code, proved with the working space as an argument
(`Verified.lean`), in a frame that allocates it.
`init`'s working space is its fourth argument, in `r3`: its frame is the 2560
bytes of working space (`Verified.regScratch`). That of `stream_init` and
`stream_aad` is passed on the stack: their frames of 2576 bytes hold the
copies of the other arguments passed on the stack (none for `stream_init`,
`data` and `len` for `stream_aad`), the buffer's address and the saved `lr`
too (`Verified.stackScratch`); so do the frames of 2592 bytes of
`stream_encrypt` and `stream_decrypt`, with copies of their six words of
stack arguments (`aad_len`, `text_len`, `data` and `len`), and those of
`stream_finish` and `seal` (five words) and of `stream_verify` and `open`
(six). The copies are read only where the pre- and postconditions read the
buffers (`Proof/AesGcm/Scratch.lean`).
-/

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Impl.AesGcm.Arm

/-- A state satisfying `vg_aes_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State :=
  VG.Proof.AesGcm.Arm.mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 16 | .r2 => 0x2000 | _ => 0)
    [⟨0x1000, 16⟩] [⟨0x2000, 256⟩]

theorem initFrameSat_pre : ∃ s, (Spec.Gcm.initContract Arm.abi 2568).pre s := by
  implies_sat [Spec.Gcm.initContract, Spec.Gcm.initSig, Spec.Gcm.initPre, Spec.Gcm.initPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, mkSat] using VG.Proof.AesGcm.Arm.initFrameSat

theorem init_framed : Verified Arm.target (Impl.StackScratch.Arm.withRegScratch 2560 .r3 init)
    (Spec.Gcm.initContract Arm.abi 2568) :=
  Arm.Verified.regScratch (sig := Spec.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.initPre Arm.abi.ptrBits) (post := Spec.Gcm.initPost Arm.abi.ptrBits)
    (wa := true) (stack := 8) VG.Proof.AesGcm.Arm.init_verified (by decide) (by decide) (by decide) VG.Proof.AesGcm.Arm.initFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition, without the
working space. -/
def streamInitFrameSat : State :=
  VG.Proof.AesGcm.Arm.mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0 | .r3 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩] [⟨0x3000, 80⟩]

theorem streamInitFrameSat_pre : ∃ s, (Spec.Gcm.streamInitContract Arm.abi 2584).pre s := by
  implies_sat [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, Spec.Gcm.streamInitPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [streamInitFrameSat, mkSat] using VG.Proof.AesGcm.Arm.streamInitFrameSat

theorem streamInit_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2576 0 streamInit)
      (Spec.Gcm.streamInitContract Arm.abi 2584) :=
  Arm.Verified.stackScratch (sig := Spec.Gcm.streamInitSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamInitPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (m := 0) VG.Proof.AesGcm.Arm.streamInit_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (streamInitPost_local _)
    VG.Proof.AesGcm.Arm.streamInitFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition, without the
working space. -/
def streamAadFrameSat : State :=
  VG.Proof.AesGcm.Arm.mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0, 0⟩, ⟨0x8000, 8⟩] [⟨0x3000, 80⟩]

theorem streamAadFrameSat_pre : ∃ s, (Spec.Gcm.streamAadContract Arm.abi 2584).pre s := by
  implies_sat [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, Spec.Gcm.streamAadPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [streamAadFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using VG.Proof.AesGcm.Arm.streamAadFrameSat

theorem streamAad_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2576 2 streamAad)
      (Spec.Gcm.streamAadContract Arm.abi 2584) :=
  Arm.Verified.stackScratch (sig := Spec.Gcm.streamAadSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamAadPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (m := 2) VG.Proof.AesGcm.Arm.streamAad_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (streamAadPost_local _)
    VG.Proof.AesGcm.Arm.streamAadFrameSat_pre

/-- A state satisfying the preconditions of `vg_aes_gcm_stream_encrypt` and
`vg_aes_gcm_stream_decrypt`, without the working space: their six words of
stack arguments at `0x8000`. -/
def crFrameSat : State :=
  VG.Proof.AesGcm.Arm.mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x8000, 24⟩] [⟨0x3000, 80⟩, ⟨0, 0⟩]

theorem streamEncryptFrameSat_pre : ∃ s, (Spec.Gcm.streamEncryptContract Arm.abi 2600).pre s := by
  implies_sat [Spec.Gcm.streamEncryptContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Spec.Gcm.streamEncryptPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [crFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using VG.Proof.AesGcm.Arm.crFrameSat

theorem streamEncrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 6 streamEncrypt)
      (Spec.Gcm.streamEncryptContract Arm.abi 2600) :=
  Arm.Verified.stackScratch (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre Arm.abi.ptrBits)
    (post := Spec.Gcm.streamEncryptPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (m := 6) VG.Proof.AesGcm.Arm.streamEncrypt_verified (by decide) (by decide) (by decide) (by decide)
    (streamTextPre_local _) (streamEncryptPost_local _) VG.Proof.AesGcm.Arm.streamEncryptFrameSat_pre

theorem streamDecryptFrameSat_pre : ∃ s, (Spec.Gcm.streamDecryptContract Arm.abi 2600).pre s := by
  implies_sat [Spec.Gcm.streamDecryptContract, Spec.Gcm.streamCryptSig, Spec.Gcm.streamTextPre,
    Spec.Gcm.streamDecryptPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [crFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using VG.Proof.AesGcm.Arm.crFrameSat

theorem streamDecrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 6 streamDecrypt)
      (Spec.Gcm.streamDecryptContract Arm.abi 2600) :=
  Arm.Verified.stackScratch (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre Arm.abi.ptrBits)
    (post := Spec.Gcm.streamDecryptPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (m := 6) VG.Proof.AesGcm.Arm.streamDecrypt_verified (by decide) (by decide) (by decide) (by decide)
    (streamTextPre_local _) (streamDecryptPost_local _) VG.Proof.AesGcm.Arm.streamDecryptFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_finish`'s precondition, without the
working space: its five words of stack arguments at `0x8000`. -/
def finFrameSat : State :=
  VG.Proof.AesGcm.Arm.mkSat4 (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x8000, 20⟩] [⟨0x3000, 80⟩, ⟨0x4000, 16⟩]

theorem finFrameSat_pre : ∃ s, (Spec.Gcm.streamFinishContract Arm.abi 2600).pre s := by
  implies_sat [Spec.Gcm.streamFinishContract, Spec.Gcm.streamFinishSig, Spec.Gcm.streamFinishPre, Spec.Gcm.streamFinishPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finFrameSat, mkSat4, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using VG.Proof.AesGcm.Arm.finFrameSat

theorem streamFinish_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 5 streamFinish)
      (Spec.Gcm.streamFinishContract Arm.abi 2600) :=
  Arm.Verified.stackScratch (sig := Spec.Gcm.streamFinishSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamFinishPre Arm.abi.ptrBits)
    (post := Spec.Gcm.streamFinishPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (m := 5) VG.Proof.AesGcm.Arm.streamFinish_verified (by decide) (by decide) (by decide) (by decide)
    (streamFinishPre_local _) (streamFinishPost_local _) VG.Proof.AesGcm.Arm.finFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_verify`'s precondition, without the
working space: its six words of stack arguments at `0x8000`. -/
def verFrameSat : State :=
  VG.Proof.AesGcm.Arm.mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x3000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0, 0⟩, ⟨0x8000, 24⟩] [⟨0x3000, 80⟩]

theorem verFrameSat_pre : ∃ s, (Spec.Gcm.streamVerifyContract Arm.abi 2600).pre s := by
  implies_sat [Spec.Gcm.streamVerifyContract, Spec.Gcm.streamVerifySig, Spec.Gcm.streamVerifyPre, Spec.Gcm.streamVerifyPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [verFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using VG.Proof.AesGcm.Arm.verFrameSat

theorem streamVerify_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 6 streamVerify)
      (Spec.Gcm.streamVerifyContract Arm.abi 2600) :=
  Arm.Verified.stackScratch (sig := Spec.Gcm.streamVerifySig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamVerifyPre Arm.abi.ptrBits)
    (post := Spec.Gcm.streamVerifyPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (m := 6) VG.Proof.AesGcm.Arm.streamVerify_verified (by decide) (by decide) (by decide) (by decide)
    (streamVerifyPre_local _) (streamVerifyPost_local _) VG.Proof.AesGcm.Arm.verFrameSat_pre

/-- A state satisfying `vg_aes_gcm_seal`'s precondition, without the working
space: its five words of stack arguments at `0x8000`. -/
def sealFrameSat : State :=
  VG.Proof.AesGcm.Arm.mkSat4 (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0x8000, 20⟩] [⟨0, 0⟩, ⟨0x4000, 16⟩]

theorem sealFrameSat_pre : ∃ s, (Spec.Gcm.sealContract Arm.abi 2600).pre s := by
  implies_sat [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, Spec.Gcm.sealPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [sealFrameSat, mkSat4, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using VG.Proof.AesGcm.Arm.sealFrameSat

theorem seal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 5 «seal»)
      (Spec.Gcm.sealContract Arm.abi 2600) :=
  Arm.Verified.stackScratch (sig := Spec.Gcm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.sealPre Arm.abi.ptrBits)
    (post := Spec.Gcm.sealPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (m := 5) VG.Proof.AesGcm.Arm.seal_verified (by decide) (by decide) (by decide) (by decide)
    (sealPre_local _) (sealPost_local _) VG.Proof.AesGcm.Arm.sealFrameSat_pre

/-- A state satisfying `vg_aes_gcm_open`'s precondition, without the working
space: its six words of stack arguments at `0x8000`. -/
def openFrameSat : State :=
  VG.Proof.AesGcm.Arm.mkSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | _ => 0)
    [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x8000, 24⟩] [⟨0, 0⟩]

theorem openFrameSat_pre : ∃ s, (Spec.Gcm.openContract Arm.abi 2600).pre s := by
  implies_sat [Spec.Gcm.openContract, Spec.Gcm.openSig, Spec.Gcm.openPre, Spec.Gcm.openPost, Spec.Gcm.openLeak,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [openFrameSat, mkSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using VG.Proof.AesGcm.Arm.openFrameSat

theorem open_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2592 6 «open»)
      (Spec.Gcm.openContract Arm.abi 2600) :=
  Arm.Verified.stackScratch (sig := Spec.Gcm.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.openPre Arm.abi.ptrBits)
    (post := Spec.Gcm.openPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (leak := some (Spec.Gcm.openLeak Arm.abi.ptrBits))
    (m := 6) VG.Proof.AesGcm.Arm.open_verified (by decide) (by decide) (by decide) (by decide)
    (openPre_local _) (openPost_local _) VG.Proof.AesGcm.Arm.openFrameSat_pre
    (hleak := openLeak_local _)

end VG.Proof.AesGcm.Arm

end
