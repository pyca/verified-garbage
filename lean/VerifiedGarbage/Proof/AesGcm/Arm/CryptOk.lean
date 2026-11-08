module

public import VerifiedGarbage.Proof.AesGcm.Arm.Crypt
public import VerifiedGarbage.Proof.AesGcm.Arm.Blocks
public import VerifiedGarbage.Proof.Cmac.Mem32
import VerifiedGarbage.Proof.AesGcm.Arm.Flush
import VerifiedGarbage.Proof.AesGcm.Arm.Ghash1
import VerifiedGarbage.Proof.AesGcm.Arm.Loops
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES-GCM on ARMv7: `crypt`

Untrusted: everything here is checked by Lean (see `Crypt.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith)
open VG.Proof.Gcm (Ctr xorKs)

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

/-- The rest of the keystream block. -/
theorem cryptHead_ok {R : Nat} {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {s : State}
    (h : CrIn c st w sp k7 k8 R icb P D n s) (hn : n ≠ 0) (hP : P % 16 ≠ 0) :
    WP isa cryptHead s (fun s' => ∃ j, j = min (16 - P % 16) n ∧ CrMid c st w sp k7 k8 R icb P D n s.mem j s') := by
  have hlt : P % 16 < 16 := Nat.mod_lt _ (by decide)
  have hn' := h.data.ok.lt32
  have he := h.env
  refine WP.seq (WP.mono (minLen_ok s h.r6 h.r5 (by omega_arith) hn') fun s₁ ⟨h3, hg, hk⟩ => ?_)
  obtain ⟨k, hk'⟩ : ∃ k, min (16 - P % 16) n = k := ⟨_, rfl⟩
  rw [hk'] at h3
  have hk1 : 1 ≤ k := by omega_arith
  have hk16 : P % 16 + k ≤ 16 := by omega_arith
  have hkn : k ≤ n := by omega_arith
  obtain ⟨s₂, run₂, h1, h2, h4, h5, h3', hg₂, hk₂⟩ : ∃ s₂, runBlock isa [addI .r1 .r10 64,
      .dp .add .r1 .r1 (.reg .r6), .mov .r2 (.reg .r4), .dp .add .r4 .r4 (.reg .r3), .dp .sub .r5 .r5 (.reg .r3)]
      s₁ = some s₂ ∧
      s₂.gpr .r1 = st + BitVec.ofNat 32 (64 + P % 16) ∧ s₂.gpr .r2 = D ∧
      s₂.gpr .r4 = D + BitVec.ofNat 32 k ∧ s₂.gpr .r5 = BitVec.ofNat 32 (n - k) ∧
      s₂.gpr .r3 = BitVec.ofNat 32 k ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r4 → r ≠ .r5 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    have e10 := hg .r10 (by decide) (by decide)
    have e4 := hg .r4 (by decide) (by decide)
    have e5 := hg .r5 (by decide) (by decide)
    have e6 := hg .r6 (by decide) (by decide)
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, e10, e6, he.r10, h.r6, add32_ofNat_assoc]
    · simp [gpr_setReg, e4, h.r4]
    · simp [gpr_setReg, e4, h.r4, h3]
    · simp [gpr_setReg, e5, h.r5, h3, ofNat_sub32 hkn hn']
    · simp [gpr_setReg, h3]
    · intro r a b c d; simp [gpr_setReg, a, b, c, d]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have hk₂' := hk.trans hk₂
  have eK : State.addr (st + BitVec.ofNat 32 (64 + P % 16)) = State.addr st + BitVec.ofNat 64 (64 + P % 16) :=
    L.stA (by omega_arith)
  have lp : LoopPre s₂ (st + BitVec.ofNat 32 (64 + P % 16)) D k := by
    refine ⟨h1, h2, h3', hk1, by omega_arith, by rw [L.stN (by omega_arith)]; have := L.sw; omega_arith,
      by have := h.data.ok.fit; omega_arith, ?_, ?_, ?_⟩
    · rw [hk₂'.rd, hk₂'.wr, eK]; exact covers_left (he.perm.stC (by omega_arith))
    · rw [hk₂'.wr]; exact (h.data.take hkn).wr
    · rw [eK]; exact ((h.data.take hkn).ok.st.sub_right (Lay.stSub (by omega_arith))).symm
  refine WP.mono (xorLoop_ok s₂ lp) fun s₃ ⟨hm₃, lo⟩ => ?_
  rw [eK, hk₂'.mem] at hm₃
  have hxl := length_xorBytes s.mem (State.addr D) (State.addr st + BitVec.ofNat 64 (64 + P % 16)) k
  have fw : Frame [⟨State.addr D, k⟩] s.mem s₃.mem := by rw [hm₃]; exact writeBytes_frame' _ hxl
  have hdisjst : ∀ r ∈ [(⟨State.addr D, k⟩ : Region)],
      (⟨State.addr st + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r ∧
      (⟨State.addr st + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact ⟨((h.data.take hkn).ok.st.sub_right (Lay.stSub (by decide))).symm,
      ((h.data.take hkn).ok.st.sub_right (Lay.stSub (by decide))).symm⟩
  have g : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .r4 → r ≠ .r5 → s₃.gpr r = s.gpr r :=
    fun r a b c d e f i => by rw [lo.other r a b c d e, hg₂ r b c f i, hg r d e]
  have he₃ : Env c st w sp k7 k8 s₃ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (lo.sp.trans hk₂'.sp) (lo.rd.trans hk₂'.rd) (lo.wr.trans hk₂'.wr)
  have hc₃ : ciphOf s₃.mem (State.addr c) R = ciphOf s.mem (State.addr c) R :=
    ciph_frame fw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (h.data.take hkn).ctx) h.rounds
  refine ⟨k, hk'.symm, he₃, hkn, by rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide), h4],
    by rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide), h5],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r8],
    h.rounds, h.data.of_eq (lo.rd.trans hk₂'.rd) (lo.wr.trans hk₂'.wr), ?_, ?_, ?_, ?_, ?_, nofun,
    (h.data.of_eq (lo.rd.trans hk₂'.rd) (lo.wr.trans hk₂'.wr)).ok, rfl⟩
  · intro hc₀
    refine (hc₀.head hP hk16).congr (blockAt_frame fw fun r hr => (hdisjst r hr).1)
      (blockAt_frame fw fun r hr => (hdisjst r hr).2)
  · intro hc₀
    have e := bytesAt_writeBytes_self s.mem (State.addr D)
      (xorBytes s.mem (State.addr D) (State.addr st + BitVec.ofNat 64 (64 + P % 16)) k) (by rw [hxl]; omega_arith)
    rw [hxl] at e
    rw [hm₃, e, xorBytes]
    have := Proof.Gcm.ctr_head hc₀ hP (d := bytesAt s.mem (State.addr D) k) (by rw [length_bytesAt]; exact hk16)
    rw [length_bytesAt, add_ofNat_assoc] at this
    exact this
  · exact bytesAt_frame fw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (split_disj hkn h.data.ok.lt).symm) (by omega_arith)
  · by_cases hkk : k = n
    · left; omega_arith
    · right; omega_arith
  · exact fw.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Region.sub_prefix hkn⟩

omit L in
/-- The split of the rest into whole blocks for `vg_aes_ctr32` and the last bytes. -/
theorem splitCtr_ok {s : State} {D : BitVec 32} {n j : Nat} (hj : j ≤ n) (hn : n < 2 ^ 32)
    (h4 : s.gpr .r4 = D + BitVec.ofNat 32 j) (h5 : s.gpr .r5 = BitVec.ofNat 32 (n - j)) :
    ∃ s', runBlock isa splitCtr s = some s' ∧
      s'.gpr .r3 = D + BitVec.ofNat 32 j ∧ s'.gpr .r12 = BitVec.ofNat 32 ((n - j) / 16) ∧
      s'.gpr .r4 = D + BitVec.ofNat 32 (j + 16 * ((n - j) / 16)) ∧
      s'.gpr .r5 = BitVec.ofNat 32 (n - (j + 16 * ((n - j) / 16))) ∧
      s'.z = decide ((n - j) / 16 = 0) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have hand := and15 (BitVec.ofNat 32 (n - j))
  rw [toNat32 (by omega_arith)] at hand
  have hsub : BitVec.ofNat 32 (n - j) - BitVec.ofNat 32 ((n - j) % 16) = BitVec.ofNat 32 (16 * ((n - j) / 16)) := by
    rw [ofNat_sub32 (Nat.mod_le _ _) (by omega_arith)]; congr 1; omega_arith
  refine ⟨_, by simp only [splitCtr]; arun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, h4]
  · simp [gpr_setReg, h5, shr4 (show n - j < 2 ^ 32 by omega_arith)]
  · simp only [gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h4, h5, hand, hsub, add32_ofNat_assoc]
  · simp only [gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, hand]
    congr 1; omega_arith
  · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5,
      shr4 (show n - j < 2 ^ 32 by omega_arith)]
    rw [z_cmp (by omega_arith) (by decide)]
  · intro r a b c d e f; simp [gpr_setReg, a, b, c, d, e, f]
  · exact ⟨rfl, rfl, rfl, rfl⟩

omit L in
/-- The arguments of `vg_aes_ctr32` for the whole blocks. -/
theorem wholeArgs_ok {s : State} (he : Env c st w sp k7 k8 s) :
    ∃ s', runBlock isa [.mov .r0 (.reg .r9), .mov .r1 (.reg .r8), addI .r2 .r10 48, addI .lr .r11 scrO] s = some s' ∧
      s'.gpr .r0 = c ∧ s'.gpr .r1 = s.gpr .r8 ∧ s'.gpr .r2 = st + BitVec.ofNat 32 48 ∧
      s'.gpr .lr = w + BitVec.ofNat 32 512 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .lr → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have h9 := he.r9; have h10 := he.r10; have h11 := he.r11
  refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, h9]
  · simp [gpr_setReg]
  · simp [gpr_setReg, h10]
  · simp [gpr_setReg, h11]
  · intro r a b d e; simp [gpr_setReg, a, b, d, e]
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- The arguments of `vg_aes_ctr32` on `nb` whole blocks at `D + j`. -/
theorem ctrWhole_mk {R : Nat} {D : BitVec 32} {j nb : Nat} {s : State} (he : Env c st w sp k7 k8 s)
    (h0 : s.gpr .r0 = c) (h1 : s.gpr .r1 = BitVec.ofNat 32 R) (h2 : s.gpr .r2 = st + BitVec.ofNat 32 48)
    (h3 : s.gpr .r3 = D + BitVec.ofNat 32 j) (h12 : s.gpr .r12 = BitVec.ofNat 32 nb)
    (hlr : s.gpr .lr = w + BitVec.ofNat 32 512) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hdj : DataW c st w sp k7 k8 s (D + BitVec.ofNat 32 j) (16 * nb)) :
    CtrCall s c (st + BitVec.ofNat 32 48) (D + BitVec.ofNat 32 j) (w + BitVec.ofNat 32 512) R nb := by
  have eC := L.stA (d := 48) (by decide)
  have eS := L.wA (d := 512) (by decide)
  have hk := he.sp
  refine ⟨h0, h1, h2, h3, h12, hlr, hR,
    by rw [hk]; exact L.sp8, by have := L.cw; omega_arith, by rw [L.stN (by decide)]; have := L.sw; omega_arith,
    by have := hdj.ok.fit; omega_arith, by rw [L.wN (by decide)]; have := L.ww; omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  all_goals try simp only [eC, eS, hk]
  · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide))
  · exact hdj.ctx.sub_left (Region.sub_prefix (by decide))
  · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
  · exact (hdj.ok.st.sub_right (Lay.stSub (by decide))).symm
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact hdj.ok.w.sub_right (Lay.wSub (by decide))
  · exact L.kc.sub_right (Region.sub_prefix (by decide))
  · exact L.stk_st (by decide)
  · exact hdj.ok.stk
  · exact L.stk_w (by decide)
  · exact covers_prefix he.perm.ctx (by decide)
  · exact covers_cons (he.perm.stC (by decide)) (covers_cons hdj.wr (he.perm.wC (by decide)))

/-- The arguments of `vg_aes_ctr32` on the keystream block. -/
theorem ctrTail_mk {R : Nat} {s : State} (he : Env c st w sp k7 k8 s)
    (h0 : s.gpr .r0 = c) (h1 : s.gpr .r1 = BitVec.ofNat 32 R) (h2 : s.gpr .r2 = st + BitVec.ofNat 32 48)
    (h3 : s.gpr .r3 = st + BitVec.ofNat 32 64) (h12 : s.gpr .r12 = BitVec.ofNat 32 1)
    (hlr : s.gpr .lr = w + BitVec.ofNat 32 512) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    CtrCall s c (st + BitVec.ofNat 32 48) (st + BitVec.ofNat 32 64) (w + BitVec.ofNat 32 512) R 1 := by
  have eC := L.stA (d := 48) (by decide)
  have eK := L.stA (d := 64) (by decide)
  have eS := L.wA (d := 512) (by decide)
  have hk := he.sp
  refine ⟨h0, h1, h2, h3, h12, hlr, hR, by rw [hk]; exact L.sp8, by have := L.cw; omega_arith,
    by rw [L.stN (by decide)]; have := L.sw; omega_arith, by rw [L.stN (by decide)]; have := L.sw; omega_arith,
    by rw [L.wN (by decide)]; have := L.ww; omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [eC, eK, eS, hk]
  · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide))
  · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide))
  · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
  · exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.kc.sub_right (Region.sub_prefix (by decide))
  · exact L.stk_st (by decide)
  · exact L.stk_st (by decide)
  · exact L.stk_w (by decide)
  · exact covers_prefix he.perm.ctx (by decide)
  · exact covers_cons (he.perm.stC (by decide)) (covers_cons (he.perm.stC (by decide))
      (he.perm.wC (by decide)))

/-- Whole blocks. -/
theorem cryptWhole_ok {R : Nat} {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid c st w sp k7 k8 R icb P D n m₀ j s) (hc : ciphOf s.mem (State.addr c) R = ciphOf m₀ (State.addr c) R) :
    WP isa (cryptWholeG false) s (fun s' => ∃ j', j' = j + 16 * ((n - j) / 16) ∧ CrMid c st w sp k7 k8 R icb P D n m₀ j' s' ∧
      n - j' < 16) := by
  have hn' := h.data.ok.lt32
  have he := h.env
  obtain ⟨s₁, run₁, h3, h12, h4, h5, hz, hg₁, hk₁⟩ := splitCtr_ok h.le hn' h.r4 h.r5
  generalize hnb : (n - j) / 16 = nb at h12 h4 h5 hz
  have h16 : 16 * nb ≤ n - j := by omega_arith
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env c st w sp k7 k8 s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)) hk₁.sp hk₁.rd hk₁.wr
  have hd₁ : DataW c st w sp k7 k8 s₁ D n := h.data.of_eq hk₁.rd hk₁.wr
  have r8₁ : s₁.gpr .r8 = BitVec.ofNat 32 R := by
    rw [hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r8]
  refine WP.ite (decide (nb = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : nb = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨j, by omega_arith, ⟨he₁, h.le, by rw [h4]; rfl, by rw [h5]; rfl, r8₁, h.rounds, hd₁,
      fun hc₀ => by rw [hk₁.mem]; exact h.ctr hc₀, fun hc₀ => by rw [hk₁.mem]; exact h.done hc₀,
      by rw [hk₁.mem]; exact h.rest, h.whole, by rw [hk₁.mem]; exact h.frame, nofun, hd₁.ok, rfl⟩, by omega_arith⟩
  · have h0 : nb ≠ 0 := by simpa using hf
    have hw : (P + j) % 16 = 0 := h.whole.resolve_left (by omega_arith)
    have hdj := h.data.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith)
    have eD := h.data.ok.addr (j := j) (by omega_arith)
    obtain ⟨s₂, run₂, h0', h1', h2', hlr', hg₂, hk₂⟩ := wholeArgs_ok he₁
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have he₂ : Env c st w sp k7 k8 s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide) (by decide))
      hk₂.sp hk₂.rd hk₂.wr
    have eC := L.stA (d := 48) (by decide)
    have eS := L.wA (d := 512) (by decide)
    have hk := he₂.sp
    have hcall : CtrCall s₂ c (st + BitVec.ofNat 32 48) (D + BitVec.ofNat 32 j) (w + BitVec.ofNat 32 512) R nb :=
      ctrWhole_mk L he₂ h0' (by rw [h1', r8₁]) h2' (by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h3])
        (by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h12]) hlr' h.rounds
        (hdj.of_eq (hk₂.rd.trans hk₁.rd) (hk₂.wr.trans hk₁.wr))
    refine WP.mono (ctr_call hcall) fun s₃ g => ?_
    have gout := g.out; have gctr := g.ctr; have gframe := g.frame
    simp only [hk₂.mem, hk₁.mem, eC, eS, eD, hk] at gout gctr gframe
    have hcw := fun hc₀ => Proof.Gcm.ctr_whole (h.ctr hc₀) hw (m' := s₃.mem)
      (dp := State.addr D + BitVec.ofNat 64 j) (nb := nb) (by rw [gout, ← hc]) gctr
    refine ⟨j + 16 * nb, by omega_arith, ⟨he₂.of_saved g.saved g.sp g.rd g.wr, by omega_arith, ?_, ?_, ?_, h.rounds,
      hd₁.of_eq (g.rd.trans hk₂.rd) (g.wr.trans hk₂.wr), ?_, ?_, ?_, .inr (by omega_arith), ?_, nofun,
      (hd₁.of_eq (g.rd.trans hk₂.rd) (g.wr.trans hk₂.wr)).ok, rfl⟩, by omega_arith⟩
    · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide), h4]
    · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide), h5]
    · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide), r8₁]
    · intro hc₀; rw [← Nat.add_assoc]; exact (hcw hc₀).2
    · -- The bytes done.
      intro hc₀
      have hj16 : bytesAt s₃.mem (State.addr D + BitVec.ofNat 64 j) (16 * nb) =
          xorKs (ciphOf m₀ (State.addr c) R) icb (P + j) (bytesAt m₀ (State.addr D + BitVec.ofNat 64 j) (16 * nb)) := by
        rw [(hcw hc₀).1]
        congr 1
        have e := congrArg (List.take (16 * nb)) h.rest
        rwa [show n - j = 16 * nb + (n - j - 16 * nb) by omega_arith, bytesAt_add, bytesAt_add,
          List.take_left' (length_bytesAt _ _ _), List.take_left' (length_bytesAt _ _ _)] at e
      have hjd : bytesAt s₃.mem (State.addr D) j = bytesAt s.mem (State.addr D) j := bytesAt_frame gframe (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (h.data.take h.le).ok.st.sub_right (Lay.stSub (by decide))
        · exact split_disj (D := State.addr D) (j := j) (n := n) h.le h.data.ok.lt |>.sub_right
            (Region.sub_prefix (by omega_arith))
        · exact (h.data.take h.le).ok.w.sub_right (Lay.wSub (by decide))
        · exact (h.data.take h.le).ok.stk.symm) (by omega_arith)
      exact done_append (hjd.trans (h.done hc₀)) hj16
    · -- The bytes left.
      have hdis : ∀ r ∈ [⟨State.addr st + BitVec.ofNat 64 48, 16⟩, ⟨State.addr D + BitVec.ofNat 64 j, 16 * nb⟩,
          ⟨State.addr w + BitVec.ofNat 64 512, 2048⟩, below sp],
          (⟨State.addr D + BitVec.ofNat 64 (j + 16 * nb), n - (j + 16 * nb)⟩ : Region).Disjoint r := by
        have hst := h.data.ok.st; have hW := h.data.ok.w; have hK := h.data.ok.stk
        have hs : Region.Sub ⟨State.addr D + BitVec.ofNat 64 (j + 16 * nb), n - (j + 16 * nb)⟩ ⟨State.addr D, n⟩ :=
          Offset.sub_base _ (by omega_arith)
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (hst.sub_left hs).sub_right (Lay.stSub (by decide))
        · rw [← add_ofNat_assoc]
          have := split_disj (D := State.addr D + BitVec.ofNat 64 j) (j := 16 * nb) (n := n - j) h16 (by omega_arith)
          rw [show n - j - 16 * nb = n - (j + 16 * nb) by omega_arith] at this
          exact this.symm
        · exact (hW.sub_left hs).sub_right (Lay.wSub (by decide))
        · exact (hK.sub_right hs).symm
      rw [bytesAt_frame gframe hdis (by omega_arith)]
      have e := congrArg (List.drop (16 * nb)) h.rest
      have e₂ : ∀ m : Mem, (bytesAt m (State.addr D + BitVec.ofNat 64 j) (n - j)).drop (16 * nb) =
          bytesAt m (State.addr D + BitVec.ofNat 64 (j + 16 * nb)) (n - (j + 16 * nb)) := fun m => by
        rw [show n - j = 16 * nb + (n - (j + 16 * nb)) by omega_arith, bytesAt_add,
          List.drop_left' (length_bytesAt _ _ _), add_ofNat_assoc]
      simpa only [e₂] using e
    · refine h.frame.trans (gframe.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., (Offset.sub_base _ (by omega_arith))⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
      · exact ⟨_, by simp [crFrameG], fun _ h => h⟩

omit L in
/-- `crFrameG` holds the regions of `crFrame`. -/
theorem crFrame_sub {to : Bool} {st w sp D : BitVec 32} {n : Nat} :
    ∀ r ∈ crFrame st w sp D n, r ∈ crFrameG to st w sp D n := fun r hr => by
  cases to
  · exact hr
  · exact List.mem_append_left _ hr

omit L in
/-- `Proof.Gcm.ctr_whole`, from the blocks at `sp` to those at `tp`. -/
theorem ctr_whole_to {m m' : Mem} {cb ks sp tp : Addr} {ciph : Block → Block} {icb : Block} {n nb : Nat}
    (h : Ctr m cb ks ciph icb n) (h0 : n % 16 = 0)
    (hd : blocksAt m' tp nb = Spec.Gcm.ctr32 ciph (blockAt m cb) (blocksAt m sp nb))
    (hc : blockAt m' cb = Nat.repeat Spec.Gcm.inc32 nb (blockAt m cb)) :
    bytesAt m' tp (16 * nb) = xorKs ciph icb n (bytesAt m sp (16 * nb)) ∧ Ctr m' cb ks ciph icb (n + 16 * nb) := by
  open VG.Proof.Gcm in
  have hcb : blockAt m cb = Nat.repeat Spec.Gcm.inc32 (n / 16) icb := by rw [h.1]; congr 1; omega
  refine ⟨?_, ?_, fun h1 => absurd (by omega) h1⟩
  · refine Proof.Gcm.list_ext (by simp [Proof.Gcm.length_xorKs, Cmac.bytesAt_length]) fun k hk => ?_
    simp only [Cmac.bytesAt_length] at hk
    rw [Proof.Gcm.getD_xorKs _ _ _ _ (by rw [Cmac.bytesAt_length]; exact hk), Proof.Gcm.getD_bytesAt' _ _ hk,
      Proof.Gcm.getD_bytesAt' _ _ hk]
    have hq : k / 16 < nb := by omega
    have e₁ := congrArg (fun L => L.getD (k / 16) 0) hd
    rw [Proof.Gcm.ctr32_getD _ _ _ (by rw [Proof.Gcm.length_blocksAt]; exact hq), Proof.Gcm.blocksAt_getD _ _ _ hq,
      Proof.Gcm.blocksAt_getD _ _ _ hq] at e₁
    have ea : ∀ p : Addr, p + BitVec.ofNat 64 k = p + BitVec.ofNat 64 (16 * (k / 16)) + BitVec.ofNat 64 (k % 16) :=
      fun p => by rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
    rw [ea tp, ea sp, Proof.Gcm.bytes_toBytes_blockAt m' _ (by omega), Proof.Gcm.bytes_toBytes_blockAt m _ (by omega),
      e₁, Proof.Aes.toBytes_xor _ _ (by omega), Proof.Gcm.ksByte, hcb, ← Proof.Gcm.repeat_add,
      show (n + k) / 16 = k / 16 + n / 16 by omega, show (n + k) % 16 = k % 16 by omega]
  · rw [hc, hcb, ← Proof.Gcm.repeat_add]; congr 1; omega

/-- Out of place, the whole blocks with `vg_aes_ctr32_to`, and the
destination advanced past them. -/
theorem cryptWholeTo_ok {R : Nat} {icb : Block} {P : Nat} {S T : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat}
    {s : State} (h : CrMidG true c st w sp k7 k8 R icb P S T n m₀ j s)
    (hc : ciphOf s.mem (State.addr c) R = ciphOf m₀ (State.addr c) R) :
    WP isa (cryptWholeG true) s (fun s' => ∃ j', j' = j + 16 * ((n - j) / 16) ∧
      CrMidG true c st w sp k7 k8 R icb P S T n m₀ j' s' ∧ n - j' < 16) := by
  have hn' := h.data.ok.lt32
  have he := h.env
  obtain ⟨dST, sp12, bc, bst, bw, bS, bT⟩ := h.mode
  obtain ⟨s₁, run₁, h3, h12, h4, h5, hz, hg₁, hk₁⟩ := splitCtr_ok h.le hn' h.r4 h.r5
  generalize hnb : (n - j) / 16 = nb at h12 h4 h5 hz
  have h16 : 16 * nb ≤ n - j := by omega_arith
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env c st w sp k7 k8 s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)) hk₁.sp hk₁.rd hk₁.wr
  have hd₁ : DataW c st w sp k7 k8 s₁ T n := h.data.of_eq hk₁.rd hk₁.wr
  have hs₁ : DataOk st w sp s₁ S n := h.src.of_eq hk₁.rd hk₁.wr
  have r8₁ : s₁.gpr .r8 = BitVec.ofNat 32 R := by
    rw [hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r8]
  have r6₁ : s₁.gpr .r6 = T + BitVec.ofNat 32 j := by
    rw [hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r6 rfl]
  refine WP.ite (decide (nb = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : nb = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨j, by omega_arith, ⟨he₁, h.le, by rw [h4]; rfl, by rw [h5]; rfl, r8₁, h.rounds, hd₁,
      fun hc₀ => by rw [hk₁.mem]; exact h.ctr hc₀, fun hc₀ => by rw [hk₁.mem]; exact h.done hc₀,
      by rw [hk₁.mem]; exact h.rest, h.whole, by rw [hk₁.mem]; exact h.frame, fun _ => r6₁, hs₁, h.mode⟩,
      by omega_arith⟩
  · have h0 : nb ≠ 0 := by simpa using hf
    have hw : (P + j) % 16 = 0 := h.whole.resolve_left (by omega_arith)
    have hdj := h.data.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith)
    have hsj := h.src.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith)
    have eD := h.data.ok.addr (j := j) (by omega_arith)
    have eS := h.src.addr (j := j) (by omega_arith)
    obtain ⟨s₂, run₂, h0', h1', h2', hg₂, hk₂⟩ : ∃ s₂, runBlock isa
        [.mov .r2 (.reg .r6), .mov .r0 (.reg .r12), addI .r1 .r11 scrO] s₁ = some s₂ ∧
        s₂.gpr .r0 = BitVec.ofNat 32 nb ∧ s₂.gpr .r1 = w + BitVec.ofNat 32 512 ∧
        s₂.gpr .r2 = T + BitVec.ofNat 32 j ∧
        (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
      refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, h12]
      · simp [gpr_setReg, he₁.r11]
      · simp [gpr_setReg, r6₁]
      · intro r a b d; simp [gpr_setReg, a, b, d]
      · exact ⟨rfl, rfl, rfl, rfl⟩
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have he₂ : Env c st w sp k7 k8 s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide))
      hk₂.sp hk₂.rd hk₂.wr
    have eC := L.stA (d := 48) (by decide)
    have eW := L.wA (d := 512) (by decide)
    have hk := he₂.sp
    have hdj₂ := hdj.of_eq (hk₂.rd.trans hk₁.rd) (hk₂.wr.trans hk₁.wr)
    have hsj₂ := hsj.of_eq (hk₂.rd.trans hk₁.rd) (hk₂.wr.trans hk₁.wr)
    have dtj : (⟨State.addr (S + BitVec.ofNat 32 j), 16 * nb⟩ : Region).Disjoint
        ⟨State.addr (T + BitVec.ofNat 32 j), 16 * nb⟩ := by
      rw [eS, eD]
      exact (dST.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))
    have b12 : ∀ {R' : Region}, Region.Sub R' ⟨State.addr S, n⟩ → (below12 s₂.sp).Disjoint R' := fun hs => by
      rw [hk]; exact bS.sub_right hs
    have b12T : ∀ {R' : Region}, Region.Sub R' ⟨State.addr T, n⟩ → (below12 s₂.sp).Disjoint R' := fun hs => by
      rw [hk]; exact bT.sub_right hs
    have hcall : CtrToCall s₂ c (st + BitVec.ofNat 32 48) (S + BitVec.ofNat 32 j) (T + BitVec.ofNat 32 j)
        (w + BitVec.ofNat 32 512) R nb := by
      refine ⟨by rw [hg₂ _ (by decide) (by decide) (by decide)]; exact he₁.r9,
        by rw [hg₂ _ (by decide) (by decide) (by decide), r8₁],
        by rw [hg₂ _ (by decide) (by decide) (by decide), he₁.r10],
        by rw [hg₂ _ (by decide) (by decide) (by decide), h3], h0', h1', h2', h.rounds, by rw [hk]; exact sp12,
        by have := L.cw; omega_arith, by rw [L.stN (by decide)]; have := L.sw; omega_arith, hsj.fit, hdj.ok.fit,
        by rw [L.wN (by decide)]; have := L.ww; omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, dtj, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_⟩
      all_goals try simp only [eC, eW]
      · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide))
      · exact hdj.ctx.sub_left (Region.sub_prefix (by decide))
      · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
      · exact (hdj.ok.st.sub_right (Lay.stSub (by decide))).symm
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact hdj.ok.w.sub_right (Lay.wSub (by decide))
      · exact hsj.st.sub_right (Lay.stSub (by decide))
      · exact hsj.w.sub_right (Lay.wSub (by decide))
      · rw [hk]; exact bc.sub_right (Region.sub_prefix (by decide))
      · rw [hk]; exact bst.sub_right (Lay.stSub (by decide))
      · rw [eS]; exact b12 (Offset.sub_base _ (by omega_arith))
      · rw [eD]; exact b12T (Offset.sub_base _ (by omega_arith))
      · rw [hk]; exact bw.sub_right (Lay.wSub (by decide))
      · exact covers_cons (covers_prefix he₂.perm.ctx (by decide)) hsj₂.rd
      · exact covers_cons (he₂.perm.stC (by decide)) (covers_cons hdj₂.wr (he₂.perm.wC (by decide)))
    refine WP.seq (WP.mono (ctrTo_call hcall) fun s₃ g => ?_)
    have gout := g.out; have gctr := g.ctr; have gframe := g.frame
    simp only [hk₂.mem, hk₁.mem, eC, eW, eD, eS, hk] at gout gctr gframe
    obtain ⟨s₄, run₄, h6₄, hg₄, hk₄⟩ : ∃ s₄, runBlock isa [.dp .add .r6 .r6 (.shifted .r12 .lsl 4)] s₃ = some s₄ ∧
        s₄.gpr .r6 = T + BitVec.ofNat 32 (j + 16 * nb) ∧ (∀ r, r ≠ .r6 → s₄.gpr r = s₃.gpr r) ∧ Keeps s₃ s₄ := by
      refine ⟨_, by arun [], ?_, ?_, ?_⟩
      · have r6₃ : s₃.gpr .r6 = T + BitVec.ofNat 32 j := by
          rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide), r6₁]
        have r12₃ : s₃.gpr .r12 = BitVec.ofNat 32 nb := by rw [g.r12, h0']
        simp only [gpr_setReg, ite_true, r6₃, r12₃]
        rw [Proof.Aes.Arm.shl4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), BitVec.add_assoc,
          ← BitVec.ofNat_add]
      · intro r hr; simp [gpr_setReg, hr]
      · exact ⟨rfl, rfl, rfl, rfl⟩
    refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
    have hcw := fun hc₀ => ctr_whole_to (h.ctr hc₀) hw (m' := s₃.mem)
      (sp := State.addr S + BitVec.ofNat 64 j) (tp := State.addr T + BitVec.ofNat 64 j) (nb := nb)
      (by rw [gout, ← hc]) gctr
    have g₄ : ∀ r ∈ preserved, r ≠ .lr → r ≠ .r6 → s₄.gpr r = s₂.gpr r := fun r hr hl h6 => by
      rw [hg₄ r h6, g.saved r hr hl]
    refine ⟨j + 16 * nb, by omega_arith, ⟨?_, by omega_arith, ?_, ?_, ?_, h.rounds,
      hd₁.of_eq (hk₄.rd.trans (g.rd.trans hk₂.rd)) (hk₄.wr.trans (g.wr.trans hk₂.wr)), ?_, ?_, ?_,
      .inr (by omega_arith), ?_, fun _ => h6₄,
      hs₁.of_eq (hk₄.rd.trans (g.rd.trans hk₂.rd)) (hk₄.wr.trans (g.wr.trans hk₂.wr)), h.mode⟩, by omega_arith⟩
    · refine (he₂.of_saved g.saved g.sp g.rd g.wr).keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₄ _ (by decide)) hk₄.sp hk₄.rd hk₄.wr
    · rw [g₄ _ (by decide) (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide), h4]
    · rw [g₄ _ (by decide) (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide), h5]
    · rw [g₄ _ (by decide) (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide), r8₁]
    · intro hc₀; rw [hk₄.mem, ← Nat.add_assoc]; exact (hcw hc₀).2
    · -- The bytes done.
      intro hc₀
      have hj16 : bytesAt s₃.mem (State.addr T + BitVec.ofNat 64 j) (16 * nb) =
          xorKs (ciphOf m₀ (State.addr c) R) icb (P + j) (bytesAt m₀ (State.addr S + BitVec.ofNat 64 j) (16 * nb)) := by
        rw [(hcw hc₀).1]
        congr 1
        have e := congrArg (List.take (16 * nb)) h.rest
        rwa [show n - j = 16 * nb + (n - j - 16 * nb) by omega_arith, bytesAt_add, bytesAt_add,
          List.take_left' (length_bytesAt _ _ _), List.take_left' (length_bytesAt _ _ _)] at e
      have hdt := (h.data.take h.le).ok
      have hjd : bytesAt s₃.mem (State.addr T) j = bytesAt s.mem (State.addr T) j := bytesAt_frame gframe (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hdt.st.sub_right (Lay.stSub (by decide))
        · exact split_disj (D := State.addr T) (j := j) (n := n) h.le h.data.ok.lt |>.sub_right
            (Region.sub_prefix (by omega_arith))
        · exact hdt.w.sub_right (Lay.wSub (by decide))
        · exact (bT.sub_right (Region.sub_prefix h.le)).symm) (by omega_arith)
      rw [hk₄.mem]
      exact done_append (hjd.trans (h.done hc₀)) hj16
    · -- The bytes left.
      have hs : Region.Sub ⟨State.addr S + BitVec.ofNat 64 (j + 16 * nb), n - (j + 16 * nb)⟩ ⟨State.addr S, n⟩ :=
        Offset.sub_base _ (by omega_arith)
      have hdis : ∀ r ∈ [⟨State.addr st + BitVec.ofNat 64 48, 16⟩, ⟨State.addr T + BitVec.ofNat 64 j, 16 * nb⟩,
          ⟨State.addr w + BitVec.ofNat 64 512, 2048⟩, below12 sp],
          (⟨State.addr S + BitVec.ofNat 64 (j + 16 * nb), n - (j + 16 * nb)⟩ : Region).Disjoint r := by
        have hst := h.src.st; have hW := h.src.w
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (hst.sub_left hs).sub_right (Lay.stSub (by decide))
        · exact (dST.sub_left hs).sub_right (Offset.sub_base _ (by omega_arith))
        · exact (hW.sub_left hs).sub_right (Lay.wSub (by decide))
        · exact (bS.sub_right hs).symm
      rw [hk₄.mem, bytesAt_frame gframe hdis (by omega_arith)]
      have e := congrArg (List.drop (16 * nb)) h.rest
      have e₂ : ∀ m : Mem, (bytesAt m (State.addr S + BitVec.ofNat 64 j) (n - j)).drop (16 * nb) =
          bytesAt m (State.addr S + BitVec.ofNat 64 (j + 16 * nb)) (n - (j + 16 * nb)) := fun m => by
        rw [show n - j = 16 * nb + (n - (j + 16 * nb)) by omega_arith, bytesAt_add,
          List.drop_left' (length_bytesAt _ _ _), add_ofNat_assoc]
      simpa only [e₂, hk₂.mem, hk₁.mem] using e
    · rw [hk₄.mem]
      refine h.frame.trans (gframe.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, crFrame_sub _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Region.sub_prefix (by decide)⟩
      · exact ⟨_, crFrame_sub _ (List.mem_cons_self ..), (Offset.sub_base _ (by omega_arith))⟩
      · exact ⟨_, crFrame_sub _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
          fun _ h => h⟩
      · exact ⟨_, by simp [crFrameG], fun _ h => h⟩

/-- Whole blocks, in place or out of place. -/
theorem cryptWholeG_ok {to : Bool} {R : Nat} {icb : Block} {P : Nat} {S T : BitVec 32} {n : Nat} {m₀ : Mem}
    {j : Nat} {s : State} (h : CrMidG to c st w sp k7 k8 R icb P S T n m₀ j s)
    (hc : ciphOf s.mem (State.addr c) R = ciphOf m₀ (State.addr c) R) :
    WP isa (cryptWholeG to) s (fun s' => ∃ j', j' = j + 16 * ((n - j) / 16) ∧
      CrMidG to c st w sp k7 k8 R icb P S T n m₀ j' s' ∧ n - j' < 16) := by
  cases to
  · have e : S = T := h.mode
    subst e
    exact cryptWhole_ok L h hc
  · exact cryptWholeTo_ok L h hc

/-- The keystream block zeroed and the arguments of `vg_aes_ctr32` on it. -/
theorem tailArgs_ok {s : State} (he : Env c st w sp k7 k8 s) :
    ∃ s', runBlock isa tailArgs s = some s' ∧
      s'.mem = Cmac.store4 s.mem (State.addr st + BitVec.ofNat 64 64) 0 0 0 0 ∧
      s'.gpr .r0 = c ∧ s'.gpr .r1 = s.gpr .r8 ∧ s'.gpr .r2 = st + BitVec.ofNat 32 48 ∧
      s'.gpr .r3 = st + BitVec.ofNat 32 64 ∧ s'.gpr .r12 = BitVec.ofNat 32 1 ∧
      s'.gpr .lr = w + BitVec.ofNat 32 512 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h9 := he.r9; have h10 := he.r10; have h11 := he.r11
  have w₀ := he.perm.stW (show 64 + 4 ≤ 80 by decide)
  have w₁ := he.perm.stW (show 68 + 4 ≤ 80 by decide)
  have w₂ := he.perm.stW (show 72 + 4 ≤ 80 by decide)
  have w₃ := he.perm.stW (show 76 + 4 ≤ 80 by decide)
  refine ⟨_, by simp only [tailArgs]; arun [h10, L.stA, w₀, w₁, w₂, w₃], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc]; rfl
  · simp [gpr_setReg, h9]
  · simp [gpr_setReg]
  · simp [gpr_setReg, h10]
  · simp [gpr_setReg, h10]
  · simp [gpr_setReg]
  · simp [gpr_setReg, h11]
  · intro r a b d e f i; simp [gpr_setReg, a, b, d, e, f, i]
  all_goals rfl

/-- The last bytes' keystream block, from `vg_aes_ctr32`. -/
structure TailKs (to : Bool) (c st w sp k7 k8 : BitVec 32) (R : Nat) (icb : Block) (P : Nat) (S T : BitVec 32)
    (n : Nat) (m₀ : Mem) (j : Nat) (s₀ s : State) : Prop where
  mid : CrMidG to c st w sp k7 k8 R icb P S T n m₀ j s₀
  env : Env c st w sp k7 k8 s
  r4 : s.gpr .r4 = S + BitVec.ofNat 32 j
  r5 : s.gpr .r5 = BitVec.ofNat 32 (n - j)
  r6 : to = true → s.gpr .r6 = T + BitVec.ofNat 32 j
  r8 : s.gpr .r8 = BitVec.ofNat 32 R
  ks : blockAt s.mem (State.addr st + BitVec.ofNat 64 64) =
    ciphOf m₀ (State.addr c) R (blockAt s₀.mem (State.addr st + BitVec.ofNat 64 48))
  cb : blockAt s.mem (State.addr st + BitVec.ofNat 64 48) =
    Spec.Gcm.inc32 (blockAt s₀.mem (State.addr st + BitVec.ofNat 64 48))
  frame : Frame [⟨State.addr st + BitVec.ofNat 64 48, 32⟩, ⟨State.addr w + BitVec.ofNat 64 512, 2048⟩, below sp]
    s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The new keystream block. -/
theorem tailKs_ok {to : Bool} {R : Nat} {icb : Block} {P : Nat} {S T : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat}
    {s : State} (h : CrMidG to c st w sp k7 k8 R icb P S T n m₀ j s)
    (hc : ciphOf s.mem (State.addr c) R = ciphOf m₀ (State.addr c) R) :
    WP isa (.seq (.block tailArgs) ctrFrame) s (TailKs to c st w sp k7 k8 R icb P S T n m₀ j s) := by
  have he := h.env
  obtain ⟨s₂, run₂, hm₂, h0, h1, h2, h3, h12, hlr, hg₂, hrd₂, hwr₂, hsp₂⟩ := tailArgs_ok L he
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have he₂ : Env c st w sp k7 k8 s₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hsp₂ hrd₂ hwr₂
  have hk := he₂.sp
  have eC := L.stA (d := 48) (by decide)
  have eK := L.stA (d := 64) (by decide)
  have eS := L.wA (d := 512) (by decide)
  have fz : Frame [⟨State.addr st + BitVec.ofNat 64 64, 16⟩] s.mem s₂.mem := by
    rw [hm₂]; exact Cmac.frame_store4 _ _ _ _ _
  have hKS0 : blockAt s₂.mem (State.addr st + BitVec.ofNat 64 64) = 0 := by
    rw [blockAt, hm₂, store4_zero_bytes]; decide
  have hCB : blockAt s₂.mem (State.addr st + BitVec.ofNat 64 48) = blockAt s.mem (State.addr st + BitVec.ofNat 64 48) :=
    blockAt_frame fz fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
  have hc₂ : ciphOf s₂.mem (State.addr c) R = ciphOf m₀ (State.addr c) R := by
    rw [ciph_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cs.sub_right (Lay.stSub (by decide))) h.rounds, hc]
  have hcall : CtrCall s₂ c (st + BitVec.ofNat 32 48) (st + BitVec.ofNat 32 64) (w + BitVec.ofNat 32 512) R 1 :=
    ctrTail_mk L he₂ h0 (by rw [h1, h.r8]) h2 h3 h12 hlr h.rounds
  refine WP.mono (ctr_call hcall) fun s₃ g => ?_
  have gout := g.out; have gctr := g.ctr; have gframe := g.frame
  simp only [eC, eK, eS, hk] at gout gctr gframe
  rw [blocksAt_one, blocksAt_one, hKS0, Cmac.ctr32_one, List.cons.injEq] at gout
  refine ⟨h, he₂.of_saved g.saved g.sp g.rd g.wr, ?_, ?_, fun ht => ?_, ?_, ?_, ?_, ?_, by rw [g.rd, hrd₂],
    by rw [g.wr, hwr₂]⟩
  · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r4]
  · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r5]
  · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r6 ht]
  · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r8]
  · rw [gout.1, ← hc₂, hCB]
  · rw [gctr, hCB]; rfl
  · refine (fz.sub fun r hr => ?_).trans (gframe.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩

omit L in
theorem ne_xsrc {to : Bool} {r : Reg} (h₂ : r ≠ .r2) (h₄ : r ≠ .r4) : r ≠ xsrc to := by
  cases to
  · exact h₂
  · exact h₄

/-- The last bytes of the source, at `S + j`, XORed with the new keystream
block and written to `T + j` (in place, `S = T`), in one pass. -/
theorem tailXor_ok {to : Bool} {R : Nat} {icb : Block} {P : Nat} {S T : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat}
    {s₀ s : State} (h : TailKs to c st w sp k7 k8 R icb P S T n m₀ j s₀ s) (hj : n - j < 16) (h0 : n - j ≠ 0)
    (hb : bytesAt s.mem (State.addr S + BitVec.ofNat 64 j) (n - j) =
      bytesAt m₀ (State.addr S + BitVec.ofNat 64 j) (n - j)) :
    WP isa (tailXor to) s (CrOutG to c st w sp k7 k8 R icb P S T n m₀) := by
  have hm := h.mid
  have hn' := hm.data.ok.lt32
  have hw : (P + j) % 16 = 0 := hm.whole.resolve_left h0
  have hdj := hm.data.sub (j := j) (k := n - j) (by omega_arith) (by omega_arith)
  have eD := hm.data.ok.addr (j := j) (by omega_arith)
  have hsj := hm.src.sub (j := j) (k := n - j) (by omega_arith) (by omega_arith)
  have eS := hm.src.addr (j := j) (by omega_arith)
  have he₃ := h.env
  have hd : s.gpr (dreg to) = T + BitVec.ofNat 32 j := by
    cases to
    · have e : S = T := hm.mode
      subst e
      exact h.r4
    · exact h.r6 rfl
  obtain ⟨s₄, run₄, h1, h2, h3, hg₄, hk₄⟩ : ∃ s₄, runBlock isa
      [addI .r1 .r10 64, .mov .r2 (.reg (dreg to)), .mov .r3 (.reg .r5)] s = some s₄ ∧
      s₄.gpr .r1 = st + BitVec.ofNat 32 64 ∧ s₄.gpr .r2 = T + BitVec.ofNat 32 j ∧
      s₄.gpr .r3 = BitVec.ofNat 32 (n - j) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₄.gpr r = s.gpr r) ∧ Keeps s s₄ := by
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, he₃.r10]
    · have : dreg to ≠ .r1 := by cases to <;> decide
      simp [gpr_setReg, this, hd]
    · simp [gpr_setReg, h.r5]
    · intro r a b d; simp [gpr_setReg, a, b, d]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  have eK := L.stA (d := 64) (by decide)
  have lp : LoopPre s₄ (st + BitVec.ofNat 32 64) (T + BitVec.ofNat 32 j) (n - j) := by
    refine ⟨h1, h2, h3, by omega_arith, by omega_arith, by rw [L.stN (by decide)]; have := L.sw; omega_arith,
      hdj.ok.fit, ?_, ?_, ?_⟩
    · rw [hk₄.rd, hk₄.wr, eK]; exact covers_left (he₃.perm.stC (by omega_arith))
    · rw [hk₄.wr, h.wr]; exact hdj.wr
    · rw [eK]; exact (hdj.ok.st.sub_right (Lay.stSub (by omega_arith))).symm
  have xs : XSrc to s₄ (S + BitVec.ofNat 32 j) (T + BitVec.ofNat 32 j) (n - j) := by
    refine ⟨?_, hsj.fit, by rw [hk₄.rd, hk₄.wr, h.rd, h.wr]; exact hsj.rd, fun ht => ?_⟩
    · cases to
      · have e : S = T := hm.mode
        rw [e]; exact h2
      · rw [show xsrc true = .r4 from rfl, hg₄ .r4 (by decide) (by decide) (by decide)]; exact h.r4
    · subst ht
      rw [eS, eD]
      exact (hm.mode.1.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))
  refine WP.mono (xorLoopG_ok s₄ lp xs) fun s₅ ⟨hm₅, _, _, _, other, rd₅, wr₅, sp₅⟩ => ?_
  rw [hk₄.mem, eK, eD, eS] at hm₅
  have hxl := length_xorBytes s.mem (State.addr S + BitVec.ofNat 64 j) (State.addr st + BitVec.ofNat 64 64) (n - j)
  have fw : Frame [⟨State.addr T + BitVec.ofNat 64 j, n - j⟩] s.mem s₅.mem := by
    rw [hm₅]; exact writeBytes_frame' _ hxl
  have dst := hdj.ok.st; have dw := hdj.ok.w; have dk := hdj.ok.stk
  rw [eD] at dst dw dk
  have dS : ∀ r ∈ [(⟨State.addr T + BitVec.ofNat 64 j, n - j⟩ : Region)], ∀ k, k + 16 ≤ 80 →
      (⟨State.addr st + BitVec.ofNat 64 k, 16⟩ : Region).Disjoint r := by
    intro r hr k hk; simp only [List.mem_singleton] at hr; subst hr
    exact (dst.sub_right (Lay.stSub hk)).symm
  have ht := fun hc₀ => Proof.Gcm.ctr_tail (hm.ctr hc₀) hw (m₁ := s.mem) h.ks (by rw [h.cb])
    (d := bytesAt m₀ (State.addr S + BitVec.ofNat 64 j) (n - j)) (by rw [length_bytesAt]; omega_arith)
    (by rw [length_bytesAt]; omega_arith)
  rw [length_bytesAt] at ht
  have g : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → s₅.gpr r = s.gpr r :=
    fun r a b c d e f => by rw [other r a b c d f (ne_xsrc c e), hg₄ r b c d]
  refine ⟨he₃.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        exact g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (sp₅.trans hk₄.sp) (rd₅.trans hk₄.rd) (wr₅.trans hk₄.wr),
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r8], ?_, ?_, ?_⟩
  · intro hc₀
    rw [show P + n = P + j + (n - j) by omega_arith]
    exact (ht hc₀).2.congr (blockAt_frame fw fun r hr => dS r hr 48 (by decide))
      (blockAt_frame fw fun r hr => dS r hr 64 (by decide))
  · intro hc₀
    have hdt := (hm.data.take hm.le).ok
    have sj : ∀ r ∈ [(⟨State.addr T + BitVec.ofNat 64 j, n - j⟩ : Region)],
        (⟨State.addr T, j⟩ : Region).Disjoint r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact split_disj hm.le hm.data.ok.lt
    have hdone : bytesAt s₅.mem (State.addr T) j = bytesAt s₀.mem (State.addr T) j := by
      rw [bytesAt_frame fw sj (by omega_arith), bytesAt_frame h.frame (fun r hr => ?_) (by omega_arith)]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hdt.st.sub_right (Lay.stSub (by decide))
      · exact hdt.w.sub_right (Lay.wSub (by decide))
      · exact hdt.stk.symm
    have hpiece : bytesAt s₅.mem (State.addr T + BitVec.ofNat 64 j) (n - j) =
        xorKs (ciphOf m₀ (State.addr c) R) icb (P + j) (bytesAt m₀ (State.addr S + BitVec.ofNat 64 j) (n - j)) := by
      have e := bytesAt_writeBytes_self s.mem (State.addr T + BitVec.ofNat 64 j)
        (xorBytes s.mem (State.addr S + BitVec.ofNat 64 j) (State.addr st + BitVec.ofNat 64 64) (n - j))
        (by rw [hxl]; omega_arith)
      rw [hxl] at e
      rw [hm₅, e, xorBytes, hb, (ht hc₀).1]
    rw [show n = j + (n - j) by omega_arith]
    exact done_append (hdone.trans (hm.done hc₀)) hpiece
  · have sT : Region.Sub ⟨State.addr T + BitVec.ofNat 64 j, n - j⟩ ⟨State.addr T, n⟩ :=
      Offset.sub_base _ (by omega_arith)
    refine hm.frame.trans (Frame.trans (h.frame.sub fun r hr => ?_) (fw.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, crFrame_sub _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
      · exact ⟨_, crFrame_sub _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
          fun _ h => h⟩
      · exact ⟨_, crFrame_sub _ (by simp), fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, crFrame_sub _ (List.mem_cons_self ..), sT⟩

/-- The last bytes, with a new keystream block. -/
theorem cryptTail_ok {to : Bool} {R : Nat} {icb : Block} {P : Nat} {S T : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat}
    {s : State} (h : CrMidG to c st w sp k7 k8 R icb P S T n m₀ j s) (hj : n - j < 16)
    (hc : ciphOf s.mem (State.addr c) R = ciphOf m₀ (State.addr c) R) :
    WP isa (cryptTailG to) s (CrOutG to c st w sp k7 k8 R icb P S T n m₀) := by
  have hn' := h.data.ok.lt32
  have he := h.env
  obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r5 h.r5 (by omega_arith)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : Env c st w sp k7 k8 s₁ := he.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁
  have h₁ : CrMidG to c st w sp k7 k8 R icb P S T n m₀ j s₁ :=
    ⟨he₁, h.le, (by rw [hg₁]; exact h.r4), (by rw [hg₁]; exact h.r5), (by rw [hg₁]; exact h.r8), h.rounds,
      h.data.of_eq hrd₁ hwr₁, (fun hc₀ => by rw [hm₁]; exact h.ctr hc₀), (fun hc₀ => by rw [hm₁]; exact h.done hc₀),
      (by rw [hm₁]; exact h.rest), h.whole, (by rw [hm₁]; exact h.frame), fun ht => by rw [hg₁]; exact h.r6 ht,
      h.src.of_eq hrd₁ hwr₁, h.mode⟩
  refine WP.ite (decide (n - j = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : j = n := by have := h.le; simp at ht; omega_arith
    subst h0
    exact WP.block_nil ⟨he₁, h₁.r8, fun hc₀ => h₁.ctr hc₀, fun hc₀ => h₁.done hc₀, h₁.frame⟩
  · have h0 : n - j ≠ 0 := by simpa using hf
    refine WP.seq (WP.mono (tailKs_ok L h₁ (by rw [hm₁]; exact hc)) fun s₂ ht => ?_)
    refine tailXor_ok L ht hj h0 ?_
    rw [← h₁.rest, bytesAt_frame ht.frame (fun r hr => ?_) (by have := h.le; omega_arith)]
    have hsj := h₁.src.sub (j := j) (k := n - j) (by omega_arith) (by omega_arith)
    have eS := h₁.src.addr (j := j) (by omega_arith)
    have sst := hsj.st; have ssw := hsj.w; have ssk := hsj.stk
    rw [eS] at sst ssw ssk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sst.sub_right (Lay.stSub (by decide))
    · exact ssw.sub_right (Lay.wSub (by decide))
    · exact ssk.symm

theorem CrMidG.ciph {to : Bool} {R : Nat} {icb : Block} {P : Nat} {S T : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat}
    {s : State} (h : CrMidG to c st w sp k7 k8 R icb P S T n m₀ j s) :
    ciphOf s.mem (State.addr c) R = ciphOf m₀ (State.addr c) R :=
  ciph_frame h.frame (ctx_crFrameG L h.data h.mode) h.rounds

omit L in
theorem CrIn.keep {R : Nat} {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {s s' : State}
    (h : CrIn c st w sp k7 k8 R icb P D n s) (hg : s'.gpr = s.gpr) (hk : Keeps s s') : CrIn c st w sp k7 k8 R icb P D n s' :=
  ⟨h.env.keep (fun r _ => by rw [hg]) hk.sp hk.rd hk.wr, by rw [hg]; exact h.r4, by rw [hg]; exact h.r5,
    by rw [hg]; exact h.r6, by rw [hg]; exact h.r8, h.rounds, h.data.of_eq hk.rd hk.wr⟩

/-- The rest of the keystream block first, if there is one. -/
theorem cryptFill_ok {R : Nat} {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {s : State}
    (h : CrIn c st w sp k7 k8 R icb P D n s) (h0 : n ≠ 0) :
    WP isa cryptFill s (fun s' => ∃ j, j = (if P % 16 = 0 then 0 else min (16 - P % 16) n) ∧
      CrMid c st w sp k7 k8 R icb P D n s.mem j s') := by
  obtain ⟨s₂, run₂, hz₂, hg₂, hm₂, hrd₂, hwr₂, hsp₂⟩ := cmp0_ok s .r6 h.r6
    (by have := Nat.mod_lt P (show 16 > 0 by decide); omega_arith)
  have h₂ := h.keep hg₂ ⟨hm₂, hrd₂, hwr₂, hsp₂⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  refine WP.ite (decide (P % 16 = 0)) (eval_eq' hz₂) (fun ht => ?_) (fun hf => ?_)
  · have ho : P % 16 = 0 := by simpa using ht
    exact WP.block_nil ⟨0, by simp [ho], h₂.env, by omega_arith, by rw [h₂.r4, add_ofNat_zero], by rw [h₂.r5, Nat.sub_zero], h₂.r8,
      h₂.rounds, h₂.data, fun hc₀ => by rw [hm₂]; simpa using hc₀, fun _ => by simp [bytesAt]; rfl,
      by rw [hm₂, add_ofNat_zero], .inr (by omega_arith), by rw [hm₂]; exact Frame.refl _ _, nofun, h₂.data.ok, rfl⟩
  · have hP : P % 16 ≠ 0 := by simpa using hf
    have := cryptHead_ok L h₂ h0 hP
    rw [hm₂] at this
    exact WP.mono this fun _ ⟨j, hj, hm⟩ => ⟨j, by simp only [hP, ite_false]; exact hj, hm⟩

/-- `crypt`. -/
theorem crypt_ok {R : Nat} {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {s : State}
    (h : CrIn c st w sp k7 k8 R icb P D n s) :
    WP isa crypt s (CrOut c st w sp k7 k8 R icb P D n s.mem) := by
  have hn' := h.data.ok.lt32
  obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r5 h.r5 hn'
  have h₁ := h.keep hg₁ ⟨hm₁, hrd₁, hwr₁, hsp₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨h₁.env, h₁.r8, fun hc₀ => by rw [hm₁]; exact hc₀,
      fun _ => by simp [bytesAt]; rfl, by rw [hm₁]; exact Frame.refl _ _⟩
  · have h0 : n ≠ 0 := by simpa using hf
    rw [← hm₁]
    refine WP.seq (WP.mono (cryptFill_ok L h₁ h0) fun s' ⟨j, _, hj⟩ => ?_)
    refine WP.seq (WP.mono (cryptWholeG_ok L hj (CrMidG.ciph L hj)) fun s'' ⟨j', _, hj', hlt⟩ => ?_)
    exact cryptTail_ok L hj' hlt (CrMidG.ciph L hj')

/-- `cryptTo`: out of place, from a whole number of blocks of text so far
(`r6` holds the destination). -/
theorem cryptTo_ok {R : Nat} {icb : Block} {P : Nat} {S T : BitVec 32} {n : Nat} {s : State}
    (h : CrMidG true c st w sp k7 k8 R icb P S T n s.mem 0 s) :
    WP isa cryptTo s (CrOutG true c st w sp k7 k8 R icb P S T n s.mem) := by
  have hn' := h.data.ok.lt32
  obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r5 (by rw [h.r5, Nat.sub_zero]) hn'
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have h₁ : CrMidG true c st w sp k7 k8 R icb P S T n s.mem 0 s₁ :=
    ⟨h.env.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁, h.le, (by rw [hg₁]; exact h.r4),
      (by rw [hg₁]; exact h.r5), (by rw [hg₁]; exact h.r8), h.rounds,
      h.data.of_eq hrd₁ hwr₁, (fun hc₀ => by rw [hm₁]; exact h.ctr hc₀), (fun hc₀ => by rw [hm₁]; exact h.done hc₀),
      (by rw [hm₁]), h.whole, (by rw [hm₁]; exact h.frame), fun ht => by rw [hg₁]; exact h.r6 ht,
      h.src.of_eq hrd₁ hwr₁, h.mode⟩
  refine WP.ite (decide (n = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨h₁.env, h₁.r8, fun hc₀ => h₁.ctr hc₀, fun _ => by simp [bytesAt]; rfl, h₁.frame⟩
  · refine WP.seq (WP.mono (cryptWholeG_ok L h₁ (CrMidG.ciph L h₁)) fun s'' ⟨j', _, hj', hlt⟩ => ?_)
    exact cryptTail_ok L hj' hlt (CrMidG.ciph L hj')

end

end VG.Proof.AesGcm.Arm
