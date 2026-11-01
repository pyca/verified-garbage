module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Crypt
import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.AesGcm.RISCV64.Ghash1
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Callee
import VerifiedGarbage.Proof.AesGcm.RISCV64.Loops
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
public import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-GCM on RISCV64: `crypt`

Untrusted: everything here is checked by Lean (see `Crypt.lean`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith)
open VG.Proof.Gcm (Ctr xorKs)

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s1) (V .s0))
include L

omit L in
/-- The rest of the keystream block. -/
theorem cryptHead_ok {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {s : State}
    (h : CrIn V sp R icb P D n s) (hn : n ≠ 0) (hP : P % 16 ≠ 0) :
    WP isa cryptHead s (fun s' => ∃ j, j = min (16 - P % 16) n ∧ CrMid V sp R icb P D n s.mem j s') := by
  have hlt : P % 16 < 16 := Nat.mod_lt _ (by decide)
  have hn' := h.data.ok.lt
  have he := h.env
  refine WP.seq (WP.mono (minLen_ok s h.s6 h.s5 (by omega_arith) hn') fun s₁ ⟨h5, hg, hk⟩ => ?_)
  obtain ⟨k, hk'⟩ : ∃ k, min (16 - P % 16) n = k := ⟨_, rfl⟩
  rw [hk'] at h5
  have hk1 : 1 ≤ k := by omega_arith
  have hk16 : P % 16 + k ≤ 16 := by omega_arith
  have hkn : k ≤ n := by omega_arith
  have e30 : s₁.gpr .s1 = V .s1 := (hg _ (by decide) (by decide)).trans he.s1
  have e24 : s₁.gpr .s4 = D := (hg _ (by decide) (by decide)).trans h.s4
  have e25 : s₁.gpr .s5 = BitVec.ofNat 64 n := (hg _ (by decide) (by decide)).trans h.s5
  have e26 : s₁.gpr .s6 = BitVec.ofNat 64 (P % 16) := (hg _ (by decide) (by decide)).trans h.s6
  have h₂ : WP isa (.block [.addi .a0 .s1 64, .add .a0 .a0 .s6, mov .a1 .s4, .add .s4 .s4 .a2,
      .sub .s5 .s5 .a2]) s₁ (fun s₂ : State =>
      s₂.gpr .a0 = V .s1 + BitVec.ofNat 64 (64 + P % 16) ∧ s₂.gpr .a1 = D ∧
      s₂.gpr .s4 = D + BitVec.ofNat 64 k ∧ s₂.gpr .s5 = BitVec.ofNat 64 (n - k) ∧
      s₂.gpr .a2 = BitVec.ofNat 64 k ∧
      (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .s4 → r ≠ .s5 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂) := by
    crun [Int.reduceNatCast', e30, e24, e25, e26, h5, mov, BitVec.or_self]
    exact ⟨by rw [add_ofNat_assoc], ofNat_sub64 hkn hn', fun r a b c d => by simp [a, b, c, d],
      ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₂ fun s₂ ⟨h3, h4, h24, h25, h5', hg₂, hk₂⟩ => ?_)
  have hk₂' := hk.trans hk₂
  have hdk := h.data.take hkn
  have lp : LoopPre s₂ (V .s1 + BitVec.ofNat 64 (64 + P % 16)) D k := by
    refine ⟨h3, h4, h5', hk1, by omega_arith, ?_, ?_, ?_⟩
    · rw [hk₂'.rd, hk₂'.wr]; exact covers_left (he.perm.stC (by omega_arith))
    · rw [hk₂'.wr]; exact hdk.wr
    · exact (hdk.ok.st.sub_right (Lay.stSub (by omega_arith))).symm
  refine WP.mono (xorLoop_ok s₂ lp) fun s₃ ⟨hm₃, lo⟩ => ?_
  rw [hk₂'.mem] at hm₃
  have hxl := length_xorBytes s.mem D (V .s1 + BitVec.ofNat 64 (64 + P % 16)) k
  have fw : Frame [⟨D, k⟩] s.mem s₃.mem := by rw [hm₃]; exact writeBytes_frame' _ hxl
  have hdisjst : ∀ r ∈ [(⟨D, k⟩ : Region)],
      (⟨V .s1 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r ∧
      (⟨V .s1 + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(hdk.ok.st.sub_right (Lay.stSub (by decide))).symm, (hdk.ok.st.sub_right (Lay.stSub (by decide))).symm⟩
  have g : ∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → r ≠ .s4 → r ≠ .s5 →
      s₃.gpr r = s.gpr r :=
    fun r a b c d e f i => by rw [lo.other r a b c d e, hg₂ r b c f i, hg r d e]
  have he₃ : Env V sp s₃ := he.keep (fun r hr => g r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide)) (lo.keeps.2.2.trans hk₂'.sp) (lo.keeps.1.trans hk₂'.rd)
    (lo.keeps.2.1.trans hk₂'.wr)
  refine ⟨k, hk'.symm, he₃, hkn, by rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide), h24],
    by rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide), h25],
    h.s3, h.rounds, h.data.of_eq (lo.keeps.1.trans hk₂'.rd) (lo.keeps.2.1.trans hk₂'.wr) (lo.keeps.2.2.trans hk₂'.sp), ?_, ?_, ?_, ?_, ?_⟩
  · intro hc₀
    exact (hc₀.head hP hk16).congr (blockAt_frame fw fun r hr => (hdisjst r hr).1)
      (blockAt_frame fw fun r hr => (hdisjst r hr).2)
  · intro hc₀
    have e := bytesAt_writeBytes_self s.mem D (xorBytes s.mem D (V .s1 + BitVec.ofNat 64 (64 + P % 16)) k)
      (by rw [hxl]; omega_arith)
    rw [hxl] at e
    rw [hm₃, e, xorBytes]
    have := Proof.Gcm.ctr_head hc₀ hP (d := bytesAt s.mem D k) (by rw [length_bytesAt]; exact hk16)
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
theorem CrMid.data_eq {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid V sp R icb P D n m₀ j s) : bytesAt s.mem D n =
      bytesAt s.mem D j ++ bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) := by
  rw [← bytesAt_add, Nat.add_sub_cancel' h.le]

omit L in
/-- The split of the rest into whole blocks for `vg_aes_ctr32` and the last bytes. -/
theorem splitCtr_ok {s : State} {D : Addr} {n j : Nat} (hj : j ≤ n) (hn : n < 2 ^ 64)
    (h24 : s.gpr .s4 = D + BitVec.ofNat 64 j) (h25 : s.gpr .s5 = BitVec.ofNat 64 (n - j)) :
    WP isa (.block splitCtr) s fun s' =>
      s'.gpr .a3 = D + BitVec.ofNat 64 j ∧ s'.gpr .a4 = BitVec.ofNat 64 ((n - j) / 16) ∧
      s'.gpr .s4 = D + BitVec.ofNat 64 (j + 16 * ((n - j) / 16)) ∧
      s'.gpr .s5 = BitVec.ofNat 64 (n - (j + 16 * ((n - j) / 16))) ∧
      (∀ r, r ≠ .t0 → r ≠ .a3 → r ≠ .a4 → r ≠ .a5 → r ≠ .a6 → r ≠ .s4 → r ≠ .s5 →
        s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have hand := and15 (BitVec.ofNat 64 (n - j))
  rw [toNat64 (by omega_arith)] at hand
  have hsub : BitVec.ofNat 64 (n - j) - BitVec.ofNat 64 ((n - j) % 16) =
      BitVec.ofNat 64 (16 * ((n - j) / 16)) := by
    rw [ofNat_sub64 (Nat.mod_le _ _) (by omega_arith)]; congr 1; omega_arith
  simp only [splitCtr]
  crun [Int.reduceNatCast', h24, h25, mov, BitVec.or_self, hand, hsub, shr4 (show n - j < 2 ^ 64 by omega_arith), add_ofNat_assoc]
  refine ⟨by congr 1; omega_arith, fun r a b c d e f g => by simp [a, b, c, d, e, f, g],
    ⟨rfl, rfl, rfl, rfl⟩⟩

omit L in
/-- The arguments of `vg_aes_ctr32` but the data and their number. -/
theorem ctrArgs_ok {s : State} (he : Env V sp s) {R : Nat} (hR : V .s3 = BitVec.ofNat 64 R) :
    WP isa (.block (ctrArgs 48)) s fun s' =>
      s'.gpr .a0 = V .s2 ∧ s'.gpr .a1 = BitVec.ofNat 64 R ∧ s'.gpr .a2 = V .s1 + BitVec.ofNat 64 48 ∧
      s'.gpr .a5 = V .s0 + BitVec.ofNat 64 512 ∧
      (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a5 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have h28 := he.s3; have h29 := he.s2; have h30 := he.s1; have h31 := he.s0
  simp only [ctrArgs]
  crun [Int.reduceNatCast', scrO, h28, h29, h30, h31, hR, mov, BitVec.or_self]
  exact ⟨fun r a b c d => by simp [a, b, c, d], ⟨rfl, rfl, rfl, rfl⟩⟩

/-- The arguments of `vg_aes_ctr32` on `nb` whole blocks at `D + j`. -/
theorem ctrWhole_mk {R : Nat} {D : Addr} {j nb : Nat} {s : State} (he : Env V sp s)
    (h3 : s.gpr .a0 = V .s2) (h4 : s.gpr .a1 = BitVec.ofNat 64 R) (h5 : s.gpr .a2 = V .s1 + BitVec.ofNat 64 48)
    (h6 : s.gpr .a3 = D + BitVec.ofNat 64 j) (h7 : s.gpr .a4 = BitVec.ofNat 64 nb)
    (h8 : s.gpr .a5 = V .s0 + BitVec.ofNat 64 512) (hR : R = 10 ∨ R = 12 ∨ R = 14) (hnb : nb < 2 ^ 64)
    (hdj : DataW (V .s2) (V .s1) (V .s0) s (D + BitVec.ofNat 64 j) (16 * nb)) :
    CtrCall s (V .s2) (V .s1 + BitVec.ofNat 64 48) (D + BitVec.ofNat 64 j) (V .s0 + BitVec.ofNat 64 512) R nb := by
  refine ⟨h3, h4, h5, h6, h7, h8, hR, hnb, ?_, ?_, ?_, ?_, ?_, ?_, hdj.ok.fit, ?_, ?_⟩
  · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide))
  · exact hdj.ctx.sub_left (Region.sub_prefix (by decide))
  · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
  · exact (hdj.ok.st.sub_right (Lay.stSub (by decide))).symm
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact hdj.ok.w.sub_right (Lay.wSub (by decide))
  · exact Covers.cons (covers_prefix he.perm.ctx (by decide)) (Covers.cons
      (covers_left (he.perm.stC (by decide))) (Covers.cons (covers_left hdj.wr)
        (Covers.cons (covers_left (he.perm.wC (by decide))) Covers.nil)))
  · exact Covers.cons (he.perm.stC (by decide)) (Covers.cons hdj.wr
      (Covers.cons (he.perm.wC (by decide)) Covers.nil))

/-- Whole blocks. -/
theorem cryptWhole_ok {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid V sp R icb P D n m₀ j s) (hc : ciphOf s.mem (V .s2) R = ciphOf m₀ (V .s2) R) :
    WP isa cryptWhole s (fun s' => ∃ j', j' = j + 16 * ((n - j) / 16) ∧ CrMid V sp R icb P D n m₀ j' s' ∧
      n - j' < 16) := by
  have hn' := h.data.ok.lt
  have he := h.env
  refine WP.seq (WP.mono (splitCtr_ok h.le hn' h.s4 h.s5) fun s₁ ⟨h6, h7, h24, h25, hg₁, hk₁⟩ => ?_)
  generalize hnb : (n - j) / 16 = nb at h7 h24 h25
  have h16 : 16 * nb ≤ n - j := by omega_arith
  have he₁ : Env V sp s₁ := he.keep (fun r hr => hg₁ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide)) hk₁.sp hk₁.rd hk₁.wr
  have hd₁ := h.data.of_eq hk₁.rd hk₁.wr hk₁.sp
  refine WP.ite (decide (nb = 0)) (eval_zero h7 (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : nb = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨j, by omega_arith, ⟨he₁, h.le, by rw [h24]; rfl, by rw [h25]; rfl, h.s3, h.rounds, hd₁,
      fun hc₀ => by rw [hk₁.mem]; exact h.ctr hc₀, fun hc₀ => by rw [hk₁.mem]; exact h.done hc₀,
      by rw [hk₁.mem]; exact h.rest, h.whole, by rw [hk₁.mem]; exact h.frame⟩, by omega_arith⟩
  · have h0 : nb ≠ 0 := by simpa using hf
    have hw : (P + j) % 16 = 0 := h.whole.resolve_left (by omega_arith)
    have hdj := h.data.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith)
    refine WP.seq (WP.mono (ctrArgs_ok he₁ h.s3) fun s₂ ⟨a3, a4, a5, a8, hg₂, hk₂⟩ => ?_)
    have he₂ : Env V sp s₂ := he₁.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr
    have hcall := ctrWhole_mk L he₂ a3 a4 a5 (by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h6])
      (by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h7]) a8 h.rounds (by omega_arith)
      (hdj.of_eq (hk₂.rd.trans hk₁.rd) (hk₂.wr.trans hk₁.wr) (hk₂.sp.trans hk₁.sp))
    refine WP.mono (ctr_call hcall) fun s₃ g => ?_
    have gout := g.out; have gctr := g.ctr; have gframe := g.frame
    simp only [hk₂.mem, hk₁.mem] at gout gctr gframe
    have hcw := fun hc₀ => Proof.Gcm.ctr_whole (h.ctr hc₀) hw (m' := s₃.mem)
      (dp := D + BitVec.ofNat 64 j) (nb := nb) (by rw [gout, ← hc]) gctr
    refine ⟨j + 16 * nb, by omega_arith, ⟨he₂.of_saved g.saved g.sp g.rd g.wr, by omega_arith, ?_, ?_, h.s3, h.rounds,
      hd₁.of_eq (g.rd.trans hk₂.rd) (g.wr.trans hk₂.wr) (g.sp.trans hk₂.sp), ?_, ?_, ?_, .inr (by omega_arith), ?_⟩, by omega_arith⟩
    · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide), h24]
    · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide), h25]
    · intro hc₀; rw [← Nat.add_assoc]; exact (hcw hc₀).2
    · intro hc₀
      have hj16 : bytesAt s₃.mem (D + BitVec.ofNat 64 j) (16 * nb) =
          xorKs (ciphOf m₀ (V .s2) R) icb (P + j) (bytesAt m₀ (D + BitVec.ofNat 64 j) (16 * nb)) := by
        rw [(hcw hc₀).1]
        congr 1
        have e := congrArg (List.take (16 * nb)) h.rest
        rwa [show n - j = 16 * nb + (n - j - 16 * nb) by omega_arith, bytesAt_add, bytesAt_add,
          List.take_left' (length_bytesAt _ _ _), List.take_left' (length_bytesAt _ _ _)] at e
      have hjd : bytesAt s₃.mem D j = bytesAt s.mem D j := bytesAt_frame gframe (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact (h.data.take h.le).ok.st.sub_right (Lay.stSub (by decide))
        · exact split_disj (D := D) (j := j) (n := n) h.le h.data.ok.lt |>.sub_right
            (Region.sub_prefix (by omega_arith))
        · exact (h.data.take h.le).ok.w.sub_right (Lay.wSub (by decide))) (by omega_arith)
      exact done_append (hjd.trans (h.done hc₀)) hj16
    · have hdis : ∀ r ∈ [⟨V .s1 + BitVec.ofNat 64 48, 16⟩, ⟨D + BitVec.ofNat 64 j, 16 * nb⟩,
          ⟨V .s0 + BitVec.ofNat 64 512, 2048⟩],
          (⟨D + BitVec.ofNat 64 (j + 16 * nb), n - (j + 16 * nb)⟩ : Region).Disjoint r := by
        have hst := h.data.ok.st; have hW := h.data.ok.w
        have hs : Region.Sub ⟨D + BitVec.ofNat 64 (j + 16 * nb), n - (j + 16 * nb)⟩ ⟨D, n⟩ :=
          Offset.sub_base _ (by omega_arith)
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact (hst.sub_left hs).sub_right (Lay.stSub (by decide))
        · rw [← add_ofNat_assoc]
          have := split_disj (D := D + BitVec.ofNat 64 j) (j := 16 * nb) (n := n - j) h16 (by omega_arith)
          rw [show n - j - 16 * nb = n - (j + 16 * nb) by omega_arith] at this
          exact this.symm
        · exact (hW.sub_left hs).sub_right (Lay.wSub (by decide))
      rw [bytesAt_frame gframe hdis (by omega_arith)]
      have e := congrArg (List.drop (16 * nb)) h.rest
      have e₂ : ∀ m : Mem, (bytesAt m (D + BitVec.ofNat 64 j) (n - j)).drop (16 * nb) =
          bytesAt m (D + BitVec.ofNat 64 (j + 16 * nb)) (n - (j + 16 * nb)) := fun m => by
        rw [show n - j = 16 * nb + (n - (j + 16 * nb)) by omega_arith, bytesAt_add,
          List.drop_left' (length_bytesAt _ _ _), add_ofNat_assoc]
      simpa only [e₂] using e
    · refine h.frame.trans (gframe.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., (Offset.sub_base _ (by omega_arith))⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩

/-- The keystream block zeroed and the arguments of `vg_aes_ctr32` on it. -/
theorem tailArgs_ok {s : State} (he : Env V sp s) {R : Nat} (hR : V .s3 = BitVec.ofNat 64 R) :
    WP isa (.block tailArgs) s fun s' =>
      s'.mem = (s.mem.writeW (V .s1 + BitVec.ofNat 64 64) (0 : BitVec 64)).writeW
        (V .s1 + BitVec.ofNat 64 64 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s'.gpr .a0 = V .s2 ∧ s'.gpr .a1 = BitVec.ofNat 64 R ∧ s'.gpr .a2 = V .s1 + BitVec.ofNat 64 48 ∧
      s'.gpr .a3 = V .s1 + BitVec.ofNat 64 64 ∧ s'.gpr .a4 = BitVec.ofNat 64 1 ∧
      s'.gpr .a5 = V .s0 + BitVec.ofNat 64 512 ∧
      (∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → r ≠ .a4 → r ≠ .a5 → s'.gpr r = s.gpr r) ∧
      Keeps' s s' := by
  have h28 := he.s3; have h29 := he.s2; have h30 := he.s1; have h31 := he.s0
  have w₀ := he.perm.stW (show 64 + 8 ≤ 80 by decide)
  have w₁ := he.perm.stW (show 72 + 8 ≤ 80 by decide)
  have a₀ := L.stal (d := 64) (by decide) (by decide)
  have a₁ := L.stal (d := 72) (by decide) (by decide)
  simp only [tailArgs, ctrArgs, List.cons_append, List.nil_append]
  crun [Int.reduceNatCast', scrO, h28, h29, h30, h31, hR, w₀, w₁, a₀, a₁, mov, BitVec.or_self, write_8]
  exact ⟨by simp only [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.reduceAdd],
    fun r a b c d e f i => by simp [a, b, c, d, e, f, i], ⟨rfl, rfl, rfl⟩⟩

/-- The arguments of `vg_aes_ctr32` on the keystream block. -/
theorem ctrTail_mk {R : Nat} {s : State} (he : Env V sp s)
    (h3 : s.gpr .a0 = V .s2) (h4 : s.gpr .a1 = BitVec.ofNat 64 R) (h5 : s.gpr .a2 = V .s1 + BitVec.ofNat 64 48)
    (h6 : s.gpr .a3 = V .s1 + BitVec.ofNat 64 64) (h7 : s.gpr .a4 = BitVec.ofNat 64 1)
    (h8 : s.gpr .a5 = V .s0 + BitVec.ofNat 64 512) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    CtrCall s (V .s2) (V .s1 + BitVec.ofNat 64 48) (V .s1 + BitVec.ofNat 64 64)
      (V .s0 + BitVec.ofNat 64 512) R 1 := by
  refine ⟨h3, h4, h5, h6, h7, h8, hR, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide))
  · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide))
  · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
  · exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · have := L.sw
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 64) (by decide),
      Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  · exact Covers.cons (covers_prefix he.perm.ctx (by decide)) (Covers.cons
      (covers_left (he.perm.stC (by decide))) (Covers.cons (covers_left (he.perm.stC (by decide)))
        (Covers.cons (covers_left (he.perm.wC (by decide))) Covers.nil)))
  · exact Covers.cons (he.perm.stC (by decide)) (Covers.cons (he.perm.stC (by decide))
      (Covers.cons (he.perm.wC (by decide)) Covers.nil))

/-- The last bytes' keystream block, from `vg_aes_ctr32`. -/
structure TailKs (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (icb : Block) (P : Nat) (D : Addr) (n : Nat)
    (m₀ : Mem) (j : Nat) (s₀ s : State) : Prop where
  mid : CrMid V sp R icb P D n m₀ j s₀
  env : Env V sp s
  s4 : s.gpr .s4 = D + BitVec.ofNat 64 j
  s5 : s.gpr .s5 = BitVec.ofNat 64 (n - j)
  ks : blockAt s.mem (V .s1 + BitVec.ofNat 64 64) =
    ciphOf m₀ (V .s2) R (blockAt s₀.mem (V .s1 + BitVec.ofNat 64 48))
  cb : blockAt s.mem (V .s1 + BitVec.ofNat 64 48) =
    Spec.Gcm.inc32 (blockAt s₀.mem (V .s1 + BitVec.ofNat 64 48))
  frame : Frame [⟨V .s1 + BitVec.ofNat 64 48, 32⟩, ⟨V .s0 + BitVec.ofNat 64 512, 2048⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The new keystream block. -/
theorem tailKs_ok {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid V sp R icb P D n m₀ j s) (hc : ciphOf s.mem (V .s2) R = ciphOf m₀ (V .s2) R) :
    WP isa (.seq (.block tailArgs) ctrCall) s (TailKs V sp R icb P D n m₀ j s) := by
  have he := h.env
  refine WP.seq (WP.mono (tailArgs_ok L he h.s3) fun s₂ ⟨hm₂, a3, a4, a5, a6, a7, a8, hg₂, hk₂⟩ => ?_)
  have he₂ : Env V sp s₂ := he.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr
  have fz : Frame [⟨V .s1 + BitVec.ofNat 64 64, 16⟩] s.mem s₂.mem := by
    rw [hm₂]; exact Proof.Cmac.frame_store2 _ _ _
  have hKS0 : blockAt s₂.mem (V .s1 + BitVec.ofNat 64 64) = 0 := by
    rw [hm₂, blockAt, zeroT_bytes]; decide
  have hCB : blockAt s₂.mem (V .s1 + BitVec.ofNat 64 48) = blockAt s.mem (V .s1 + BitVec.ofNat 64 48) :=
    blockAt_frame fz fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
  have hc₂ : ciphOf s₂.mem (V .s2) R = ciphOf m₀ (V .s2) R := by
    rw [ciph_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cs.sub_right (Lay.stSub (by decide))) h.rounds, hc]
  refine WP.mono (ctr_call (ctrTail_mk L he₂ a3 a4 a5 a6 a7 a8 h.rounds)) fun s₃ g => ?_
  have gout := g.out; have gctr := g.ctr; have gframe := g.frame
  rw [blocksAt_one, blocksAt_one, hKS0, Proof.Cmac.ctr32_one, List.cons.injEq] at gout
  refine ⟨h, he₂.of_saved g.saved g.sp g.rd g.wr, ?_, ?_, ?_, ?_, ?_, by rw [g.rd, hk₂.rd], by rw [g.wr, hk₂.wr]⟩
  · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.s4]
  · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.s5]
  · rw [gout.1, ← hc₂, hCB]
  · rw [gctr, hCB]; rfl
  · refine (fz.sub fun r hr => ?_).trans (gframe.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

omit L in
/-- The last bytes XORed with the new keystream block. -/
theorem tailXor_ok {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s₀ s : State}
    (h : TailKs V sp R icb P D n m₀ j s₀ s) (hj : n - j < 16) (h0 : n - j ≠ 0) :
    WP isa (.seq (.block [.addi .a0 .s1 64, mov .a1 .s4, mov .a2 .s5]) xorLoop) s
      (CrOut V sp R icb P D n m₀) := by
  have hm := h.mid
  have hn' := hm.data.ok.lt
  have hw : (P + j) % 16 = 0 := hm.whole.resolve_left h0
  have hdj := hm.data.sub (j := j) (k := n - j) (by omega_arith) (by omega_arith)
  have he₃ := h.env
  have h30 := he₃.s1
  have h₄ : WP isa (.block [.addi .a0 .s1 64, mov .a1 .s4, mov .a2 .s5]) s fun s₄ =>
      s₄.gpr .a0 = V .s1 + BitVec.ofNat 64 64 ∧ s₄.gpr .a1 = D + BitVec.ofNat 64 j ∧
      s₄.gpr .a2 = BitVec.ofNat 64 (n - j) ∧
      (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → s₄.gpr r = s.gpr r) ∧ Keeps s s₄ := by
    crun [Int.reduceNatCast', h30, h.s4, h.s5, mov, BitVec.or_self]
    exact ⟨fun r a b d => by simp [a, b, d], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₄ fun s₄ ⟨h3, h4, h5, hg₄, hk₄⟩ => ?_)
  have lp : LoopPre s₄ (V .s1 + BitVec.ofNat 64 64) (D + BitVec.ofNat 64 j) (n - j) := by
    refine ⟨h3, h4, h5, by omega_arith, by omega_arith, ?_, ?_, ?_⟩
    · rw [hk₄.rd, hk₄.wr]; exact covers_left (he₃.perm.stC (by omega_arith))
    · rw [hk₄.wr, h.wr]; exact hdj.wr
    · exact (hdj.ok.st.sub_right (Lay.stSub (by omega_arith))).symm
  refine WP.mono (xorLoop_ok s₄ lp) fun s₅ ⟨hm₅, lo⟩ => ?_
  rw [hk₄.mem] at hm₅
  have hxl := length_xorBytes s.mem (D + BitVec.ofNat 64 j) (V .s1 + BitVec.ofNat 64 64) (n - j)
  have fw : Frame [⟨D + BitVec.ofNat 64 j, n - j⟩] s.mem s₅.mem := by
    rw [hm₅]; exact writeBytes_frame' _ hxl
  have dst := hdj.ok.st; have dw := hdj.ok.w
  have hd₃ : bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j) := by
    rw [← hm.rest, bytesAt_frame h.frame (fun r hr => ?_) (by omega_arith)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dst.sub_right (Lay.stSub (by decide))
    · exact dw.sub_right (Lay.wSub (by decide))
  have ht := fun hc₀ => Proof.Gcm.ctr_tail (hm.ctr hc₀) hw (m₁ := s.mem) h.ks (by rw [h.cb])
    (d := bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)) (by rw [length_bytesAt]; omega_arith)
    (by rw [length_bytesAt]; omega_arith)
  rw [length_bytesAt] at ht
  have dS : ∀ r ∈ [(⟨D + BitVec.ofNat 64 j, n - j⟩ : Region)], ∀ k, k + 16 ≤ 80 →
      (⟨V .s1 + BitVec.ofNat 64 k, 16⟩ : Region).Disjoint r := by
    intro r hr k hk; simp only [List.mem_singleton] at hr; subst hr
    exact (dst.sub_right (Lay.stSub hk)).symm
  have g : ∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → s₅.gpr r = s.gpr r :=
    fun r a b c d e => by rw [lo.other r a b c d e, hg₄ r b c d]
  refine ⟨he₃.keep (fun r hr => g r (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide))
      (lo.keeps.2.2.trans hk₄.sp) (lo.keeps.1.trans hk₄.rd) (lo.keeps.2.1.trans hk₄.wr), ?_, ?_, ?_⟩
  · intro hc₀
    rw [show P + n = P + j + (n - j) by omega_arith]
    exact (ht hc₀).2.congr (blockAt_frame fw fun r hr => dS r hr 48 (by decide))
      (blockAt_frame fw fun r hr => dS r hr 64 (by decide))
  · intro hc₀
    have hdone : bytesAt s₅.mem D j = bytesAt s₀.mem D j := by
      have hdt := (hm.data.take hm.le).ok
      rw [bytesAt_frame fw (fun r hr => ?_) (by omega_arith), bytesAt_frame h.frame (fun r hr => ?_) (by omega_arith)]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hdt.st.sub_right (Lay.stSub (by decide))
        · exact hdt.w.sub_right (Lay.wSub (by decide))
      · simp only [List.mem_singleton] at hr; subst hr; exact split_disj hm.le hm.data.ok.lt
    have hpiece : bytesAt s₅.mem (D + BitVec.ofNat 64 j) (n - j) =
        xorKs (ciphOf m₀ (V .s2) R) icb (P + j) (bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)) := by
      have e := bytesAt_writeBytes_self s.mem (D + BitVec.ofNat 64 j)
        (xorBytes s.mem (D + BitVec.ofNat 64 j) (V .s1 + BitVec.ofNat 64 64) (n - j)) (by rw [hxl]; omega_arith)
      rw [hxl] at e
      rw [hm₅, e, xorBytes, hd₃, (ht hc₀).1]
    rw [show n = j + (n - j) by omega_arith]
    exact done_append (hdone.trans (hm.done hc₀)) hpiece
  · refine hm.frame.trans (Frame.trans (h.frame.sub fun r hr => ?_) (fw.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by omega_arith)⟩

/-- The last bytes, with a new keystream block. -/
theorem cryptTail_ok {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid V sp R icb P D n m₀ j s) (hj : n - j < 16)
    (hc : ciphOf s.mem (V .s2) R = ciphOf m₀ (V .s2) R) :
    WP isa cryptTail s (CrOut V sp R icb P D n m₀) := by
  have hn' := h.data.ok.lt
  refine WP.ite (decide (n - j = 0)) (eval_zero h.s5 (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : j = n := by have := h.le; simp at ht; omega_arith
    subst h0
    exact WP.block_nil ⟨h.env, fun hc₀ => h.ctr hc₀, fun hc₀ => h.done hc₀, h.frame⟩
  · have h0 : n - j ≠ 0 := by simpa using hf
    exact WP.seq (WP.mono (tailKs_ok L h hc) fun _ ht => tailXor_ok ht hj h0)

theorem CrMid.ciph {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid V sp R icb P D n m₀ j s) : ciphOf s.mem (V .s2) R = ciphOf m₀ (V .s2) R :=
  ciph_frame h.frame (ctx_crFrame L h.data) h.rounds

omit L in
/-- The rest of the keystream block first, if there is one. -/
theorem cryptFill_ok {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {s : State}
    (h : CrIn V sp R icb P D n s) (h0 : n ≠ 0) :
    WP isa cryptFill s (fun s' => ∃ j, j = (if P % 16 = 0 then 0 else min (16 - P % 16) n) ∧
      CrMid V sp R icb P D n s.mem j s') := by
  refine WP.ite (decide (P % 16 = 0)) (eval_zero h.s6 (by have := Nat.mod_lt P (show 16 > 0 by decide); omega_arith))
    (fun ht => ?_) (fun hf => ?_)
  · have ho : P % 16 = 0 := by simpa using ht
    exact WP.block_nil ⟨0, by simp [ho], h.env, by omega_arith, by rw [h.s4, BitVec.add_zero], by rw [h.s5, Nat.sub_zero],
      h.s3, h.rounds, h.data, fun hc₀ => by simpa using hc₀, fun _ => by simp [bytesAt]; rfl,
      by rw [BitVec.add_zero, Nat.sub_zero], .inr (by omega_arith), Frame.refl _ _⟩
  · have hP : P % 16 ≠ 0 := by simpa using hf
    exact WP.mono (cryptHead_ok h h0 hP) fun _ ⟨j, hj, hm⟩ => ⟨j, by simp only [hP, ite_false]; exact hj, hm⟩

/-- `crypt`. -/
theorem crypt_ok {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {s : State}
    (h : CrIn V sp R icb P D n s) :
    WP isa crypt s (CrOut V sp R icb P D n s.mem) := by
  have hn' := h.data.ok.lt
  refine WP.ite (decide (n = 0)) (eval_zero h.s5 hn') (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨h.env, fun hc₀ => hc₀, fun _ => by simp [bytesAt]; rfl, Frame.refl _ _⟩
  · have h0 : n ≠ 0 := by simpa using hf
    refine WP.seq (WP.mono (cryptFill_ok h h0) fun s' ⟨j, _, hj⟩ => ?_)
    refine WP.seq (WP.mono (cryptWhole_ok L hj (hj.ciph L)) fun s'' ⟨j', _, hj', hlt⟩ => ?_)
    exact cryptTail_ok L hj' hlt (hj'.ciph L)

end

end VG.Proof.AesGcm.RISCV64
