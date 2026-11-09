module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Crypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Flush
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Callee
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Loops
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
public import VerifiedGarbage.Impl.AesGcm.PPC64LE

/-!
# AES-GCM on PPC64LE: `crypt`

Untrusted: everything here is checked by Lean (see `Crypt.lean`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith)
open VG.Proof.Gcm (Ctr xorKs)

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r30) (V .r31))
include L

omit L in
/-- The rest of the keystream block. -/
theorem cryptHead_ok {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {s : State}
    (h : CrIn V sp R icb P D n s) (hn : n ≠ 0) (hP : P % 16 ≠ 0) :
    WP isa cryptHead s (fun s' => ∃ j, j = min (16 - P % 16) n ∧ CrMid V sp R icb P D n s.mem j s') := by
  have hlt : P % 16 < 16 := Nat.mod_lt _ (by decide)
  have hn' := h.data.ok.lt
  have he := h.env
  refine WP.seq (WP.mono (minLen_ok s h.r26 h.r25 (by omega_arith) hn') fun s₁ ⟨h5, hg, hk⟩ => ?_)
  obtain ⟨k, hk'⟩ : ∃ k, min (16 - P % 16) n = k := ⟨_, rfl⟩
  rw [hk'] at h5
  have hk1 : 1 ≤ k := by omega_arith
  have hk16 : P % 16 + k ≤ 16 := by omega_arith
  have hkn : k ≤ n := by omega_arith
  have e30 : s₁.gpr .r30 = V .r30 := (hg _ (by decide) (by decide)).trans he.r30
  have e24 : s₁.gpr .r24 = D := (hg _ (by decide) (by decide)).trans h.r24
  have e25 : s₁.gpr .r25 = BitVec.ofNat 64 n := (hg _ (by decide) (by decide)).trans h.r25
  have e26 : s₁.gpr .r26 = BitVec.ofNat 64 (P % 16) := (hg _ (by decide) (by decide)).trans h.r26
  have h₂ : WP isa (.block [.addi .r3 .r30 64, .add .r3 .r3 .r26, mov .r4 .r24, .add .r24 .r24 .r5,
      .sub .r25 .r25 .r5]) s₁ (fun s₂ : State =>
      s₂.gpr .r3 = V .r30 + BitVec.ofNat 64 (64 + P % 16) ∧ s₂.gpr .r4 = D ∧
      s₂.gpr .r24 = D + BitVec.ofNat 64 k ∧ s₂.gpr .r25 = BitVec.ofNat 64 (n - k) ∧
      s₂.gpr .r5 = BitVec.ofNat 64 k ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r24 → r ≠ .r25 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂) := by
    crun [e30, e24, e25, e26, h5, mov, BitVec.or_self]
    exact ⟨by rw [add_ofNat_assoc], ofNat_sub64 hkn hn', fun r a b c d => by simp [a, b, c, d],
      ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₂ fun s₂ ⟨h3, h4, h24, h25, h5', hg₂, hk₂⟩ => ?_)
  have hk₂' := hk.trans hk₂
  have hdk := h.data.take hkn
  have lp : LoopPre s₂ (V .r30 + BitVec.ofNat 64 (64 + P % 16)) D k := by
    refine ⟨h3, h4, h5', hk1, by omega_arith, ?_, ?_, ?_⟩
    · rw [hk₂'.rd, hk₂'.wr]; exact covers_left (he.perm.stC (by omega_arith))
    · rw [hk₂'.wr]; exact hdk.wr
    · exact (hdk.ok.st.sub_right (Lay.stSub (by omega_arith))).symm
  refine WP.mono (xorLoop_ok s₂ lp) fun s₃ ⟨hm₃, lo⟩ => ?_
  rw [hk₂'.mem] at hm₃
  have hxl := length_xorBytes s.mem D (V .r30 + BitVec.ofNat 64 (64 + P % 16)) k
  have fw : Frame [⟨D, k⟩] s.mem s₃.mem := by rw [hm₃]; exact writeBytes_frame' _ hxl
  have hdisjst : ∀ r ∈ [(⟨D, k⟩ : Region)],
      (⟨V .r30 + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r ∧
      (⟨V .r30 + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(hdk.ok.st.sub_right (Lay.stSub (by decide))).symm, (hdk.ok.st.sub_right (Lay.stSub (by decide))).symm⟩
  have g : ∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r24 → r ≠ .r25 →
      s₃.gpr r = s.gpr r :=
    fun r a b c d e f i => by rw [lo.other r a b c d e, hg₂ r b c f i, hg r d e]
  have he₃ : Env V sp s₃ := he.keep (fun r hr => g r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide)) (lo.keeps.2.2.1.trans hk₂'.sp) (lo.keeps.1.trans hk₂'.rd)
    (lo.keeps.2.1.trans hk₂'.wr)
  refine ⟨k, hk'.symm, he₃, hkn, by rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide), h24],
    by rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide), h25],
    h.r28, h.rounds, h.data.of_eq (lo.keeps.1.trans hk₂'.rd) (lo.keeps.2.1.trans hk₂'.wr), ?_, ?_, ?_, ?_, ?_⟩
  · intro hc₀
    exact (hc₀.head hP hk16).congr (blockAt_frame fw fun r hr => (hdisjst r hr).1)
      (blockAt_frame fw fun r hr => (hdisjst r hr).2)
  · intro hc₀
    have e := bytesAt_writeBytes_self s.mem D (xorBytes s.mem D (V .r30 + BitVec.ofNat 64 (64 + P % 16)) k)
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
/-- The split of the rest into whole blocks for `vg_aes_ctr32` and the last bytes. -/
theorem splitCtr_ok {s : State} {D : Addr} {n j : Nat} (hj : j ≤ n) (hn : n < 2 ^ 64)
    (h24 : s.gpr .r24 = D + BitVec.ofNat 64 j) (h25 : s.gpr .r25 = BitVec.ofNat 64 (n - j)) :
    WP isa (.block splitCtr) s fun s' =>
      s'.gpr .r6 = D + BitVec.ofNat 64 j ∧ s'.gpr .r7 = BitVec.ofNat 64 ((n - j) / 16) ∧
      s'.gpr .r24 = D + BitVec.ofNat 64 (j + 16 * ((n - j) / 16)) ∧
      s'.gpr .r25 = BitVec.ofNat 64 (n - (j + 16 * ((n - j) / 16))) ∧
      s'.gpr .r9 = BitVec.ofNat 64 (16 * ((n - j) / 16)) ∧
      (∀ r, r ≠ .r0 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → r ≠ .r9 → r ≠ .r24 → r ≠ .r25 →
        s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have hand := and15 (BitVec.ofNat 64 (n - j))
  rw [toNat64 (by omega_arith)] at hand
  have hsub : BitVec.ofNat 64 (n - j) - BitVec.ofNat 64 ((n - j) % 16) =
      BitVec.ofNat 64 (16 * ((n - j) / 16)) := by
    rw [ofNat_sub64 (Nat.mod_le _ _) (by omega_arith)]; congr 1; omega_arith
  simp only [splitCtr]
  crun [h24, h25, mov, BitVec.or_self, hand, hsub, shr4 (show n - j < 2 ^ 64 by omega_arith), add_ofNat_assoc]
  refine ⟨by congr 1; omega_arith, fun r a b c d e f g => by simp [a, b, c, d, e, f, g],
    ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

omit L in
/-- The arguments of `vg_aes_ctr32` but the data and their number. -/
theorem ctrArgs_ok {s : State} (he : Env V sp s) {R : Nat} (hR : V .r28 = BitVec.ofNat 64 R) :
    WP isa (.block (ctrArgs 48)) s fun s' =>
      s'.gpr .r3 = V .r29 ∧ s'.gpr .r4 = BitVec.ofNat 64 R ∧ s'.gpr .r5 = V .r30 + BitVec.ofNat 64 48 ∧
      s'.gpr .r8 = V .r31 + BitVec.ofNat 64 512 ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have h28 := he.r28; have h29 := he.r29; have h30 := he.r30; have h31 := he.r31
  simp only [ctrArgs]
  crun [scrO, h28, h29, h30, h31, hR, mov, BitVec.or_self]
  exact ⟨fun r a b c d => by simp [a, b, c, d], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

/-- The arguments of `vg_aes_ctr32` on `nb` whole blocks at `D + j`. -/
theorem ctrWhole_mk {R : Nat} {D : Addr} {j nb : Nat} {s : State} (he : Env V sp s)
    (h3 : s.gpr .r3 = V .r29) (h4 : s.gpr .r4 = BitVec.ofNat 64 R) (h5 : s.gpr .r5 = V .r30 + BitVec.ofNat 64 48)
    (h6 : s.gpr .r6 = D + BitVec.ofNat 64 j) (h7 : s.gpr .r7 = BitVec.ofNat 64 nb)
    (h8 : s.gpr .r8 = V .r31 + BitVec.ofNat 64 512) (hR : R = 10 ∨ R = 12 ∨ R = 14) (hnb : nb < 2 ^ 64)
    (hdj : DataW (V .r29) (V .r30) (V .r31) s (D + BitVec.ofNat 64 j) (16 * nb)) :
    CtrCall s (V .r29) (V .r30 + BitVec.ofNat 64 48) (D + BitVec.ofNat 64 j) (V .r31 + BitVec.ofNat 64 512) R nb := by
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

omit L in
/-- `wholeWith split args call`: `split` leaves the number of whole blocks,
`nb`, in `r7`; with none, nothing more runs, and otherwise `args` and `call`. -/
theorem wholeWith_ok {split args : List Instr} {call : Prog isa} {nb : Nat} {s : State}
    {P Q : State → Prop} (hnb : nb < 2 ^ 64) (hsplit : WP isa (.block split) s P)
    (h7 : ∀ s₁, P s₁ → s₁.gpr .r7 = BitVec.ofNat 64 nb) (hnone : ∀ s₁, P s₁ → nb = 0 → Q s₁)
    (hsome : ∀ s₁, P s₁ → nb ≠ 0 → WP isa (.seq (.block args) call) s₁ Q) :
    WP isa (wholeWith split args call) s Q :=
  WP.seq (WP.mono hsplit fun s₁ hp =>
    WP.ite (decide (nb = 0)) (eval_zero (h7 s₁ hp) hnb) (fun ht => WP.block_nil (hnone s₁ hp (by simpa using ht)))
      fun hf => hsome s₁ hp (by simpa using hf))

/-- Whole blocks. -/
theorem cryptWhole_ok {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid V sp R icb P D n m₀ j s) (hc : ciphOf s.mem (V .r29) R = ciphOf m₀ (V .r29) R) :
    WP isa cryptWhole s (fun s' => ∃ j', j' = j + 16 * ((n - j) / 16) ∧ CrMid V sp R icb P D n m₀ j' s' ∧
      n - j' < 16) := by
  have hn' := h.data.ok.lt
  have he := h.env
  refine wholeWith_ok (nb := (n - j) / 16) (by omega_arith) (splitCtr_ok h.le hn' h.r24 h.r25) (fun _ h => h.2.1)
    (fun s₁ ⟨h6, h7, h24, h25, _, hg₁, hk₁⟩ h0 => ?_) (fun s₁ ⟨h6, h7, h24, h25, _, hg₁, hk₁⟩ h0 => ?_)
  all_goals (
    generalize hnb : (n - j) / 16 = nb at h0 h7 h24 h25 ⊢
    have h16 : 16 * nb ≤ n - j := by omega_arith
    have he₁ : Env V sp s₁ := he.keep (fun r hr => hg₁ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide)) hk₁.sp hk₁.rd hk₁.wr
    have hd₁ := h.data.of_eq hk₁.rd hk₁.wr)
  · subst h0
    exact ⟨j, by omega_arith, ⟨he₁, h.le, by rw [h24]; rfl, by rw [h25]; rfl, h.r28, h.rounds, hd₁,
      fun hc₀ => by rw [hk₁.mem]; exact h.ctr hc₀, fun hc₀ => by rw [hk₁.mem]; exact h.done hc₀,
      by rw [hk₁.mem]; exact h.rest, h.whole, by rw [hk₁.mem]; exact h.frame⟩, by omega_arith⟩
  · have hw : (P + j) % 16 = 0 := h.whole.resolve_left (by omega_arith)
    have hdj := h.data.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith)
    refine WP.seq (WP.mono (ctrArgs_ok he₁ h.r28) fun s₂ ⟨a3, a4, a5, a8, hg₂, hk₂⟩ => ?_)
    have he₂ : Env V sp s₂ := he₁.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr
    have hcall := ctrWhole_mk L he₂ a3 a4 a5 (by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h6])
      (by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h7]) a8 h.rounds (by omega_arith)
      (hdj.of_eq (hk₂.rd.trans hk₁.rd) (hk₂.wr.trans hk₁.wr))
    refine WP.mono (ctr_call hcall) fun s₃ g => ?_
    have gout := g.out; have gctr := g.ctr; have gframe := g.frame
    simp only [hk₂.mem, hk₁.mem] at gout gctr gframe
    have hcw := fun hc₀ => Proof.Gcm.ctr_whole (h.ctr hc₀) hw (m' := s₃.mem)
      (dp := D + BitVec.ofNat 64 j) (nb := nb) (by rw [gout, ← hc]) gctr
    refine ⟨j + 16 * nb, by omega_arith, ⟨he₂.of_saved g.saved g.sp g.rd g.wr, by omega_arith, ?_, ?_, h.r28, h.rounds,
      hd₁.of_eq (g.rd.trans hk₂.rd) (g.wr.trans hk₂.wr), ?_, ?_, ?_, .inr (by omega_arith), ?_⟩, by omega_arith⟩
    · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide), h24]
    · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide), h25]
    · intro hc₀; rw [← Nat.add_assoc]; exact (hcw hc₀).2
    · intro hc₀
      have hj16 : bytesAt s₃.mem (D + BitVec.ofNat 64 j) (16 * nb) =
          xorKs (ciphOf m₀ (V .r29) R) icb (P + j) (bytesAt m₀ (D + BitVec.ofNat 64 j) (16 * nb)) := by
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
    · have hdis : ∀ r ∈ [⟨V .r30 + BitVec.ofNat 64 48, 16⟩, ⟨D + BitVec.ofNat 64 j, 16 * nb⟩,
          ⟨V .r31 + BitVec.ofNat 64 512, 2048⟩],
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

omit L in
/-- The keystream block zeroed and the arguments of `vg_aes_ctr32` on it. -/
theorem tailArgs_ok {s : State} (he : Env V sp s) {R : Nat} (hR : V .r28 = BitVec.ofNat 64 R) :
    WP isa (.block tailArgs) s fun s' =>
      s'.mem = (s.mem.writeW (V .r30 + BitVec.ofNat 64 64) (0 : BitVec 64)).writeW
        (V .r30 + BitVec.ofNat 64 64 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s'.gpr .r3 = V .r29 ∧ s'.gpr .r4 = BitVec.ofNat 64 R ∧ s'.gpr .r5 = V .r30 + BitVec.ofNat 64 48 ∧
      s'.gpr .r6 = V .r30 + BitVec.ofNat 64 64 ∧ s'.gpr .r7 = BitVec.ofNat 64 1 ∧
      s'.gpr .r8 = V .r31 + BitVec.ofNat 64 512 ∧
      (∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → s'.gpr r = s.gpr r) ∧
      Keeps' s s' := by
  have h28 := he.r28; have h29 := he.r29; have h30 := he.r30; have h31 := he.r31
  have w₀ := he.perm.stW (show 64 + 8 ≤ 80 by decide)
  have w₁ := he.perm.stW (show 72 + 8 ≤ 80 by decide)
  simp only [tailArgs, ctrArgs, List.cons_append, List.nil_append]
  crun [scrO, h28, h29, h30, h31, hR, w₀, w₁, mov, BitVec.or_self, write_8]
  exact ⟨by simp only [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.reduceAdd],
    fun r a b c d e f i => by simp [a, b, c, d, e, f, i], ⟨rfl, rfl, rfl, rfl⟩⟩

/-- The arguments of `vg_aes_ctr32` on the keystream block. -/
theorem ctrTail_mk {R : Nat} {s : State} (he : Env V sp s)
    (h3 : s.gpr .r3 = V .r29) (h4 : s.gpr .r4 = BitVec.ofNat 64 R) (h5 : s.gpr .r5 = V .r30 + BitVec.ofNat 64 48)
    (h6 : s.gpr .r6 = V .r30 + BitVec.ofNat 64 64) (h7 : s.gpr .r7 = BitVec.ofNat 64 1)
    (h8 : s.gpr .r8 = V .r31 + BitVec.ofNat 64 512) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    CtrCall s (V .r29) (V .r30 + BitVec.ofNat 64 48) (V .r30 + BitVec.ofNat 64 64)
      (V .r31 + BitVec.ofNat 64 512) R 1 := by
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

/-- Before the last `k` bytes (fewer than 16) of the text, at `S` (`r24`),
which go to `E`: `S` itself in place, or with `to` the address in `r26`,
then `S` or apart from it. If `X` (in `crypt`, the counter's state on
entry), the counter and keystream blocks are those after the text's first
`Q` bytes, under `cph`. -/
structure TailIn (to : Bool) (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (icb : Block) (Q : Nat)
    (S E : Addr) (k : Nat) (cph : Block → Block) (X : Prop) (s : State) : Prop where
  env : Env V sp s
  r24 : s.gpr .r24 = S
  r25 : s.gpr .r25 = BitVec.ofNat 64 k
  r26 : to → s.gpr .r26 = E
  r28 : V .r28 = BitVec.ofNat 64 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  whole : k = 0 ∨ Q % 16 = 0
  src : DataOk (V .r30) (V .r31) s S k
  dst : DataW (V .r29) (V .r30) (V .r31) s E k
  inPlace : to = false → E = S
  alias : E = S ∨ (⟨S, k⟩ : Region).Disjoint ⟨E, k⟩
  ciph : ciphOf s.mem (V .r29) R = cph
  ctr : X → Ctr s.mem (V .r30 + BitVec.ofNat 64 48) (V .r30 + BitVec.ofNat 64 64) cph icb Q

/-- After the last bytes, from `s₀`: the source XORed with the keystream, at `E`. -/
structure TailOut (V : Reg → BitVec 64) (sp : Addr) (icb : Block) (Q : Nat) (S E : Addr) (k : Nat)
    (cph : Block → Block) (X : Prop) (s₀ s : State) : Prop where
  env : Env V sp s
  ctr : X → Ctr s.mem (V .r30 + BitVec.ofNat 64 48) (V .r30 + BitVec.ofNat 64 64) cph icb (Q + k)
  out : X → bytesAt s.mem E k = xorKs cph icb Q (bytesAt s₀.mem S k)
  frame : Frame (crFrame (V .r30) (V .r31) E k) s₀.mem s.mem

/-- The last bytes' keystream block, from `vg_aes_ctr32`. -/
structure TailKs (V : Reg → BitVec 64) (sp : Addr) (S : Addr) (k : Nat) (cph : Block → Block)
    (s₀ s : State) : Prop where
  env : Env V sp s
  r24 : s.gpr .r24 = S
  r25 : s.gpr .r25 = BitVec.ofNat 64 k
  r26 : s.gpr .r26 = s₀.gpr .r26
  ks : blockAt s.mem (V .r30 + BitVec.ofNat 64 64) = cph (blockAt s₀.mem (V .r30 + BitVec.ofNat 64 48))
  cb : blockAt s.mem (V .r30 + BitVec.ofNat 64 48) =
    Spec.Gcm.inc32 (blockAt s₀.mem (V .r30 + BitVec.ofNat 64 48))
  frame : Frame [⟨V .r30 + BitVec.ofNat 64 48, 32⟩, ⟨V .r31 + BitVec.ofNat 64 512, 2048⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The new keystream block. -/
theorem tailKs_ok {to : Bool} {R : Nat} {icb : Block} {Q : Nat} {S E : Addr} {k : Nat} {cph : Block → Block}
    {X : Prop} {s : State} (h : TailIn to V sp R icb Q S E k cph X s) :
    WP isa (.seq (.block tailArgs) ctrCall) s (TailKs V sp S k cph s) := by
  have he := h.env
  refine WP.seq (WP.mono (tailArgs_ok he h.r28) fun s₂ ⟨hm₂, a3, a4, a5, a6, a7, a8, hg₂, hk₂⟩ => ?_)
  have he₂ : Env V sp s₂ := he.keep (fun r hr => hg₂ r (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide)) hk₂.sp hk₂.rd hk₂.wr
  have fz : Frame [⟨V .r30 + BitVec.ofNat 64 64, 16⟩] s.mem s₂.mem := by
    rw [hm₂]; exact Proof.Cmac.frame_store2 _ _ _
  have hKS0 : blockAt s₂.mem (V .r30 + BitVec.ofNat 64 64) = 0 := by
    rw [hm₂, blockAt, zeroT_bytes]; decide
  have hCB : blockAt s₂.mem (V .r30 + BitVec.ofNat 64 48) = blockAt s.mem (V .r30 + BitVec.ofNat 64 48) :=
    blockAt_frame fz fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
  have hc₂ : ciphOf s₂.mem (V .r29) R = cph := by
    rw [ciph_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cs.sub_right (Lay.stSub (by decide))) h.rounds, h.ciph]
  refine WP.mono (ctr_call (ctrTail_mk L he₂ a3 a4 a5 a6 a7 a8 h.rounds)) fun s₃ g => ?_
  have gout := g.out; have gctr := g.ctr; have gframe := g.frame
  rw [blocksAt_one, blocksAt_one, hKS0, Proof.Cmac.ctr32_one, List.cons.injEq] at gout
  refine ⟨he₂.of_saved g.saved g.sp g.rd g.wr, ?_, ?_, ?_, ?_, ?_, ?_, by rw [g.rd, hk₂.rd], by rw [g.wr, hk₂.wr]⟩
  · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r24]
  · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r25]
  · rw [g.saved _ (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
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
/-- The last bytes XORed with the new keystream block, into `E`. -/
theorem tailXor_ok {to : Bool} {R : Nat} {icb : Block} {Q : Nat} {S E : Addr} {k : Nat} {cph : Block → Block}
    {X : Prop} {s₀ s : State} (h : TailIn to V sp R icb Q S E k cph X s₀) (hk : TailKs V sp S k cph s₀ s)
    (hlt : k < 16) (h0 : k ≠ 0) :
    WP isa (.seq (.block (xorArgs to)) (xorLoopWith to)) s (TailOut V sp icb Q S E k cph X s₀) := by
  have hw : Q % 16 = 0 := h.whole.resolve_left h0
  have he₃ := hk.env
  have h30 := he₃.r30
  have h₄ : WP isa (.block (xorArgs to)) s fun s₄ =>
      s₄.gpr .r3 = V .r30 + BitVec.ofNat 64 64 ∧ s₄.gpr .r4 = S ∧ s₄.gpr .r5 = BitVec.ofNat 64 k ∧
      (to → s₄.gpr .r7 = E) ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → (to → r ≠ .r7) → s₄.gpr r = s.gpr r) ∧ Keeps s s₄ := by
    cases to
    · simp only [xorArgs, Bool.false_eq_true, ite_false, List.append_nil]
      crun [h30, hk.r24, hk.r25, mov, BitVec.or_self]
      exact ⟨False.elim, fun r a b d _ => by simp [a, b, d], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    · have h26 : s.gpr .r26 = E := hk.r26.trans (h.r26 rfl)
      simp only [xorArgs, ite_true, List.cons_append, List.nil_append]
      crun [h30, hk.r24, hk.r25, h26, mov, BitVec.or_self]
      exact ⟨fun r a b d e => by simp [a, b, d, e], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₄ fun s₄ ⟨h3, h4, h5, h7, hg₄, hk₄⟩ => ?_)
  have dst := h.dst.ok.st; have dw := h.dst.ok.w
  have xp : XorPre to s₄ (V .r30 + BitVec.ofNat 64 64) S E k := by
    refine ⟨h3, h4, h7, h5, by omega, by omega, ?_, ?_, ?_, ?_, h.inPlace, h.alias⟩
    · rw [hk₄.rd, hk₄.wr]; exact covers_left (he₃.perm.stC (by omega))
    · rw [hk₄.rd, hk₄.wr, hk.rd, hk.wr]; exact h.src.rd
    · rw [hk₄.wr, hk.wr]; exact h.dst.wr
    · exact (dst.sub_right (Lay.stSub (by omega))).symm
  refine WP.mono (xorLoopWith_ok to s₄ xp) fun s₅ o => ?_
  have hm₅ := o.mem
  rw [hk₄.mem] at hm₅
  have hxl := length_xorBytes s.mem S (V .r30 + BitVec.ofNat 64 64) k
  have fw : Frame [⟨E, k⟩] s.mem s₅.mem := by
    rw [hm₅]; exact writeBytes_frame' _ hxl
  have hd₃ : bytesAt s.mem S k = bytesAt s₀.mem S k := by
    refine bytesAt_frame hk.frame (fun r hr => ?_) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.src.st.sub_right (Lay.stSub (by decide))
    · exact h.src.w.sub_right (Lay.wSub (by decide))
  have ht := fun x => Proof.Gcm.ctr_tail (h.ctr x) hw (m₁ := s.mem) hk.ks (by rw [hk.cb])
    (d := bytesAt s₀.mem S k) (by rw [length_bytesAt]; omega) (by rw [length_bytesAt]; omega)
  rw [length_bytesAt] at ht
  have dS : ∀ r ∈ [(⟨E, k⟩ : Region)], ∀ x, x + 16 ≤ 80 →
      (⟨V .r30 + BitVec.ofNat 64 x, 16⟩ : Region).Disjoint r := by
    intro r hr x hx; simp only [List.mem_singleton] at hr; subst hr
    exact (dst.sub_right (Lay.stSub hx)).symm
  have g : ∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s₅.gpr r = s.gpr r :=
    fun r a b c d e f => by rw [o.other r a b c d e (fun _ => f), hg₄ r b c d (fun _ => f)]
  refine ⟨he₃.keep (fun r hr => g r (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide) (by revert r; decide))
      (o.keeps.2.2.1.trans hk₄.sp) (o.keeps.1.trans hk₄.rd) (o.keeps.2.1.trans hk₄.wr), ?_, ?_, ?_⟩
  · intro x
    exact (ht x).2.congr (blockAt_frame fw fun r hr => dS r hr 48 (by decide))
      (blockAt_frame fw fun r hr => dS r hr 64 (by decide))
  · intro x
    have e := bytesAt_writeBytes_self s.mem E (xorBytes s.mem S (V .r30 + BitVec.ofNat 64 64) k)
      (by rw [hxl]; exact h.dst.ok.lt)
    rw [hxl] at e
    rw [hm₅, e, xorBytes, hd₃, (ht x).1]
  · refine (hk.frame.sub fun r hr => ?_).trans (fw.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., fun _ h => h⟩

/-- The last bytes, with a new keystream block, in place or to a destination. -/
theorem cryptTailWith_ok {to : Bool} {R : Nat} {icb : Block} {Q : Nat} {S E : Addr} {k : Nat}
    {cph : Block → Block} {X : Prop} {s : State} (h : TailIn to V sp R icb Q S E k cph X s) (hlt : k < 16) :
    WP isa (cryptTailWith to) s (TailOut V sp icb Q S E k cph X s) := by
  refine WP.ite (decide (k = 0)) (eval_zero h.r25 h.src.lt) (fun ht => ?_) (fun hf => ?_)
  · have h0 : k = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨h.env, h.ctr, fun _ => by simp [bytesAt, Proof.Gcm.xorKs_nil], Frame.refl _ _⟩
  · have h0 : k ≠ 0 := by simpa using hf
    exact WP.seq (WP.mono (tailKs_ok L h) fun _ hk => tailXor_ok h hk hlt h0)

omit L in
/-- `crypt`'s last bytes, in place, from `CrMid`. -/
theorem CrMid.tailIn {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid V sp R icb P D n m₀ j s) (hc : ciphOf s.mem (V .r29) R = ciphOf m₀ (V .r29) R) :
    TailIn false V sp R icb (P + j) (D + BitVec.ofNat 64 j) (D + BitVec.ofNat 64 j) (n - j) (ciphOf m₀ (V .r29) R)
      (Ctr m₀ (V .r30 + BitVec.ofNat 64 48) (V .r30 + BitVec.ofNat 64 64) (ciphOf m₀ (V .r29) R) icb P) s := by
  have hn' := h.data.ok.lt
  have hle := h.le
  have hdj := h.data.drop hle
  exact ⟨h.env, h.r24, h.r25, (fun h => nomatch h), h.r28, h.rounds, h.whole, hdj.ok, hdj, fun _ => rfl,
    .inl rfl, hc, h.ctr⟩

omit L in
/-- What `crypt`'s last bytes leave, in place: `CrOut`. -/
theorem CrMid.crOut {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s s' : State}
    (h : CrMid V sp R icb P D n m₀ j s)
    (o : TailOut V sp icb (P + j) (D + BitVec.ofNat 64 j) (D + BitVec.ofNat 64 j) (n - j) (ciphOf m₀ (V .r29) R)
      (Ctr m₀ (V .r30 + BitVec.ofNat 64 48) (V .r30 + BitVec.ofNat 64 64) (ciphOf m₀ (V .r29) R) icb P) s s') :
    CrOut V sp R icb P D n m₀ s' := by
  have hn' := h.data.ok.lt
  have hle := h.le
  refine ⟨o.env, fun x => ?_, fun x => ?_, ?_⟩
  · rw [show P + n = P + j + (n - j) by omega_arith]; exact o.ctr x
  · have hdt := (h.data.take h.le).ok
    have hdone : bytesAt s'.mem D j = bytesAt s.mem D j := by
      refine bytesAt_frame o.frame (fun r hr => ?_) (by omega_arith)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact split_disj hle hn'
      · exact hdt.st.sub_right (Lay.stSub (by decide))
      · exact hdt.w.sub_right (Lay.wSub (by decide))
    rw [show n = j + (n - j) by omega_arith]
    exact done_append (hdone.trans (h.done x)) (by rw [o.out x, h.rest])
  · refine h.frame.trans (o.frame.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by omega_arith)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩

/-- The last bytes, with a new keystream block, in place. -/
theorem cryptTail_ok {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid V sp R icb P D n m₀ j s) (hj : n - j < 16)
    (hc : ciphOf s.mem (V .r29) R = ciphOf m₀ (V .r29) R) :
    WP isa cryptTail s (CrOut V sp R icb P D n m₀) :=
  WP.mono (cryptTailWith_ok L (h.tailIn hc) hj) fun _ o => h.crOut o

theorem CrMid.ciph {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid V sp R icb P D n m₀ j s) : ciphOf s.mem (V .r29) R = ciphOf m₀ (V .r29) R :=
  ciph_frame h.frame (ctx_crFrame L h.data) h.rounds

omit L in
/-- The rest of the keystream block first, if there is one. -/
theorem cryptFill_ok {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {s : State}
    (h : CrIn V sp R icb P D n s) (h0 : n ≠ 0) :
    WP isa cryptFill s (fun s' => ∃ j, j = (if P % 16 = 0 then 0 else min (16 - P % 16) n) ∧
      CrMid V sp R icb P D n s.mem j s') := by
  refine WP.ite (decide (P % 16 = 0)) (eval_zero h.r26 (by have := Nat.mod_lt P (show 16 > 0 by decide); omega_arith))
    (fun ht => ?_) (fun hf => ?_)
  · have ho : P % 16 = 0 := by simpa using ht
    exact WP.block_nil ⟨0, by simp [ho], h.env, by omega_arith, by rw [h.r24, BitVec.add_zero], by rw [h.r25, Nat.sub_zero],
      h.r28, h.rounds, h.data, fun hc₀ => by simpa using hc₀, fun _ => by simp [bytesAt]; rfl,
      by rw [BitVec.add_zero, Nat.sub_zero], .inr (by omega_arith), Frame.refl _ _⟩
  · have hP : P % 16 ≠ 0 := by simpa using hf
    exact WP.mono (cryptHead_ok h h0 hP) fun _ ⟨j, hj, hm⟩ => ⟨j, by simp only [hP, ite_false]; exact hj, hm⟩

/-- `crypt`. -/
theorem crypt_ok {R : Nat} {icb : Block} {P : Nat} {D : Addr} {n : Nat} {s : State}
    (h : CrIn V sp R icb P D n s) :
    WP isa crypt s (CrOut V sp R icb P D n s.mem) := by
  have hn' := h.data.ok.lt
  refine WP.ite (decide (n = 0)) (eval_zero h.r25 hn') (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨h.env, fun hc₀ => hc₀, fun _ => by simp [bytesAt]; rfl, Frame.refl _ _⟩
  · have h0 : n ≠ 0 := by simpa using hf
    refine WP.seq (WP.mono (cryptFill_ok h h0) fun s' ⟨j, _, hj⟩ => ?_)
    refine WP.seq (WP.mono (cryptWhole_ok L hj (hj.ciph L)) fun s'' ⟨j', _, hj', hlt⟩ => ?_)
    exact cryptTail_ok L hj' hlt (hj'.ciph L)

end

end VG.Proof.AesGcm.PPC64LE
