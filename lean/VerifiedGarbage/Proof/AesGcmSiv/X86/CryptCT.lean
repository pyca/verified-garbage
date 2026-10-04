import VerifiedGarbage.Proof.AesGcmSiv.X86.PolyvalCT

/-!
# AES-GCM-SIV on x86: the tag and counter mode are constant time

Untrusted: everything here is checked by Lean. `tag o` calls `vg_aes_ctr32`
on public pointers (`tag_ct`); counter mode encrypts block after block of
the data, through the pointer in `esi`, as many as its public length says
(`crypt_ct`), and XORs the last bytes in a loop from public pointers and
counts (`cryptTail_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4 xorLoop)
open VG.Proof.AesGcm.X86 (CT w64 slotv slotv_eq GcmImpl xorLoop_ct XorPre xorLoop_ok covers_off covers_left)

theorem tag_ct (v : GcmImpl) {p : Prm} (L : Lay p) {o : Nat} (ho : TagO o) : CT (Env p) (tag v.callees o) := by
  have hc : CT (Env p) (.block (copy16 cbO ccO ++ zero4 o ++ ctrArgs o)) := by
    rcases ho with rfl | rfl | rfl <;> exact CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide)
  refine CT.seq (J := fun t₁ => ∃ t, TagCall p o t t₁) hc
    (fun t E => by obtain ⟨t₁, run₁, C⟩ := tagArgs_ok L E ho; exact WP.of_runBlock ⟨t₁, run₁, t, C⟩)
    (callCtr_ct v L fun t₁ ⟨_, C⟩ => ⟨C.env, keyS L C.env.perm, C.dst, C.eax, C.ecx, C.edx, C.ebx, C.edi⟩)

/-! ## A block -/

/-- What a block's call starts from. -/
structure BlkCall (p : Prm) (j : Nat) (t₁ : State) : Prop where
  env : Env p t₁
  dst : Dst p t₁ (p.W + BitVec.ofNat 32 512) (p.D + BitVec.ofNat 32 (16 * j)) (16 * 1)
  eax : t₁.gpr .eax = p.W + BitVec.ofNat 32 512
  ecx : t₁.gpr .ecx = BitVec.ofNat 32 p.R
  edx : t₁.gpr .edx = p.W + BitVec.ofNat 32 112
  ebx : t₁.gpr .ebx = p.D + BitVec.ofNat 32 (16 * j)
  edi : t₁.gpr .edi = BitVec.ofNat 32 1
  esi : t₁.gpr .esi = p.D + BitVec.ofNat 32 (16 * j)

theorem blkCall_of {p : Prm} (L : Lay p) {t : State} (E : Env p t) {j : Nat} (hj : 16 * (j + 1) ≤ p.n)
    (hsi : t.gpr .esi = p.D + BitVec.ofNat 32 (16 * j)) :
    ∃ t₁, runBlock isa blockArgs t = some t₁ ∧ BlkCall p j t₁ := by
  have hw := L.ww
  have hn' := L.n32
  have hdw := L.dw
  obtain ⟨t₁, run₁, hm₁, eax, ecx, edx, ebx, edi, bp₁, sp₁, si₁, rd₁, wr₁⟩ := blkArgs_ok L E hsi
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩] t.mem t₁.mem := by rw [hm₁]; exact copyMem_frame _ _
  have E₁ : Env p t₁ := E.mut L bp₁ sp₁ rd₁ wr₁ (frame_toMut f₁ fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact inMut_w p (.inl (by decide)))
  have eQ : w64 (p.D + BitVec.ofNat 32 (16 * j)) = w64 p.D + BitVec.ofNat 64 (16 * j) := L.dA (by omega)
  have dQ : (⟨w64 p.D + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint ⟨w64 p.W, 4096⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega))
  have hD : Dst p t₁ (p.W + BitVec.ofNat 32 512) (p.D + BitVec.ofNat 32 (16 * j)) (16 * 1) := by
    refine ⟨?_, by rw [L.dN (by omega)]; omega, ?_, ?_, ?_, ?_⟩ <;> rw [eQ]
    · exact covers_off E₁.perm.d (by omega) (by omega)
    · rw [L.aW (by decide)]; exact (dQ.sub_right (Lay.wSub (show 512 + 240 ≤ 4096 by decide))).symm
    · exact dQ.sub_right (Lay.wSub (by decide))
    · exact dQ.sub_right (Lay.wSub (by decide))
    · exact L.bd.sub_right (Offset.sub_base _ (by omega))
  exact ⟨t₁, run₁, E₁, hD, eax, ecx, edx, ebx, edi, by rw [si₁, hsi]⟩

theorem cryptBlock_ct (v : GcmImpl) {p : Prm} (L : Lay p) {j : Nat} (hj : 16 * (j + 1) ≤ p.n) :
    CT (fun s => Env p s ∧ s.gpr .esi = p.D + BitVec.ofNat 32 (16 * j)) (cryptBlock v.callees) := by
  have hdw := L.dw
  refine CT.seq (J := BlkCall p j)
    (CT.taint [.ebp, .esi] (pin2 fun _ h => ⟨h.1.ebp, h.2⟩) (by taint_decide))
    (fun t ⟨E, si⟩ => by obtain ⟨t₁, run₁, C⟩ := blkCall_of L E hj si; exact WP.of_runBlock ⟨t₁, run₁, C⟩) ?_
  refine CT.seq (J := fun s => s.gpr .ebp = p.W ∧ s.gpr .esi = p.D + BitVec.ofNat 32 (16 * j))
    (callCtr_ct v L fun t₁ C => ⟨C.env, keyS L C.env.perm, C.dst, C.eax, C.ecx, C.edx, C.ebx, C.edi⟩)
    (fun t₁ C => WP.mono (callCtr_ok v L C.env (keyS L C.env.perm) C.dst
      (by rw [L.dA (by omega)]; exact ⟨⟨w64 p.D, p.n⟩, by simp, Offset.sub_base _ (by omega)⟩) C.eax C.ecx C.edx
      C.ebx C.edi) fun s P => ⟨P.env.ebp, by rw [P.saved _ (by decide), C.esi]⟩)
    (CT.taint [.ebp, .esi] (pin2 fun _ h => h) (by taint_decide))

/-- The whole blocks of the data, from `t`. -/
def BlocksI (p : Prm) (j : Nat) (s : State) : Prop :=
  ∃ t ciph icb x, x.length = p.n ∧ Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R = ciph ∧
    BlocksPost p ciph icb x j t s

theorem blocks_ct (v : GcmImpl) {p : Prm} (L : Lay p) (hb1 : 1 ≤ p.n / 16) :
    CT (BlocksI p 0) (.loop (cryptBlock v.callees) .ne) := by
  refine (CT.loopN (fun k s => ∃ j, k = p.n / 16 - j ∧ j < p.n / 16 ∧ BlocksI p j s) (fun k => ?_)
    (fun k s ⟨j, hk, hj, t, ciph, icb, x, hxl, hc, P⟩ => ?_) (p.n / 16)).mono
    fun s h => ⟨0, by omega, by omega, h⟩
  · by_cases hkk : 0 < k ∧ k ≤ p.n / 16
    · exact (cryptBlock_ct v L (j := p.n / 16 - k) (by omega)).mono fun s ⟨j, hk', hj, _, _, _, _, _, _, P⟩ => by
        rw [show p.n / 16 - k = j by omega]; exact ⟨P.env, P.esi⟩
    · exact CT.of_empty fun s ⟨j, hk', hj, _⟩ => hkk ⟨by omega, by omega⟩
  · have hc' : Spec.GcmSiv.ctxCiph s.mem (w64 p.W + BitVec.ofNat 64 512) p.R = ciph := by
      rw [ciph_cryR L P.frame, hc]
    refine WP.mono (cryptBlock_ok v L P.env hxl (j := j) (by omega) P.esi P.n P.ctr P.data hc') fun t'' Q => ?_
    refine ⟨by omega, by rw [eval_ne Q.z]; simp; omega, fun hk1 => ⟨j + 1, by omega, by omega, t, ciph, icb, x, hxl, hc,
      ⟨Q.env, Q.rd.trans P.rd, Q.wr.trans P.wr, Q.esi, Q.n, Q.ctr, Q.data, P.frame.trans Q.frame⟩⟩⟩

/-! ## The last bytes -/

theorem cryptTail_ct (v : GcmImpl) {p : Prm} (L : Lay p) {b r : Nat} (hn : p.n = 16 * b + r) (hr1 : 1 ≤ r)
    (hr : r < 16) :
    CT (fun s => Env p s ∧ s.gpr .esi = p.D + BitVec.ofNat 32 (16 * b) ∧ slotv s.mem p.W nO = BitVec.ofNat 32 r)
      (cryptTail v.callees) := by
  have hn' := L.n32
  have hdw := L.dw
  have hw := L.ww
  refine CT.seq (J := fun s => Env p s ∧ s.gpr .esi = p.D + BitVec.ofNat 32 (16 * b) ∧
      slotv s.mem p.W nO = BitVec.ofNat 32 r) ((tag_ct v L (o := 224) (by decide)).mono fun _ h => h.1)
    (fun t ⟨E, si, n⟩ => WP.mono (tag_ok v L E (o := 224) (by decide)) fun t₂ T => ⟨T.env, by rw [T.esi, si], ?_⟩) ?_
  · rw [← n]
    exact T.frame.readW (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm) (by decide)
  refine CT.seq (J := fun s => XorPre s (p.W + BitVec.ofNat 32 224) (p.D + BitVec.ofNat 32 (16 * b)) r)
    (CT.taint [.ebp, .esi] (pin2 fun _ h => ⟨h.1.ebp, h.2.1⟩) (by taint_decide)) (fun t₂ ⟨E, si, n⟩ => ?_)
    (xorLoop_ct (pin3 fun _ h => ⟨h.edi, h.edx, h.ecx⟩))
  simp only [slotv_eq, nO] at n
  obtain ⟨t₃, run₃, dx₃, di₃, cx₃, m₃, rd₃, wr₃⟩ : ∃ t₃ : State, runBlock isa
      [.mov .edx (.reg .ebp), .alu .add .edx (imm bO), .mov .edi (.reg .esi), .mov .ecx (slot nO)] t₂ = some t₃ ∧
      t₃.gpr .edx = p.W + BitVec.ofNat 32 224 ∧ t₃.gpr .edi = p.D + BitVec.ofNat 32 (16 * b) ∧
      t₃.gpr .ecx = BitVec.ofNat 32 r ∧ t₃.mem = t₂.mem ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr :=
    ⟨_, by grun [E.ebp, L.aW, E.perm.wR, n], by gregs [E.ebp], by gregs [si], by gregs [n], by gmems [], by gmems [],
      by gmems []⟩
  have eD := L.dA (j := 16 * b) (by omega)
  have dQ : (⟨w64 p.D + BitVec.ofNat 64 (16 * b), r⟩ : Region).Disjoint ⟨w64 p.W, 4096⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega))
  refine WP.of_runBlock ⟨t₃, run₃, dx₃, di₃, cx₃, by omega, by omega, by rw [L.nW (by decide)]; omega,
    by rw [L.dN (by omega)]; omega, ?_, ?_, ?_⟩
  · rw [rd₃, wr₃, L.aW (by decide)]
    exact covers_prefix (E.perm.wCR (show 224 + 16 ≤ 4096 by decide)) (by omega)
  · rw [wr₃, eD]; exact covers_off E.perm.d (by omega) (by omega)
  · rw [eD, L.aW (by decide)]
    exact ((dQ.sub_right (Lay.wSub (show 224 + 16 ≤ 4096 by decide))).sub_right (Region.sub_prefix (by omega))).symm

/-! ## `crypt` -/

theorem crypt_ct (v : GcmImpl) {p : Prm} (L : Lay p) : CT (Env p) (crypt v.callees) := by
  have hn := L.n32
  refine CT.seq (J := fun s => ∃ t, CStart p t s) (CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide))
    (fun t E => by obtain ⟨t₁, run₁, S⟩ := cryptStart_ok L E; exact WP.of_runBlock ⟨t₁, run₁, t, S⟩) ?_
  refine CT.seq (J := fun s => Env p s ∧ s.gpr .esi = p.D + BitVec.ofNat 32 (16 * (p.n / 16)) ∧
      slotv s.mem p.W nO = BitVec.ofNat 32 (p.n % 16))
    (CT.ite (decide (p.n / 16 = 0)) (fun s ⟨_, S⟩ => eval_e S.z) (fun _ => CT.nil) fun hf => ?_)
    (fun t₁ ⟨t, S⟩ => ?_) ?_
  · have h0 : p.n / 16 ≠ 0 := of_decide_eq_false hf
    refine (blocks_ct v L (by omega)).mono fun s ⟨t, S⟩ => ⟨s, _, _, bytesAt s.mem (w64 p.D) p.n,
      Proof.Cmac.bytesAt_length _ _ _, rfl, ⟨S.env, rfl, rfl, by rw [S.esi, Nat.mul_zero, BitVec.add_zero],
        by rw [S.n, Nat.mul_zero, Nat.sub_zero], S.ctr, by rw [Nat.mul_zero, GcmSiv.ctrPart_zero], Frame.refl _ _⟩⟩
  · have hxl : (bytesAt t₁.mem (w64 p.D) p.n).length = p.n := Proof.Cmac.bytesAt_length _ _ _
    refine WP.mono (Q := BlocksPost p (Spec.GcmSiv.ctxCiph t₁.mem (w64 p.W + BitVec.ofNat 64 512) p.R)
        (Spec.GcmSiv.initialCounter (bytesAt t.mem (w64 p.W) 16)) (bytesAt t₁.mem (w64 p.D) p.n) (p.n / 16) t₁)
      ?_ fun t₂ B => ⟨B.env, B.esi, by rw [B.n]; congr 1; omega⟩
    refine WP.ite (decide (p.n / 16 = 0)) (eval_e S.z) (fun ht => ?_) (fun hf => ?_)
    · have h0 : p.n / 16 = 0 := by simpa using ht
      refine WP.block_nil ?_
      rw [h0]
      exact ⟨S.env, rfl, rfl, by rw [S.esi, Nat.mul_zero, BitVec.add_zero], by rw [S.n, Nat.mul_zero, Nat.sub_zero],
        S.ctr, by rw [Nat.mul_zero, GcmSiv.ctrPart_zero], Frame.refl _ _⟩
    · have h0 : p.n / 16 ≠ 0 := by simpa using hf
      exact blocks_ok v L S.env hxl (by omega) S.esi S.n S.ctr rfl rfl
  refine CT.seq (J := fun s => (Env p s ∧ s.gpr .esi = p.D + BitVec.ofNat 32 (16 * (p.n / 16)) ∧
      slotv s.mem p.W nO = BitVec.ofNat 32 (p.n % 16)) ∧ s.zf = some (decide (p.n % 16 = 0)))
    (CT.taint [.ebp] (pin_ebp fun _ h => h.1.ebp) (by taint_decide)) (fun s ⟨E, si, n⟩ => ?_) ?_
  · obtain ⟨s₁, run₁, z₁, E₁, si₁, m₁, -, -⟩ := anyLeft_ok L E (by omega) n
    exact WP.of_runBlock ⟨s₁, run₁, ⟨E₁, by rw [si₁, si], by rw [slotv_eq, m₁]; exact n⟩, z₁⟩
  refine CT.ite (decide (p.n % 16 = 0)) (fun s h => eval_e h.2) (fun _ => CT.nil) fun hf => ?_
  have h0 : p.n % 16 ≠ 0 := of_decide_eq_false hf
  exact (cryptTail_ct v L (b := p.n / 16) (r := p.n % 16) (by omega) (by omega) (by omega)).mono
    fun s ⟨h, _⟩ => h

end VG.Proof.AesGcmSiv.X86
