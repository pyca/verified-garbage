import VerifiedGarbage.Proof.Ed448.Arm.ScalarNat
import VerifiedGarbage.Proof.X448.Arm.RowPass
import VerifiedGarbage.Proof.X25519.Arm.Field
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# Ed448 scalar arithmetic on ARMv7: one chunk

`fold o` computes the limbs of `l + h c` into `TF` from the remainder at `o`
and the chunk in `r11` (`fold_ok`); `reduceT o` the remainder of `TF`
modulo `L` into `o` (`reduceT_ok`); together, `step o` folds a chunk into
the remainder (`step_ok`). The working space is `r0`'s 8192 bytes
(`CtxN 4096`), with the limb mask in `r6`.
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X25519.Arm
open VG.Proof.X448.Arm (carryPass_ok CarryInv)
open VG.Spec.Ed448 (L)

/-- The working space at `b`, 8192 bytes. -/
abbrev Ctx8 := CtxN 4096

/-- Every limb of the 28-limb number at `o` is below `2¹⁶`. -/
def Lim28 (m : Mem) (B : Addr) (o : Nat) : Prop := ∀ k < 28, limb m B o k < 65536

/-- The 28-limb number at `o`. -/
def V28 (m : Mem) (B : Addr) (o : Nat) : Nat := val16 (limb m B o) 28

/-- A remainder's place: after `TF`, with offsets below 4096. -/
def Buf (o : Nat) : Prop := TF + 112 ≤ o ∧ o + 112 ≤ 4096

theorem TF_eq : TF = 64 := rfl

/-- The region of the 28 limbs at `o`. -/
abbrev limbsR (b : BitVec 32) (o : Nat) : Region := ⟨State.addr b + BitVec.ofNat 64 o, 112⟩

/-- The limbs at `o` across a frame of regions of the working space that do not
overlap them. -/
theorem limb_frame28 {b : BitVec 32} {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {o : Nat}
    (hd : ∀ r ∈ rs, ∀ k < 28, (⟨State.addr b + BitVec.ofNat 64 (o + 4 * k), 4⟩ : Region).Disjoint r) :
    ∀ k < 28, limb m' (State.addr b) o k = limb m (State.addr b) o k :=
  fun k hk => wd_frame hf fun r hr => hd r hr k hk

section
variable {b : BitVec 32}

/-! ## Folding a chunk in -/

theorem foldHead_ok {o : Nat} (ho : Buf o) {s : State} (hc : Ctx8 b s)
    (h27 : limb s.mem (State.addr b) o 27 < 16384) (h26 : limb s.mem (State.addr b) o 26 < 65536) :
    WP isa (.block (foldHead o)) s fun t =>
      (t.gpr .r1).toNat = foldH (limb s.mem (State.addr b) o) ∧ (t.gpr .r5).toNat = 0 ∧
      Rest [.r1, .r2, .r5] s t ∧ t.mem = s.mem := by
  obtain ⟨_, ho2⟩ := ho
  unfold foldHead
  refine ldr0_ok hc (d := o + 104) (by omega) fun s1 u1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  have hc2 := hc.of_rest ((u1.rest (ws := [.r1, .r2, .r5]) (by decide)).trans (u2.rest (by decide)))
    (by decide)
  refine ldr0_ok hc2 (d := o + 108) (by omega) fun s3 u3 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s4 u4 => wp_mov (op2_imm (by decide)) fun s5 u5 => ?_
  refine WP.block_nil ⟨?_, by rw [u5.gpr]; rfl, ?_, by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]⟩
  · have e1 : (s3.gpr .r1).toNat = limb s.mem (State.addr b) o 26 / 16384 := by
      rw [u3.other _ (by decide), u2.gpr, toNat_shr, u1.gpr]; rfl
    have e2 : (s3.gpr .r2).toNat = limb s.mem (State.addr b) o 27 := by
      rw [u3.gpr, u2.mem, u1.mem]; rfl
    rw [u5.other _ (by decide), u4.gpr]
    show (s3.gpr .r1 + s3.gpr .r2 <<< 2).toNat = _
    have e3 : (s3.gpr .r2 <<< 2).toNat = 4 * limb s.mem (State.addr b) o 27 := by
      rw [toNat_shl, e2, Nat.mod_eq_of_lt (by omega)]; omega
    rw [toNat_add_lt (by rw [e1, e3]; omega), e1, e3]
    rfl
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide)))))

theorem toNat_movw {v : Nat} (h : v < 65536) : ((BitVec.ofNat 16 v).setWidth 32).toNat = v := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]

/-- `(x << 18) >> 18` keeps the low 14 bits. -/
theorem toNat_mask14 (x : BitVec 32) : ((x <<< 18) >>> 18).toNat = x.toNat % 16384 := by
  rw [toNat_shr, toNat_shl, show (2 : Nat) ^ 32 = 16384 * 2 ^ 18 from rfl, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (by decide)]

/-- One source of `fold`: limb `k` of `l + h c` before carrying. -/
theorem foldSrc_ok {o : Nat} (ho : Buf o) {s0 : State} {w : Nat}
    (hh : foldH (limb s0.mem (State.addr b) o) < 65536)
    (hsum : ∀ k < 28, foldC (limb s0.mem (State.addr b) o) w k + 65536 ≤ 2 ^ 32)
    {k : Nat} (hk : k < 28) {s : State} (hc : Ctx8 b s)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 TF, 4 * k⟩] s0.mem s.mem)
    (h1 : (s.gpr .r1).toNat = foldH (limb s0.mem (State.addr b) o)) (h11 : (s.gpr .r11).toNat = w) :
    WP isa (.block (foldSrc o k)) s fun s' =>
      (s'.gpr .r3).toNat = foldC (limb s0.mem (State.addr b) o) w k ∧ Rest [.r2, .r3, .r4] s s' ∧
        s'.mem = s.mem := by
  obtain ⟨ho1, ho2⟩ := ho
  have hT := TF_eq
  generalize hr : limb s0.mem (State.addr b) o = r at hh hsum h1
  unfold foldC at hsum ⊢
  generalize foldH r = hv at hh h1 hsum ⊢
  have lr : ∀ j < 28, wd s.mem (State.addr b) (o + 4 * j) = r j := fun j hj => by
    rw [← hr]
    exact wd_frame hf fun z hz => by
      rw [List.mem_singleton.mp hz]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  have hs := hsum k hk
  unfold foldSrc
  by_cases k0 : k = 0
  · subst k0
    rw [ite_eq_left rfl]
    refine wp_movw fun s1 u1 => wp_mul fun s2 u2 => wp_dp (op2_reg _ _) fun s3 u3 => WP.block_nil ?_
    refine ⟨?_, (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide))),
      by rw [u3.mem, u2.mem, u1.mem]⟩
    have hc0 := cLimb_lt 0
    have e2 : (s2.gpr .r2).toNat = hv * cLimb 0 := by
      rw [u2.gpr, u1.other _ (by decide), u1.gpr, toNat_mul_lt (by
        rw [h1, toNat_movw hc0]; exact Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_of_lt_succ hh)
          (Nat.le_of_lt_succ hc0)) (by decide)), h1, toNat_movw hc0]
    rw [u3.gpr]
    show (s2.gpr .r11 + s2.gpr .r2).toNat = _
    have e11 : (s2.gpr .r11).toNat = w := by rw [u2.other _ (by decide), u1.other _ (by decide), h11]
    simp only [foldL, ite_true] at hs ⊢
    rw [toNat_add_lt (by rw [e11, e2]; omega), e11, e2]
  rw [ite_eq_right k0]
  by_cases k14 : k < 14
  · rw [ite_eq_left k14]
    refine ldr0_ok hc (d := o + 4 * (k - 1)) (by omega) fun s1 u1 => ?_
    refine wp_movw fun s2 u2 => wp_mul fun s3 u3 => wp_dp (op2_reg _ _) fun s4 u4 => WP.block_nil ?_
    refine ⟨?_, (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      (u4.rest (by decide)))), by rw [u4.mem, u3.mem, u2.mem, u1.mem]⟩
    have hck := cLimb_lt k
    have e1 : (s3.gpr .r1).toNat = hv := by
      rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), h1]
    have e2 : (s3.gpr .r2).toNat = hv * cLimb k := by
      rw [u3.gpr, u2.other _ (by decide), u2.gpr, u1.other _ (by decide), toNat_mul_lt (by
        rw [h1, toNat_movw hck]; exact Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_of_lt_succ hh)
          (Nat.le_of_lt_succ hck)) (by decide)), h1, toNat_movw hck]
    have e3 : (s3.gpr .r3).toNat = r (k - 1) := by
      rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr]; exact lr (k - 1) (by omega)
    rw [u4.gpr]
    show (s3.gpr .r3 + s3.gpr .r2).toNat = _
    simp only [foldL, k0, ite_false, show k < 27 by omega, ite_true] at hs ⊢
    rw [toNat_add_lt (by rw [e3, e2]; omega), e3, e2]
  rw [ite_eq_right k14]
  by_cases k27 : k < 27
  · rw [ite_eq_left k27]
    refine ldr0_ok hc (d := o + 4 * (k - 1)) (by omega) fun s1 u1 => WP.block_nil ?_
    refine ⟨?_, u1.rest (by decide), u1.mem⟩
    rw [u1.gpr]
    simp only [foldL, k0, ite_false, k27, ite_true, cLimb_high (by omega : 14 ≤ k), Nat.mul_zero,
      Nat.add_zero]
    exact lr (k - 1) (by omega)
  · rw [ite_eq_right k27]
    refine ldr0_ok hc (d := o + 104) (by omega) fun s1 u1 => ?_
    refine wp_mov (op2_lsl (by decide)) fun s2 u2 => wp_mov (op2_lsr (by decide)) fun s3 u3 => ?_
    refine WP.block_nil ⟨?_, (u1.rest (by decide)).trans ((u2.rest (by decide)).trans
      (u3.rest (by decide))), by rw [u3.mem, u2.mem, u1.mem]⟩
    rw [u3.gpr, u2.gpr, u1.gpr, toNat_mask14]
    simp only [foldL, k0, ite_false, k27, cLimb_high (by omega : 14 ≤ k), Nat.mul_zero, Nat.add_zero]
    rw [show o + 104 = o + 4 * 26 from rfl]
    exact congrArg (· % 16384) (lr 26 (by decide))

/-- `fold o`: the limbs of `l + h c` into `TF`. -/
theorem fold_ok {o : Nat} (ho : Buf o) {s : State} (hc : Ctx8 b s) (h6 : s.gpr .r6 = mask16)
    (hl : Lim28 s.mem (State.addr b) o) (hv : V28 s.mem (State.addr b) o < L)
    (hw : (s.gpr .r11).toNat < 65536) :
    WP isa (.block (fold o)) s fun t =>
      Rest [.r1, .r2, .r3, .r4, .r5] s t ∧ Frame [limbsR b TF] s.mem t.mem ∧
      Lim28 t.mem (State.addr b) TF ∧ V28 t.mem (State.addr b) TF < 2 * L ∧
      V28 t.mem (State.addr b) TF % L = ((s.gpr .r11).toNat + 65536 * V28 s.mem (State.addr b) o) % L := by
  have hT := TF_eq
  obtain ⟨ho1, ho2⟩ := ho
  obtain ⟨h27, hH, hsum, hlt, hmod⟩ := fold_facts hl hv hw
  unfold fold
  refine WP.append (foldHead_ok ⟨ho1, ho2⟩ hc h27 (hl 26 (by decide))) fun s1 ⟨e1, e5, k1, m1⟩ => ?_
  have hc1 := hc.of_rest k1 (by decide)
  have r0 : s1.gpr .r0 = b := hc1.r0
  refine WP.mono (carryPass_ok (rb := .r0) (o := TF) (s0 := s1) (c := foldC (limb s.mem (State.addr b) o) (s.gpr .r11).toNat) (cin := 0) (by decide)
    (by omega) (by rw [r0]; have := hc.fit; omega)
    (fun k hk => by rw [r0]; exact hc1.inW (by omega)) ((k1.gpr _ (by decide)).trans h6) e5
    hsum (by decide) ?_) fun t ht => ?_
  · intro k hk s' hp
    have hc' := hc1.of_rest hp.rest (by decide)
    have hf : Frame [⟨State.addr b + BitVec.ofNat 64 TF, 4 * k⟩] s.mem s'.mem := by
      have := hp.frame; rwa [r0, m1] at this
    exact foldSrc_ok ⟨ho1, ho2⟩ hH hsum hk hc' hf
      (by rw [hp.rest.gpr _ (by decide)]; exact e1)
      (by rw [hp.rest.gpr _ (by decide), k1.gpr _ (by decide)])
  · generalize foldC (limb s.mem (State.addr b) o) (s.gpr .r11).toNat = c at ht hlt hmod
    have outs : ∀ k < 28, limb t.mem (State.addr b) TF k = out c 0 k := by
      intro k hk; have := ht.outs k hk; rwa [r0] at this
    have hval := chain_val c 0 28
    have hlim : Lim28 t.mem (State.addr b) TF := fun k hk => by rw [outs k hk]; exact out_lt _ _ _
    have hV : V28 t.mem (State.addr b) TF = val16 c 28 := by
      have e : V28 t.mem (State.addr b) TF = val16 (out c 0) 28 := val16_congr outs
      have hz : chain c 0 28 = 0 := by
        rcases Nat.eq_zero_or_pos (chain c 0 28) with h | h
        · exact h
        · have h448 := pow2_split 446 2 (16 * 28) rfl
          have := L_lt
          have := Nat.mul_le_mul_left (2 ^ (16 * 28 : Nat)) h
          omega
      rw [e]; simp only [hz, Nat.mul_zero, Nat.add_zero] at hval; exact hval
    refine ⟨(k1.mono (by decide)).trans (ht.rest.mono (by decide)), ?_, hlim, by rw [hV]; exact hlt,
      by rw [hV]; exact hmod⟩
    have := ht.frame; rw [r0, m1] at this; exact this

/-! ## The conditional subtraction -/

/-- One source of the subtraction: limb `k` of `TF` plus limb `k` of `K`. -/
theorem csubSrc_ok {k : Nat} (hk : k < 28) {s : State} (hc : Ctx8 b s)
    (hl : limb s.mem (State.addr b) TF k < 65536) :
    WP isa (.block (csubSrc k)) s fun s' =>
      (s'.gpr .r3).toNat = limb s.mem (State.addr b) TF k + kLimb k ∧ Rest [.r2, .r3, .r4] s s' ∧
        s'.mem = s.mem := by
  have hT := TF_eq
  unfold csubSrc
  by_cases hkk : k < 14 ∨ k = 27
  · rw [ite_eq_left hkk]
    refine ldr0_ok hc (d := TF + 4 * k) (by omega) fun s1 u1 => wp_movw fun s2 u2 =>
      wp_dp (op2_reg _ _) fun s3 u3 => WP.block_nil ⟨?_, (u1.rest (by decide)).trans
        ((u2.rest (by decide)).trans (u3.rest (by decide))), by rw [u3.mem, u2.mem, u1.mem]⟩
    have hkl := kLimb_lt k
    have e3 : (s2.gpr .r3).toNat = limb s.mem (State.addr b) TF k := by
      rw [u2.other _ (by decide), u1.gpr]; rfl
    have e2 : (s2.gpr .r2).toNat = kLimb k := by rw [u2.gpr, toNat_movw hkl]
    rw [u3.gpr]
    show (s2.gpr .r3 + s2.gpr .r2).toNat = _
    rw [toNat_add_lt (by rw [e3, e2]; omega), e3, e2]
  · rw [ite_eq_right hkk]
    refine ldr0_ok hc (d := TF + 4 * k) (by omega) fun s1 u1 => WP.block_nil
      ⟨?_, u1.rest (by decide), u1.mem⟩
    rw [u1.gpr, kLimb_mid (by omega) (by omega), Nat.add_zero]; rfl

/-- The selection of `selectStep`, under the mask `-sw`. -/
theorem sel_mask (u v : BitVec 32) {sw : Nat} (h : sw ≤ 1) :
    ((u ^^^ v) &&& (0 - BitVec.ofNat 32 sw)) ^^^ v = if sw = 1 then u else v := by
  rcases (by omega : sw = 0 ∨ sw = 1) with rfl | rfl
  · simp
  · have : (0 : BitVec 32) - BitVec.ofNat 32 1 = BitVec.allOnes 32 := by decide
    rw [this, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]; rfl

/-- While selecting into `o`, after `k` limbs. -/
structure SelInv (b : BitVec 32) (o sw : Nat) (s0 : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.r2, .r3] s0 s
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 o, 4 * k⟩] s0.mem s.mem
  outs : ∀ j < k, limb s.mem (State.addr b) o j =
    if sw = 1 then limb s0.mem (State.addr b) o j else limb s0.mem (State.addr b) TF j

theorem select_ok {o : Nat} (ho : Buf o) {s0 : State} (hc : Ctx8 b s0) {sw : Nat} (hsw : sw ≤ 1)
    (h9 : s0.gpr .r9 = 0 - BitVec.ofNat 32 sw) :
    WP isa (.block ((List.range 28).flatMap (selectStep o))) s0 (SelInv b o sw s0 28) := by
  obtain ⟨ho1, ho2⟩ := ho
  have hT := TF_eq
  refine wp_range_flatMap (M := isa) (SelInv b o sw s0) (fun k s hk h => ?_) 28 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hcs := hc.of_rest h.rest (by decide)
  have wo : wd s.mem (State.addr b) (o + 4 * k) = limb s0.mem (State.addr b) o k :=
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  have wt : wd s.mem (State.addr b) (TF + 4 * k) = limb s0.mem (State.addr b) TF k :=
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  unfold selectStep
  refine ldr0_ok hcs (d := o + 4 * k) (by omega) fun t1 v1 => ?_
  refine ldr0_ok (hcs.of_rest (v1.rest (ws := [.r3]) (by decide)) (by decide)) (d := TF + 4 * k)
    (by omega) fun t2 v2 => ?_
  refine wp_dp (op2_reg _ _) fun t3 v3 => wp_dp (op2_reg _ _) fun t4 v4 => ?_
  refine wp_dp (op2_reg _ _) fun t5 v5 => ?_
  have hr5 : Rest [.r2, .r3] s t5 :=
    (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans (v5.rest (by decide)))))
  refine str0_ok (hcs.of_rest hr5 (by decide)) (d := o + 4 * k) (by omega) fun t6 v6 => WP.block_nil ?_
  have a1 : t2.gpr .r3 = s.mem.readW (State.addr b + BitVec.ofNat 64 (o + 4 * k)) 32 := by
    rw [v2.other _ (by decide), v1.gpr]
  have a2 : t2.gpr .r2 = s.mem.readW (State.addr b + BitVec.ofNat 64 (TF + 4 * k)) 32 := by
    rw [v2.gpr, v1.mem]
  have a9 : t2.gpr .r9 = 0 - BitVec.ofNat 32 sw := by
    rw [v2.other _ (by decide), v1.other _ (by decide), h.rest.gpr _ (by decide), h9]
  have e5 : t5.gpr .r3 = if sw = 1 then s.mem.readW (State.addr b + BitVec.ofNat 64 (o + 4 * k)) 32
      else s.mem.readW (State.addr b + BitVec.ofNat 64 (TF + 4 * k)) 32 := by
    rw [v5.gpr]
    show t4.gpr .r3 ^^^ t4.gpr .r2 = _
    rw [v4.gpr, v4.other .r2 (by decide)]
    show (t3.gpr .r3 &&& t3.gpr .r9) ^^^ t3.gpr .r2 = _
    rw [v3.gpr, v3.other .r9 (by decide), v3.other .r2 (by decide)]
    show ((t2.gpr .r3 ^^^ t2.gpr .r2) &&& t2.gpr .r9) ^^^ t2.gpr .r2 = _
    rw [a1, a2, a9]
    exact sel_mask _ _ hsw
  refine ⟨h.rest.trans (hr5.trans (v6.rest _)), ?_, fun j hj => ?_⟩
  · have hm : t5.mem = s.mem := by rw [v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
    rw [v6.mem, hm]
    refine (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) (t5.gpr .r3)
      (Offset.contains _ (d := o + 4 * k) (n := 4) (e := o) (k := 4 * (k + 1)) (by omega) (by omega) (by omega))
    rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)
  · have hm : t5.mem = s.mem := by rw [v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
    show wd t6.mem (State.addr b) (o + 4 * j) = _
    rw [v6.mem, hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h.outs j hj
    · rw [wd_write_self, e5]
      split
      · exact wo
      · exact wt

/-- `reduceT o`: `TF` (below `2L`) modulo `L`, into `o`. -/
theorem reduceT_ok {o : Nat} (ho : Buf o) {s : State} (hc : Ctx8 b s) (h6 : s.gpr .r6 = mask16)
    (hl : Lim28 s.mem (State.addr b) TF) (hv : V28 s.mem (State.addr b) TF < 2 * L) :
    WP isa (.block (reduceT o)) s fun t =>
      Rest [.r2, .r3, .r4, .r5, .r9] s t ∧ Frame [limbsR b o] s.mem t.mem ∧
      Lim28 t.mem (State.addr b) o ∧ V28 t.mem (State.addr b) o = V28 s.mem (State.addr b) TF % L := by
  obtain ⟨ho1, ho2⟩ := ho
  have hT := TF_eq
  unfold reduceT
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  have hc1 := hc.of_rest (u1.rest (ws := [.r5]) (by decide)) (by decide)
  have r0 : s1.gpr .r0 = b := hc1.r0
  refine WP.append (carryPass_ok (rb := .r0) (o := o) (s0 := s1)
    (c := fun k => limb s.mem (State.addr b) TF k + kLimb k) (cin := 0) (by decide)
    (by omega) (by rw [r0]; have := hc.fit; omega)
    (fun k hk => by rw [r0]; exact hc1.inW (by omega)) ((u1.other _ (by decide)).trans h6)
    (by rw [u1.gpr]; rfl) (fun k hk => by have := hl k hk; have := kLimb_lt k; omega) (by decide)
    ?_) fun s2 h2 => ?_
  · intro k hk s' hp
    have hc' := hc1.of_rest hp.rest (by decide)
    have hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 4 * k⟩] s.mem s'.mem := by
      have := hp.frame; rwa [r0, u1.mem] at this
    have et : limb s'.mem (State.addr b) TF k = limb s.mem (State.addr b) TF k :=
      wd_frame hf fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
    refine WP.mono (csubSrc_ok hk hc' (by rw [et]; exact hl k hk)) fun t ⟨e, kt, mt⟩ => ⟨?_, kt, mt⟩
    rw [e, et]
  generalize hcf : (fun k => limb s.mem (State.addr b) TF k + kLimb k) = c at h2
  have outs : ∀ k < 28, limb s2.mem (State.addr b) o k = out c 0 k := by
    intro k hk; have := h2.outs k hk; rwa [r0] at this
  have hf2 : Frame [limbsR b o] s.mem s2.mem := by
    have := h2.frame; rwa [r0, u1.mem] at this
  have hval := (chain_val c 0 28).trans (Nat.add_zero _)
  have hcv : val16 c 28 = V28 s.mem (State.addr b) TF + (2 ^ (16 * 28 : Nat) - L) := by
    unfold V28; rw [← hcf, val16_add, val16_kLimb]
  have hy := val16_lt (f := out c 0) (n := 28) fun k _ => out_lt _ _ _
  rw [hcv] at hval
  have hLM := two_L_le
  generalize (2 : Nat) ^ (16 * 28 : Nat) = M at hy hval hLM
  obtain ⟨hc1', hsel⟩ := csub_facts hLM hv hy hval
  refine wp_mov (op2_imm (by decide)) fun s3 u3 => wp_dp (op2_reg _ _) fun s4 u4 => ?_
  have k4 : Rest [.r2, .r3, .r4, .r5, .r9] s s4 :=
    ((u1.rest (by decide)).trans (h2.rest.mono (by decide))).trans
      ((u3.rest (by decide)).trans (u4.rest (by decide)))
  have h9 : s4.gpr .r9 = 0 - BitVec.ofNat 32 (chain c 0 28) := by
    rw [u4.gpr]
    show s3.gpr .r9 - s3.gpr .r5 = _
    rw [u3.gpr, u3.other _ (by decide)]
    apply congrArg (fun x : BitVec 32 => 0 - x)
    apply BitVec.eq_of_toNat_eq
    rw [toNat_imm (by omega), h2.r5]
  have m4 : s4.mem = s2.mem := by rw [u4.mem, u3.mem]
  refine WP.mono (select_ok ⟨ho1, ho2⟩ (hc.of_rest k4 (by decide)) hc1' h9) fun t ht => ?_
  have hlt : ∀ k < 28, limb t.mem (State.addr b) o k =
      if chain c 0 28 = 1 then out c 0 k else limb s.mem (State.addr b) TF k := by
    intro k hk
    rw [ht.outs k hk, m4, outs k hk]
    congr 1
    exact wd_frame hf2 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  refine ⟨k4.trans (ht.rest.mono (by decide)), ?_, fun k hk => ?_, ?_⟩
  · refine hf2.trans ?_
    rw [← m4]; exact ht.frame
  · rw [hlt k hk]; split
    · exact out_lt _ _ _
    · exact hl k hk
  · rw [← hsel]
    unfold V28
    rw [val16_congr hlt]
    split
    · rfl
    · rfl

/-! ## One chunk -/

/-- What a step leaves unchanged: all but `r1`–`r5` and `r9` (and the flags),
and the memory outside `TF` and the remainder at `o`. -/
structure StepKeep (b : BitVec 32) (o : Nat) (s t : State) : Prop where
  rest : Rest [.r1, .r2, .r3, .r4, .r5, .r9] s t
  frame : Frame [limbsR b TF, limbsR b o] s.mem t.mem

/-- `step o`: the chunk in `r11` folded into the remainder at `o`. -/
theorem step_ok {o : Nat} (ho : Buf o) {s : State} (hc : Ctx8 b s) (h6 : s.gpr .r6 = mask16)
    (hl : Lim28 s.mem (State.addr b) o) (hv : V28 s.mem (State.addr b) o < L)
    (hw : (s.gpr .r11).toNat < 65536) :
    WP isa (.block (step o)) s fun t =>
      StepKeep b o s t ∧ Lim28 t.mem (State.addr b) o ∧
      V28 t.mem (State.addr b) o = ((s.gpr .r11).toNat + 65536 * V28 s.mem (State.addr b) o) % L := by
  unfold step
  refine WP.append (fold_ok ho hc h6 hl hv hw) fun u ⟨ku, fu, lu, vu, mu⟩ => ?_
  refine WP.mono (reduceT_ok ho (hc.of_rest ku (by decide)) ((ku.gpr _ (by decide)).trans h6) lu vu)
    fun t ⟨kt, ft, lt, vt⟩ => ⟨⟨(ku.mono (by decide)).trans (kt.mono (by decide)),
      (fu.mono (by simp)).trans (ft.mono (by simp))⟩, lt, by rw [vt, mu]⟩

end

end VG.Proof.Ed448.Arm
