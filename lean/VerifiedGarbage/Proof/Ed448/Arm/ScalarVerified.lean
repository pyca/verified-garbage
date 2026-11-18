module

public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ed448.Arm.ScalarLit
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ed448.Arm.ScalarLit
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.X448.Radix16
import VerifiedGarbage.Proof.X448.Arm.MulLoop
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X448.Arm.Init
import VerifiedGarbage.Proof.X448.Arm.RowPass
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Ed448.Arm.ScalarNat
public import VerifiedGarbage.Proof.X25519.Arm.Field
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.X448.Radix16
meta import VerifiedGarbage.Proof.X448.Arm.MulLoop
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.X448.Arm.Init
meta import VerifiedGarbage.Proof.X448.Arm.RowPass
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Ed448.Arm.ScalarNat
meta import VerifiedGarbage.Proof.X25519.Arm.Field
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.WriteBytes

/-! ### `Ed448.Arm.ScalarMulAddMain`, which this module and modules that import it used -/

section

/-! ### `Ed448.Arm.ScalarMain`, which this module and modules that import it used -/

section

/-! ### `Ed448.Arm.ScalarIO`, which this module and modules that import it used -/

section

/-! ### `Ed448.Arm.ScalarLoop`, which only this module used -/

section

/-! ### `Ed448.Arm.ScalarStep`, which only this module used -/

section

/-!
# Ed448 scalar arithmetic on ARMv7: one chunk

`fold o` computes the limbs of `l + h c` into `TF` from the remainder at `o`
and the chunk in `r11` (`fold_ok`); `reduceT o` the remainder of `TF`
modulo `L` into `o` (`reduceT_ok`); together, `step o` folds a chunk into
the remainder (`step_ok`). The working space is `r0`'s 8192 bytes
(`CtxN 4096`), with the limb mask in `r6`.
-/

@[expose] public section

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
  refine ldr0_ok hc (d := o + 104) (by omega_arith) fun s1 u1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  obtain hc2 := hc.of_rest ((u1.rest (ws := [.r1, .r2, .r5]) (by decide)).trans (u2.rest (by decide)))
    (by decide)
  refine ldr0_ok hc2 (d := o + 108) (by omega_arith) fun s3 u3 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s4 u4 => wp_mov (op2_imm (by decide)) fun s5 u5 => ?_
  refine WP.block_nil ⟨?_, by rw [u5.gpr]; rfl, ?_, by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]⟩
  · have e1 : (s3.gpr .r1).toNat = limb s.mem (State.addr b) o 26 / 16384 := by
      rw [u3.other _ (by decide), u2.gpr, toNat_shr, u1.gpr]; rfl
    obtain e2 : (s3.gpr .r2).toNat = limb s.mem (State.addr b) o 27 := by
      rw [u3.gpr, u2.mem, u1.mem]; rfl
    rw [u5.other _ (by decide), u4.gpr]
    show (s3.gpr .r1 + s3.gpr .r2 <<< 2).toNat = _
    obtain e3 : (s3.gpr .r2 <<< 2).toNat = 4 * limb s.mem (State.addr b) o 27 := by
      rw [toNat_shl, e2, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
    rw [toNat_add_lt (by rw [e1, e3]; omega_arith), e1, e3]
    rfl
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide)))))

theorem toNat_movw {v : Nat} (h : v < 65536) : ((BitVec.ofNat 16 v).setWidth 32).toNat = v := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega_arith)]

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
  obtain lr : ∀ j < 28, wd s.mem (State.addr b) (o + 4 * j) = r j := fun j hj => by
    rw [← hr]
    exact wd_frame hf fun z hz => by
      rw [List.mem_singleton.mp hz]; exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  obtain hs := hsum k hk
  unfold foldSrc
  by_cases k0 : k = 0
  · subst k0
    rw [ite_eq_left rfl]
    refine wp_movw fun s1 u1 => wp_mul fun s2 u2 => wp_dp (op2_reg _ _) fun s3 u3 => WP.block_nil ?_
    refine ⟨?_, (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide))),
      by rw [u3.mem, u2.mem, u1.mem]⟩
    obtain hc0 := cLimb_lt 0
    obtain e2 : (s2.gpr .r2).toNat = hv * cLimb 0 := by
      rw [u2.gpr, u1.other _ (by decide), u1.gpr, toNat_mul_lt (by
        rw [h1, toNat_movw hc0]; exact Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_of_lt_succ hh)
          (Nat.le_of_lt_succ hc0)) (by decide)), h1, toNat_movw hc0]
    rw [u3.gpr]
    show (s2.gpr .r11 + s2.gpr .r2).toNat = _
    obtain e11 : (s2.gpr .r11).toNat = w := by rw [u2.other _ (by decide), u1.other _ (by decide), h11]
    simp only [foldL, ite_true] at hs ⊢
    rw [toNat_add_lt (by rw [e11, e2]; omega_arith), e11, e2]
  rw [ite_eq_right k0]
  by_cases k14 : k < 14
  · rw [ite_eq_left k14]
    refine ldr0_ok hc (d := o + 4 * (k - 1)) (by omega_arith) fun s1 u1 => ?_
    refine wp_movw fun s2 u2 => wp_mul fun s3 u3 => wp_dp (op2_reg _ _) fun s4 u4 => WP.block_nil ?_
    refine ⟨?_, (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      (u4.rest (by decide)))), by rw [u4.mem, u3.mem, u2.mem, u1.mem]⟩
    obtain hck := cLimb_lt k
    obtain e1 : (s3.gpr .r1).toNat = hv := by
      rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), h1]
    obtain e2 : (s3.gpr .r2).toNat = hv * cLimb k := by
      rw [u3.gpr, u2.other _ (by decide), u2.gpr, u1.other _ (by decide), toNat_mul_lt (by
        rw [h1, toNat_movw hck]; exact Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_of_lt_succ hh)
          (Nat.le_of_lt_succ hck)) (by decide)), h1, toNat_movw hck]
    obtain e3 : (s3.gpr .r3).toNat = r (k - 1) := by
      rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr]; exact lr (k - 1) (by omega_arith)
    rw [u4.gpr]
    show (s3.gpr .r3 + s3.gpr .r2).toNat = _
    simp only [foldL, k0, ite_false, show k < 27 by omega_arith, ite_true] at hs ⊢
    rw [toNat_add_lt (by rw [e3, e2]; omega_arith), e3, e2]
  rw [ite_eq_right k14]
  by_cases k27 : k < 27
  · rw [ite_eq_left k27]
    refine ldr0_ok hc (d := o + 4 * (k - 1)) (by omega_arith) fun s1 u1 => WP.block_nil ?_
    refine ⟨?_, u1.rest (by decide), u1.mem⟩
    rw [u1.gpr]
    simp only [foldL, k0, ite_false, k27, ite_true, cLimb_high (by omega_arith : 14 ≤ k), Nat.mul_zero,
      Nat.add_zero]
    exact lr (k - 1) (by omega_arith)
  · rw [ite_eq_right k27]
    refine ldr0_ok hc (d := o + 104) (by omega_arith) fun s1 u1 => ?_
    refine wp_mov (op2_lsl (by decide)) fun s2 u2 => wp_mov (op2_lsr (by decide)) fun s3 u3 => ?_
    refine WP.block_nil ⟨?_, (u1.rest (by decide)).trans ((u2.rest (by decide)).trans
      (u3.rest (by decide))), by rw [u3.mem, u2.mem, u1.mem]⟩
    rw [u3.gpr, u2.gpr, u1.gpr, toNat_mask14]
    simp only [foldL, k0, ite_false, k27, cLimb_high (by omega_arith : 14 ≤ k), Nat.mul_zero, Nat.add_zero]
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
  obtain hc1 := hc.of_rest k1 (by decide)
  have r0 : s1.gpr .r0 = b := hc1.r0
  refine WP.mono (carryPass_ok (rb := .r0) (o := TF) (s0 := s1) (c := foldC (limb s.mem (State.addr b) o) (s.gpr .r11).toNat) (cin := 0) (by decide)
    (by omega_arith) (by rw [r0]; have := hc.fit; omega_arith)
    (fun k hk => by rw [r0]; exact hc1.inW (by omega_arith)) ((k1.gpr _ (by decide)).trans h6) e5
    hsum (by decide) ?_) fun t ht => ?_
  · intro k hk s' hp
    obtain hc' := hc1.of_rest hp.rest (by decide)
    obtain hf : Frame [⟨State.addr b + BitVec.ofNat 64 TF, 4 * k⟩] s.mem s'.mem := by
      have := hp.frame; rwa [r0, m1] at this
    exact foldSrc_ok ⟨ho1, ho2⟩ hH hsum hk hc' hf
      (by rw [hp.rest.gpr _ (by decide)]; exact e1)
      (by rw [hp.rest.gpr _ (by decide), k1.gpr _ (by decide)])
  · generalize foldC (limb s.mem (State.addr b) o) (s.gpr .r11).toNat = c at ht hlt hmod
    obtain outs : ∀ k < 28, limb t.mem (State.addr b) TF k = out c 0 k := by
      intro k hk; have := ht.outs k hk; rwa [r0] at this
    obtain hval := chain_val c 0 28
    obtain hlim : Lim28 t.mem (State.addr b) TF := fun k hk => by rw [outs k hk]; exact out_lt _ _ _
    obtain hV : V28 t.mem (State.addr b) TF = val16 c 28 := by
      obtain e : V28 t.mem (State.addr b) TF = val16 (out c 0) 28 := val16_congr outs
      obtain hz : chain c 0 28 = 0 := by
        rcases Nat.eq_zero_or_pos (chain c 0 28) with h | h
        · exact h
        · have h448 := pow2_split 446 2 (16 * 28) rfl
          have := L_lt
          have := Nat.mul_le_mul_left (2 ^ (16 * 28 : Nat)) h
          omega_arith
      generalize (2 : Nat) ^ (16 * 28) = P at hval
      rw [hz, Nat.mul_zero, Nat.add_zero, Nat.add_zero] at hval; exact e.trans hval
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
    refine ldr0_ok hc (d := TF + 4 * k) (by omega_arith) fun s1 u1 => wp_movw fun s2 u2 =>
      wp_dp (op2_reg _ _) fun s3 u3 => WP.block_nil ⟨?_, (u1.rest (by decide)).trans
        ((u2.rest (by decide)).trans (u3.rest (by decide))), by rw [u3.mem, u2.mem, u1.mem]⟩
    obtain hkl := kLimb_lt k
    obtain e3 : (s2.gpr .r3).toNat = limb s.mem (State.addr b) TF k := by
      rw [u2.other _ (by decide), u1.gpr]; rfl
    obtain e2 : (s2.gpr .r2).toNat = kLimb k := by rw [u2.gpr, toNat_movw hkl]
    rw [u3.gpr]
    show (s2.gpr .r3 + s2.gpr .r2).toNat = _
    rw [toNat_add_lt (by rw [e3, e2]; omega_arith), e3, e2]
  · rw [ite_eq_right hkk]
    refine ldr0_ok hc (d := TF + 4 * k) (by omega_arith) fun s1 u1 => WP.block_nil
      ⟨?_, u1.rest (by decide), u1.mem⟩
    rw [u1.gpr, kLimb_mid (by omega_arith) (by omega_arith), Nat.add_zero]; rfl

/-- The selection of `selectStep`, under the mask `-sw`. -/
theorem sel_mask (u v : BitVec 32) {sw : Nat} (h : sw ≤ 1) :
    ((u ^^^ v) &&& (0 - BitVec.ofNat 32 sw)) ^^^ v = if sw = 1 then u else v := by
  rcases (by omega_arith : sw = 0 ∨ sw = 1) with rfl | rfl
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
  obtain hcs := hc.of_rest h.rest (by decide)
  obtain wo : wd s.mem (State.addr b) (o + 4 * k) = limb s0.mem (State.addr b) o k :=
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  obtain wt : wd s.mem (State.addr b) (TF + 4 * k) = limb s0.mem (State.addr b) TF k :=
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  unfold selectStep
  refine ldr0_ok hcs (d := o + 4 * k) (by omega_arith) fun t1 v1 => ?_
  refine ldr0_ok (hcs.of_rest (v1.rest (ws := [.r3]) (by decide)) (by decide)) (d := TF + 4 * k)
    (by omega_arith) fun t2 v2 => ?_
  refine wp_dp (op2_reg _ _) fun t3 v3 => wp_dp (op2_reg _ _) fun t4 v4 => ?_
  refine wp_dp (op2_reg _ _) fun t5 v5 => ?_
  obtain hr5 : Rest [.r2, .r3] s t5 :=
    (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans (v5.rest (by decide)))))
  refine str0_ok (hcs.of_rest hr5 (by decide)) (d := o + 4 * k) (by omega_arith) fun t6 v6 => WP.block_nil ?_
  obtain a1 : t2.gpr .r3 = s.mem.readW (State.addr b + BitVec.ofNat 64 (o + 4 * k)) 32 := by
    rw [v2.other _ (by decide), v1.gpr]
  obtain a2 : t2.gpr .r2 = s.mem.readW (State.addr b + BitVec.ofNat 64 (TF + 4 * k)) 32 := by
    rw [v2.gpr, v1.mem]
  obtain a9 : t2.gpr .r9 = 0 - BitVec.ofNat 32 sw := by
    rw [v2.other _ (by decide), v1.other _ (by decide), h.rest.gpr _ (by decide), h9]
  obtain e5 : t5.gpr .r3 = if sw = 1 then s.mem.readW (State.addr b + BitVec.ofNat 64 (o + 4 * k)) 32
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
      (Offset.contains _ (d := o + 4 * k) (n := 4) (e := o) (k := 4 * (k + 1)) (by omega_arith) (by omega_arith) (by omega_arith))
    rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_arith)
  · have hm : t5.mem = s.mem := by rw [v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
    show wd t6.mem (State.addr b) (o + 4 * j) = _
    rw [v6.mem, hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact h.outs j hj
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
  obtain hc1 := hc.of_rest (u1.rest (ws := [.r5]) (by decide)) (by decide)
  have r0 : s1.gpr .r0 = b := hc1.r0
  refine WP.append (carryPass_ok (rb := .r0) (o := o) (s0 := s1)
    (c := fun k => limb s.mem (State.addr b) TF k + kLimb k) (cin := 0) (by decide)
    (by omega_arith) (by rw [r0]; have := hc.fit; omega_arith)
    (fun k hk => by rw [r0]; exact hc1.inW (by omega_arith)) ((u1.other _ (by decide)).trans h6)
    (by rw [u1.gpr]; rfl) (fun k hk => by have := hl k hk; have := kLimb_lt k; omega_arith) (by decide)
    ?_) fun s2 h2 => ?_
  · intro k hk s' hp
    obtain hc' := hc1.of_rest hp.rest (by decide)
    obtain hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 4 * k⟩] s.mem s'.mem := by
      have := hp.frame; rwa [r0, u1.mem] at this
    obtain et : limb s'.mem (State.addr b) TF k = limb s.mem (State.addr b) TF k :=
      wd_frame hf fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    refine WP.mono (csubSrc_ok hk hc' (by rw [et]; exact hl k hk)) fun t ⟨e, kt, mt⟩ => ⟨?_, kt, mt⟩
    rw [e, et]
  generalize hcf : (fun k => limb s.mem (State.addr b) TF k + kLimb k) = c at h2
  obtain outs : ∀ k < 28, limb s2.mem (State.addr b) o k = out c 0 k := by
    intro k hk; have := h2.outs k hk; rwa [r0] at this
  obtain hf2 : Frame [limbsR b o] s.mem s2.mem := by
    have := h2.frame; rwa [r0, u1.mem] at this
  obtain hval := (chain_val c 0 28).trans (Nat.add_zero _)
  obtain hcv : val16 c 28 = V28 s.mem (State.addr b) TF + (2 ^ (16 * 28 : Nat) - L) := by
    unfold V28; rw [← hcf, val16_add, val16_kLimb]
  obtain hy := val16_lt (f := out c 0) (n := 28) fun k _ => out_lt _ _ _
  rw [hcv] at hval
  have hLM := two_L_le
  generalize (2 : Nat) ^ (16 * 28 : Nat) = M at hy hval hLM
  obtain ⟨hc1', hsel⟩ := csub_facts hLM hv hy hval
  refine wp_mov (op2_imm (by decide)) fun s3 u3 => wp_dp (op2_reg _ _) fun s4 u4 => ?_
  obtain k4 : Rest [.r2, .r3, .r4, .r5, .r9] s s4 :=
    ((u1.rest (by decide)).trans (h2.rest.mono (by decide))).trans
      ((u3.rest (by decide)).trans (u4.rest (by decide)))
  obtain h9 : s4.gpr .r9 = 0 - BitVec.ofNat 32 (chain c 0 28) := by
    rw [u4.gpr]
    show s3.gpr .r9 - s3.gpr .r5 = _
    rw [u3.gpr, u3.other _ (by decide)]
    apply congrArg (fun x : BitVec 32 => 0 - x)
    apply BitVec.eq_of_toNat_eq
    rw [toNat_imm (by omega_arith), h2.r5]
  obtain m4 : s4.mem = s2.mem := by rw [u4.mem, u3.mem]
  refine WP.mono (select_ok ⟨ho1, ho2⟩ (hc.of_rest k4 (by decide)) hc1' h9) fun t ht => ?_
  obtain hlt : ∀ k < 28, limb t.mem (State.addr b) o k =
      if chain c 0 28 = 1 then out c 0 k else limb s.mem (State.addr b) TF k := by
    intro k hk
    rw [ht.outs k hk, m4, outs k hk]
    congr 1
    exact wd_frame hf2 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
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

end

end


/-!
# Ed448 scalar arithmetic on ARMv7: the loops

The remainder of an input's bytes from the top, sixteen bits at a time
(`byteLoop_ok`), and of the product's limbs (`limbLoop_ok`), and the
remainders they start from (`zeroR_ok`, `init57_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X25519.Arm
open VG.Spec.Ed448 (L bytesAt decodeLE)

/-! ## The numbers -/

theorem mod_fold (w D : Nat) : (w + 65536 * (D % L)) % L = (w + 65536 * D) % L := by
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

/-- Two bytes more of a suffix. -/
theorem decode_drop2 (m : Mem) (p : Addr) {N n : Nat} (h : n + 2 ≤ N) :
    decodeLE ((bytesAt m p N).drop n) = (m (p + BitVec.ofNat 64 n)).toNat +
      256 * (m (p + BitVec.ofNat 64 (n + 1))).toNat + 65536 * decodeLE ((bytesAt m p N).drop (n + 2)) := by
  rw [List.drop_eq_getElem_cons (by rw [bytesAt_length]; omega_arith),
    List.drop_eq_getElem_cons (by rw [bytesAt_length]; omega_arith)]
  simp only [decodeLE, bytesAt, List.getElem_map, List.getElem_range]
  rw [show n + 1 + 1 = n + 2 from rfl]
  omega_arith

/-- A suffix as the bytes it starts with. -/
theorem decode_drop1 (m : Mem) (p : Addr) {N n : Nat} (h : n + 1 = N) :
    decodeLE ((bytesAt m p N).drop n) = (m (p + BitVec.ofNat 64 n)).toNat := by
  rw [List.drop_eq_getElem_cons (by rw [bytesAt_length]; omega_arith),
    List.drop_eq_nil_of_le (by rw [bytesAt_length]; omega_arith)]
  simp only [decodeLE, bytesAt, List.getElem_map, List.getElem_range, Nat.mul_zero, Nat.add_zero]

section
variable {b : BitVec 32}

/-! ## Reading two bytes -/

theorem readBytes_ok {s : State} {p : BitVec 32} {n N : Nat} (hn : n + 2 ≤ N)
    (hp : s.gpr .r12 = p) (hfit : p.toNat + N ≤ 2 ^ 32)
    (h10 : s.gpr .r10 = BitVec.ofNat 32 (n + 2))
    (hr : ∀ i < N, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1) :
    WP isa (.block readBytes) s fun t =>
      Rest [.r2, .r3, .r10, .r11] s t ∧ t.mem = s.mem ∧ t.gpr .r10 = BitVec.ofNat 32 n ∧
      (t.gpr .r11).toNat = (s.mem (State.addr p + BitVec.ofNat 64 n)).toNat +
        256 * (s.mem (State.addr p + BitVec.ofNat 64 (n + 1))).toNat := by
  unfold readBytes
  refine wp_dp (op2_imm (by decide)) fun u1 v1 => wp_dp (op2_reg _ _) fun u2 v2 => ?_
  obtain e10 : u1.gpr .r10 = BitVec.ofNat 32 n := by
    rw [v1.gpr]
    change s.gpr .r10 - BitVec.ofNat 32 2 = _
    rw [h10, BitVec.ofNat_add, BitVec.add_sub_cancel]
  obtain e2 : u2.gpr .r2 = p + BitVec.ofNat 32 n := by
    rw [v2.gpr]; change u1.gpr .r12 + u1.gpr .r10 = _
    rw [v1.other _ (by decide), hp, e10]
  obtain hpn : (p + BitVec.ofNat 32 n).toNat = p.toNat + n := by
    rw [toNat_add_lt (by rw [toNat_imm (by omega_arith)]; omega_arith), toNat_imm (by omega_arith)]
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 n) (by decide)
    (by rw [e2, BitVec.add_zero]; exact addr_add (by omega_arith))
    (by rw [v2.rd, v2.wr, v1.rd, v1.wr]; exact hr n (by omega_arith)) fun u3 v3 => ?_
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 (n + 1)) (by decide)
    (by rw [v3.other _ (by decide), e2, addr_add (by omega_arith), addr_add (by omega_arith), Offset.add_add])
    (by rw [v3.rd, v3.wr, v2.rd, v2.wr, v1.rd, v1.wr]; exact hr (n + 1) (by omega_arith)) fun u4 v4 => ?_
  refine wp_dp (op2_lsl (by decide)) fun t vt => WP.block_nil ?_
  obtain m4 : u4.mem = s.mem := by rw [v4.mem, v3.mem, v2.mem, v1.mem]
  refine ⟨(v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans (vt.rest (by decide))))), by rw [vt.mem, m4], ?_, ?_⟩
  · rw [vt.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide),
      v2.other _ (by decide), e10]
  · rw [vt.gpr]
    show (u4.gpr .r11 + u4.gpr .r3 <<< 8).toNat = _
    obtain e11 : (u4.gpr .r11).toNat = (s.mem (State.addr p + BitVec.ofNat 64 n)).toNat := by
      rw [v4.other _ (by decide), v3.gpr, BitVec.toNat_setWidth_of_le (by decide), v2.mem, v1.mem]
    obtain e3 : (u4.gpr .r3).toNat = (s.mem (State.addr p + BitVec.ofNat 64 (n + 1))).toNat := by
      rw [v4.gpr, BitVec.toNat_setWidth_of_le (by decide), v3.mem, v2.mem, v1.mem]
    obtain b1 := (s.mem (State.addr p + BitVec.ofNat 64 (n + 1))).isLt
    obtain b0 := (s.mem (State.addr p + BitVec.ofNat 64 n)).isLt
    obtain e3' : (u4.gpr .r3 <<< 8).toNat = 256 * (s.mem (State.addr p + BitVec.ofNat 64 (n + 1))).toNat := by
      rw [toNat_shl, e3, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
    rw [toNat_add_lt (by rw [e11, e3']; omega_arith), e11, e3']

/-! ## The byte loop -/

/-- What the loops change. -/
structure LoopKeep (b : BitVec 32) (o : Nat) (s t : State) : Prop where
  rest : Rest [.r1, .r2, .r3, .r4, .r5, .r9, .r10, .r11] s t
  frame : Frame [limbsR b TF, limbsR b o] s.mem t.mem

theorem LoopKeep.refl (b : BitVec 32) (o : Nat) (s : State) : LoopKeep b o s s :=
  ⟨Rest.refl _ _, Frame.refl _ _⟩

theorem LoopKeep.trans {o : Nat} {s t u : State} (h : LoopKeep b o s t) (h' : LoopKeep b o t u) :
    LoopKeep b o s u := ⟨h.rest.trans h'.rest, h.frame.trans h'.frame⟩

/-- After the steps from the top down to byte `n`. -/
structure ByteInv (b : BitVec 32) (o N : Nat) (p : Addr) (s0 : State) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ N
  even : n % 2 = 0
  counter : s.gpr .r10 = BitVec.ofNat 32 n
  limbs : Lim28 s.mem (State.addr b) o
  value : V28 s.mem (State.addr b) o = decodeLE ((bytesAt s0.mem p N).drop n) % L
  keeps : LoopKeep b o s0 s

theorem byteLoop_ok {o N : Nat} (ho : Buf o) {p : BitVec 32} {s0 : State} (hc : Ctx8 b s0)
    (h6 : s0.gpr .r6 = mask16) (hp : s0.gpr .r12 = p) (hfit : p.toNat + N ≤ 2 ^ 32)
    (hread : ∀ i < N, InRegions (s0.rd ++ s0.wr) (State.addr p + BitVec.ofNat 64 i) 1)
    (hsep : ∀ r ∈ [limbsR b TF, limbsR b o], (⟨State.addr p, N⟩ : Region).Disjoint r)
    {n0 : Nat} (hn0 : 0 < n0) (hle : n0 ≤ N) (heven : n0 % 2 = 0)
    (h10 : s0.gpr .r10 = BitVec.ofNat 32 n0) (hl : Lim28 s0.mem (State.addr b) o)
    (hv : V28 s0.mem (State.addr b) o = decodeLE ((bytesAt s0.mem (State.addr p) N).drop n0) % L) :
    WP isa (.loop (.block (byteStep o)) .ne) s0 fun t => LoopKeep b o s0 t ∧
      Lim28 t.mem (State.addr b) o ∧
      V28 t.mem (State.addr b) o = decodeLE (bytesAt s0.mem (State.addr p) N) % L := by
  obtain hN : N ≤ 2 ^ 32 := by omega_arith
  apply WP.loop (ByteInv b o N (State.addr p) s0) (n := n0)
  · intro n s hi
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by have := hi.even; have := hi.positive; omega_arith⟩
    have hk : k + 2 ≤ N := hi.bound
    obtain hcs : Ctx8 b s := hc.of_rest hi.keeps.rest (by decide)
    obtain hps : s.gpr .r12 = p := (hi.keeps.rest.gpr _ (by decide)).trans hp
    obtain hrs : ∀ i < N, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1 := by
      rw [hi.keeps.rest.rd, hi.keeps.rest.wr]; exact hread
    unfold byteStep
    rw [List.append_assoc]
    refine WP.append (readBytes_ok hk hps hfit hi.counter hrs) fun u ⟨ku, mu, cu, wu⟩ => ?_
    obtain hcu : Ctx8 b u := hcs.of_rest ku (by decide)
    obtain h6u : u.gpr .r6 = mask16 :=
      (ku.gpr _ (by decide)).trans ((hi.keeps.rest.gpr _ (by decide)).trans h6)
    obtain hwu : (u.gpr .r11).toNat < 65536 := by
      rw [wu]
      have := (s.mem (State.addr p + BitVec.ofNat 64 k)).isLt
      have := (s.mem (State.addr p + BitVec.ofNat 64 (k + 1))).isLt
      omega_arith
    refine WP.append (step_ok ho hcu h6u (mu ▸ hi.limbs)
      (by rw [mu, hi.value]; exact Nat.mod_lt _ L_pos) hwu) fun v ⟨kv, lv, vv⟩ => ?_
    refine wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
    obtain mb : ∀ i < N, s.mem (State.addr p + BitVec.ofNat 64 i) =
        s0.mem (State.addr p + BitVec.ofNat 64 i) :=
      fun i hi' => hi.keeps.frame.bytes hsep (by show N ≤ 2 ^ 64; omega_arith) hi'
    obtain val : V28 t.mem (State.addr b) o = decodeLE ((bytesAt s0.mem (State.addr p) N).drop k) % L := by
      rw [ht.mem, vv, wu, mu, hi.value, mod_fold, mb k (by omega_arith), mb (k + 1) (by omega_arith),
        decode_drop2 _ _ hk]
    have keep : LoopKeep b o s0 t := hi.keeps.trans
      ⟨(ku.mono (by decide)).trans ((kv.rest.mono (by decide)).trans (ht.rest _)),
        by rw [ht.mem, ← mu]; exact kv.frame⟩
    obtain c10 : t.gpr .r10 = BitVec.ofNat 32 k := by
      rw [ht.gpr, kv.rest.gpr _ (by decide), cu]
    obtain zt : t.z = decide (k = 0) := by
      obtain he : BitVec.ofNat 32 k - (0 : BitVec 32) = BitVec.ofNat 32 k := BitVec.sub_zero _
      rw [hz, kv.rest.gpr _ (by decide), cu, he, ofNat_beq_zero (by omega_arith)]
    by_cases k0 : k = 0
    · subst k0
      refine .inl ⟨by rw [eval_ne, zt]; rfl, keep, ht.mem ▸ lv, ?_⟩
      simpa only [List.drop_zero] using val
    · refine .inr ⟨by rw [eval_ne, zt]; simp only [k0, decide_false, Bool.not_false], k, by omega_arith,
        ⟨by omega_arith, by omega_arith, by have := hi.even; omega_arith, c10, ht.mem ▸ lv, val, keep⟩⟩
  · exact ⟨hn0, hle, heven, h10, hl, hv, LoopKeep.refl _ _ _⟩

/-! ## The product's limbs -/

theorem ACC_eq : Impl.X448.Arm.ACC = 3584 := rfl

theorem readLimb_ok {s : State} (hc : Ctx8 b s) {j : Nat} (hj : j < 56)
    (h10 : s.gpr .r10 = BitVec.ofNat 32 (4 * (j + 1))) :
    WP isa (.block readLimb) s fun t =>
      Rest [.r2, .r10, .r11] s t ∧ t.mem = s.mem ∧ t.gpr .r10 = BitVec.ofNat 32 (4 * j) ∧
      (t.gpr .r11).toNat = limb s.mem (State.addr b) Impl.X448.Arm.ACC j := by
  have hA := ACC_eq
  have hfit := hc.fit
  unfold readLimb
  refine wp_dp (op2_imm (by decide)) fun u1 v1 => wp_dp (op2_reg _ _) fun u2 v2 => ?_
  obtain e10 : u1.gpr .r10 = BitVec.ofNat 32 (4 * j) := by
    rw [v1.gpr]
    change s.gpr .r10 - BitVec.ofNat 32 4 = _
    rw [h10, show 4 * (j + 1) = 4 * j + 4 by omega_arith, BitVec.ofNat_add, BitVec.add_sub_cancel]
  obtain e2 : u2.gpr .r2 = b + BitVec.ofNat 32 (4 * j) := by
    rw [v2.gpr]; change u1.gpr .r0 + u1.gpr .r10 = _
    rw [v1.other _ (by decide), hc.r0, e10]
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (Impl.X448.Arm.ACC + 4 * j)) (by omega_arith)
    (by rw [e2, Offset.add_add]; rw [Nat.add_comm]; exact addr_add (by omega_arith))
    (by rw [v2.rd, v2.wr, v1.rd, v1.wr]; exact hc.inR (by omega_arith)) fun t vt => WP.block_nil ?_
  refine ⟨(v1.rest (by decide)).trans ((v2.rest (by decide)).trans (vt.rest (by decide))),
    by rw [vt.mem, v2.mem, v1.mem], by rw [vt.other _ (by decide), v2.other _ (by decide), e10], ?_⟩
  rw [vt.gpr, v2.mem, v1.mem]; rfl

/-- The number of the product's limbs from `j` up. -/
abbrev accFrom (m : Mem) (B : Addr) (j : Nat) : Nat :=
  val16 (fun i => limb m B Impl.X448.Arm.ACC (j + i)) (56 - j)

theorem accFrom_step (m : Mem) (B : Addr) {j : Nat} (hj : j < 56) :
    accFrom m B j = limb m B Impl.X448.Arm.ACC j + 65536 * accFrom m B (j + 1) := by
  unfold accFrom
  rw [show 56 - j = 1 + (56 - (j + 1)) by omega_arith, val16_append]
  simp only [val16, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero]
  refine congrArg (_ + ·) (congrArg (65536 * ·) (val16_congr fun i _ => ?_))
  rw [Nat.add_assoc]

/-- After the steps from the top limb down to limb `j`. -/
structure LimbInv (b : BitVec 32) (s0 : State) (j : Nat) (s : State) : Prop where
  positive : 0 < j
  bound : j ≤ 56
  counter : s.gpr .r10 = BitVec.ofNat 32 (4 * j)
  limbs : Lim28 s.mem (State.addr b) RA
  value : V28 s.mem (State.addr b) RA = accFrom s0.mem (State.addr b) j % L
  keeps : LoopKeep b RA s0 s

theorem limbLoop_ok {s0 : State} (hc : Ctx8 b s0) (h6 : s0.gpr .r6 = mask16)
    (hacc : ∀ j < 56, limb s0.mem (State.addr b) Impl.X448.Arm.ACC j < 65536)
    (h10 : s0.gpr .r10 = BitVec.ofNat 32 (4 * 56)) (hl : Lim28 s0.mem (State.addr b) RA)
    (hv : V28 s0.mem (State.addr b) RA = 0) :
    WP isa (.loop (.block limbStep) .ne) s0 fun t => LoopKeep b RA s0 t ∧
      Lim28 t.mem (State.addr b) RA ∧
      V28 t.mem (State.addr b) RA = val16 (limb s0.mem (State.addr b) Impl.X448.Arm.ACC) 56 % L := by
  have hA := ACC_eq
  have hT := TF_eq
  have hR : RA = 192 := rfl
  obtain ho : Buf RA := ⟨by omega_arith, by omega_arith⟩
  apply WP.loop (LimbInv b s0) (n := 56)
  · intro n s hi
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by have := hi.positive; omega_arith⟩
    have hj : j < 56 := hi.bound
    obtain hcs : Ctx8 b s := hc.of_rest hi.keeps.rest (by decide)
    obtain la : ∀ i < 56, limb s.mem (State.addr b) Impl.X448.Arm.ACC i =
        limb s0.mem (State.addr b) Impl.X448.Arm.ACC i := fun i hi' =>
      wd_frame hi.keeps.frame fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    unfold limbStep
    rw [List.append_assoc]
    refine WP.append (readLimb_ok hcs hj hi.counter) fun u ⟨ku, mu, cu, wu⟩ => ?_
    obtain hcu : Ctx8 b u := hcs.of_rest ku (by decide)
    obtain h6u : u.gpr .r6 = mask16 :=
      (ku.gpr _ (by decide)).trans ((hi.keeps.rest.gpr _ (by decide)).trans h6)
    obtain hwu : (u.gpr .r11).toNat < 65536 := by rw [wu, la j hj]; exact hacc j hj
    refine WP.append (step_ok ho hcu h6u (mu ▸ hi.limbs)
      (by rw [mu, hi.value]; exact Nat.mod_lt _ L_pos) hwu) fun v ⟨kv, lv, vv⟩ => ?_
    refine wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
    obtain val : V28 t.mem (State.addr b) RA = accFrom s0.mem (State.addr b) j % L := by
      rw [ht.mem, vv, wu, mu, hi.value, mod_fold, la j hj, accFrom_step _ _ hj]
    have keep : LoopKeep b RA s0 t := hi.keeps.trans
      ⟨(ku.mono (by decide)).trans ((kv.rest.mono (by decide)).trans (ht.rest _)),
        by rw [ht.mem, ← mu]; exact kv.frame⟩
    obtain c10 : t.gpr .r10 = BitVec.ofNat 32 (4 * j) := by
      rw [ht.gpr, kv.rest.gpr _ (by decide), cu]
    obtain zt : t.z = decide (j = 0) := by
      obtain he : BitVec.ofNat 32 (4 * j) - (0 : BitVec 32) = BitVec.ofNat 32 (4 * j) := BitVec.sub_zero _
      rw [hz, kv.rest.gpr _ (by decide), cu, he, ofNat_beq_zero (by omega_arith)]
      exact decide_eq_decide.mpr (by omega_arith)
    by_cases j0 : j = 0
    · subst j0
      refine .inl ⟨by rw [eval_ne, zt]; rfl, keep, ht.mem ▸ lv, ?_⟩
      rw [val]
      exact congrArg (· % L) (val16_congr fun i _ => by rw [Nat.zero_add])
    · refine .inr ⟨by rw [eval_ne, zt]; simp only [j0, decide_false, Bool.not_false], j, by omega_arith,
        ⟨by omega_arith, by omega_arith, c10, ht.mem ▸ lv, val, keep⟩⟩
  · refine ⟨by decide, by decide, h10, hl, ?_, LoopKeep.refl _ _ _⟩
    rw [hv]
    exact (Nat.zero_mod _).symm.trans (by rfl)

/-! ## The remainders the loops start from -/

theorem zeroR_ok {o : Nat} (ho : o + 112 ≤ 4096) {s : State} (hc : Ctx8 b s) :
    WP isa (.block (zeroR o)) s fun t =>
      Rest [.r3] s t ∧ Frame [limbsR b o] s.mem t.mem ∧ ∀ k < 28, limb t.mem (State.addr b) o k = 0 := by
  unfold zeroR
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  obtain hc1 := hc.of_rest (u1.rest (ws := [.r3]) (by decide)) (by decide)
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n t => Rest [] s1 t ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 4 * n⟩] s1.mem t.mem ∧
      ∀ k < n, limb t.mem (State.addr b) o k = 0)
    (fun n t hn ⟨h1, h2, h3⟩ => ?_) 28 (Nat.le_refl _) s1
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun t ⟨h1, h2, h3⟩ => ⟨(u1.rest (by decide)).trans (h1.mono (by decide)),
      by rw [← u1.mem]; exact h2, h3⟩
  refine str0_ok (hc1.of_rest h1 (by decide)) (d := o + 4 * n) (by omega_arith) fun t2 v2 =>
    WP.block_nil ⟨h1.trans (v2.rest _), ?_, fun k hk => ?_⟩
  · rw [v2.mem]
    exact (h2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_arith)⟩).writeW
      (List.mem_singleton_self _) (t.gpr .r3)
      (Offset.contains _ (d := o + 4 * n) (n := 4) (e := o) (k := 4 * (n + 1)) (by omega_arith) (by omega_arith)
        (by omega_arith))
  · show wd t2.mem _ _ = 0
    rw [v2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact h3 k hk
    · rw [wd_write_self, h1.gpr _ (by decide), u1.gpr]; rfl

theorem V28_zero {m : Mem} {B : Addr} {o : Nat} (h : ∀ k < 28, limb m B o k = 0) : V28 m B o = 0 :=
  (val16_congr h).trans (val16_zero_fn 28)

theorem Lim28_zero {m : Mem} {B : Addr} {o : Nat} (h : ∀ k < 28, limb m B o k = 0) : Lim28 m B o :=
  fun k hk => by rw [h k hk]; decide


end

end VG.Proof.Ed448.Arm

end

end


/-!
# Ed448 scalar arithmetic on ARMv7: entry and exit

The callee-saved registers saved in the working space (`saveAt_ok`) and
restored (`restore_ok`), the remainders the input loops start from
(`reduce114_ok`, `reduce57_ok`), and the result: the remainder's limbs as 56
bytes and a zero byte (`pack_ok`), which are its encoding (`encode_57`).
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X25519.Arm
open VG.Spec.Ed448 (L bytesAt decodeLE encodeLE)

/-- The registers `g` saved at `[0, 32)` of the working space at `B`. -/
def Saved (B : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  ∀ i < 8, m.readW (B + BitVec.ofNat 64 (4 * i)) 32 = g (savedReg i)

section
variable {b : BitVec 32}

theorem saveAt_ok {s : State} {base : Reg} (h3 : s.gpr base = b) (hfit : b.toNat + 8192 ≤ 2 ^ 32)
    (hw : (⟨State.addr b, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block (saveAt base)) s fun s' =>
      Saved (State.addr b) s.gpr s'.mem ∧ Frame [⟨State.addr b, 32⟩] s.mem s'.mem ∧
        s'.gpr = s.gpr ∧ Rest [] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.mem.readW (State.addr b + BitVec.ofNat 64 (4 * i)) 32 = s.gpr (savedReg i)) ∧
      Frame [⟨State.addr b, 4 * n⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s')
    (fun n s' hn ⟨h1, h2, h3', h4⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, rfl, Rest.refl _ _⟩)
    fun s' h => ⟨h.1, h.2.1, h.2.2⟩
  refine wp_str (a := State.addr b + BitVec.ofNat 64 (4 * n)) (by omega_arith)
    (by rw [h3', h3]; exact addr_add (by omega_arith)) (by rw [h4.wr]; exact in_base hw (by omega_arith) (by omega_arith))
    fun s2 u2 => WP.block_nil ⟨fun i hi => ?_, ?_, by rw [u2.gpr, h3'], h4.trans (u2.rest _)⟩
  · rw [u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]; exact h1 i hi
    · rw [Mem.readW_writeW_self32, h3']
  · rw [u2.mem]
    exact (h2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_arith)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))

theorem restore_ok {s : State} (hc : Ctx8 b s) {g : Reg → BitVec 32} (hs : Saved (State.addr b) g s.mem) :
    WP isa (.block restore) s fun s' => (∀ i < 8, s'.gpr (savedReg i) = g (savedReg i)) ∧
      Rest [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s' ∧ s'.mem = s.mem := by
  obtain hsr : ∀ i < 8, savedReg i ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] := by decide
  obtain hinj : ∀ i < 8, ∀ j < 8, savedReg i = savedReg j → i = j := by decide
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.gpr (savedReg i) = g (savedReg i)) ∧
      Rest [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s' ∧ s'.mem = s.mem)
    (fun n s' hn ⟨hl, hr, hm⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Rest.refl _ _, rfl⟩) fun s' h => h
  refine ldr0_ok (hc.of_rest hr (by decide)) (d := 4 * n) (by omega_arith) fun s1 u1 =>
    WP.block_nil ⟨fun i hi => ?_, hr.trans (u1.rest (hsr n hn)), by rw [u1.mem, hm]⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
  · rw [u1.other _ (fun e => absurd (hinj _ (by omega_arith) _ hn e) (by omega_arith))]; exact hl i h'
  · rw [u1.gpr, hm, hs i hn]

/-- The saved registers stay where no code writes. -/
theorem Saved.frame {g : Reg → BitVec 32} {m m' : Mem} (hs : Saved (State.addr b) g m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, ∀ i < 8, Region.Disjoint ⟨State.addr b + BitVec.ofNat 64 (4 * i), 4⟩ r) :
    Saved (State.addr b) g m' := fun i hi => by
  rw [hf.readW (Region.contains_self _ _) (fun r hr => hd r hr i hi) (by decide)]; exact hs i hi

/-! ## The remainders of the inputs -/

theorem init114_ok {o : Nat} (ho : Buf o) {s : State} (hc : Ctx8 b s) :
    WP isa (.block (zeroR o ++ ([.mov .r10 (.imm 114)] : List Instr))) s fun v => LoopKeep b o s v ∧
      v.gpr .r10 = BitVec.ofNat 32 114 ∧ Lim28 v.mem (State.addr b) o ∧ V28 v.mem (State.addr b) o = 0 :=
  WP.append (zeroR_ok ho.2 hc) fun u ⟨ku, fu, zu⟩ =>
    wp_mov (op2_imm (by decide)) fun v hv => WP.block_nil
      ⟨⟨(ku.mono (by decide)).trans (hv.rest (by decide)), by rw [hv.mem]; exact fu.mono (by simp)⟩,
        hv.gpr, by rw [hv.mem]; exact Lim28_zero zu, by rw [hv.mem]; exact V28_zero zu⟩

/-- The bytes of an input across a frame of regions it does not overlap. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {N : Nat}
    (hd : ∀ r ∈ rs, (⟨p, N⟩ : Region).Disjoint r) (hN : N ≤ 2 ^ 64) :
    bytesAt m' p N = bytesAt m p N := by
  unfold bytesAt; apply List.map_congr_left
  intro n hn
  exact hf.bytes hd hN (List.mem_range.mp hn)

theorem reduce114_ok {o : Nat} (ho : Buf o) {p : BitVec 32} {s : State} (hc : Ctx8 b s)
    (h6 : s.gpr .r6 = mask16) (hp : s.gpr .r12 = p) (hfit : p.toNat + 114 ≤ 2 ^ 32)
    (hread : ∀ i < 114, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1)
    (hsep : ∀ r ∈ [limbsR b TF, limbsR b o], (⟨State.addr p, 114⟩ : Region).Disjoint r) :
    WP isa (reduce114 o) s fun t => LoopKeep b o s t ∧ Lim28 t.mem (State.addr b) o ∧
      V28 t.mem (State.addr b) o = decodeLE (bytesAt s.mem (State.addr p) 114) % L := by
  unfold reduce114
  refine WP.seq (WP.mono (init114_ok ho hc) fun v ⟨kv, cv, lv, vv⟩ => ?_)
  obtain mb := bytesAt_frame kv.frame hsep (by decide)
  refine WP.mono (byteLoop_ok (N := 114) ho (hc.of_rest kv.rest (by decide))
    ((kv.rest.gpr _ (by decide)).trans h6) ((kv.rest.gpr _ (by decide)).trans hp) hfit
    (by rw [kv.rest.rd, kv.rest.wr]; exact hread) hsep (n0 := 114) (by decide) (by decide)
    (by decide) cv lv (by rw [vv, List.drop_eq_nil_of_le (by rw [bytesAt_length]), show decodeLE [] = 0 from rfl,
      Nat.zero_mod]))
    fun t ⟨kt, lt, vt⟩ => ⟨kv.trans kt, lt, by rw [vt, mb]⟩

theorem init57_ok {o : Nat} (ho : Buf o) {p : BitVec 32} {s : State} (hc : Ctx8 b s)
    (hp : s.gpr .r12 = p) (hfit : p.toNat + 57 ≤ 2 ^ 32)
    (hread : ∀ i < 57, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1)
    (hsep : ∀ r ∈ [limbsR b TF, limbsR b o], (⟨State.addr p, 57⟩ : Region).Disjoint r) :
    WP isa (.block (zeroR o ++ ([.ldrb .r3 .r12 56, .str .r3 .r0 o, .mov .r10 (.imm 56)] : List Instr))) s fun v =>
      LoopKeep b o s v ∧ v.gpr .r10 = BitVec.ofNat 32 56 ∧ Lim28 v.mem (State.addr b) o ∧
      V28 v.mem (State.addr b) o = decodeLE ((bytesAt s.mem (State.addr p) 57).drop 56) % L := by
  obtain ⟨ho1, ho2⟩ := ho
  have hT := TF_eq
  refine WP.append (zeroR_ok ho2 hc) fun u ⟨ku, fu, zu⟩ => ?_
  obtain hpu : u.gpr .r12 = p := (ku.gpr _ (by decide)).trans hp
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 56) (by decide)
    (by rw [hpu]; exact addr_add (by omega_arith)) (by rw [ku.rd, ku.wr]; exact hread 56 (by decide))
    fun u1 v1 => ?_
  refine str0_ok (hc.of_rest (ku.trans (v1.rest (ws := [.r3]) (by decide))) (by decide)) (d := o)
    (by omega_arith) fun u2 v2 => wp_mov (op2_imm (by decide)) fun v hv => WP.block_nil ?_
  obtain m2 : v.mem = u.mem.writeW (State.addr b + BitVec.ofNat 64 (o + 4 * 0))
      ((u.mem (State.addr p + BitVec.ofNat 64 56)).setWidth 32) := by
    rw [hv.mem, v2.mem, v1.gpr, v1.mem]; rfl
  obtain lv : ∀ k < 28, limb v.mem (State.addr b) o k =
      if k = 0 then (u.mem (State.addr p + BitVec.ofNat 64 56)).toNat else 0 := by
    intro k hk
    show wd v.mem _ _ = _
    rw [m2]
    by_cases k0 : k = 0
    · subst k0
      rw [wd_write_self, BitVec.toNat_setWidth_of_le (by decide)]; rfl
    · rw [wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), ite_eq_right k0]; exact zu k hk
  obtain fv : Frame [limbsR b o] s.mem v.mem := by
    rw [m2]
    exact fu.writeW (List.mem_singleton_self _) _ (Offset.contains _ (d := o + 4 * 0) (n := 4) (e := o)
      (k := 112) (by omega_arith) (by omega_arith) (by omega_arith))
  obtain hbyte : (u.mem (State.addr p + BitVec.ofNat 64 56)).toNat =
      (s.mem (State.addr p + BitVec.ofNat 64 56)).toNat := by
    rw [fu.bytes (R := ⟨State.addr p, 57⟩) (fun r hr => hsep r (by
      simp only [List.mem_singleton] at hr; simp [hr])) (by show 57 ≤ 2 ^ 64; omega_arith) (by decide : 56 < 57)]
  obtain hlt := (u.mem (State.addr p + BitVec.ofNat 64 56)).isLt
  refine ⟨⟨((ku.mono (by decide)).trans ((v1.rest (by decide)).trans ((v2.rest _).trans
    (hv.rest (by decide))))), fv.mono (by simp)⟩, hv.gpr, fun k hk => ?_, ?_⟩
  · rw [lv k hk]; split
    · omega_arith
    · decide
  · rw [decode_drop1 _ _ (by decide : 56 + 1 = 57), ← hbyte]
    obtain hL : 256 < L := by decide +kernel
    rw [Nat.mod_eq_of_lt (by omega_arith)]
    unfold V28
    rw [show (28 : Nat) = 1 + 27 from rfl, val16_append,
      val16_congr (n := 27) (g := fun _ => 0) (fun k hk => by rw [lv _ (by omega_arith), ite_eq_right (by omega_arith)]),
      val16_zero_fn]
    simp only [val16, lv 0 (by decide), ite_true, Nat.mul_zero, Nat.pow_zero, Nat.one_mul,
      Nat.zero_add, Nat.add_zero]

theorem reduce57_ok {o : Nat} (ho : Buf o) {p : BitVec 32} {s : State} (hc : Ctx8 b s)
    (h6 : s.gpr .r6 = mask16) (hp : s.gpr .r12 = p) (hfit : p.toNat + 57 ≤ 2 ^ 32)
    (hread : ∀ i < 57, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1)
    (hsep : ∀ r ∈ [limbsR b TF, limbsR b o], (⟨State.addr p, 57⟩ : Region).Disjoint r) :
    WP isa (reduce57 o) s fun t => LoopKeep b o s t ∧ Lim28 t.mem (State.addr b) o ∧
      V28 t.mem (State.addr b) o = decodeLE (bytesAt s.mem (State.addr p) 57) % L := by
  unfold reduce57
  refine WP.seq (WP.mono (init57_ok ho hc hp hfit hread hsep) fun v ⟨kv, cv, lv, vv⟩ => ?_)
  obtain mb := bytesAt_frame kv.frame hsep (by decide)
  refine WP.mono (byteLoop_ok (N := 57) ho (hc.of_rest kv.rest (by decide))
    ((kv.rest.gpr _ (by decide)).trans h6) ((kv.rest.gpr _ (by decide)).trans hp) hfit
    (by rw [kv.rest.rd, kv.rest.wr]; exact hread) hsep (n0 := 56) (by decide) (by decide)
    (by decide) cv lv (by rw [vv, mb])) fun t ⟨kt, lt, vt⟩ => ⟨kv.trans kt, lt, by rw [vt, mb]⟩

/-! ## The result -/

theorem byte_eq {v : BitVec 32} {n : Nat} (h : v.toNat = n) : v.setWidth 8 = BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, h]

/-- After `k` limbs of `packLimb`. -/
structure PackInv (q : Addr) (f : Nat → Nat) (s0 : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.r3] s0 s
  frame : Frame [⟨q, 2 * k⟩] s0.mem s.mem
  b0 : ∀ i < k, s.mem (q + BitVec.ofNat 64 (2 * i)) = BitVec.ofNat 8 (f i)
  b1 : ∀ i < k, s.mem (q + BitVec.ofNat 64 (2 * i + 1)) = BitVec.ofNat 8 (f i / 256)

theorem pack_ok {q : BitVec 32} {o : Nat} (ho : o + 112 ≤ 4096) {s0 : State} (hc : Ctx8 b s0)
    (hq : s0.gpr .r12 = q) (hfit : q.toNat + 57 ≤ 2 ^ 32)
    (hw : (⟨State.addr q, 57⟩ : Region) ∈ s0.wr)
    (hsep : (⟨State.addr q, 57⟩ : Region).Disjoint ⟨State.addr b, 8192⟩) :
    WP isa (.block ((List.range 28).flatMap (packLimb o))) s0
      (PackInv (State.addr q) (limb s0.mem (State.addr b) o) s0 28) := by
  let O := State.addr q
  refine wp_range_flatMap (M := isa) (PackInv O (limb s0.mem (State.addr b) o) s0)
    (fun k s hk h => ?_) 28 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => by omega_arith, fun _ h => by omega_arith⟩
  obtain hcs := hc.of_rest h.rest (by decide)
  obtain hq' : s.gpr .r12 = q := (h.rest.gpr _ (by decide)).trans hq
  obtain he : wd s.mem (State.addr b) (o + 4 * k) = limb s0.mem (State.addr b) o k :=
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (hsep.symm.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Region.sub_prefix (by omega_arith))
  unfold packLimb
  refine ldr0_ok hcs (by omega_arith) fun s1 u1 => ?_
  obtain e1 : (s1.gpr .r3).toNat = limb s0.mem (State.addr b) o k := by rw [u1.gpr]; exact he
  refine wp_strb (a := O + BitVec.ofNat 64 (2 * k)) (by omega_arith)
    (by rw [u1.other _ (by decide), hq', addr_add (by omega_arith)])
    (by rw [u1.wr, h.rest.wr]; exact in_base hw (by omega_arith) (by omega_arith))
    fun s2 u2 => wp_mov (op2_lsr (by decide)) fun s3 u3 => ?_
  refine wp_strb (a := O + BitVec.ofNat 64 (2 * k + 1)) (by omega_arith)
    (by rw [u3.other _ (by decide), u2.gpr, u1.other _ (by decide), hq', addr_add (by omega_arith)])
    (by rw [u3.wr, u2.wr, u1.wr, h.rest.wr]; exact in_base hw (by omega_arith) (by omega_arith))
    fun t ht => WP.block_nil ?_
  obtain hm : t.mem = (s.mem.writeW (O + BitVec.ofNat 64 (2 * k)) ((s1.gpr .r3).setWidth 8)).writeW
      (O + BitVec.ofNat 64 (2 * k + 1)) ((s1.gpr .r3 >>> 8).setWidth 8) := by
    rw [ht.mem, u3.gpr, u2.gpr, u3.mem, u2.mem, u1.mem]
  obtain ne : ∀ i j : Nat, i < 57 → j < 57 → i ≠ j → O + BitVec.ofNat 64 i ≠ O + BitVec.ofNat 64 j :=
    fun i j hi hj hij => Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) hij
  refine ⟨h.rest.trans ((u1.rest (by decide)).trans ((u2.rest _).trans
    ((u3.rest (by decide)).trans (ht.rest _)))), ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hm]
    refine ((h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_arith)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  · rw [hm, VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply,
      ite_eq_right (ne _ _ (by omega_arith) (by omega_arith) (by omega_arith))]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right (ne _ _ (by omega_arith) (by omega_arith) (by omega_arith))]; exact h.b0 i hi
    · rw [ite_eq_left rfl]; exact byte_eq e1
  · rw [hm, VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right (ne _ _ (by omega_arith) (by omega_arith) (by omega_arith)),
        ite_eq_right (ne _ _ (by omega_arith) (by omega_arith) (by omega_arith))]
      exact h.b1 i hi
    · rw [ite_eq_left rfl]; exact byte_eq (by rw [toNat_shr, e1])

/-- Twenty-eight 16-bit limbs and a zero byte are the 57-byte encoding of
their number. -/
theorem encode_57 {m : Mem} {q : Addr} {f : Nat → Nat} (hl : ∀ k < 28, f k < 65536)
    (h0 : ∀ k < 28, m (q + BitVec.ofNat 64 (2 * k)) = BitVec.ofNat 8 (f k))
    (h1 : ∀ k < 28, m (q + BitVec.ofNat 64 (2 * k + 1)) = BitVec.ofNat 8 (f k / 256))
    (h56 : m (q + BitVec.ofNat 64 56) = 0) :
    bytesAt m q 57 = encodeLE 57 (val16 f 28) := by
  let g : Nat → Nat := fun k => if k < 28 then f k else 0
  obtain hg : ∀ k < 29, g k < 65536 := fun k _ => by
    simp only [g]; split
    · exact hl k (by omega_arith)
    · decide
  obtain hv : val16 f 28 = val16 g 29 := by
    obtain e1 := val16_succ g 28
    have e2 : g 28 = 0 := rfl
    rw [e2] at e1
    obtain e3 : val16 f 28 = val16 g 28 := val16_congr fun k hk => (ite_eq_left hk).symm
    exact e3.trans ((Nat.add_zero _).symm.trans
      ((congrArg (val16 g 28 + ·) (Nat.mul_zero _).symm).trans e1.symm))
  apply List.ext_getElem (by rw [bytesAt_length]; simp only [encodeLE, List.length_map, List.length_range])
  intro i hi _
  rw [bytesAt_length] at hi
  simp only [bytesAt, encodeLE, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, hv]
  obtain ⟨k, rfl | rfl⟩ : ∃ k, i = 2 * k ∨ i = 2 * k + 1 := ⟨i / 2, by omega_arith⟩
  · have hd := val16_div hg (k := k) (by omega_arith)
    rw [show 8 * (2 * k) = 16 * k by omega_arith, ← Nat.mod_mod_of_dvd _ (by decide : 256 ∣ 65536), hd]
    by_cases hk : k < 28
    · rw [h0 k hk, BitVec.toNat_ofNat, show g k = f k from ite_eq_left hk]
    · rw [show 2 * k = 56 by omega_arith, h56, show g k = 0 from ite_eq_right hk]; rfl
  · have hk : k < 28 := by omega_arith
    obtain hd := val16_div hg (k := k) (by omega_arith)
    rw [show 8 * (2 * k + 1) = 16 * k + 8 by omega_arith, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      show (2 : Nat) ^ 8 = 256 from rfl, h1 k hk, BitVec.toNat_ofNat,
      ← Nat.mod_mul_right_div_self (val16 g 29 / 2 ^ (16 * k)) 256 256,
      show (256 : Nat) * 256 = 65536 from rfl, hd, show g k = f k from ite_eq_left hk]
    have := hl k hk
    omega_arith

theorem OUT_eq : OUT = 32 := rfl

/-- `output o`: the remainder at `o` as 57 bytes at `r12`, and the
callee-saved registers restored. -/
theorem output_ok {q : BitVec 32} {o : Nat} (ho : o + 112 ≤ 4096) {s : State} (hc : Ctx8 b s)
    (hl : Lim28 s.mem (State.addr b) o) (hq : s.gpr .r12 = q) (hfit : q.toNat + 57 ≤ 2 ^ 32)
    (hw : (⟨State.addr q, 57⟩ : Region) ∈ s.wr)
    (hsep : (⟨State.addr q, 57⟩ : Region).Disjoint ⟨State.addr b, 8192⟩)
    {g : Reg → BitVec 32} (hs : Saved (State.addr b) g s.mem) :
    WP isa (.block (output o)) s fun t =>
      (∀ i < 8, t.gpr (savedReg i) = g (savedReg i)) ∧
      Rest [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s t ∧
      Frame [⟨State.addr q, 57⟩] s.mem t.mem ∧
      bytesAt t.mem (State.addr q) 57 = encodeLE 57 (V28 s.mem (State.addr b) o) := by
  unfold output
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (pack_ok (q := q) (o := o) ho hc hq hfit hw hsep) fun v hv => ?_
  obtain hcv := hc.of_rest hv.rest (by decide)
  refine wp_mov (op2_imm (by decide)) fun v1 w1 => ?_
  refine wp_strb (a := State.addr q + BitVec.ofNat 64 56) (by decide)
    (by rw [w1.other _ (by decide), hv.rest.gpr _ (by decide), hq]; exact addr_add (by omega_arith))
    (by rw [w1.wr, hv.rest.wr]; exact in_base hw (by decide) (by decide)) fun v2 w2 => ?_
  obtain m2 : v2.mem = v.mem.writeW (State.addr q + BitVec.ofNat 64 56) (0 : BitVec 8) := by
    rw [w2.mem, w1.gpr, w1.mem]; rfl
  obtain f2 : Frame [⟨State.addr q, 57⟩] s.mem v2.mem := by
    rw [m2]
    refine (?_ : Frame [⟨State.addr q, 57⟩] s.mem v.mem).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by decide) (by decide))
    exact hv.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩
  obtain hcv2 := hcv.of_rest ((w1.rest (ws := [.r3])  (by decide)).trans (w2.rest _)) (by decide)
  obtain hs2 : Saved (State.addr b) g v2.mem :=
    hs.frame f2 fun r hr i hi => by
      rw [List.mem_singleton.mp hr]
      exact (hsep.symm.sub_left (Offset.sub_base _ (by omega_arith)))
  refine WP.mono (restore_ok hcv2 hs2) fun t ⟨gt, kt, mt⟩ => ?_
  obtain ne : ∀ i j : Nat, i < 57 → j < 57 → i ≠ j →
      State.addr q + BitVec.ofNat 64 i ≠ State.addr q + BitVec.ofNat 64 j :=
    fun i j hi hj hij => Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) hij
  refine ⟨gt, (hv.rest.mono (by decide)).trans ((w1.rest (by decide)).trans
    ((w2.rest _).trans (kt.mono (by decide)))), by rw [mt]; exact f2, ?_⟩
  rw [mt]
  refine encode_57 (fun k hk => hl k hk) (fun k hk => ?_) (fun k hk => ?_) ?_
  · rw [m2, VG.WriteBytes.writeW8_apply, ite_eq_right (ne _ _ (by omega_arith) (by decide) (by omega_arith))]
    exact hv.b0 k hk
  · rw [m2, VG.WriteBytes.writeW8_apply, ite_eq_right (ne _ _ (by omega_arith) (by decide) (by omega_arith))]
    exact hv.b1 k hk
  · rw [m2, VG.WriteBytes.writeW8_apply, ite_eq_left rfl]

/-- `finish o`: `output o` to the output's address, saved at `OUT`. -/
theorem finish_ok {q : BitVec 32} {o : Nat} (ho : o + 112 ≤ 4096) {s : State} (hc : Ctx8 b s)
    (hl : Lim28 s.mem (State.addr b) o)
    (hq : s.mem.readW (State.addr b + BitVec.ofNat 64 OUT) 32 = q) (hfit : q.toNat + 57 ≤ 2 ^ 32)
    (hw : (⟨State.addr q, 57⟩ : Region) ∈ s.wr)
    (hsep : (⟨State.addr q, 57⟩ : Region).Disjoint ⟨State.addr b, 8192⟩)
    {g : Reg → BitVec 32} (hs : Saved (State.addr b) g s.mem) :
    WP isa (.block (finish o)) s fun t =>
      (∀ i < 8, t.gpr (savedReg i) = g (savedReg i)) ∧
      Rest [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] s t ∧
      Frame [⟨State.addr q, 57⟩] s.mem t.mem ∧
      bytesAt t.mem (State.addr q) 57 = encodeLE 57 (V28 s.mem (State.addr b) o) := by
  have hO := OUT_eq
  unfold finish
  refine ldr0_ok hc (d := OUT) (by omega_arith) fun u hu => ?_
  obtain hcu := hc.of_rest (hu.rest (ws := [.r12]) (by decide)) (by decide)
  refine WP.mono (output_ok ho hcu (hu.mem ▸ hl) (by rw [hu.gpr, hq]) hfit (by rw [hu.wr]; exact hw)
    hsep (hu.mem ▸ hs)) fun t ⟨gt, kt, ft, bt⟩ => ⟨gt, (hu.rest (by decide)).trans (kt.mono (by decide)),
      by rw [← hu.mem]; exact ft, by rw [bt, hu.mem]⟩

end

end VG.Proof.Ed448.Arm

end

end

/-!
# Ed448 scalar reduction on ARMv7: the whole function

`vg_ed448_scalar_reduce(out = r0, wide = r1, scratch = r2)` against a local
contract (`scalarReduceLocal`), the ABI included.
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X25519.Arm
open VG.Spec.Ed448 (L bytesAt decodeLE encodeLE)

def scalarReduceLocal : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 57⟩
    let wide : Region := ⟨State.addr (s.gpr .r1), 114⟩
    let ws : Region := ⟨State.addr (s.gpr .r2), 8192⟩
    s.rd = [wide] ∧ s.wr = [out, ws] ∧ out.Disjoint wide ∧ out.Disjoint ws ∧
      wide.Disjoint ws ∧ (s.gpr .r0).toNat + 57 ≤ 2 ^ 32 ∧
      (s.gpr .r1).toNat + 114 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32
  post s t := bytesAt t.mem (State.addr (s.gpr .r0)) 57 =
    Spec.Ed448.scalarReduce (bytesAt s.mem (State.addr (s.gpr .r1)) 114)
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2

structure ReducePre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r1), 114⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r0), 57⟩, ⟨State.addr (s.gpr .r2), 8192⟩]
  out_wide : (⟨State.addr (s.gpr .r0), 57⟩ : Region).Disjoint ⟨State.addr (s.gpr .r1), 114⟩
  out_ws : (⟨State.addr (s.gpr .r0), 57⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩
  wide_ws : (⟨State.addr (s.gpr .r1), 114⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩
  f0 : (s.gpr .r0).toNat + 57 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 114 ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32

theorem ReducePre.of {s : State} (h : scalarReduceLocal.pre s) : ReducePre s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem ctx8_of {b : BitVec 32} {s : State} (h0 : s.gpr .r0 = b) (hfit : b.toNat + 8192 ≤ 2 ^ 32)
    (hw : (⟨State.addr b, 8192⟩ : Region) ∈ s.wr) : Ctx8 b s := ⟨h0, hfit, hw⟩

theorem reduceSetup_ok {s : State} (h : ReducePre s) :
    WP isa (.block (saveAt .r2 ++ ([.str .r0 .r2 OUT, .mov .r0 (.reg .r2), .mov .r12 (.reg .r1),
      .movw .r6 0xffff] : List Instr))) s fun t =>
      Ctx8 (s.gpr .r2) t ∧ t.gpr .r6 = mask16 ∧ t.gpr .r12 = s.gpr .r1 ∧
      Saved (State.addr (s.gpr .r2)) s.gpr t.mem ∧
      t.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 OUT) 32 = s.gpr .r0 ∧
      Rest [.r0, .r6, .r12] s t ∧ Frame [⟨State.addr (s.gpr .r2), 36⟩] s.mem t.mem := by
  have hw : (⟨State.addr (s.gpr .r2), 8192⟩ : Region) ∈ s.wr := by rw [h.wr]; simp
  have hO := OUT_eq
  refine WP.append (saveAt_ok rfl h.f2 hw) fun u ⟨su, fu, gu, ku⟩ => ?_
  refine wp_str (a := State.addr (s.gpr .r2) + BitVec.ofNat 64 32) (by decide)
    (by rw [gu]; exact addr_add (by have := h.f2; omega_using [hO, this]))
    (by rw [ku.wr]; exact in_base hw (by decide) (by decide)) fun v hv => ?_
  refine wp_mov (op2_reg _ _) fun w hw' => wp_mov (op2_reg _ _) fun x hx =>
    wp_movw fun t ht => WP.block_nil ?_
  have kt : Rest [.r0, .r6, .r12] s t :=
    (ku.mono (by decide)).trans ((hv.rest _).trans ((hw'.rest (by decide)).trans
      ((hx.rest (by decide)).trans (ht.rest (by decide)))))
  have mt : t.mem = u.mem.writeW (State.addr (s.gpr .r2) + BitVec.ofNat 64 32) (s.gpr .r0) := by
    rw [ht.mem, hx.mem, hw'.mem, hv.mem, gu]
  refine ⟨ctx8_of ?_ h.f2 (by rw [kt.wr]; exact hw), ht.gpr, ?_, ?_, ?_, kt, ?_⟩
  · rw [ht.other _ (by decide), hx.other _ (by decide), hw'.gpr, hv.gpr, gu]
  · rw [ht.other _ (by decide), hx.gpr, hw'.other _ (by decide), hv.gpr, gu]
  · intro i hi
    rw [mt, Mem.readW_writeW_sep (Offset.sep _ (d := 4 * i) (e := 32) (n := 4) (k := 4) (by omega_using [hi])
      (by omega_using [hi]) (by omega_using [])) (by decide)]
    exact su i hi
  · rw [mt]; exact Mem.readW_writeW_self32 _ _ _
  · rw [mt]
    exact (fu.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))

theorem RA_buf : Buf RA := ⟨by decide, by decide⟩

theorem reduce_regions_sub {b : BitVec 32} {r : Region} (h : r ∈ [limbsR b TF, limbsR b RA]) :
    r.Sub ⟨State.addr b, 8192⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> exact Offset.sub_base _ (by decide)

theorem scalarReduce_correct {s : State} (h : ReducePre s) :
    WP isa scalarReduce s fun t => abiPreserved s t ∧ scalarReduceLocal.post s t := by
  have hT := TF_eq
  have hO := OUT_eq
  have hR : RA = 192 := rfl
  unfold scalarReduce
  refine WP.seq (WP.mono (reduceSetup_ok h) fun u ⟨hcu, h6u, pu, su, ou, ku, fu⟩ => ?_)
  have wide : (⟨State.addr (s.gpr .r1), 114⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.rd]; simp
  refine WP.seq (WP.mono (reduce114_ok RA_buf hcu h6u pu h.f1
    (fun n hn => by rw [ku.rd, ku.wr]; exact in_base wide (by omega_using [hn]) (by omega_using [hn]))
    (fun r hr => h.wide_ws.sub_right (reduce_regions_sub hr))) fun v ⟨kv, lv, vv⟩ => ?_)
  have sv : Saved (State.addr (s.gpr .r2)) s.gpr v.mem :=
    su.frame kv.frame fun r hr i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_using [hi]) (by decide)
  have ov : v.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 OUT) 32 = s.gpr .r0 := by
    rw [kv.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), ou]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_using [hO]) (by decide)
  refine WP.mono (finish_ok (by decide) (hcu.of_rest kv.rest (by decide)) lv ov h.f0
    (by rw [kv.rest.wr, ku.wr, h.wr]; simp) h.out_ws sv) fun t ⟨gt, kt, _, bt⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [kt.sp, kv.rest.sp, ku.sp]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact gt 0 (by decide)
    · exact gt 1 (by decide)
    · exact gt 2 (by decide)
    · exact gt 3 (by decide)
    · exact gt 4 (by decide)
    · exact gt 5 (by decide)
    · exact gt 6 (by decide)
    · exact gt 7 (by decide)
    · rw [kt.gpr _ (by decide), kv.rest.gpr _ (by decide), ku.gpr _ (by decide)]
  · change bytesAt t.mem _ 57 = encodeLE 57 _
    rw [bt, vv]
    refine congrArg (fun bs => encodeLE 57 (decodeLE bs % L)) ?_
    exact bytesAt_frame fu (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact h.wide_ws.sub_right (Region.sub_prefix (by decide)))
      (by decide)

end VG.Proof.Ed448.Arm

end

end

/-! ### `Ed448.Arm.ScalarMulAdd`, which only this module used -/

section

/-!
# Ed448 scalar multiply-add on ARMv7

`vg_ed448_scalar_mul_add(out = r0, r = r1, k = r2, s = r3, scratch = [sp])`
against a local contract (`scalarMulAddLocal`), the ABI included: the three
inputs reduced (`reduceArg_ok`), the product of two with X448's rows
(`product_ok`), its limbs reduced (`reduceProduct_ok`), and the sum with the
third (`addPass_ok`) reduced once more.
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X25519.Arm
open VG.Spec.Ed448 (L bytesAt decodeLE encodeLE)

section
variable {b : BitVec 32}

/-! ## The arguments -/

/-- The argument registers `g (argReg i)` saved from `OUT` in the working space at `B`. -/
def Args (B : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  ∀ i < 4, m.readW (B + BitVec.ofNat 64 (OUT + 4 * i)) 32 = g (argReg i)

theorem storeArgs_ok {s : State} (h3 : s.gpr .r12 = b) (hfit : b.toNat + 8192 ≤ 2 ^ 32)
    (hw : (⟨State.addr b, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block ((List.range 4).flatMap fun i => [.str (argReg i) .r12 (OUT + 4 * i)])) s fun s' =>
      Args (State.addr b) s.gpr s'.mem ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 OUT, 16⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s' := by
  have hO := OUT_eq
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.mem.readW (State.addr b + BitVec.ofNat 64 (OUT + 4 * i)) 32 =
        s.gpr (argReg i)) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 OUT, 4 * n⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s')
    (fun n s' hn ⟨h1, h2, h3', h4⟩ => ?_) 4 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, rfl, Rest.refl _ _⟩)
    fun s' h => ⟨h.1, h.2.1, h.2.2⟩
  refine wp_str (a := State.addr b + BitVec.ofNat 64 (OUT + 4 * n)) (by omega_arith)
    (by rw [h3', h3]; exact addr_add (by omega_arith)) (by rw [h4.wr]; exact in_base hw (by omega_arith) (by omega_arith))
    fun s2 u2 => WP.block_nil ⟨fun i hi => ?_, ?_, by rw [u2.gpr, h3'], h4.trans (u2.rest _)⟩
  · rw [u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]; exact h1 i hi
    · rw [Mem.readW_writeW_self32, h3']
  · rw [u2.mem]
    exact (h2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_arith)⟩).writeW
      (List.mem_singleton_self _) _
      (Offset.contains _ (d := OUT + 4 * n) (n := 4) (e := OUT) (k := 4 * (n + 1)) (by omega_arith)
        (by omega_arith) (by omega_arith))

theorem ldrSp_ok {s : State} {is : List Instr} {Q : State → Prop}
    (hr : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (k : ∀ t, Upd s t .r12 (stackArg s 0) → WP isa (.block is) t Q) :
    WP isa (.block (.ldrSp .r12 0 :: is)) s Q := by
  refine WP.cons (s' := s.setReg .r12 (stackArg s 0)) ?_ (k _ (Upd.setReg _ _ _))
  simp only [exec, show (0 : Nat) < 4096 from by decide, ite_true, State.load32,
    BitVec.add_zero, hr, Option.map_some]
  simp [stackArg, stackArgAddr]

theorem mulAddArgs_ok {s : State} (hr : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (hfit : (stackArg s 0).toNat + 8192 ≤ 2 ^ 32)
    (hw : (⟨State.addr (stackArg s 0), 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block mulAddArgs) s fun t =>
      Ctx8 (stackArg s 0) t ∧ t.gpr .r6 = mask16 ∧ Saved (State.addr (stackArg s 0)) s.gpr t.mem ∧
      Args (State.addr (stackArg s 0)) s.gpr t.mem ∧ Rest [.r0, .r6, .r12] s t ∧
      Frame [⟨State.addr (stackArg s 0), 48⟩] s.mem t.mem := by
  have hO := OUT_eq
  unfold mulAddArgs
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine ldrSp_ok hr fun u hu => ?_
  refine WP.append (saveAt_ok hu.gpr hfit (hu.wr ▸ hw)) fun v ⟨sv, fv, gv, kv⟩ => ?_
  refine WP.append (storeArgs_ok (by rw [gv]; exact hu.gpr) hfit
    (by rw [kv.wr, hu.wr]; exact hw)) fun w ⟨aw, fw, gw, kw⟩ => ?_
  refine wp_mov (op2_reg _ _) fun x hx => wp_movw fun t ht => WP.block_nil ?_
  obtain kt : Rest [.r0, .r6, .r12] s t := (hu.rest (by decide)).trans
    ((kv.mono (by decide)).trans ((kw.mono (by decide)).trans ((hx.rest (by decide)).trans
      (ht.rest (by decide)))))
  obtain mt : t.mem = w.mem := by rw [ht.mem, hx.mem]
  refine ⟨⟨?_, hfit, by rw [kt.wr]; exact hw⟩, ht.gpr, ?_, ?_, kt, ?_⟩
  · rw [ht.other _ (by decide), hx.gpr, gw, gv, hu.gpr]
  · have sn : ∀ i < 8, savedReg i ≠ .r12 := by decide
    intro i hi
    rw [mt, fw.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), sv i hi]
    · exact hu.other _ (sn i hi)
    · rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by decide)
  · have an : ∀ i < 4, argReg i ≠ .r12 := by decide
    intro i hi
    rw [mt, aw i hi, gv]
    exact hu.other _ (an i hi)
  · rw [mt, ← hu.mem]
    exact (fv.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩).trans
      (fw.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by decide)⟩)

/-! ## The inputs -/

theorem reduceArg_ok {o off : Nat} (ho : Buf o) (hoff : off + 4 ≤ 64) {p : BitVec 32} {s : State}
    (hc : Ctx8 b s) (h6 : s.gpr .r6 = mask16)
    (hp : s.mem.readW (State.addr b + BitVec.ofNat 64 off) 32 = p) (hfit : p.toNat + 57 ≤ 2 ^ 32)
    (hr : (⟨State.addr p, 57⟩ : Region) ∈ s.rd ++ s.wr)
    (hsep : (⟨State.addr p, 57⟩ : Region).Disjoint ⟨State.addr b, 8192⟩) :
    WP isa (reduceArg off o) s fun t => Rest [.r1, .r2, .r3, .r4, .r5, .r9, .r10, .r11, .r12] s t ∧
      Frame [limbsR b TF, limbsR b o] s.mem t.mem ∧ Lim28 t.mem (State.addr b) o ∧
      V28 t.mem (State.addr b) o = decodeLE (bytesAt s.mem (State.addr p) 57) % L := by
  have hT := TF_eq
  obtain ⟨ho1, ho2⟩ := ho
  unfold reduceArg
  obtain hld : WP isa (.block [.ldr .r12 .r0 off]) s fun u =>
      Rest [.r12] s u ∧ u.mem = s.mem ∧ u.gpr .r12 = p :=
    ldr0_ok hc (d := off) (by omega_arith) fun u hu => WP.block_nil ⟨hu.rest (by decide), hu.mem,
      by rw [hu.gpr, hp]⟩
  refine WP.seq (WP.mono hld fun u ⟨ku, mu, pu⟩ => ?_)
  refine WP.mono (reduce57_ok ⟨ho1, ho2⟩ (hc.of_rest ku (by decide)) ((ku.gpr _ (by decide)).trans h6) pu
    hfit (fun i hi => by rw [ku.rd, ku.wr]; exact in_base hr (by omega_arith) (by omega_arith))
    (fun r hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl <;> exact hsep.sub_right (Offset.sub_base _ (by omega_arith))))
    fun t ⟨kt, lt, vt⟩ => ⟨(ku.mono (by decide)).trans (kt.rest.mono (by decide)), by
      rw [← mu]; exact kt.frame, lt, by rw [vt, mu]⟩

/-! ## The product -/

theorem valN_eq (f : Nat → Nat) (n : Nat) : Proof.X448.Radix16.valN f n = val16 f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Proof.X448.Radix16.valN_succ, val16_succ, ih, Proof.X448.Radix16.radix, ← Nat.pow_mul]

theorem SK_eq : SK = 320 := rfl
theorem SS_eq : SS = 448 := rfl
theorem SR_eq : SR = 576 := rfl
theorem RA_eq : RA = 192 := rfl

theorem product_ok {s : State} (hc : Ctx8 b s) (h6 : s.gpr .r6 = mask16)
    (hk : Lim28 s.mem (State.addr b) SK) (hs : Lim28 s.mem (State.addr b) SS) :
    WP isa product s fun t => Rest [.r1, .r2, .r3, .r4, .r5, .r7, .r9] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 Impl.X448.Arm.ACC, 224⟩] s.mem t.mem ∧
      (∀ j < 56, limb t.mem (State.addr b) Impl.X448.Arm.ACC j < 65536) ∧
      val16 (limb t.mem (State.addr b) Impl.X448.Arm.ACC) 56 =
        V28 s.mem (State.addr b) SK * V28 s.mem (State.addr b) SS := by
  obtain hrc : Proof.X448.Arm.RowCtx b s := ⟨hc.r0, by have := hc.fit; omega_arith, hc.wr⟩
  unfold product
  refine WP.seq (WP.mono (Proof.X448.Arm.mulPre_ok (x := SK) (y := SS) hrc h6) fun u hu => ?_)
  refine WP.mono (Proof.X448.Arm.mulLoop_ok (by decide) (by decide) hk hs hu) fun t ht => ?_
  refine ⟨ht.rest, ht.frame, ht.lt, ?_⟩
  obtain e : val16 (limb t.mem (State.addr b) Impl.X448.Arm.ACC) 56 =
      Proof.X448.Radix16.valN (Proof.X448.Arm.accw t.mem (State.addr b)) (28 + 28) := (valN_eq _ _).symm
  obtain e' : Proof.X448.Radix16.valN (Proof.X448.Arm.limbs s.mem (State.addr b) SK) 28 *
      Proof.X448.Arm.fe s.mem (State.addr b) SS = V28 s.mem (State.addr b) SK * V28 s.mem (State.addr b) SS := by
    unfold Proof.X448.Arm.fe; rw [valN_eq, valN_eq]; rfl
  exact e.trans (ht.val.trans e')

theorem reduceProduct_ok {s : State} (hc : Ctx8 b s) (h6 : s.gpr .r6 = mask16)
    (hacc : ∀ j < 56, limb s.mem (State.addr b) Impl.X448.Arm.ACC j < 65536) :
    WP isa reduceProduct s fun t => LoopKeep b RA s t ∧ Lim28 t.mem (State.addr b) RA ∧
      V28 t.mem (State.addr b) RA = val16 (limb s.mem (State.addr b) Impl.X448.Arm.ACC) 56 % L := by
  have hA := ACC_eq
  have hR := RA_eq
  have hT := TF_eq
  unfold reduceProduct
  obtain hinit : WP isa (.block (zeroR RA ++ [.mov .r10 (.imm 224)])) s fun v => LoopKeep b RA s v ∧
      v.gpr .r10 = BitVec.ofNat 32 (4 * 56) ∧ Lim28 v.mem (State.addr b) RA ∧
      V28 v.mem (State.addr b) RA = 0 :=
    WP.append (zeroR_ok (o := RA) (by decide) hc) fun u ⟨ku, fu, zu⟩ =>
      wp_mov (op2_imm (by decide)) fun v hv => WP.block_nil
        ⟨⟨(ku.mono (by decide)).trans (hv.rest (by decide)), by rw [hv.mem]; exact fu.mono (by simp)⟩,
          hv.gpr, by rw [hv.mem]; exact Lim28_zero zu, by rw [hv.mem]; exact V28_zero zu⟩
  refine WP.seq (WP.mono hinit fun v ⟨kv, cv, lv, vv⟩ => ?_)
  obtain la : ∀ j < 56, limb v.mem (State.addr b) Impl.X448.Arm.ACC j =
      limb s.mem (State.addr b) Impl.X448.Arm.ACC j := fun j hj =>
    wd_frame kv.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine WP.mono (limbLoop_ok (hc.of_rest kv.rest (by decide)) ((kv.rest.gpr _ (by decide)).trans h6)
    (fun j hj => by rw [la j hj]; exact hacc j hj) cv lv vv) fun t ⟨kt, lt, vt⟩ =>
    ⟨kv.trans kt, lt, by rw [vt, val16_congr la]⟩

/-! ## The sum -/

theorem addPass_ok {s : State} (hc : Ctx8 b s) (h6 : s.gpr .r6 = mask16)
    (ha : Lim28 s.mem (State.addr b) RA) (hr : Lim28 s.mem (State.addr b) SR)
    (hva : V28 s.mem (State.addr b) RA < L) (hvr : V28 s.mem (State.addr b) SR < L) :
    WP isa (.block addPass) s fun t => Rest [.r2, .r3, .r4, .r5] s t ∧
      Frame [limbsR b TF] s.mem t.mem ∧ Lim28 t.mem (State.addr b) TF ∧
      V28 t.mem (State.addr b) TF = V28 s.mem (State.addr b) RA + V28 s.mem (State.addr b) SR := by
  have hT := TF_eq
  have hR := RA_eq
  have hS := SR_eq
  unfold addPass
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  obtain hc1 := hc.of_rest (u1.rest (ws := [.r5]) (by decide)) (by decide)
  have r0 : s1.gpr .r0 = b := hc1.r0
  refine WP.mono (VG.Proof.X448.Arm.carryPass_ok (rb := .r0) (o := TF) (s0 := s1)
    (c := fun k => limb s.mem (State.addr b) RA k + limb s.mem (State.addr b) SR k) (cin := 0)
    (by decide) (by omega_arith) (by rw [r0]; have := hc.fit; omega_arith)
    (fun k hk => by rw [r0]; exact hc1.inW (by omega_arith)) ((u1.other _ (by decide)).trans h6)
    (by rw [u1.gpr]; rfl) (fun k hk => by have := ha k hk; have := hr k hk; omega_arith) (by decide)
    ?_) fun t ht => ?_
  · intro k hk s' hp
    obtain hc' := hc1.of_rest hp.rest (by decide)
    obtain hf : Frame [⟨State.addr b + BitVec.ofNat 64 TF, 4 * k⟩] s.mem s'.mem := by
      have := hp.frame; rwa [r0, u1.mem] at this
    obtain e1 : wd s'.mem (State.addr b) (RA + 4 * k) = limb s.mem (State.addr b) RA k :=
      wd_frame hf fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
    obtain e2 : wd s'.mem (State.addr b) (SR + 4 * k) = limb s.mem (State.addr b) SR k :=
      wd_frame hf fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
    unfold addSrc
    refine ldr0_ok hc' (d := RA + 4 * k) (by omega_arith) fun v1 w1 => ?_
    refine ldr0_ok (hc'.of_rest (w1.rest (ws := [.r3]) (by decide)) (by decide)) (d := SR + 4 * k)
      (by omega_arith) fun v2 w2 => wp_dp (op2_reg _ _) fun v3 w3 => WP.block_nil ⟨?_,
        (w1.rest (by decide)).trans ((w2.rest (by decide)).trans (w3.rest (by decide))),
        by rw [w3.mem, w2.mem, w1.mem]⟩
    obtain x1 : (v2.gpr .r3).toNat = limb s.mem (State.addr b) RA k := by
      rw [w2.other _ (by decide), w1.gpr]; exact e1
    obtain x2 : (v2.gpr .r2).toNat = limb s.mem (State.addr b) SR k := by
      rw [w2.gpr, w1.mem]; exact e2
    rw [w3.gpr]
    show (v2.gpr .r3 + v2.gpr .r2).toNat = _
    rw [toNat_add_lt (by rw [x1, x2]; have := ha k hk; have := hr k hk; omega_arith), x1, x2]
  · generalize hcf : (fun k => limb s.mem (State.addr b) RA k + limb s.mem (State.addr b) SR k) = c at ht
    obtain outs : ∀ k < 28, limb t.mem (State.addr b) TF k = out c 0 k := by
      intro k hk; have := ht.outs k hk; rwa [r0] at this
    obtain hval := (chain_val c 0 28).trans (Nat.add_zero _)
    obtain hcv : val16 c 28 = V28 s.mem (State.addr b) RA + V28 s.mem (State.addr b) SR := by
      unfold V28; rw [← hcf, val16_add]
    rw [hcv] at hval
    have hLM := two_L_le
    obtain hV : V28 t.mem (State.addr b) TF = val16 (out c 0) 28 := val16_congr outs
    refine ⟨(u1.rest (by decide)).trans (ht.rest.mono (by decide)), ?_,
      fun k hk => by rw [outs k hk]; exact out_lt _ _ _, ?_⟩
    · have := ht.frame; rw [r0, u1.mem] at this; exact this
    · rw [hV]
      generalize (2 : Nat) ^ (16 * 28 : Nat) = M at hval hLM
      rcases Nat.eq_zero_or_pos (chain c 0 28) with h | h
      · rw [h, Nat.mul_zero, Nat.add_zero] at hval; exact hval
      · have := Nat.mul_le_mul_left M h
        omega_arith

/-! ## Composing the steps -/

/-- A region of the working space at `b` above its first 64 bytes. -/
def Hi (b : BitVec 32) (r : Region) : Prop :=
  ∃ d n, r = ⟨State.addr b + BitVec.ofNat 64 d, n⟩ ∧ 64 ≤ d ∧ d + n ≤ 8192

theorem hi_of {d n : Nat} (h1 : 64 ≤ d) (h2 : d + n ≤ 8192) :
    Hi b ⟨State.addr b + BitVec.ofNat 64 d, n⟩ := ⟨d, n, rfl, h1, h2⟩

/-- A word of the first 64 bytes across a frame of regions above them. -/
theorem readW_lo {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (hrs : ∀ r ∈ rs, Hi b r)
    {e : Nat} (he : e + 4 ≤ 64) :
    m'.readW (State.addr b + BitVec.ofNat 64 e) 32 = m.readW (State.addr b + BitVec.ofNat 64 e) 32 :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    obtain ⟨d, n, rfl, h1, h2⟩ := hrs r hr
    exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide)

theorem Saved.hi {g : Reg → BitVec 32} {m m' : Mem} (hs : Saved (State.addr b) g m) {rs : List Region}
    (hf : Frame rs m m') (hrs : ∀ r ∈ rs, Hi b r) : Saved (State.addr b) g m' := fun i hi => by
  rw [readW_lo hf hrs (by omega_arith)]; exact hs i hi

theorem Args.hi {g : Reg → BitVec 32} {m m' : Mem} (hs : Args (State.addr b) g m) {rs : List Region}
    (hf : Frame rs m m') (hrs : ∀ r ∈ rs, Hi b r) : Args (State.addr b) g m' := fun i hi => by
  have hO := OUT_eq
  rw [readW_lo hf hrs (by omega_arith)]; exact hs i hi

/-- The inputs and their pointers: `g (argReg i)` points to 57 readable bytes
outside the working space. -/
def Input (b : BitVec 32) (s : State) (p : BitVec 32) : Prop :=
  p.toNat + 57 ≤ 2 ^ 32 ∧ (⟨State.addr p, 57⟩ : Region) ∈ s.rd ++ s.wr ∧
    (⟨State.addr p, 57⟩ : Region).Disjoint ⟨State.addr b, 8192⟩

theorem Input.of_rest {s t : State} {ws : List Reg} {p : BitVec 32} (h : Input b s p) (hr : Rest ws s t) :
    Input b t p := ⟨h.1, by rw [hr.rd, hr.wr]; exact h.2.1, h.2.2⟩

/-- The bytes of an input across a frame of regions of the working space. -/
theorem Input.bytes {s : State} {p : BitVec 32} (h : Input b s p) {rs : List Region} {m m' : Mem}
    (hf : Frame rs m m') (hrs : ∀ r ∈ rs, Hi b r) :
    bytesAt m' (State.addr p) 57 = bytesAt m (State.addr p) 57 :=
  bytesAt_frame hf (fun r hr => by
    obtain ⟨d, n, rfl, h1, h2⟩ := hrs r hr
    exact h.2.2.sub_right (Offset.sub_base _ h2)) (by decide)

theorem limbs_frame_hi {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {o : Nat}
    (hrs : ∀ r ∈ rs, ∃ d n, r = ⟨State.addr b + BitVec.ofNat 64 d, n⟩ ∧ (d + n ≤ o ∨ o + 112 ≤ d) ∧
      d + n ≤ 8192) (ho : o + 112 ≤ 8192) :
    ∀ k < 28, limb m' (State.addr b) o k = limb m (State.addr b) o k :=
  limb_frame28 hf fun r hr k hk => by
    obtain ⟨d, n, rfl, h1, h2⟩ := hrs r hr
    exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

theorem inputs_ok {s : State} (hc : Ctx8 b s) (h6 : s.gpr .r6 = mask16) {g : Reg → BitVec 32}
    (ha : Args (State.addr b) g s.mem) (hin : ∀ i, 1 ≤ i → i < 4 → Input b s (g (argReg i))) :
    WP isa inputs s fun t => Rest [.r1, .r2, .r3, .r4, .r5, .r9, .r10, .r11, .r12] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 TF, 624⟩] s.mem t.mem ∧
      Lim28 t.mem (State.addr b) SK ∧ Lim28 t.mem (State.addr b) SS ∧ Lim28 t.mem (State.addr b) SR ∧
      V28 t.mem (State.addr b) SK = decodeLE (bytesAt s.mem (State.addr (g .r2)) 57) % L ∧
      V28 t.mem (State.addr b) SS = decodeLE (bytesAt s.mem (State.addr (g .r3)) 57) % L ∧
      V28 t.mem (State.addr b) SR = decodeLE (bytesAt s.mem (State.addr (g .r1)) 57) % L := by
  have hT := TF_eq
  have hK := SK_eq
  have hS := SS_eq
  have hR := SR_eq
  have hO := OUT_eq
  obtain sub : ∀ o, TF ≤ o → o + 112 ≤ 688 → ∀ r ∈ [limbsR b TF, limbsR b o],
      ∃ e ∈ [(⟨State.addr b + BitVec.ofNat 64 TF, 624⟩ : Region)], Region.Sub r e := fun o h1 h2 r hr => by
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub _ (by omega_arith) (by omega_arith)
  obtain hiTF : ∀ o, TF ≤ o → o + 112 ≤ 4096 → ∀ r ∈ [limbsR b TF, limbsR b o], Hi b r := fun o h1 h2 r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact hi_of (by omega_arith) (by omega_arith)
  unfold inputs
  -- k
  obtain ⟨k1, k2, k3⟩ := hin 2 (by decide) (by decide)
  refine WP.seq (WP.mono (reduceArg_ok (o := SK) ⟨by omega_arith, by omega_arith⟩ (by omega_arith) hc h6 (ha 2 (by decide))
    k1 k2 k3) fun u ⟨ku, fu, lu, vu⟩ => ?_)
  obtain hcu := hc.of_rest ku (by decide)
  obtain h6u : u.gpr .r6 = mask16 := (ku.gpr _ (by decide)).trans h6
  obtain hau := ha.hi fu (hiTF SK (by omega_arith) (by omega_arith))
  -- s
  obtain ⟨s1, s2, s3⟩ := (hin 3 (by decide) (by decide)).of_rest ku
  refine WP.seq (WP.mono (reduceArg_ok (o := SS) ⟨by omega_arith, by omega_arith⟩ (by omega_arith) hcu h6u (hau 3 (by decide))
    s1 s2 s3) fun v ⟨kv, fv, lv, vv⟩ => ?_)
  obtain hcv := hcu.of_rest kv (by decide)
  obtain h6v : v.gpr .r6 = mask16 := (kv.gpr _ (by decide)).trans h6u
  obtain hav := hau.hi fv (hiTF SS (by omega_arith) (by omega_arith))
  -- r
  obtain ⟨r1, r2, r3⟩ := ((hin 1 (by decide) (by decide)).of_rest ku).of_rest kv
  refine WP.mono (reduceArg_ok (o := SR) ⟨by omega_arith, by omega_arith⟩ (by omega_arith) hcv h6v (hav 1 (by decide))
    r1 r2 r3) fun t ⟨kt, ft, lt, vt⟩ => ?_
  obtain hiW : ∀ r ∈ [(⟨State.addr b + BitVec.ofNat 64 TF, 624⟩ : Region)], Hi b r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hi_of (by omega_arith) (by omega_arith)
  obtain fu' := fu.sub (sub SK (by omega_arith) (by omega_arith))
  obtain fv' := fv.sub (sub SS (by omega_arith) (by omega_arith))
  obtain ft' := ft.sub (sub SR (by omega_arith) (by omega_arith))
  obtain pr : ∀ {o : Nat} {m m' : Mem}, o + 112 ≤ 4096 → Frame [limbsR b TF, limbsR b o] m m' →
      ∀ {o' : Nat}, (o + 112 ≤ o' ∨ o' + 112 ≤ o) → TF + 112 ≤ o' → o' + 112 ≤ 4096 →
      ∀ k < 28, limb m' (State.addr b) o' k = limb m (State.addr b) o' k := fun ho hf o' h1 h2 h3 =>
    limbs_frame_hi hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, _, rfl, by omega_arith, by omega_arith⟩) (by omega_arith)
  obtain fK : ∀ k < 28, limb t.mem (State.addr b) SK k = limb u.mem (State.addr b) SK k := fun k hk => by
    rw [pr (o := SR) (by omega_arith) ft (o' := SK) (by omega_arith) (by omega_arith) (by omega_arith) k hk,
      pr (o := SS) (by omega_arith) fv (o' := SK) (by omega_arith) (by omega_arith) (by omega_arith) k hk]
  obtain fS : ∀ k < 28, limb t.mem (State.addr b) SS k = limb v.mem (State.addr b) SS k :=
    pr (o := SR) (by omega_arith) ft (o' := SS) (by omega_arith) (by omega_arith) (by omega_arith)
  obtain bS := (hin 3 (by decide) (by decide)).bytes fu' hiW
  obtain bR := (hin 1 (by decide) (by decide)).bytes (fu'.trans fv') hiW
  refine ⟨(ku.trans kv).trans kt, fu'.trans (fv'.trans ft'), fun k hk => by rw [fK k hk]; exact lu k hk,
    fun k hk => by rw [fS k hk]; exact lv k hk, lt, ?_, ?_, ?_⟩
  · change _ = decodeLE (bytesAt s.mem (State.addr (g (argReg 2))) 57) % L
    rw [← vu]; exact val16_congr fK
  · change _ = decodeLE (bytesAt s.mem (State.addr (g (argReg 3))) 57) % L
    rw [← bS, ← vv]; exact val16_congr fS
  · change _ = decodeLE (bytesAt s.mem (State.addr (g (argReg 1))) 57) % L
    rw [← bR, vt]

end

end VG.Proof.Ed448.Arm

end

end


/-!
# Ed448 scalar multiply-add on ARMv7: the whole function

`vg_ed448_scalar_mul_add(out = r0, r = r1, k = r2, s = r3, scratch = [sp])`
against a local contract (`scalarMulAddLocal`), the ABI included.
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X25519.Arm
open VG.Spec.Ed448 (L bytesAt decodeLE encodeLE)

def scalarMulAddLocal : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 57⟩
    let r : Region := ⟨State.addr (s.gpr .r1), 57⟩
    let k : Region := ⟨State.addr (s.gpr .r2), 57⟩
    let a : Region := ⟨State.addr (s.gpr .r3), 57⟩
    let ws : Region := ⟨State.addr (stackArg s 0), 8192⟩
    let args : Region := ⟨State.addr s.sp, 4⟩
    s.rd = [r, k, a, args] ∧ s.wr = [out, ws] ∧
      out.Disjoint ws ∧ r.Disjoint ws ∧ k.Disjoint ws ∧ a.Disjoint ws ∧
      out.Disjoint args ∧ ws.Disjoint args ∧
      (s.gpr .r0).toNat + 57 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 57 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 57 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + 57 ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + 8192 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32
  post s t := bytesAt t.mem (State.addr (s.gpr .r0)) 57 =
    Spec.Ed448.scalarMulAdd (bytesAt s.mem (State.addr (s.gpr .r1)) 57)
      (bytesAt s.mem (State.addr (s.gpr .r2)) 57) (bytesAt s.mem (State.addr (s.gpr .r3)) 57)
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧
    s.gpr .r2 = t.gpr .r2 ∧ s.gpr .r3 = t.gpr .r3 ∧ stackArg s 0 = stackArg t 0

structure MulAddPre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r1), 57⟩, ⟨State.addr (s.gpr .r2), 57⟩,
    ⟨State.addr (s.gpr .r3), 57⟩, ⟨State.addr s.sp, 4⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r0), 57⟩, ⟨State.addr (stackArg s 0), 8192⟩]
  out_ws : (⟨State.addr (s.gpr .r0), 57⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 8192⟩
  r_ws : (⟨State.addr (s.gpr .r1), 57⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 8192⟩
  k_ws : (⟨State.addr (s.gpr .r2), 57⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 8192⟩
  a_ws : (⟨State.addr (s.gpr .r3), 57⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 8192⟩
  out_args : (⟨State.addr (s.gpr .r0), 57⟩ : Region).Disjoint ⟨State.addr s.sp, 4⟩
  ws_args : (⟨State.addr (stackArg s 0), 8192⟩ : Region).Disjoint ⟨State.addr s.sp, 4⟩
  f0 : (s.gpr .r0).toNat + 57 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 57 ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 57 ≤ 2 ^ 32
  f3 : (s.gpr .r3).toNat + 57 ≤ 2 ^ 32
  fs : (stackArg s 0).toNat + 8192 ≤ 2 ^ 32
  fsp : s.sp.toNat + 4 ≤ 2 ^ 32

theorem MulAddPre.of {s : State} (h : scalarMulAddLocal.pre s) : MulAddPre s := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem MulAddPre.input {s : State} (h : MulAddPre s) {i : Nat} (h1 : 1 ≤ i) (h4 : i < 4) :
    Input (stackArg s 0) s (s.gpr (argReg i)) := by
  rcases (by omega_using [h1, h4] : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
  · exact ⟨h.f1, by rw [h.rd]; simp [argReg], h.r_ws⟩
  · exact ⟨h.f2, by rw [h.rd]; simp [argReg], h.k_ws⟩
  · exact ⟨h.f3, by rw [h.rd]; simp [argReg], h.a_ws⟩

theorem mulAdd_mod (r k s : Nat) : ((k % L * (s % L)) % L + r % L) % L = (r + k * s) % L := by
  rw [← Nat.mul_mod, ← Nat.add_mod, Nat.add_comm]

theorem scalarMulAdd_correct {s : State} (h : MulAddPre s) :
    WP isa scalarMulAdd s fun t => abiPreserved s t ∧ scalarMulAddLocal.post s t := by
  have hT := TF_eq
  have hK := SK_eq
  have hS := SS_eq
  have hR := SR_eq
  have hA := RA_eq
  have hC := ACC_eq
  have hO := OUT_eq
  obtain hw : (⟨State.addr (stackArg s 0), 8192⟩ : Region) ∈ s.wr := by rw [h.wr]; simp
  obtain ha : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4 :=
    ⟨_, by rw [h.rd]; simp, Region.contains_self _ _⟩
  unfold scalarMulAdd
  refine WP.seq (WP.mono (mulAddArgs_ok ha h.fs hw) fun u ⟨hcu, h6u, su, au, ku, fu⟩ => ?_)
  refine WP.seq (WP.mono (inputs_ok hcu h6u au fun i h1 h4 => (h.input h1 h4).of_rest ku)
    fun v ⟨kv, fv, lK, lS, lR, vK, vS, vR⟩ => ?_)
  obtain hcv0 := hcu.of_rest kv (by decide)
  obtain hiv : ∀ r ∈ [(⟨State.addr (stackArg s 0) + BitVec.ofNat 64 TF, 624⟩ : Region)], Hi (stackArg s 0) r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hi_of (by omega_using [hT]) (by omega_using [hT])
  obtain av := au.hi fv hiv
  obtain hld : WP isa (.block [.ldr .r12 .r0 OUT]) v fun v' =>
      Rest [.r12] v v' ∧ v'.mem = v.mem ∧ v'.gpr .r12 = s.gpr .r0 :=
    ldr0_ok hcv0 (d := OUT) (by omega_using [hO]) fun v' hv' => WP.block_nil ⟨hv'.rest (by decide), hv'.mem,
      by rw [hv'.gpr]; exact av 0 (by decide)⟩
  refine WP.seq (WP.mono hld fun v' ⟨kv', mv', qv'⟩ => ?_)
  obtain hcv := hcv0.of_rest kv' (by decide)
  obtain h6v : v'.gpr .r6 = mask16 := (kv'.gpr _ (by decide)).trans ((kv.gpr _ (by decide)).trans h6u)
  rw [← mv'] at lK lS lR vK vS vR fv
  refine WP.seq (WP.mono (product_ok hcv h6v lK lS) fun w ⟨kw, fw, aw, vw⟩ => ?_)
  obtain hcw := hcv.of_rest kw (by decide)
  obtain h6w : w.gpr .r6 = mask16 := (kw.gpr _ (by decide)).trans h6v
  obtain hiw : ∀ r ∈ [(⟨State.addr (stackArg s 0) + BitVec.ofNat 64 Impl.X448.Arm.ACC, 224⟩ : Region)], Hi (stackArg s 0) r :=
    fun r hr => by rw [List.mem_singleton.mp hr]; exact hi_of (by omega_using [hC]) (by omega_using [hC])
  refine WP.seq (WP.mono (reduceProduct_ok hcw h6w aw) fun x ⟨kx, lx, vx⟩ => ?_)
  obtain hcx := hcw.of_rest kx.rest (by decide)
  obtain h6x : x.gpr .r6 = mask16 := (kx.rest.gpr _ (by decide)).trans h6w
  obtain hix : ∀ r ∈ [limbsR (stackArg s 0) TF, limbsR (stackArg s 0) RA], Hi (stackArg s 0) r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact hi_of (by omega_arith) (by omega_arith)
  -- The reduced `r` survives the product and its reduction.
  obtain eR : ∀ k < 28, limb x.mem (State.addr (stackArg s 0)) SR k = limb v'.mem (State.addr (stackArg s 0)) SR k := fun k hk => by
    rw [limbs_frame_hi kx.frame (o := SR) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, _, rfl, by omega_arith, by omega_arith⟩) (by omega_using [hR]) k hk,
      limbs_frame_hi fw (o := SR) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, _, rfl, by omega_using [hR, hC], by omega_using [hC]⟩) (by omega_using [hR]) k hk]
  obtain lRx : Lim28 x.mem (State.addr (stackArg s 0)) SR := fun k hk => by rw [eR k hk]; exact lR k hk
  obtain vRx : V28 x.mem (State.addr (stackArg s 0)) SR = V28 v'.mem (State.addr (stackArg s 0)) SR := val16_congr eR
  rw [List.append_assoc]
  refine WP.append (addPass_ok hcx h6x lx lRx (by rw [vx]; exact Nat.mod_lt _ L_pos)
    (by rw [vRx, vR]; exact Nat.mod_lt _ L_pos)) fun y ⟨ky, fy, ly, vy⟩ => ?_
  obtain hcy := hcx.of_rest ky (by decide)
  refine WP.append (reduceT_ok RA_buf hcy ((ky.gpr _ (by decide)).trans h6x) ly
    (by rw [vy, vx, vRx, vR]; have := Nat.mod_lt (val16 (limb w.mem (State.addr (stackArg s 0)) Impl.X448.Arm.ACC) 56) L_pos
        have := Nat.mod_lt (decodeLE (bytesAt u.mem (State.addr (s.gpr .r1)) 57)) L_pos
        omega_arith)) fun z ⟨kz, fz, lz, vz⟩ => ?_
  obtain hcz := hcy.of_rest kz (by decide)
  obtain hiy : ∀ r ∈ [limbsR (stackArg s 0) TF], Hi (stackArg s 0) r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hi_of (by omega_using [hT]) (by omega_using [hT])
  obtain hiz : ∀ r ∈ [limbsR (stackArg s 0) RA], Hi (stackArg s 0) r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hi_of (by omega_using [hA]) (by omega_using [hA])
  obtain sz := ((((su.hi fv hiv).hi fw hiw).hi kx.frame hix).hi fy hiy).hi fz hiz
  obtain rz' : Rest [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r9, .r10, .r11] w z :=
    (kx.rest.mono (by decide)).trans ((ky.mono (by decide)).trans (kz.mono (by decide)))
  obtain qz : z.gpr .r12 = s.gpr .r0 := by
    rw [rz'.gpr _ (by decide), kw.gpr _ (by decide), qv']
  obtain rz : Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r9, .r10, .r11, .r12] s z :=
    (ku.mono (by decide)).trans ((kv.mono (by decide)).trans ((kv'.mono (by decide)).trans
      ((kw.mono (by decide)).trans (rz'.mono (by decide)))))
  refine WP.mono (output_ok (by decide) hcz lz qz h.f0 (by rw [rz.wr, h.wr]; simp) h.out_ws sz)
    fun t ⟨gt, kt, _, bt⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [kt.sp, rz.sp]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact gt 0 (by decide)
    · exact gt 1 (by decide)
    · exact gt 2 (by decide)
    · exact gt 3 (by decide)
    · exact gt 4 (by decide)
    · exact gt 5 (by decide)
    · exact gt 6 (by decide)
    · exact gt 7 (by decide)
    · rw [kt.gpr _ (by decide), rz.gpr _ (by decide)]
  · have hu : ∀ i, 1 ≤ i → i < 4 → bytesAt u.mem (State.addr (s.gpr (argReg i))) 57 =
        bytesAt s.mem (State.addr (s.gpr (argReg i))) 57 := fun i h1 h4 =>
      bytesAt_frame fu (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact (h.input h1 h4).2.2.sub_right (Region.sub_prefix (by decide))) (by decide)
    change bytesAt t.mem _ 57 = encodeLE 57 _
    rw [bt, vz, vy, vx, vw, vRx, vK, vS, vR, mulAdd_mod]
    rw [show s.gpr .r1 = s.gpr (argReg 1) from rfl, show s.gpr .r2 = s.gpr (argReg 2) from rfl,
      show s.gpr .r3 = s.gpr (argReg 3) from rfl, hu 1 (by decide) (by decide),
      hu 2 (by decide) (by decide), hu 3 (by decide) (by decide)]

end VG.Proof.Ed448.Arm

end

end

/-!
# Ed448 scalar arithmetic on ARMv7: `Verified`

Correctness includes the ABI. Taint analysis checks that secret input bytes
never determine branches or memory addresses. A concrete witness proves the
signature contract is satisfiable.
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm

theorem scalarReduce_ok (s : State) (hs : scalarReduceLocal.pre s) :
    ∃ t s', Exec isa scalarReduce s t s' ∧ abiPreserved s s' ∧ scalarReduceLocal.post s s' :=
  scalarReduce_correct (ReducePre.of hs)

/-- The arguments are public, and so is what the code stores in the working
space (writable region 1, at `r2`): the output's address, at `OUT`. -/
def scalarReduceTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2], flags := false, lens := [57, 8192], bases := [(.r2, 1)] }

theorem scalarReduceTaint_wf {s : State} (h : scalarReduceLocal.pre s) :
    VG.Arm.Taint.Wf scalarReduceTaint s := by
  have hp := ReducePre.of h
  refine ⟨fun _ => ⟨by simp [hp.wr, scalarReduceTaint], ?_, ?_⟩, ?_,
    fun h => absurd h (by decide), fun _ h => (List.not_mem_nil h).elim⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact hp.out_ws
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · simpa only [State.addr, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using hp.f0
    · simpa only [State.addr, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using hp.f2
  · intro p hm
    simp only [scalarReduceTaint, List.mem_singleton] at hm
    subst hm
    simp [VG.Arm.Taint.region, hp.wr]

theorem scalarReduce_ct :
    ConstantTime isa scalarReduceLocal.pre scalarReduceLocal.pub scalarReduce := by
  refine VG.Taint.constantTime (A := taint) scalarReduceTaint ?_ (by native_taint_decide)
  intro s t hs ht ⟨_, h0, h1, h2⟩
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, scalarReduceTaint_wf hs,
    scalarReduceTaint_wf ht, fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (by decide), fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  · simp only [scalarReduceTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
  · rw [(ReducePre.of hs).wr, (ReducePre.of ht).wr, h0, h2]

theorem scalarMulAdd_ok (s : State) (hs : scalarMulAddLocal.pre s) :
    ∃ t s', Exec isa scalarMulAdd s t s' ∧ abiPreserved s s' ∧ scalarMulAddLocal.post s s' :=
  scalarMulAdd_correct (MulAddPre.of hs)

/-- The arguments are public, and so is what the code stores in the working
space (writable region 1, whose address is the stack argument): the
arguments' addresses, from `OUT`. -/
def scalarMulAddTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [57, 8192],
    argLen := 4, argBases := [(0, 1)] }

theorem scalarMulAddTaint_wf {s : State} (h : scalarMulAddLocal.pre s) :
    VG.Arm.Taint.Wf scalarMulAddTaint s := by
  have hp := MulAddPre.of h
  refine ⟨fun _ => ⟨by simp [hp.wr, scalarMulAddTaint], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨hp.fsp, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact hp.out_ws
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · simpa only [State.addr, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using hp.f0
    · simpa only [State.addr, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using hp.fs
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.out_args.symm
    · exact hp.ws_args.symm
  · intro p hm
    simp only [scalarMulAddTaint, List.mem_singleton] at hm
    subst hm
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem scalarMulAdd_argByte (s : State) (k : Nat) :
    VG.Arm.Taint.argByte s k = stackArgAddr s 0 + BitVec.ofNat 64 k := by
  simp [VG.Arm.Taint.argByte, stackArgAddr]

theorem scalarMulAdd_ct :
    ConstantTime isa scalarMulAddLocal.pre scalarMulAddLocal.pub scalarMulAdd := by
  refine VG.Taint.constantTime (A := taint) scalarMulAddTaint ?_ (by native_taint_decide)
  intro s t hs ht ⟨hsp, h0, h1, h2, h3, ha⟩
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, scalarMulAddTaint_wf hs,
    scalarMulAddTaint_wf ht, fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => hsp, fun k hk => ?_⟩
  · simp only [scalarMulAddTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · rw [(MulAddPre.of hs).wr, (MulAddPre.of ht).wr, h0, ha]
  · rw [scalarMulAdd_argByte, scalarMulAdd_argByte, Mem.readW_byte s.mem _ hk, Mem.readW_byte t.mem _ hk]
    exact congrArg (fun v : BitVec 32 => v.extractLsb' (8 * k) 8) ha

end VG.Proof.Ed448.Arm
