import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Impl.Ed448.Arm.Scalar
import VerifiedGarbage.Proof.X448.Arm.Verified
import VerifiedGarbage.Proof.X25519.Arm.Verified
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.Ed448.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.ScalarNat`. -/
section

/-!
# Ed448 scalar arithmetic on ARMv7: the numbers

The remainder is twenty-eight 16-bit limbs `r` (`val16 r 28 < L`). Folding a
chunk `w` in (`foldC`): the limbs of `l` (`foldL`, `w` and `r` shifted up
by one limb, the top masked to 14 bits) plus `h = foldH r` times the limbs
of `c = 2^446 - L` (`cLimb`), each sum below `2^32 - 2^16`; their number is
below `2L` and congruent to `w + 2^16 r` (`fold_facts`). The limbs of
`K = 2^448 - L` (`kLimb`) for the conditional subtraction.
-/

namespace VG.Proof.Ed448.Arm

open VG.Proof.X25519.Arm (val16 val16_succ val16_congr val16_lt val16_add val16_cmul val16_append)
open VG.Impl.Ed448.Arm
open VG.Spec.Ed448 (L)

/-! ## Constants -/

theorem cLimb_high {k : Nat} (h : 14 ≤ k) : cLimb k = 0 := by
  rw [cLimb, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
    simp only [cLimbs, List.length_cons, List.length_nil]; omega)]
  rfl

theorem cLimb_lt (k : Nat) : cLimb k < 65536 := by
  by_cases h : k < 14
  · have : ∀ k < 14, cLimb k < 65536 := by decide
    exact this k h
  · rw [VG.Proof.Ed448.Arm.cLimb_high (by omega)]; decide

theorem kLimb_lt (k : Nat) : kLimb k < 65536 := by
  unfold kLimb; split
  · decide
  · exact VG.Proof.Ed448.Arm.cLimb_lt k

theorem kLimb_mid {k : Nat} (h1 : 14 ≤ k) (h2 : k ≠ 27) : kLimb k = 0 := by
  rw [kLimb, ite_eq_right h2, VG.Proof.Ed448.Arm.cLimb_high h1]

theorem val16_cLimb : val16 cLimb 28 = cL := by decide +kernel

theorem val16_kLimb : val16 kLimb 28 = 2 ^ (16 * 28 : Nat) - L := by decide +kernel

/-- `2^c = 2^a 2^b`, without evaluating either side (the elaborator does not
evaluate powers with exponents above 256). -/
theorem pow2_split (a b c : Nat) (h : a + b = c) : (2 : Nat) ^ c = 2 ^ a * 2 ^ b := by
  rw [← h, Nat.pow_add]

/-! ## Folding a chunk in -/

/-- The limbs of `l`: the chunk `w`, then those of the remainder `r`
shifted up by one, the top one masked to 14 bits. -/
def foldL (r : Nat → Nat) (w k : Nat) : Nat :=
  if k = 0 then w else if k < 27 then r (k - 1) else r 26 % 16384

/-- `h = r₂₆ >> 14 + 4 r₂₇`, the bits of `w + 2^16 r` from 446 up. -/
def foldH (r : Nat → Nat) : Nat := r 26 / 16384 + 4 * r 27

/-- The sums of `l + h c`, before carrying. -/
def foldC (r : Nat → Nat) (w k : Nat) : Nat := VG.Proof.Ed448.Arm.foldL r w k + VG.Proof.Ed448.Arm.foldH r * cLimb k

theorem foldL_lt {r : Nat → Nat} (hr : ∀ k < 28, r k < 65536) {w : Nat} (hw : w < 65536) :
    ∀ k < 28, VG.Proof.Ed448.Arm.foldL r w k < 65536 := by
  intro k hk
  unfold VG.Proof.Ed448.Arm.foldL
  split
  · exact hw
  · split
    · exact hr _ (by omega)
    · omega

/-- `w + 2^16 r = l + 2^446 h`. -/
theorem foldL_val (r : Nat → Nat) (w : Nat) :
    val16 (VG.Proof.Ed448.Arm.foldL r w) 28 + 2 ^ 446 * VG.Proof.Ed448.Arm.foldH r = w + 65536 * val16 r 28 := by
  have e1 : val16 (VG.Proof.Ed448.Arm.foldL r w) 28 = w + 65536 * (val16 r 26 + 2 ^ 416 * (r 26 % 16384)) := by
    rw [show (28 : Nat) = 1 + 27 from rfl, val16_append]
    have hs : val16 (fun k => VG.Proof.Ed448.Arm.foldL r w (1 + k)) 27 =
        val16 (fun k => if k < 26 then r k else r 26 % 16384) 27 :=
      val16_congr fun k hk => by
        unfold VG.Proof.Ed448.Arm.foldL
        rw [ite_eq_right (by omega)]
        by_cases h : k < 26
        · rw [ite_eq_left (by omega), ite_eq_left h, show 1 + k - 1 = k by omega]
        · rw [ite_eq_right (by omega), ite_eq_right h]
    have hs2 : val16 (fun k => if k < 26 then r k else r 26 % 16384) 27 =
        val16 r 26 + 2 ^ 416 * (r 26 % 16384) := by
      rw [val16_succ, ite_eq_right (by omega), val16_congr (g := r) (n := 26) fun k hk => ite_eq_left hk,
        show 16 * 26 = 416 from rfl]
    have h1 : val16 (VG.Proof.Ed448.Arm.foldL r w) 1 = w := by
      simp only [val16, VG.Proof.Ed448.Arm.foldL, ite_true, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
    rw [hs, hs2, h1]
  have e2 : val16 r 28 = val16 r 26 + 2 ^ 416 * r 26 + 2 ^ 432 * r 27 := by
    rw [val16_succ, val16_succ, show 16 * 26 = 416 from rfl, show 16 * 27 = 432 from rfl]
  rw [e1, e2, VG.Proof.Ed448.Arm.foldH]
  generalize val16 r 26 = v
  have hd : r 26 = r 26 % 16384 + 16384 * (r 26 / 16384) := (Nat.mod_add_div _ _).symm
  generalize r 26 % 16384 = a at hd ⊢
  generalize r 26 / 16384 = b at hd ⊢
  rw [hd]
  generalize r 27 = c
  have p1 : (2 : Nat) ^ 446 = 2 ^ 416 * 2 ^ 30 := VG.Proof.Ed448.Arm.pow2_split 416 30 446 rfl
  have p2 : (2 : Nat) ^ 432 = 2 ^ 416 * 2 ^ 16 := VG.Proof.Ed448.Arm.pow2_split 416 16 432 rfl
  rw [p1, p2]
  clear p1 p2 e1 e2
  generalize (2 : Nat) ^ 416 = A
  grind

/-- The facts the code relies on: the sums fit with a carry, `h` and the
top limb fit, and the result is below `2L` and congruent to `w + 2^16 r`. -/
theorem fold_facts {r : Nat → Nat} (hr : ∀ k < 28, r k < 65536) (hv : val16 r 28 < L)
    {w : Nat} (hw : w < 65536) :
    r 27 < 16384 ∧ VG.Proof.Ed448.Arm.foldH r < 65536 ∧ (∀ k < 28, VG.Proof.Ed448.Arm.foldC r w k + 65536 ≤ 2 ^ 32) ∧
      val16 (VG.Proof.Ed448.Arm.foldC r w) 28 < 2 * L ∧
      val16 (VG.Proof.Ed448.Arm.foldC r w) 28 % L = (w + 65536 * val16 r 28) % L := by
  have hL := L_lit
  have h27 : r 27 < 16384 := by
    have e : val16 r 28 = val16 r 27 + 2 ^ 432 * r 27 := by
      rw [val16_succ, show 16 * 27 = 432 from rfl]
    have : L < 2 ^ 432 * 2 ^ 14 := by
      rw [← VG.Proof.Ed448.Arm.pow2_split 432 14 446 rfl]; exact L_lt
    rcases Nat.lt_or_ge (r 27) 16384 with h | h
    · exact h
    · have := Nat.mul_le_mul_left (2 ^ 432) h
      omega
  have hH : VG.Proof.Ed448.Arm.foldH r < 65536 := by
    unfold VG.Proof.Ed448.Arm.foldH
    have := hr 26 (by omega)
    omega
  have hl := VG.Proof.Ed448.Arm.foldL_lt hr hw
  refine ⟨h27, hH, fun k hk => ?_, ?_⟩
  · have hm : VG.Proof.Ed448.Arm.foldH r * cLimb k ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by have := VG.Proof.Ed448.Arm.cLimb_lt k; omega)
    have := hl k hk
    unfold VG.Proof.Ed448.Arm.foldC
    omega
  have eC : val16 (VG.Proof.Ed448.Arm.foldC r w) 28 = val16 (VG.Proof.Ed448.Arm.foldL r w) 28 + VG.Proof.Ed448.Arm.foldH r * cL := by
    unfold VG.Proof.Ed448.Arm.foldC
    rw [val16_add, val16_cmul, VG.Proof.Ed448.Arm.val16_cLimb]
  have hL28 : val16 (VG.Proof.Ed448.Arm.foldL r w) 28 < 2 ^ 432 * 2 ^ 14 := by
    have e : val16 (VG.Proof.Ed448.Arm.foldL r w) 28 = val16 (VG.Proof.Ed448.Arm.foldL r w) 27 + 2 ^ 432 * (r 26 % 16384) := by
      rw [val16_succ, show 16 * 27 = 432 from rfl, show VG.Proof.Ed448.Arm.foldL r w 27 = r 26 % 16384 from rfl]
    have h1 : val16 (VG.Proof.Ed448.Arm.foldL r w) 27 < 2 ^ 432 := by
      have := val16_lt (f := VG.Proof.Ed448.Arm.foldL r w) (n := 27) fun k hk => hl k (by omega)
      rwa [show 16 * 27 = 432 from rfl] at this
    have h2 := Nat.mul_le_mul_left (2 ^ 432) (by omega : r 26 % 16384 ≤ 16383)
    omega
  have hval := VG.Proof.Ed448.Arm.foldL_val r w
  have hP : (2 : Nat) ^ 446 = 2 ^ 432 * 2 ^ 14 := by
    exact VG.Proof.Ed448.Arm.pow2_split 432 14 446 rfl
  have hP' : (2 : Nat) ^ 446 = L + cL := L_add.symm
  have hcL : cL = 13818066809895115352007386748515426880336692474882178609894547503885 := rfl
  rw [hP'] at hval
  rw [← hP, hP'] at hL28
  have hHc : VG.Proof.Ed448.Arm.foldH r * cL < 65536 * cL := Nat.mul_lt_mul_of_pos_right hH (by rw [hcL]; decide)
  refine ⟨?_, ?_⟩
  · rw [eC]; rw [hL, hcL] at *; omega
  · rw [eC, ← hval]
    have e : val16 (VG.Proof.Ed448.Arm.foldL r w) 28 + (L + cL) * VG.Proof.Ed448.Arm.foldH r =
        val16 (VG.Proof.Ed448.Arm.foldL r w) 28 + VG.Proof.Ed448.Arm.foldH r * cL + VG.Proof.Ed448.Arm.foldH r * L := by
      rw [Nat.add_mul, Nat.mul_comm L, Nat.mul_comm cL]; omega
    rw [e, Nat.add_mul_mod_self_right]

/-! ## The conditional subtraction -/

/-- `x + K` for `x < 2L` carries out of `M ≥ 2L` (448 bits) exactly when
`x ≥ L`, and selecting the sum if it carried, else `x`, leaves `x mod L`. -/
theorem csub_facts {M x y c : Nat} (hLM : 2 * L ≤ M) (hx : x < 2 * L) (hy : y < M)
    (he : y + M * c = x + (M - L)) :
    c ≤ 1 ∧ (if c = 1 then y else x) = x % L := by
  have hc : c ≤ 1 := by
    rcases Nat.lt_or_ge c 2 with h | h
    · omega
    · have : M * 2 ≤ M * c := Nat.mul_le_mul_left _ h
      omega
  refine ⟨hc, ?_⟩
  have := csub_nat (M := M) (x := x) (y := y) (c := decide (c = 1)) hLM hx hy
    (by rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;> simpa using he)
  rw [← this]
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;> rfl

/-- `2L` fits in 448 bits. -/
theorem two_L_le : 2 * L ≤ 2 ^ (16 * 28 : Nat) := by
  have h := VG.Proof.Ed448.Arm.pow2_split 446 2 (16 * 28) rfl
  have := L_lt
  omega

end VG.Proof.Ed448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.ScalarStep`. -/
section

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

theorem foldHead_ok {o : Nat} (ho : VG.Proof.Ed448.Arm.Buf o) {s : State} (hc : VG.Proof.Ed448.Arm.Ctx8 b s)
    (h27 : limb s.mem (State.addr b) o 27 < 16384) (h26 : limb s.mem (State.addr b) o 26 < 65536) :
    WP isa (.block (foldHead o)) s fun t =>
      (t.gpr .r1).toNat = VG.Proof.Ed448.Arm.foldH (limb s.mem (State.addr b) o) ∧ (t.gpr .r5).toNat = 0 ∧
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
theorem foldSrc_ok {o : Nat} (ho : VG.Proof.Ed448.Arm.Buf o) {s0 : State} {w : Nat}
    (hh : VG.Proof.Ed448.Arm.foldH (limb s0.mem (State.addr b) o) < 65536)
    (hsum : ∀ k < 28, VG.Proof.Ed448.Arm.foldC (limb s0.mem (State.addr b) o) w k + 65536 ≤ 2 ^ 32)
    {k : Nat} (hk : k < 28) {s : State} (hc : VG.Proof.Ed448.Arm.Ctx8 b s)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 TF, 4 * k⟩] s0.mem s.mem)
    (h1 : (s.gpr .r1).toNat = VG.Proof.Ed448.Arm.foldH (limb s0.mem (State.addr b) o)) (h11 : (s.gpr .r11).toNat = w) :
    WP isa (.block (foldSrc o k)) s fun s' =>
      (s'.gpr .r3).toNat = VG.Proof.Ed448.Arm.foldC (limb s0.mem (State.addr b) o) w k ∧ Rest [.r2, .r3, .r4] s s' ∧
        s'.mem = s.mem := by
  obtain ⟨ho1, ho2⟩ := ho
  have hT := VG.Proof.Ed448.Arm.TF_eq
  generalize hr : limb s0.mem (State.addr b) o = r at hh hsum h1
  unfold VG.Proof.Ed448.Arm.foldC at hsum ⊢
  generalize VG.Proof.Ed448.Arm.foldH r = hv at hh h1 hsum ⊢
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
    have hc0 := VG.Proof.Ed448.Arm.cLimb_lt 0
    have e2 : (s2.gpr .r2).toNat = hv * cLimb 0 := by
      rw [u2.gpr, u1.other _ (by decide), u1.gpr, toNat_mul_lt (by
        rw [h1, VG.Proof.Ed448.Arm.toNat_movw hc0]; exact Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_of_lt_succ hh)
          (Nat.le_of_lt_succ hc0)) (by decide)), h1, VG.Proof.Ed448.Arm.toNat_movw hc0]
    rw [u3.gpr]
    show (s2.gpr .r11 + s2.gpr .r2).toNat = _
    have e11 : (s2.gpr .r11).toNat = w := by rw [u2.other _ (by decide), u1.other _ (by decide), h11]
    simp only [VG.Proof.Ed448.Arm.foldL, ite_true] at hs ⊢
    rw [toNat_add_lt (by rw [e11, e2]; omega), e11, e2]
  rw [ite_eq_right k0]
  by_cases k14 : k < 14
  · rw [ite_eq_left k14]
    refine ldr0_ok hc (d := o + 4 * (k - 1)) (by omega) fun s1 u1 => ?_
    refine wp_movw fun s2 u2 => wp_mul fun s3 u3 => wp_dp (op2_reg _ _) fun s4 u4 => WP.block_nil ?_
    refine ⟨?_, (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      (u4.rest (by decide)))), by rw [u4.mem, u3.mem, u2.mem, u1.mem]⟩
    have hck := VG.Proof.Ed448.Arm.cLimb_lt k
    have e1 : (s3.gpr .r1).toNat = hv := by
      rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), h1]
    have e2 : (s3.gpr .r2).toNat = hv * cLimb k := by
      rw [u3.gpr, u2.other _ (by decide), u2.gpr, u1.other _ (by decide), toNat_mul_lt (by
        rw [h1, VG.Proof.Ed448.Arm.toNat_movw hck]; exact Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_of_lt_succ hh)
          (Nat.le_of_lt_succ hck)) (by decide)), h1, VG.Proof.Ed448.Arm.toNat_movw hck]
    have e3 : (s3.gpr .r3).toNat = r (k - 1) := by
      rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr]; exact lr (k - 1) (by omega)
    rw [u4.gpr]
    show (s3.gpr .r3 + s3.gpr .r2).toNat = _
    simp only [VG.Proof.Ed448.Arm.foldL, k0, ite_false, show k < 27 by omega, ite_true] at hs ⊢
    rw [toNat_add_lt (by rw [e3, e2]; omega), e3, e2]
  rw [ite_eq_right k14]
  by_cases k27 : k < 27
  · rw [ite_eq_left k27]
    refine ldr0_ok hc (d := o + 4 * (k - 1)) (by omega) fun s1 u1 => WP.block_nil ?_
    refine ⟨?_, u1.rest (by decide), u1.mem⟩
    rw [u1.gpr]
    simp only [VG.Proof.Ed448.Arm.foldL, k0, ite_false, k27, ite_true, VG.Proof.Ed448.Arm.cLimb_high (by omega : 14 ≤ k), Nat.mul_zero,
      Nat.add_zero]
    exact lr (k - 1) (by omega)
  · rw [ite_eq_right k27]
    refine ldr0_ok hc (d := o + 104) (by omega) fun s1 u1 => ?_
    refine wp_mov (op2_lsl (by decide)) fun s2 u2 => wp_mov (op2_lsr (by decide)) fun s3 u3 => ?_
    refine WP.block_nil ⟨?_, (u1.rest (by decide)).trans ((u2.rest (by decide)).trans
      (u3.rest (by decide))), by rw [u3.mem, u2.mem, u1.mem]⟩
    rw [u3.gpr, u2.gpr, u1.gpr, VG.Proof.Ed448.Arm.toNat_mask14]
    simp only [VG.Proof.Ed448.Arm.foldL, k0, ite_false, k27, VG.Proof.Ed448.Arm.cLimb_high (by omega : 14 ≤ k), Nat.mul_zero, Nat.add_zero]
    rw [show o + 104 = o + 4 * 26 from rfl]
    exact congrArg (· % 16384) (lr 26 (by decide))

/-- `fold o`: the limbs of `l + h c` into `TF`. -/
theorem fold_ok {o : Nat} (ho : VG.Proof.Ed448.Arm.Buf o) {s : State} (hc : VG.Proof.Ed448.Arm.Ctx8 b s) (h6 : s.gpr .r6 = mask16)
    (hl : VG.Proof.Ed448.Arm.Lim28 s.mem (State.addr b) o) (hv : VG.Proof.Ed448.Arm.V28 s.mem (State.addr b) o < L)
    (hw : (s.gpr .r11).toNat < 65536) :
    WP isa (.block (fold o)) s fun t =>
      Rest [.r1, .r2, .r3, .r4, .r5] s t ∧ Frame [VG.Proof.Ed448.Arm.limbsR b TF] s.mem t.mem ∧
      VG.Proof.Ed448.Arm.Lim28 t.mem (State.addr b) TF ∧ VG.Proof.Ed448.Arm.V28 t.mem (State.addr b) TF < 2 * L ∧
      VG.Proof.Ed448.Arm.V28 t.mem (State.addr b) TF % L = ((s.gpr .r11).toNat + 65536 * VG.Proof.Ed448.Arm.V28 s.mem (State.addr b) o) % L := by
  have hT := VG.Proof.Ed448.Arm.TF_eq
  obtain ⟨ho1, ho2⟩ := ho
  obtain ⟨h27, hH, hsum, hlt, hmod⟩ := VG.Proof.Ed448.Arm.fold_facts hl hv hw
  unfold fold
  refine WP.append (VG.Proof.Ed448.Arm.foldHead_ok ⟨ho1, ho2⟩ hc h27 (hl 26 (by decide))) fun s1 ⟨e1, e5, k1, m1⟩ => ?_
  have hc1 := hc.of_rest k1 (by decide)
  have r0 : s1.gpr .r0 = b := hc1.r0
  refine WP.mono (carryPass_ok (rb := .r0) (o := TF) (s0 := s1) (c := VG.Proof.Ed448.Arm.foldC (limb s.mem (State.addr b) o) (s.gpr .r11).toNat) (cin := 0) (by decide)
    (by omega) (by rw [r0]; have := hc.fit; omega)
    (fun k hk => by rw [r0]; exact hc1.inW (by omega)) ((k1.gpr _ (by decide)).trans h6) e5
    hsum (by decide) ?_) fun t ht => ?_
  · intro k hk s' hp
    have hc' := hc1.of_rest hp.rest (by decide)
    have hf : Frame [⟨State.addr b + BitVec.ofNat 64 TF, 4 * k⟩] s.mem s'.mem := by
      have := hp.frame; rwa [r0, m1] at this
    exact VG.Proof.Ed448.Arm.foldSrc_ok ⟨ho1, ho2⟩ hH hsum hk hc' hf
      (by rw [hp.rest.gpr _ (by decide)]; exact e1)
      (by rw [hp.rest.gpr _ (by decide), k1.gpr _ (by decide)])
  · generalize VG.Proof.Ed448.Arm.foldC (limb s.mem (State.addr b) o) (s.gpr .r11).toNat = c at ht hlt hmod
    have outs : ∀ k < 28, limb t.mem (State.addr b) TF k = VG.Proof.X25519.Arm.out c 0 k := by
      intro k hk; have := ht.outs k hk; rwa [r0] at this
    have hval := chain_val c 0 28
    have hlim : VG.Proof.Ed448.Arm.Lim28 t.mem (State.addr b) TF := fun k hk => by rw [outs k hk]; exact out_lt _ _ _
    have hV : VG.Proof.Ed448.Arm.V28 t.mem (State.addr b) TF = val16 c 28 := by
      have e : VG.Proof.Ed448.Arm.V28 t.mem (State.addr b) TF = val16 (VG.Proof.X25519.Arm.out c 0) 28 := val16_congr outs
      have hz : chain c 0 28 = 0 := by
        rcases Nat.eq_zero_or_pos (chain c 0 28) with h | h
        · exact h
        · have h448 := VG.Proof.Ed448.Arm.pow2_split 446 2 (16 * 28) rfl
          have := L_lt
          have := Nat.mul_le_mul_left (2 ^ (16 * 28 : Nat)) h
          omega
      generalize (2 : Nat) ^ (16 * 28) = P at hval
      rw [hz, Nat.mul_zero, Nat.add_zero, Nat.add_zero] at hval; exact e.trans hval
    refine ⟨(k1.mono (by decide)).trans (ht.rest.mono (by decide)), ?_, hlim, by rw [hV]; exact hlt,
      by rw [hV]; exact hmod⟩
    have := ht.frame; rw [r0, m1] at this; exact this

/-! ## The conditional subtraction -/

/-- One source of the subtraction: limb `k` of `TF` plus limb `k` of `K`. -/
theorem csubSrc_ok {k : Nat} (hk : k < 28) {s : State} (hc : VG.Proof.Ed448.Arm.Ctx8 b s)
    (hl : limb s.mem (State.addr b) TF k < 65536) :
    WP isa (.block (csubSrc k)) s fun s' =>
      (s'.gpr .r3).toNat = limb s.mem (State.addr b) TF k + kLimb k ∧ Rest [.r2, .r3, .r4] s s' ∧
        s'.mem = s.mem := by
  have hT := VG.Proof.Ed448.Arm.TF_eq
  unfold csubSrc
  by_cases hkk : k < 14 ∨ k = 27
  · rw [ite_eq_left hkk]
    refine ldr0_ok hc (d := TF + 4 * k) (by omega) fun s1 u1 => wp_movw fun s2 u2 =>
      wp_dp (op2_reg _ _) fun s3 u3 => WP.block_nil ⟨?_, (u1.rest (by decide)).trans
        ((u2.rest (by decide)).trans (u3.rest (by decide))), by rw [u3.mem, u2.mem, u1.mem]⟩
    have hkl := VG.Proof.Ed448.Arm.kLimb_lt k
    have e3 : (s2.gpr .r3).toNat = limb s.mem (State.addr b) TF k := by
      rw [u2.other _ (by decide), u1.gpr]; rfl
    have e2 : (s2.gpr .r2).toNat = kLimb k := by rw [u2.gpr, VG.Proof.Ed448.Arm.toNat_movw hkl]
    rw [u3.gpr]
    show (s2.gpr .r3 + s2.gpr .r2).toNat = _
    rw [toNat_add_lt (by rw [e3, e2]; omega), e3, e2]
  · rw [ite_eq_right hkk]
    refine ldr0_ok hc (d := TF + 4 * k) (by omega) fun s1 u1 => WP.block_nil
      ⟨?_, u1.rest (by decide), u1.mem⟩
    rw [u1.gpr, VG.Proof.Ed448.Arm.kLimb_mid (by omega) (by omega), Nat.add_zero]; rfl

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

theorem select_ok {o : Nat} (ho : VG.Proof.Ed448.Arm.Buf o) {s0 : State} (hc : VG.Proof.Ed448.Arm.Ctx8 b s0) {sw : Nat} (hsw : sw ≤ 1)
    (h9 : s0.gpr .r9 = 0 - BitVec.ofNat 32 sw) :
    WP isa (.block ((List.range 28).flatMap (VG.Impl.Ed448.Arm.selectStep o))) s0 (VG.Proof.Ed448.Arm.SelInv b o sw s0 28) := by
  obtain ⟨ho1, ho2⟩ := ho
  have hT := VG.Proof.Ed448.Arm.TF_eq
  refine wp_range_flatMap (M := isa) (VG.Proof.Ed448.Arm.SelInv b o sw s0) (fun k s hk h => ?_) 28 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hcs := hc.of_rest h.rest (by decide)
  have wo : wd s.mem (State.addr b) (o + 4 * k) = limb s0.mem (State.addr b) o k :=
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  have wt : wd s.mem (State.addr b) (TF + 4 * k) = limb s0.mem (State.addr b) TF k :=
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  unfold VG.Impl.Ed448.Arm.selectStep
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
    exact VG.Proof.Ed448.Arm.sel_mask _ _ hsw
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
theorem reduceT_ok {o : Nat} (ho : VG.Proof.Ed448.Arm.Buf o) {s : State} (hc : VG.Proof.Ed448.Arm.Ctx8 b s) (h6 : s.gpr .r6 = mask16)
    (hl : VG.Proof.Ed448.Arm.Lim28 s.mem (State.addr b) TF) (hv : VG.Proof.Ed448.Arm.V28 s.mem (State.addr b) TF < 2 * L) :
    WP isa (.block (reduceT o)) s fun t =>
      Rest [.r2, .r3, .r4, .r5, .r9] s t ∧ Frame [VG.Proof.Ed448.Arm.limbsR b o] s.mem t.mem ∧
      VG.Proof.Ed448.Arm.Lim28 t.mem (State.addr b) o ∧ VG.Proof.Ed448.Arm.V28 t.mem (State.addr b) o = VG.Proof.Ed448.Arm.V28 s.mem (State.addr b) TF % L := by
  obtain ⟨ho1, ho2⟩ := ho
  have hT := VG.Proof.Ed448.Arm.TF_eq
  unfold reduceT
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  have hc1 := hc.of_rest (u1.rest (ws := [.r5]) (by decide)) (by decide)
  have r0 : s1.gpr .r0 = b := hc1.r0
  refine WP.append (carryPass_ok (rb := .r0) (o := o) (s0 := s1)
    (c := fun k => limb s.mem (State.addr b) TF k + kLimb k) (cin := 0) (by decide)
    (by omega) (by rw [r0]; have := hc.fit; omega)
    (fun k hk => by rw [r0]; exact hc1.inW (by omega)) ((u1.other _ (by decide)).trans h6)
    (by rw [u1.gpr]; rfl) (fun k hk => by have := hl k hk; have := VG.Proof.Ed448.Arm.kLimb_lt k; omega) (by decide)
    ?_) fun s2 h2 => ?_
  · intro k hk s' hp
    have hc' := hc1.of_rest hp.rest (by decide)
    have hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 4 * k⟩] s.mem s'.mem := by
      have := hp.frame; rwa [r0, u1.mem] at this
    have et : limb s'.mem (State.addr b) TF k = limb s.mem (State.addr b) TF k :=
      wd_frame hf fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
    refine WP.mono (VG.Proof.Ed448.Arm.csubSrc_ok hk hc' (by rw [et]; exact hl k hk)) fun t ⟨e, kt, mt⟩ => ⟨?_, kt, mt⟩
    rw [e, et]
  generalize hcf : (fun k => limb s.mem (State.addr b) TF k + kLimb k) = c at h2
  have outs : ∀ k < 28, limb s2.mem (State.addr b) o k = VG.Proof.X25519.Arm.out c 0 k := by
    intro k hk; have := h2.outs k hk; rwa [r0] at this
  have hf2 : Frame [VG.Proof.Ed448.Arm.limbsR b o] s.mem s2.mem := by
    have := h2.frame; rwa [r0, u1.mem] at this
  have hval := (chain_val c 0 28).trans (Nat.add_zero _)
  have hcv : val16 c 28 = VG.Proof.Ed448.Arm.V28 s.mem (State.addr b) TF + (2 ^ (16 * 28 : Nat) - L) := by
    unfold VG.Proof.Ed448.Arm.V28; rw [← hcf, val16_add, VG.Proof.Ed448.Arm.val16_kLimb]
  have hy := val16_lt (f := VG.Proof.X25519.Arm.out c 0) (n := 28) fun k _ => out_lt _ _ _
  rw [hcv] at hval
  have hLM := VG.Proof.Ed448.Arm.two_L_le
  generalize (2 : Nat) ^ (16 * 28 : Nat) = M at hy hval hLM
  obtain ⟨hc1', hsel⟩ := VG.Proof.Ed448.Arm.csub_facts hLM hv hy hval
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
  refine WP.mono (VG.Proof.Ed448.Arm.select_ok ⟨ho1, ho2⟩ (hc.of_rest k4 (by decide)) hc1' h9) fun t ht => ?_
  have hlt : ∀ k < 28, limb t.mem (State.addr b) o k =
      if chain c 0 28 = 1 then VG.Proof.X25519.Arm.out c 0 k else limb s.mem (State.addr b) TF k := by
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
    unfold VG.Proof.Ed448.Arm.V28
    rw [val16_congr hlt]
    split
    · rfl
    · rfl

/-! ## One chunk -/

/-- What a step leaves unchanged: all but `r1`–`r5` and `r9` (and the flags),
and the memory outside `TF` and the remainder at `o`. -/
structure StepKeep (b : BitVec 32) (o : Nat) (s t : State) : Prop where
  rest : Rest [.r1, .r2, .r3, .r4, .r5, .r9] s t
  frame : Frame [VG.Proof.Ed448.Arm.limbsR b TF, VG.Proof.Ed448.Arm.limbsR b o] s.mem t.mem

/-- `step o`: the chunk in `r11` folded into the remainder at `o`. -/
theorem step_ok {o : Nat} (ho : VG.Proof.Ed448.Arm.Buf o) {s : State} (hc : VG.Proof.Ed448.Arm.Ctx8 b s) (h6 : s.gpr .r6 = mask16)
    (hl : VG.Proof.Ed448.Arm.Lim28 s.mem (State.addr b) o) (hv : VG.Proof.Ed448.Arm.V28 s.mem (State.addr b) o < L)
    (hw : (s.gpr .r11).toNat < 65536) :
    WP isa (.block (VG.Impl.Ed448.Arm.step o)) s fun t =>
      VG.Proof.Ed448.Arm.StepKeep b o s t ∧ VG.Proof.Ed448.Arm.Lim28 t.mem (State.addr b) o ∧
      VG.Proof.Ed448.Arm.V28 t.mem (State.addr b) o = ((s.gpr .r11).toNat + 65536 * VG.Proof.Ed448.Arm.V28 s.mem (State.addr b) o) % L := by
  unfold VG.Impl.Ed448.Arm.step
  refine WP.append (VG.Proof.Ed448.Arm.fold_ok ho hc h6 hl hv hw) fun u ⟨ku, fu, lu, vu, mu⟩ => ?_
  refine WP.mono (VG.Proof.Ed448.Arm.reduceT_ok ho (hc.of_rest ku (by decide)) ((ku.gpr _ (by decide)).trans h6) lu vu)
    fun t ⟨kt, ft, lt, vt⟩ => ⟨⟨(ku.mono (by decide)).trans (kt.mono (by decide)),
      (fu.mono (by simp)).trans (ft.mono (by simp))⟩, lt, by rw [vt, mu]⟩

end

end VG.Proof.Ed448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.ScalarLoop`. -/
section

/-!
# Ed448 scalar arithmetic on ARMv7: the loops

The remainder of an input's bytes from the top, sixteen bits at a time
(`byteLoop_ok`), and of the product's limbs (`limbLoop_ok`), and the
remainders they start from (`zeroR_ok`, `init57_ok`).
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X25519.Arm
open VG.Spec.Ed448 (L bytesAt decodeLE)

/-! ## The numbers -/

theorem mod_fold (w D : Nat) : (w + 65536 * (D % L)) % L = (w + 65536 * D) % L := by
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (VG.Spec.Ed448.bytesAt m p n).length = n := by
  simp only [VG.Spec.Ed448.bytesAt, List.length_map, List.length_range]

/-- Two bytes more of a suffix. -/
theorem decode_drop2 (m : Mem) (p : Addr) {N n : Nat} (h : n + 2 ≤ N) :
    decodeLE ((VG.Spec.Ed448.bytesAt m p N).drop n) = (m (p + BitVec.ofNat 64 n)).toNat +
      256 * (m (p + BitVec.ofNat 64 (n + 1))).toNat + 65536 * decodeLE ((VG.Spec.Ed448.bytesAt m p N).drop (n + 2)) := by
  rw [List.drop_eq_getElem_cons (by rw [VG.Proof.Ed448.Arm.bytesAt_length]; omega),
    List.drop_eq_getElem_cons (by rw [VG.Proof.Ed448.Arm.bytesAt_length]; omega)]
  simp only [decodeLE, VG.Spec.Ed448.bytesAt, List.getElem_map, List.getElem_range]
  rw [show n + 1 + 1 = n + 2 from rfl]
  omega

/-- A suffix as the bytes it starts with. -/
theorem decode_drop1 (m : Mem) (p : Addr) {N n : Nat} (h : n + 1 = N) :
    decodeLE ((VG.Spec.Ed448.bytesAt m p N).drop n) = (m (p + BitVec.ofNat 64 n)).toNat := by
  rw [List.drop_eq_getElem_cons (by rw [VG.Proof.Ed448.Arm.bytesAt_length]; omega),
    List.drop_eq_nil_of_le (by rw [VG.Proof.Ed448.Arm.bytesAt_length]; omega)]
  simp only [decodeLE, VG.Spec.Ed448.bytesAt, List.getElem_map, List.getElem_range, Nat.mul_zero, Nat.add_zero]

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
  have e10 : u1.gpr .r10 = BitVec.ofNat 32 n := by
    rw [v1.gpr]
    change s.gpr .r10 - BitVec.ofNat 32 2 = _
    rw [h10, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have e2 : u2.gpr .r2 = p + BitVec.ofNat 32 n := by
    rw [v2.gpr]; change u1.gpr .r12 + u1.gpr .r10 = _
    rw [v1.other _ (by decide), hp, e10]
  have hpn : (p + BitVec.ofNat 32 n).toNat = p.toNat + n := by
    rw [toNat_add_lt (by rw [toNat_imm (by omega)]; omega), toNat_imm (by omega)]
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 n) (by decide)
    (by rw [e2, BitVec.add_zero]; exact addr_add (by omega))
    (by rw [v2.rd, v2.wr, v1.rd, v1.wr]; exact hr n (by omega)) fun u3 v3 => ?_
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 (n + 1)) (by decide)
    (by rw [v3.other _ (by decide), e2, addr_add (by omega), addr_add (by omega), Offset.add_add])
    (by rw [v3.rd, v3.wr, v2.rd, v2.wr, v1.rd, v1.wr]; exact hr (n + 1) (by omega)) fun u4 v4 => ?_
  refine wp_dp (op2_lsl (by decide)) fun t vt => WP.block_nil ?_
  have m4 : u4.mem = s.mem := by rw [v4.mem, v3.mem, v2.mem, v1.mem]
  refine ⟨(v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans (vt.rest (by decide))))), by rw [vt.mem, m4], ?_, ?_⟩
  · rw [vt.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide),
      v2.other _ (by decide), e10]
  · rw [vt.gpr]
    show (u4.gpr .r11 + u4.gpr .r3 <<< 8).toNat = _
    have e11 : (u4.gpr .r11).toNat = (s.mem (State.addr p + BitVec.ofNat 64 n)).toNat := by
      rw [v4.other _ (by decide), v3.gpr, BitVec.toNat_setWidth_of_le (by decide), v2.mem, v1.mem]
    have e3 : (u4.gpr .r3).toNat = (s.mem (State.addr p + BitVec.ofNat 64 (n + 1))).toNat := by
      rw [v4.gpr, BitVec.toNat_setWidth_of_le (by decide), v3.mem, v2.mem, v1.mem]
    have b1 := (s.mem (State.addr p + BitVec.ofNat 64 (n + 1))).isLt
    have b0 := (s.mem (State.addr p + BitVec.ofNat 64 n)).isLt
    have e3' : (u4.gpr .r3 <<< 8).toNat = 256 * (s.mem (State.addr p + BitVec.ofNat 64 (n + 1))).toNat := by
      rw [toNat_shl, e3, Nat.mod_eq_of_lt (by omega)]; omega
    rw [toNat_add_lt (by rw [e11, e3']; omega), e11, e3']

/-! ## The byte loop -/

/-- What the loops change. -/
structure LoopKeep (b : BitVec 32) (o : Nat) (s t : State) : Prop where
  rest : Rest [.r1, .r2, .r3, .r4, .r5, .r9, .r10, .r11] s t
  frame : Frame [VG.Proof.Ed448.Arm.limbsR b TF, VG.Proof.Ed448.Arm.limbsR b o] s.mem t.mem

theorem LoopKeep.refl (b : BitVec 32) (o : Nat) (s : State) : VG.Proof.Ed448.Arm.LoopKeep b o s s :=
  ⟨Rest.refl _ _, Frame.refl _ _⟩

theorem LoopKeep.trans {o : Nat} {s t u : State} (h : VG.Proof.Ed448.Arm.LoopKeep b o s t) (h' : VG.Proof.Ed448.Arm.LoopKeep b o t u) :
    VG.Proof.Ed448.Arm.LoopKeep b o s u := ⟨h.rest.trans h'.rest, h.frame.trans h'.frame⟩

/-- After the steps from the top down to byte `n`. -/
structure ByteInv (b : BitVec 32) (o N : Nat) (p : Addr) (s0 : State) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ N
  even : n % 2 = 0
  counter : s.gpr .r10 = BitVec.ofNat 32 n
  limbs : VG.Proof.Ed448.Arm.Lim28 s.mem (State.addr b) o
  value : VG.Proof.Ed448.Arm.V28 s.mem (State.addr b) o = decodeLE ((VG.Spec.Ed448.bytesAt s0.mem p N).drop n) % L
  keeps : VG.Proof.Ed448.Arm.LoopKeep b o s0 s

theorem byteLoop_ok {o N : Nat} (ho : VG.Proof.Ed448.Arm.Buf o) {p : BitVec 32} {s0 : State} (hc : VG.Proof.Ed448.Arm.Ctx8 b s0)
    (h6 : s0.gpr .r6 = mask16) (hp : s0.gpr .r12 = p) (hfit : p.toNat + N ≤ 2 ^ 32)
    (hread : ∀ i < N, InRegions (s0.rd ++ s0.wr) (State.addr p + BitVec.ofNat 64 i) 1)
    (hsep : ∀ r ∈ [VG.Proof.Ed448.Arm.limbsR b TF, VG.Proof.Ed448.Arm.limbsR b o], (⟨State.addr p, N⟩ : Region).Disjoint r)
    {n0 : Nat} (hn0 : 0 < n0) (hle : n0 ≤ N) (heven : n0 % 2 = 0)
    (h10 : s0.gpr .r10 = BitVec.ofNat 32 n0) (hl : VG.Proof.Ed448.Arm.Lim28 s0.mem (State.addr b) o)
    (hv : VG.Proof.Ed448.Arm.V28 s0.mem (State.addr b) o = decodeLE ((VG.Spec.Ed448.bytesAt s0.mem (State.addr p) N).drop n0) % L) :
    WP isa (.loop (.block (byteStep o)) .ne) s0 fun t => VG.Proof.Ed448.Arm.LoopKeep b o s0 t ∧
      VG.Proof.Ed448.Arm.Lim28 t.mem (State.addr b) o ∧
      VG.Proof.Ed448.Arm.V28 t.mem (State.addr b) o = decodeLE (VG.Spec.Ed448.bytesAt s0.mem (State.addr p) N) % L := by
  have hN : N ≤ 2 ^ 32 := by omega
  apply WP.loop (VG.Proof.Ed448.Arm.ByteInv b o N (State.addr p) s0) (n := n0)
  · intro n s hi
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by have := hi.even; have := hi.positive; omega⟩
    have hk : k + 2 ≤ N := hi.bound
    have hcs : VG.Proof.Ed448.Arm.Ctx8 b s := hc.of_rest hi.keeps.rest (by decide)
    have hps : s.gpr .r12 = p := (hi.keeps.rest.gpr _ (by decide)).trans hp
    have hrs : ∀ i < N, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1 := by
      rw [hi.keeps.rest.rd, hi.keeps.rest.wr]; exact hread
    unfold byteStep
    rw [List.append_assoc]
    refine WP.append (VG.Proof.Ed448.Arm.readBytes_ok hk hps hfit hi.counter hrs) fun u ⟨ku, mu, cu, wu⟩ => ?_
    have hcu : VG.Proof.Ed448.Arm.Ctx8 b u := hcs.of_rest ku (by decide)
    have h6u : u.gpr .r6 = mask16 :=
      (ku.gpr _ (by decide)).trans ((hi.keeps.rest.gpr _ (by decide)).trans h6)
    have hwu : (u.gpr .r11).toNat < 65536 := by
      rw [wu]
      have := (s.mem (State.addr p + BitVec.ofNat 64 k)).isLt
      have := (s.mem (State.addr p + BitVec.ofNat 64 (k + 1))).isLt
      omega
    refine WP.append (VG.Proof.Ed448.Arm.step_ok ho hcu h6u (mu ▸ hi.limbs)
      (by rw [mu, hi.value]; exact Nat.mod_lt _ L_pos) hwu) fun v ⟨kv, lv, vv⟩ => ?_
    refine wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
    have mb : ∀ i < N, s.mem (State.addr p + BitVec.ofNat 64 i) =
        s0.mem (State.addr p + BitVec.ofNat 64 i) :=
      fun i hi' => hi.keeps.frame.bytes hsep (by show N ≤ 2 ^ 64; omega) hi'
    have val : VG.Proof.Ed448.Arm.V28 t.mem (State.addr b) o = decodeLE ((VG.Spec.Ed448.bytesAt s0.mem (State.addr p) N).drop k) % L := by
      rw [ht.mem, vv, wu, mu, hi.value, VG.Proof.Ed448.Arm.mod_fold, mb k (by omega), mb (k + 1) (by omega),
        VG.Proof.Ed448.Arm.decode_drop2 _ _ hk]
    have keep : VG.Proof.Ed448.Arm.LoopKeep b o s0 t := hi.keeps.trans
      ⟨(ku.mono (by decide)).trans ((kv.rest.mono (by decide)).trans (ht.rest _)),
        by rw [ht.mem, ← mu]; exact kv.frame⟩
    have c10 : t.gpr .r10 = BitVec.ofNat 32 k := by
      rw [ht.gpr, kv.rest.gpr _ (by decide), cu]
    have zt : t.z = decide (k = 0) := by
      have he : BitVec.ofNat 32 k - (0 : BitVec 32) = BitVec.ofNat 32 k := BitVec.sub_zero _
      rw [hz, kv.rest.gpr _ (by decide), cu, he, ofNat_beq_zero (by omega)]
    by_cases k0 : k = 0
    · subst k0
      refine .inl ⟨by rw [eval_ne, zt]; rfl, keep, ht.mem ▸ lv, ?_⟩
      simpa only [List.drop_zero] using val
    · refine .inr ⟨by rw [eval_ne, zt]; simp only [k0, decide_false, Bool.not_false], k, by omega,
        ⟨by omega, by omega, by have := hi.even; omega, c10, ht.mem ▸ lv, val, keep⟩⟩
  · exact ⟨hn0, hle, heven, h10, hl, hv, LoopKeep.refl _ _ _⟩

/-! ## The product's limbs -/

theorem ACC_eq : Impl.X448.Arm.ACC = 3584 := rfl

theorem readLimb_ok {s : State} (hc : VG.Proof.Ed448.Arm.Ctx8 b s) {j : Nat} (hj : j < 56)
    (h10 : s.gpr .r10 = BitVec.ofNat 32 (4 * (j + 1))) :
    WP isa (.block readLimb) s fun t =>
      Rest [.r2, .r10, .r11] s t ∧ t.mem = s.mem ∧ t.gpr .r10 = BitVec.ofNat 32 (4 * j) ∧
      (t.gpr .r11).toNat = limb s.mem (State.addr b) Impl.X448.Arm.ACC j := by
  have hA := VG.Proof.Ed448.Arm.ACC_eq
  have hfit := hc.fit
  unfold readLimb
  refine wp_dp (op2_imm (by decide)) fun u1 v1 => wp_dp (op2_reg _ _) fun u2 v2 => ?_
  have e10 : u1.gpr .r10 = BitVec.ofNat 32 (4 * j) := by
    rw [v1.gpr]
    change s.gpr .r10 - BitVec.ofNat 32 4 = _
    rw [h10, show 4 * (j + 1) = 4 * j + 4 by omega, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have e2 : u2.gpr .r2 = b + BitVec.ofNat 32 (4 * j) := by
    rw [v2.gpr]; change u1.gpr .r0 + u1.gpr .r10 = _
    rw [v1.other _ (by decide), hc.r0, e10]
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (Impl.X448.Arm.ACC + 4 * j)) (by omega)
    (by rw [e2, Offset.add_add]; rw [Nat.add_comm]; exact addr_add (by omega))
    (by rw [v2.rd, v2.wr, v1.rd, v1.wr]; exact hc.inR (by omega)) fun t vt => WP.block_nil ?_
  refine ⟨(v1.rest (by decide)).trans ((v2.rest (by decide)).trans (vt.rest (by decide))),
    by rw [vt.mem, v2.mem, v1.mem], by rw [vt.other _ (by decide), v2.other _ (by decide), e10], ?_⟩
  rw [vt.gpr, v2.mem, v1.mem]; rfl

/-- The number of the product's limbs from `j` up. -/
abbrev accFrom (m : Mem) (B : Addr) (j : Nat) : Nat :=
  val16 (fun i => limb m B Impl.X448.Arm.ACC (j + i)) (56 - j)

theorem accFrom_step (m : Mem) (B : Addr) {j : Nat} (hj : j < 56) :
    VG.Proof.Ed448.Arm.accFrom m B j = limb m B Impl.X448.Arm.ACC j + 65536 * VG.Proof.Ed448.Arm.accFrom m B (j + 1) := by
  unfold VG.Proof.Ed448.Arm.accFrom
  rw [show 56 - j = 1 + (56 - (j + 1)) by omega, val16_append]
  simp only [val16, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero]
  refine congrArg (_ + ·) (congrArg (65536 * ·) (val16_congr fun i _ => ?_))
  rw [Nat.add_assoc]

/-- After the steps from the top limb down to limb `j`. -/
structure LimbInv (b : BitVec 32) (s0 : State) (j : Nat) (s : State) : Prop where
  positive : 0 < j
  bound : j ≤ 56
  counter : s.gpr .r10 = BitVec.ofNat 32 (4 * j)
  limbs : VG.Proof.Ed448.Arm.Lim28 s.mem (State.addr b) RA
  value : VG.Proof.Ed448.Arm.V28 s.mem (State.addr b) RA = VG.Proof.Ed448.Arm.accFrom s0.mem (State.addr b) j % L
  keeps : VG.Proof.Ed448.Arm.LoopKeep b RA s0 s

theorem limbLoop_ok {s0 : State} (hc : VG.Proof.Ed448.Arm.Ctx8 b s0) (h6 : s0.gpr .r6 = mask16)
    (hacc : ∀ j < 56, limb s0.mem (State.addr b) Impl.X448.Arm.ACC j < 65536)
    (h10 : s0.gpr .r10 = BitVec.ofNat 32 (4 * 56)) (hl : VG.Proof.Ed448.Arm.Lim28 s0.mem (State.addr b) RA)
    (hv : VG.Proof.Ed448.Arm.V28 s0.mem (State.addr b) RA = 0) :
    WP isa (.loop (.block limbStep) .ne) s0 fun t => VG.Proof.Ed448.Arm.LoopKeep b RA s0 t ∧
      VG.Proof.Ed448.Arm.Lim28 t.mem (State.addr b) RA ∧
      VG.Proof.Ed448.Arm.V28 t.mem (State.addr b) RA = val16 (limb s0.mem (State.addr b) Impl.X448.Arm.ACC) 56 % L := by
  have hA := VG.Proof.Ed448.Arm.ACC_eq
  have hT := VG.Proof.Ed448.Arm.TF_eq
  have hR : RA = 192 := rfl
  have ho : VG.Proof.Ed448.Arm.Buf RA := ⟨by omega, by omega⟩
  apply WP.loop (VG.Proof.Ed448.Arm.LimbInv b s0) (n := 56)
  · intro n s hi
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by have := hi.positive; omega⟩
    have hj : j < 56 := hi.bound
    have hcs : VG.Proof.Ed448.Arm.Ctx8 b s := hc.of_rest hi.keeps.rest (by decide)
    have la : ∀ i < 56, limb s.mem (State.addr b) Impl.X448.Arm.ACC i =
        limb s0.mem (State.addr b) Impl.X448.Arm.ACC i := fun i hi' =>
      wd_frame hi.keeps.frame fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by omega)
    unfold limbStep
    rw [List.append_assoc]
    refine WP.append (VG.Proof.Ed448.Arm.readLimb_ok hcs hj hi.counter) fun u ⟨ku, mu, cu, wu⟩ => ?_
    have hcu : VG.Proof.Ed448.Arm.Ctx8 b u := hcs.of_rest ku (by decide)
    have h6u : u.gpr .r6 = mask16 :=
      (ku.gpr _ (by decide)).trans ((hi.keeps.rest.gpr _ (by decide)).trans h6)
    have hwu : (u.gpr .r11).toNat < 65536 := by rw [wu, la j hj]; exact hacc j hj
    refine WP.append (VG.Proof.Ed448.Arm.step_ok ho hcu h6u (mu ▸ hi.limbs)
      (by rw [mu, hi.value]; exact Nat.mod_lt _ L_pos) hwu) fun v ⟨kv, lv, vv⟩ => ?_
    refine wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
    have val : VG.Proof.Ed448.Arm.V28 t.mem (State.addr b) RA = VG.Proof.Ed448.Arm.accFrom s0.mem (State.addr b) j % L := by
      rw [ht.mem, vv, wu, mu, hi.value, VG.Proof.Ed448.Arm.mod_fold, la j hj, VG.Proof.Ed448.Arm.accFrom_step _ _ hj]
    have keep : VG.Proof.Ed448.Arm.LoopKeep b RA s0 t := hi.keeps.trans
      ⟨(ku.mono (by decide)).trans ((kv.rest.mono (by decide)).trans (ht.rest _)),
        by rw [ht.mem, ← mu]; exact kv.frame⟩
    have c10 : t.gpr .r10 = BitVec.ofNat 32 (4 * j) := by
      rw [ht.gpr, kv.rest.gpr _ (by decide), cu]
    have zt : t.z = decide (j = 0) := by
      have he : BitVec.ofNat 32 (4 * j) - (0 : BitVec 32) = BitVec.ofNat 32 (4 * j) := BitVec.sub_zero _
      rw [hz, kv.rest.gpr _ (by decide), cu, he, ofNat_beq_zero (by omega)]
      exact decide_eq_decide.mpr (by omega)
    by_cases j0 : j = 0
    · subst j0
      refine .inl ⟨by rw [eval_ne, zt]; rfl, keep, ht.mem ▸ lv, ?_⟩
      rw [val]
      exact congrArg (· % L) (val16_congr fun i _ => by rw [Nat.zero_add])
    · refine .inr ⟨by rw [eval_ne, zt]; simp only [j0, decide_false, Bool.not_false], j, by omega,
        ⟨by omega, by omega, c10, ht.mem ▸ lv, val, keep⟩⟩
  · refine ⟨by decide, by decide, h10, hl, ?_, LoopKeep.refl _ _ _⟩
    rw [hv]
    exact (Nat.zero_mod _).symm.trans (by rfl)

/-! ## The remainders the loops start from -/

theorem zeroR_ok {o : Nat} (ho : o + 112 ≤ 4096) {s : State} (hc : VG.Proof.Ed448.Arm.Ctx8 b s) :
    WP isa (.block (zeroR o)) s fun t =>
      Rest [.r3] s t ∧ Frame [VG.Proof.Ed448.Arm.limbsR b o] s.mem t.mem ∧ ∀ k < 28, limb t.mem (State.addr b) o k = 0 := by
  unfold zeroR
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  have hc1 := hc.of_rest (u1.rest (ws := [.r3]) (by decide)) (by decide)
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n t => Rest [] s1 t ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 4 * n⟩] s1.mem t.mem ∧
      ∀ k < n, limb t.mem (State.addr b) o k = 0)
    (fun n t hn ⟨h1, h2, h3⟩ => ?_) 28 (Nat.le_refl _) s1
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun t ⟨h1, h2, h3⟩ => ⟨(u1.rest (by decide)).trans (h1.mono (by decide)),
      by rw [← u1.mem]; exact h2, h3⟩
  refine str0_ok (hc1.of_rest h1 (by decide)) (d := o + 4 * n) (by omega) fun t2 v2 =>
    WP.block_nil ⟨h1.trans (v2.rest _), ?_, fun k hk => ?_⟩
  · rw [v2.mem]
    exact (h2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) (t.gpr .r3)
      (Offset.contains _ (d := o + 4 * n) (n := 4) (e := o) (k := 4 * (n + 1)) (by omega) (by omega)
        (by omega))
  · show wd t2.mem _ _ = 0
    rw [v2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h3 k hk
    · rw [wd_write_self, h1.gpr _ (by decide), u1.gpr]; rfl

theorem V28_zero {m : Mem} {B : Addr} {o : Nat} (h : ∀ k < 28, limb m B o k = 0) : VG.Proof.Ed448.Arm.V28 m B o = 0 :=
  (val16_congr h).trans (val16_zero_fn 28)

theorem Lim28_zero {m : Mem} {B : Addr} {o : Nat} (h : ∀ k < 28, limb m B o k = 0) : VG.Proof.Ed448.Arm.Lim28 m B o :=
  fun k hk => by rw [h k hk]; decide


end

end VG.Proof.Ed448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.ScalarIO`. -/
section

/-!
# Ed448 scalar arithmetic on ARMv7: entry and exit

The callee-saved registers saved in the working space (`saveAt_ok`) and
restored (`restore_ok`), the remainders the input loops start from
(`reduce114_ok`, `reduce57_ok`), and the result: the remainder's limbs as 56
bytes and a zero byte (`pack_ok`), which are its encoding (`encode_57`).
-/

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
      VG.Proof.Ed448.Arm.Saved (State.addr b) s.gpr s'.mem ∧ Frame [⟨State.addr b, 32⟩] s.mem s'.mem ∧
        s'.gpr = s.gpr ∧ Rest [] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.mem.readW (State.addr b + BitVec.ofNat 64 (4 * i)) 32 = s.gpr (savedReg i)) ∧
      Frame [⟨State.addr b, 4 * n⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s')
    (fun n s' hn ⟨h1, h2, h3', h4⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, rfl, Rest.refl _ _⟩)
    fun s' h => ⟨h.1, h.2.1, h.2.2⟩
  refine wp_str (a := State.addr b + BitVec.ofNat 64 (4 * n)) (by omega)
    (by rw [h3', h3]; exact addr_add (by omega)) (by rw [h4.wr]; exact in_base hw (by omega) (by omega))
    fun s2 u2 => WP.block_nil ⟨fun i hi => ?_, ?_, by rw [u2.gpr, h3'], h4.trans (u2.rest _)⟩
  · rw [u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]; exact h1 i hi
    · rw [Mem.readW_writeW_self32, h3']
  · rw [u2.mem]
    exact (h2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

theorem restore_ok {s : State} (hc : VG.Proof.Ed448.Arm.Ctx8 b s) {g : Reg → BitVec 32} (hs : VG.Proof.Ed448.Arm.Saved (State.addr b) g s.mem) :
    WP isa (.block restore) s fun s' => (∀ i < 8, s'.gpr (savedReg i) = g (savedReg i)) ∧
      Rest [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s' ∧ s'.mem = s.mem := by
  have hsr : ∀ i < 8, savedReg i ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] := by decide
  have hinj : ∀ i < 8, ∀ j < 8, savedReg i = savedReg j → i = j := by decide
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.gpr (savedReg i) = g (savedReg i)) ∧
      Rest [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s' ∧ s'.mem = s.mem)
    (fun n s' hn ⟨hl, hr, hm⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Rest.refl _ _, rfl⟩) fun s' h => h
  refine ldr0_ok (hc.of_rest hr (by decide)) (d := 4 * n) (by omega) fun s1 u1 =>
    WP.block_nil ⟨fun i hi => ?_, hr.trans (u1.rest (hsr n hn)), by rw [u1.mem, hm]⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
  · rw [u1.other _ (fun e => absurd (hinj _ (by omega) _ hn e) (by omega))]; exact hl i h'
  · rw [u1.gpr, hm, hs i hn]

/-- The saved registers stay where no code writes. -/
theorem Saved.frame {g : Reg → BitVec 32} {m m' : Mem} (hs : VG.Proof.Ed448.Arm.Saved (State.addr b) g m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, ∀ i < 8, Region.Disjoint ⟨State.addr b + BitVec.ofNat 64 (4 * i), 4⟩ r) :
    VG.Proof.Ed448.Arm.Saved (State.addr b) g m' := fun i hi => by
  rw [hf.readW (Region.contains_self _ _) (fun r hr => hd r hr i hi) (by decide)]; exact hs i hi

/-! ## The remainders of the inputs -/

theorem init114_ok {o : Nat} (ho : VG.Proof.Ed448.Arm.Buf o) {s : State} (hc : VG.Proof.Ed448.Arm.Ctx8 b s) :
    WP isa (.block (zeroR o ++ ([.mov .r10 (.imm 114)] : List Instr))) s fun v => VG.Proof.Ed448.Arm.LoopKeep b o s v ∧
      v.gpr .r10 = BitVec.ofNat 32 114 ∧ VG.Proof.Ed448.Arm.Lim28 v.mem (State.addr b) o ∧ VG.Proof.Ed448.Arm.V28 v.mem (State.addr b) o = 0 :=
  WP.append (VG.Proof.Ed448.Arm.zeroR_ok ho.2 hc) fun u ⟨ku, fu, zu⟩ =>
    wp_mov (op2_imm (by decide)) fun v hv => WP.block_nil
      ⟨⟨(ku.mono (by decide)).trans (hv.rest (by decide)), by rw [hv.mem]; exact fu.mono (by simp)⟩,
        hv.gpr, by rw [hv.mem]; exact VG.Proof.Ed448.Arm.Lim28_zero zu, by rw [hv.mem]; exact VG.Proof.Ed448.Arm.V28_zero zu⟩

/-- The bytes of an input across a frame of regions it does not overlap. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {N : Nat}
    (hd : ∀ r ∈ rs, (⟨p, N⟩ : Region).Disjoint r) (hN : N ≤ 2 ^ 64) :
    VG.Spec.Ed448.bytesAt m' p N = VG.Spec.Ed448.bytesAt m p N := by
  unfold VG.Spec.Ed448.bytesAt; apply List.map_congr_left
  intro n hn
  exact hf.bytes hd hN (List.mem_range.mp hn)

theorem reduce114_ok {o : Nat} (ho : VG.Proof.Ed448.Arm.Buf o) {p : BitVec 32} {s : State} (hc : VG.Proof.Ed448.Arm.Ctx8 b s)
    (h6 : s.gpr .r6 = mask16) (hp : s.gpr .r12 = p) (hfit : p.toNat + 114 ≤ 2 ^ 32)
    (hread : ∀ i < 114, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1)
    (hsep : ∀ r ∈ [VG.Proof.Ed448.Arm.limbsR b TF, VG.Proof.Ed448.Arm.limbsR b o], (⟨State.addr p, 114⟩ : Region).Disjoint r) :
    WP isa (reduce114 o) s fun t => VG.Proof.Ed448.Arm.LoopKeep b o s t ∧ VG.Proof.Ed448.Arm.Lim28 t.mem (State.addr b) o ∧
      VG.Proof.Ed448.Arm.V28 t.mem (State.addr b) o = decodeLE (VG.Spec.Ed448.bytesAt s.mem (State.addr p) 114) % L := by
  unfold reduce114
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.init114_ok ho hc) fun v ⟨kv, cv, lv, vv⟩ => ?_)
  have mb := VG.Proof.Ed448.Arm.bytesAt_frame kv.frame hsep (by decide)
  refine WP.mono (VG.Proof.Ed448.Arm.byteLoop_ok (N := 114) ho (hc.of_rest kv.rest (by decide))
    ((kv.rest.gpr _ (by decide)).trans h6) ((kv.rest.gpr _ (by decide)).trans hp) hfit
    (by rw [kv.rest.rd, kv.rest.wr]; exact hread) hsep (n0 := 114) (by decide) (by decide)
    (by decide) cv lv (by rw [vv, List.drop_eq_nil_of_le (by rw [VG.Proof.Ed448.Arm.bytesAt_length]), show decodeLE [] = 0 from rfl,
      Nat.zero_mod]))
    fun t ⟨kt, lt, vt⟩ => ⟨kv.trans kt, lt, by rw [vt, mb]⟩

theorem init57_ok {o : Nat} (ho : VG.Proof.Ed448.Arm.Buf o) {p : BitVec 32} {s : State} (hc : VG.Proof.Ed448.Arm.Ctx8 b s)
    (hp : s.gpr .r12 = p) (hfit : p.toNat + 57 ≤ 2 ^ 32)
    (hread : ∀ i < 57, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1)
    (hsep : ∀ r ∈ [VG.Proof.Ed448.Arm.limbsR b TF, VG.Proof.Ed448.Arm.limbsR b o], (⟨State.addr p, 57⟩ : Region).Disjoint r) :
    WP isa (.block (zeroR o ++ ([.ldrb .r3 .r12 56, .str .r3 .r0 o, .mov .r10 (.imm 56)] : List Instr))) s fun v =>
      VG.Proof.Ed448.Arm.LoopKeep b o s v ∧ v.gpr .r10 = BitVec.ofNat 32 56 ∧ VG.Proof.Ed448.Arm.Lim28 v.mem (State.addr b) o ∧
      VG.Proof.Ed448.Arm.V28 v.mem (State.addr b) o = decodeLE ((VG.Spec.Ed448.bytesAt s.mem (State.addr p) 57).drop 56) % L := by
  obtain ⟨ho1, ho2⟩ := ho
  have hT := VG.Proof.Ed448.Arm.TF_eq
  refine WP.append (VG.Proof.Ed448.Arm.zeroR_ok ho2 hc) fun u ⟨ku, fu, zu⟩ => ?_
  have hpu : u.gpr .r12 = p := (ku.gpr _ (by decide)).trans hp
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 56) (by decide)
    (by rw [hpu]; exact addr_add (by omega)) (by rw [ku.rd, ku.wr]; exact hread 56 (by decide))
    fun u1 v1 => ?_
  refine str0_ok (hc.of_rest (ku.trans (v1.rest (ws := [.r3]) (by decide))) (by decide)) (d := o)
    (by omega) fun u2 v2 => wp_mov (op2_imm (by decide)) fun v hv => WP.block_nil ?_
  have m2 : v.mem = u.mem.writeW (State.addr b + BitVec.ofNat 64 (o + 4 * 0))
      ((u.mem (State.addr p + BitVec.ofNat 64 56)).setWidth 32) := by
    rw [hv.mem, v2.mem, v1.gpr, v1.mem]; rfl
  have lv : ∀ k < 28, limb v.mem (State.addr b) o k =
      if k = 0 then (u.mem (State.addr p + BitVec.ofNat 64 56)).toNat else 0 := by
    intro k hk
    show wd v.mem _ _ = _
    rw [m2]
    by_cases k0 : k = 0
    · subst k0
      rw [wd_write_self, BitVec.toNat_setWidth_of_le (by decide)]; rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega), ite_eq_right k0]; exact zu k hk
  have fv : Frame [VG.Proof.Ed448.Arm.limbsR b o] s.mem v.mem := by
    rw [m2]
    exact fu.writeW (List.mem_singleton_self _) _ (Offset.contains _ (d := o + 4 * 0) (n := 4) (e := o)
      (k := 112) (by omega) (by omega) (by omega))
  have hbyte : (u.mem (State.addr p + BitVec.ofNat 64 56)).toNat =
      (s.mem (State.addr p + BitVec.ofNat 64 56)).toNat := by
    rw [fu.bytes (R := ⟨State.addr p, 57⟩) (fun r hr => hsep r (by
      simp only [List.mem_singleton] at hr; simp [hr])) (by show 57 ≤ 2 ^ 64; omega) (by decide : 56 < 57)]
  have hlt := (u.mem (State.addr p + BitVec.ofNat 64 56)).isLt
  refine ⟨⟨((ku.mono (by decide)).trans ((v1.rest (by decide)).trans ((v2.rest _).trans
    (hv.rest (by decide))))), fv.mono (by simp)⟩, hv.gpr, fun k hk => ?_, ?_⟩
  · rw [lv k hk]; split
    · omega
    · decide
  · rw [VG.Proof.Ed448.Arm.decode_drop1 _ _ (by decide : 56 + 1 = 57), ← hbyte]
    have hL : 256 < L := by decide +kernel
    rw [Nat.mod_eq_of_lt (by omega)]
    unfold VG.Proof.Ed448.Arm.V28
    rw [show (28 : Nat) = 1 + 27 from rfl, val16_append,
      val16_congr (n := 27) (g := fun _ => 0) (fun k hk => by rw [lv _ (by omega), ite_eq_right (by omega)]),
      val16_zero_fn]
    simp only [val16, lv 0 (by decide), ite_true, Nat.mul_zero, Nat.pow_zero, Nat.one_mul,
      Nat.zero_add, Nat.add_zero]

theorem reduce57_ok {o : Nat} (ho : VG.Proof.Ed448.Arm.Buf o) {p : BitVec 32} {s : State} (hc : VG.Proof.Ed448.Arm.Ctx8 b s)
    (h6 : s.gpr .r6 = mask16) (hp : s.gpr .r12 = p) (hfit : p.toNat + 57 ≤ 2 ^ 32)
    (hread : ∀ i < 57, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1)
    (hsep : ∀ r ∈ [VG.Proof.Ed448.Arm.limbsR b TF, VG.Proof.Ed448.Arm.limbsR b o], (⟨State.addr p, 57⟩ : Region).Disjoint r) :
    WP isa (reduce57 o) s fun t => VG.Proof.Ed448.Arm.LoopKeep b o s t ∧ VG.Proof.Ed448.Arm.Lim28 t.mem (State.addr b) o ∧
      VG.Proof.Ed448.Arm.V28 t.mem (State.addr b) o = decodeLE (VG.Spec.Ed448.bytesAt s.mem (State.addr p) 57) % L := by
  unfold reduce57
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.init57_ok ho hc hp hfit hread hsep) fun v ⟨kv, cv, lv, vv⟩ => ?_)
  have mb := VG.Proof.Ed448.Arm.bytesAt_frame kv.frame hsep (by decide)
  refine WP.mono (VG.Proof.Ed448.Arm.byteLoop_ok (N := 57) ho (hc.of_rest kv.rest (by decide))
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

theorem pack_ok {q : BitVec 32} {o : Nat} (ho : o + 112 ≤ 4096) {s0 : State} (hc : VG.Proof.Ed448.Arm.Ctx8 b s0)
    (hq : s0.gpr .r12 = q) (hfit : q.toNat + 57 ≤ 2 ^ 32)
    (hw : (⟨State.addr q, 57⟩ : Region) ∈ s0.wr)
    (hsep : (⟨State.addr q, 57⟩ : Region).Disjoint ⟨State.addr b, 8192⟩) :
    WP isa (.block ((List.range 28).flatMap (packLimb o))) s0
      (VG.Proof.Ed448.Arm.PackInv (State.addr q) (limb s0.mem (State.addr b) o) s0 28) := by
  let O := State.addr q
  refine wp_range_flatMap (M := isa) (VG.Proof.Ed448.Arm.PackInv O (limb s0.mem (State.addr b) o) s0)
    (fun k s hk h => ?_) 28 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => by omega, fun _ h => by omega⟩
  have hcs := hc.of_rest h.rest (by decide)
  have hq' : s.gpr .r12 = q := (h.rest.gpr _ (by decide)).trans hq
  have he : wd s.mem (State.addr b) (o + 4 * k) = limb s0.mem (State.addr b) o k :=
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (hsep.symm.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by omega))
  unfold packLimb
  refine ldr0_ok hcs (by omega) fun s1 u1 => ?_
  have e1 : (s1.gpr .r3).toNat = limb s0.mem (State.addr b) o k := by rw [u1.gpr]; exact he
  refine wp_strb (a := O + BitVec.ofNat 64 (2 * k)) (by omega)
    (by rw [u1.other _ (by decide), hq', addr_add (by omega)])
    (by rw [u1.wr, h.rest.wr]; exact in_base hw (by omega) (by omega))
    fun s2 u2 => wp_mov (op2_lsr (by decide)) fun s3 u3 => ?_
  refine wp_strb (a := O + BitVec.ofNat 64 (2 * k + 1)) (by omega)
    (by rw [u3.other _ (by decide), u2.gpr, u1.other _ (by decide), hq', addr_add (by omega)])
    (by rw [u3.wr, u2.wr, u1.wr, h.rest.wr]; exact in_base hw (by omega) (by omega))
    fun t ht => WP.block_nil ?_
  have hm : t.mem = (s.mem.writeW (O + BitVec.ofNat 64 (2 * k)) ((s1.gpr .r3).setWidth 8)).writeW
      (O + BitVec.ofNat 64 (2 * k + 1)) ((s1.gpr .r3 >>> 8).setWidth 8) := by
    rw [ht.mem, u3.gpr, u2.gpr, u3.mem, u2.mem, u1.mem]
  have ne : ∀ i j : Nat, i < 57 → j < 57 → i ≠ j → O + BitVec.ofNat 64 i ≠ O + BitVec.ofNat 64 j :=
    fun i j hi hj hij => Offset.add_ofNat_ne _ (by omega) (by omega) hij
  refine ⟨h.rest.trans ((u1.rest (by decide)).trans ((u2.rest _).trans
    ((u3.rest (by decide)).trans (ht.rest _)))), ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hm]
    refine ((h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [hm, VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply,
      ite_eq_right (ne _ _ (by omega) (by omega) (by omega))]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right (ne _ _ (by omega) (by omega) (by omega))]; exact h.b0 i hi
    · rw [ite_eq_left rfl]; exact VG.Proof.Ed448.Arm.byte_eq e1
  · rw [hm, VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right (ne _ _ (by omega) (by omega) (by omega)),
        ite_eq_right (ne _ _ (by omega) (by omega) (by omega))]
      exact h.b1 i hi
    · rw [ite_eq_left rfl]; exact VG.Proof.Ed448.Arm.byte_eq (by rw [toNat_shr, e1])

/-- Twenty-eight 16-bit limbs and a zero byte are the 57-byte encoding of
their number. -/
theorem encode_57 {m : Mem} {q : Addr} {f : Nat → Nat} (hl : ∀ k < 28, f k < 65536)
    (h0 : ∀ k < 28, m (q + BitVec.ofNat 64 (2 * k)) = BitVec.ofNat 8 (f k))
    (h1 : ∀ k < 28, m (q + BitVec.ofNat 64 (2 * k + 1)) = BitVec.ofNat 8 (f k / 256))
    (h56 : m (q + BitVec.ofNat 64 56) = 0) :
    VG.Spec.Ed448.bytesAt m q 57 = encodeLE 57 (val16 f 28) := by
  let g : Nat → Nat := fun k => if k < 28 then f k else 0
  have hg : ∀ k < 29, g k < 65536 := fun k _ => by
    simp only [g]; split
    · exact hl k (by omega)
    · decide
  have hv : val16 f 28 = val16 g 29 := by
    have e1 := val16_succ g 28
    have e2 : g 28 = 0 := rfl
    rw [e2] at e1
    have e3 : val16 f 28 = val16 g 28 := val16_congr fun k hk => (ite_eq_left hk).symm
    exact e3.trans ((Nat.add_zero _).symm.trans
      ((congrArg (val16 g 28 + ·) (Nat.mul_zero _).symm).trans e1.symm))
  apply List.ext_getElem (by rw [VG.Proof.Ed448.Arm.bytesAt_length]; simp only [encodeLE, List.length_map, List.length_range])
  intro i hi _
  rw [VG.Proof.Ed448.Arm.bytesAt_length] at hi
  simp only [VG.Spec.Ed448.bytesAt, encodeLE, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, hv]
  obtain ⟨k, rfl | rfl⟩ : ∃ k, i = 2 * k ∨ i = 2 * k + 1 := ⟨i / 2, by omega⟩
  · have hd := val16_div hg (k := k) (by omega)
    rw [show 8 * (2 * k) = 16 * k by omega, ← Nat.mod_mod_of_dvd _ (by decide : 256 ∣ 65536), hd]
    by_cases hk : k < 28
    · rw [h0 k hk, BitVec.toNat_ofNat, show g k = f k from ite_eq_left hk]
    · rw [show 2 * k = 56 by omega, h56, show g k = 0 from ite_eq_right hk]; rfl
  · have hk : k < 28 := by omega
    have hd := val16_div hg (k := k) (by omega)
    rw [show 8 * (2 * k + 1) = 16 * k + 8 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      show (2 : Nat) ^ 8 = 256 from rfl, h1 k hk, BitVec.toNat_ofNat,
      ← Nat.mod_mul_right_div_self (val16 g 29 / 2 ^ (16 * k)) 256 256,
      show (256 : Nat) * 256 = 65536 from rfl, hd, show g k = f k from ite_eq_left hk]
    have := hl k hk
    omega

theorem OUT_eq : OUT = 32 := rfl

/-- `output o`: the remainder at `o` as 57 bytes at `r12`, and the
callee-saved registers restored. -/
theorem output_ok {q : BitVec 32} {o : Nat} (ho : o + 112 ≤ 4096) {s : State} (hc : VG.Proof.Ed448.Arm.Ctx8 b s)
    (hl : VG.Proof.Ed448.Arm.Lim28 s.mem (State.addr b) o) (hq : s.gpr .r12 = q) (hfit : q.toNat + 57 ≤ 2 ^ 32)
    (hw : (⟨State.addr q, 57⟩ : Region) ∈ s.wr)
    (hsep : (⟨State.addr q, 57⟩ : Region).Disjoint ⟨State.addr b, 8192⟩)
    {g : Reg → BitVec 32} (hs : VG.Proof.Ed448.Arm.Saved (State.addr b) g s.mem) :
    WP isa (.block (output o)) s fun t =>
      (∀ i < 8, t.gpr (savedReg i) = g (savedReg i)) ∧
      Rest [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s t ∧
      Frame [⟨State.addr q, 57⟩] s.mem t.mem ∧
      VG.Spec.Ed448.bytesAt t.mem (State.addr q) 57 = encodeLE 57 (VG.Proof.Ed448.Arm.V28 s.mem (State.addr b) o) := by
  unfold output
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (VG.Proof.Ed448.Arm.pack_ok (q := q) (o := o) ho hc hq hfit hw hsep) fun v hv => ?_
  have hcv := hc.of_rest hv.rest (by decide)
  refine wp_mov (op2_imm (by decide)) fun v1 w1 => ?_
  refine wp_strb (a := State.addr q + BitVec.ofNat 64 56) (by decide)
    (by rw [w1.other _ (by decide), hv.rest.gpr _ (by decide), hq]; exact addr_add (by omega))
    (by rw [w1.wr, hv.rest.wr]; exact in_base hw (by decide) (by decide)) fun v2 w2 => ?_
  have m2 : v2.mem = v.mem.writeW (State.addr q + BitVec.ofNat 64 56) (0 : BitVec 8) := by
    rw [w2.mem, w1.gpr, w1.mem]; rfl
  have f2 : Frame [⟨State.addr q, 57⟩] s.mem v2.mem := by
    rw [m2]
    refine (?_ : Frame [⟨State.addr q, 57⟩] s.mem v.mem).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by decide) (by decide))
    exact hv.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩
  have hcv2 := hcv.of_rest ((w1.rest (ws := [.r3])  (by decide)).trans (w2.rest _)) (by decide)
  have hs2 : VG.Proof.Ed448.Arm.Saved (State.addr b) g v2.mem :=
    hs.frame f2 fun r hr i hi => by
      rw [List.mem_singleton.mp hr]
      exact (hsep.symm.sub_left (Offset.sub_base _ (by omega)))
  refine WP.mono (VG.Proof.Ed448.Arm.restore_ok hcv2 hs2) fun t ⟨gt, kt, mt⟩ => ?_
  have ne : ∀ i j : Nat, i < 57 → j < 57 → i ≠ j →
      State.addr q + BitVec.ofNat 64 i ≠ State.addr q + BitVec.ofNat 64 j :=
    fun i j hi hj hij => Offset.add_ofNat_ne _ (by omega) (by omega) hij
  refine ⟨gt, (hv.rest.mono (by decide)).trans ((w1.rest (by decide)).trans
    ((w2.rest _).trans (kt.mono (by decide)))), by rw [mt]; exact f2, ?_⟩
  rw [mt]
  refine VG.Proof.Ed448.Arm.encode_57 (fun k hk => hl k hk) (fun k hk => ?_) (fun k hk => ?_) ?_
  · rw [m2, VG.WriteBytes.writeW8_apply, ite_eq_right (ne _ _ (by omega) (by decide) (by omega))]
    exact hv.b0 k hk
  · rw [m2, VG.WriteBytes.writeW8_apply, ite_eq_right (ne _ _ (by omega) (by decide) (by omega))]
    exact hv.b1 k hk
  · rw [m2, VG.WriteBytes.writeW8_apply, ite_eq_left rfl]

/-- `finish o`: `output o` to the output's address, saved at `OUT`. -/
theorem finish_ok {q : BitVec 32} {o : Nat} (ho : o + 112 ≤ 4096) {s : State} (hc : VG.Proof.Ed448.Arm.Ctx8 b s)
    (hl : VG.Proof.Ed448.Arm.Lim28 s.mem (State.addr b) o)
    (hq : s.mem.readW (State.addr b + BitVec.ofNat 64 OUT) 32 = q) (hfit : q.toNat + 57 ≤ 2 ^ 32)
    (hw : (⟨State.addr q, 57⟩ : Region) ∈ s.wr)
    (hsep : (⟨State.addr q, 57⟩ : Region).Disjoint ⟨State.addr b, 8192⟩)
    {g : Reg → BitVec 32} (hs : VG.Proof.Ed448.Arm.Saved (State.addr b) g s.mem) :
    WP isa (.block (finish o)) s fun t =>
      (∀ i < 8, t.gpr (savedReg i) = g (savedReg i)) ∧
      Rest [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] s t ∧
      Frame [⟨State.addr q, 57⟩] s.mem t.mem ∧
      VG.Spec.Ed448.bytesAt t.mem (State.addr q) 57 = encodeLE 57 (VG.Proof.Ed448.Arm.V28 s.mem (State.addr b) o) := by
  have hO := VG.Proof.Ed448.Arm.OUT_eq
  unfold finish
  refine ldr0_ok hc (d := OUT) (by omega) fun u hu => ?_
  have hcu := hc.of_rest (hu.rest (ws := [.r12]) (by decide)) (by decide)
  refine WP.mono (VG.Proof.Ed448.Arm.output_ok ho hcu (hu.mem ▸ hl) (by rw [hu.gpr, hq]) hfit (by rw [hu.wr]; exact hw)
    hsep (hu.mem ▸ hs)) fun t ⟨gt, kt, ft, bt⟩ => ⟨gt, (hu.rest (by decide)).trans (kt.mono (by decide)),
      by rw [← hu.mem]; exact ft, by rw [bt, hu.mem]⟩

end

end VG.Proof.Ed448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.ScalarLit`. -/
section

/-!
# Ed448 scalar arithmetic on ARMv7: the code as literals

The kernel checks each literal once; the taint checks reuse it.
-/

namespace VG

materialize_code Impl.Ed448.Arm.scalarReduce
materialize_code Impl.Ed448.Arm.scalarMulAdd

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.ScalarMain`. -/
section

/-!
# Ed448 scalar reduction on ARMv7: the whole function

`vg_ed448_scalar_reduce(out = r0, wide = r1, scratch = r2)` against a local
contract (`scalarReduceLocal`), the ABI included.
-/

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
  post s t := VG.Spec.Ed448.bytesAt t.mem (State.addr (s.gpr .r0)) 57 =
    Spec.Ed448.scalarReduce (VG.Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) 114)
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

theorem ReducePre.of {s : State} (h : scalarReduceLocal.pre s) : VG.Proof.Ed448.Arm.ReducePre s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem ctx8_of {b : BitVec 32} {s : State} (h0 : s.gpr .r0 = b) (hfit : b.toNat + 8192 ≤ 2 ^ 32)
    (hw : (⟨State.addr b, 8192⟩ : Region) ∈ s.wr) : VG.Proof.Ed448.Arm.Ctx8 b s := ⟨h0, hfit, hw⟩

theorem reduceSetup_ok {s : State} (h : VG.Proof.Ed448.Arm.ReducePre s) :
    WP isa (.block (saveAt .r2 ++ ([.str .r0 .r2 OUT, .mov .r0 (.reg .r2), .mov .r12 (.reg .r1),
      .movw .r6 0xffff] : List Instr))) s fun t =>
      VG.Proof.Ed448.Arm.Ctx8 (s.gpr .r2) t ∧ t.gpr .r6 = mask16 ∧ t.gpr .r12 = s.gpr .r1 ∧
      VG.Proof.Ed448.Arm.Saved (State.addr (s.gpr .r2)) s.gpr t.mem ∧
      t.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 OUT) 32 = s.gpr .r0 ∧
      Rest [.r0, .r6, .r12] s t ∧ Frame [⟨State.addr (s.gpr .r2), 36⟩] s.mem t.mem := by
  have hw : (⟨State.addr (s.gpr .r2), 8192⟩ : Region) ∈ s.wr := by rw [h.wr]; simp
  have hO := VG.Proof.Ed448.Arm.OUT_eq
  refine WP.append (VG.Proof.Ed448.Arm.saveAt_ok rfl h.f2 hw) fun u ⟨su, fu, gu, ku⟩ => ?_
  refine wp_str (a := State.addr (s.gpr .r2) + BitVec.ofNat 64 32) (by decide)
    (by rw [gu]; exact addr_add (by have := h.f2; omega))
    (by rw [ku.wr]; exact in_base hw (by decide) (by decide)) fun v hv => ?_
  refine wp_mov (op2_reg _ _) fun w hw' => wp_mov (op2_reg _ _) fun x hx =>
    wp_movw fun t ht => WP.block_nil ?_
  have kt : Rest [.r0, .r6, .r12] s t :=
    (ku.mono (by decide)).trans ((hv.rest _).trans ((hw'.rest (by decide)).trans
      ((hx.rest (by decide)).trans (ht.rest (by decide)))))
  have mt : t.mem = u.mem.writeW (State.addr (s.gpr .r2) + BitVec.ofNat 64 32) (s.gpr .r0) := by
    rw [ht.mem, hx.mem, hw'.mem, hv.mem, gu]
  refine ⟨VG.Proof.Ed448.Arm.ctx8_of ?_ h.f2 (by rw [kt.wr]; exact hw), ht.gpr, ?_, ?_, ?_, kt, ?_⟩
  · rw [ht.other _ (by decide), hx.other _ (by decide), hw'.gpr, hv.gpr, gu]
  · rw [ht.other _ (by decide), hx.gpr, hw'.other _ (by decide), hv.gpr, gu]
  · intro i hi
    rw [mt, Mem.readW_writeW_sep (Offset.sep _ (d := 4 * i) (e := 32) (n := 4) (k := 4) (by omega)
      (by omega) (by omega)) (by decide)]
    exact su i hi
  · rw [mt]; exact Mem.readW_writeW_self32 _ _ _
  · rw [mt]
    exact (fu.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))

theorem RA_buf : VG.Proof.Ed448.Arm.Buf RA := ⟨by decide, by decide⟩

theorem reduce_regions_sub {b : BitVec 32} {r : Region} (h : r ∈ [VG.Proof.Ed448.Arm.limbsR b TF, VG.Proof.Ed448.Arm.limbsR b RA]) :
    r.Sub ⟨State.addr b, 8192⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> exact Offset.sub_base _ (by decide)

theorem scalarReduce_correct {s : State} (h : VG.Proof.Ed448.Arm.ReducePre s) :
    WP isa scalarReduce s fun t => abiPreserved s t ∧ scalarReduceLocal.post s t := by
  have hT := VG.Proof.Ed448.Arm.TF_eq
  have hO := VG.Proof.Ed448.Arm.OUT_eq
  have hR : RA = 192 := rfl
  unfold scalarReduce
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.reduceSetup_ok h) fun u ⟨hcu, h6u, pu, su, ou, ku, fu⟩ => ?_)
  have wide : (⟨State.addr (s.gpr .r1), 114⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.rd]; simp
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.reduce114_ok VG.Proof.Ed448.Arm.RA_buf hcu h6u pu h.f1
    (fun n hn => by rw [ku.rd, ku.wr]; exact in_base wide (by omega) (by omega))
    (fun r hr => h.wide_ws.sub_right (VG.Proof.Ed448.Arm.reduce_regions_sub hr))) fun v ⟨kv, lv, vv⟩ => ?_)
  have sv : VG.Proof.Ed448.Arm.Saved (State.addr (s.gpr .r2)) s.gpr v.mem :=
    su.frame kv.frame fun r hr i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  have ov : v.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 OUT) 32 = s.gpr .r0 := by
    rw [kv.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), ou]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  refine WP.mono (VG.Proof.Ed448.Arm.finish_ok (by decide) (hcu.of_rest kv.rest (by decide)) lv ov h.f0
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
  · change VG.Spec.Ed448.bytesAt t.mem _ 57 = encodeLE 57 _
    rw [bt, vv]
    refine congrArg (fun bs => encodeLE 57 (decodeLE bs % L)) ?_
    exact VG.Proof.Ed448.Arm.bytesAt_frame fu (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact h.wide_ws.sub_right (Region.sub_prefix (by decide)))
      (by decide)

end VG.Proof.Ed448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.ScalarMulAdd`. -/
section

/-!
# Ed448 scalar multiply-add on ARMv7

`vg_ed448_scalar_mul_add(out = r0, r = r1, k = r2, s = r3, scratch = [sp])`
against a local contract (`scalarMulAddLocal`), the ABI included: the three
inputs reduced (`reduceArg_ok`), the product of two with X448's rows
(`product_ok`), its limbs reduced (`reduceProduct_ok`), and the sum with the
third (`addPass_ok`) reduced once more.
-/

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
      VG.Proof.Ed448.Arm.Args (State.addr b) s.gpr s'.mem ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 OUT, 16⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s' := by
  have hO := VG.Proof.Ed448.Arm.OUT_eq
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.mem.readW (State.addr b + BitVec.ofNat 64 (OUT + 4 * i)) 32 =
        s.gpr (argReg i)) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 OUT, 4 * n⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s')
    (fun n s' hn ⟨h1, h2, h3', h4⟩ => ?_) 4 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, rfl, Rest.refl _ _⟩)
    fun s' h => ⟨h.1, h.2.1, h.2.2⟩
  refine wp_str (a := State.addr b + BitVec.ofNat 64 (OUT + 4 * n)) (by omega)
    (by rw [h3', h3]; exact addr_add (by omega)) (by rw [h4.wr]; exact in_base hw (by omega) (by omega))
    fun s2 u2 => WP.block_nil ⟨fun i hi => ?_, ?_, by rw [u2.gpr, h3'], h4.trans (u2.rest _)⟩
  · rw [u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]; exact h1 i hi
    · rw [Mem.readW_writeW_self32, h3']
  · rw [u2.mem]
    exact (h2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _
      (Offset.contains _ (d := OUT + 4 * n) (n := 4) (e := OUT) (k := 4 * (n + 1)) (by omega)
        (by omega) (by omega))

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
      VG.Proof.Ed448.Arm.Ctx8 (stackArg s 0) t ∧ t.gpr .r6 = mask16 ∧ VG.Proof.Ed448.Arm.Saved (State.addr (stackArg s 0)) s.gpr t.mem ∧
      VG.Proof.Ed448.Arm.Args (State.addr (stackArg s 0)) s.gpr t.mem ∧ Rest [.r0, .r6, .r12] s t ∧
      Frame [⟨State.addr (stackArg s 0), 48⟩] s.mem t.mem := by
  have hO := VG.Proof.Ed448.Arm.OUT_eq
  unfold mulAddArgs
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine VG.Proof.Ed448.Arm.ldrSp_ok hr fun u hu => ?_
  refine WP.append (VG.Proof.Ed448.Arm.saveAt_ok hu.gpr hfit (hu.wr ▸ hw)) fun v ⟨sv, fv, gv, kv⟩ => ?_
  refine WP.append (VG.Proof.Ed448.Arm.storeArgs_ok (by rw [gv]; exact hu.gpr) hfit
    (by rw [kv.wr, hu.wr]; exact hw)) fun w ⟨aw, fw, gw, kw⟩ => ?_
  refine wp_mov (op2_reg _ _) fun x hx => wp_movw fun t ht => WP.block_nil ?_
  have kt : Rest [.r0, .r6, .r12] s t := (hu.rest (by decide)).trans
    ((kv.mono (by decide)).trans ((kw.mono (by decide)).trans ((hx.rest (by decide)).trans
      (ht.rest (by decide)))))
  have mt : t.mem = w.mem := by rw [ht.mem, hx.mem]
  refine ⟨⟨?_, hfit, by rw [kt.wr]; exact hw⟩, ht.gpr, ?_, ?_, kt, ?_⟩
  · rw [ht.other _ (by decide), hx.gpr, gw, gv, hu.gpr]
  · have sn : ∀ i < 8, savedReg i ≠ .r12 := by decide
    intro i hi
    rw [mt, fw.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), sv i hi]
    · exact hu.other _ (sn i hi)
    · rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
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

theorem reduceArg_ok {o off : Nat} (ho : VG.Proof.Ed448.Arm.Buf o) (hoff : off + 4 ≤ 64) {p : BitVec 32} {s : State}
    (hc : VG.Proof.Ed448.Arm.Ctx8 b s) (h6 : s.gpr .r6 = mask16)
    (hp : s.mem.readW (State.addr b + BitVec.ofNat 64 off) 32 = p) (hfit : p.toNat + 57 ≤ 2 ^ 32)
    (hr : (⟨State.addr p, 57⟩ : Region) ∈ s.rd ++ s.wr)
    (hsep : (⟨State.addr p, 57⟩ : Region).Disjoint ⟨State.addr b, 8192⟩) :
    WP isa (reduceArg off o) s fun t => Rest [.r1, .r2, .r3, .r4, .r5, .r9, .r10, .r11, .r12] s t ∧
      Frame [VG.Proof.Ed448.Arm.limbsR b TF, VG.Proof.Ed448.Arm.limbsR b o] s.mem t.mem ∧ VG.Proof.Ed448.Arm.Lim28 t.mem (State.addr b) o ∧
      VG.Proof.Ed448.Arm.V28 t.mem (State.addr b) o = decodeLE (VG.Spec.Ed448.bytesAt s.mem (State.addr p) 57) % L := by
  have hT := VG.Proof.Ed448.Arm.TF_eq
  obtain ⟨ho1, ho2⟩ := ho
  unfold reduceArg
  have hld : WP isa (.block [.ldr .r12 .r0 off]) s fun u =>
      Rest [.r12] s u ∧ u.mem = s.mem ∧ u.gpr .r12 = p :=
    ldr0_ok hc (d := off) (by omega) fun u hu => WP.block_nil ⟨hu.rest (by decide), hu.mem,
      by rw [hu.gpr, hp]⟩
  refine WP.seq (WP.mono hld fun u ⟨ku, mu, pu⟩ => ?_)
  refine WP.mono (VG.Proof.Ed448.Arm.reduce57_ok ⟨ho1, ho2⟩ (hc.of_rest ku (by decide)) ((ku.gpr _ (by decide)).trans h6) pu
    hfit (fun i hi => by rw [ku.rd, ku.wr]; exact in_base hr (by omega) (by omega))
    (fun r hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl <;> exact hsep.sub_right (Offset.sub_base _ (by omega))))
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

theorem product_ok {s : State} (hc : VG.Proof.Ed448.Arm.Ctx8 b s) (h6 : s.gpr .r6 = mask16)
    (hk : VG.Proof.Ed448.Arm.Lim28 s.mem (State.addr b) SK) (hs : VG.Proof.Ed448.Arm.Lim28 s.mem (State.addr b) SS) :
    WP isa product s fun t => Rest [.r1, .r2, .r3, .r4, .r5, .r7, .r9] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 Impl.X448.Arm.ACC, 224⟩] s.mem t.mem ∧
      (∀ j < 56, limb t.mem (State.addr b) Impl.X448.Arm.ACC j < 65536) ∧
      val16 (limb t.mem (State.addr b) Impl.X448.Arm.ACC) 56 =
        VG.Proof.Ed448.Arm.V28 s.mem (State.addr b) SK * VG.Proof.Ed448.Arm.V28 s.mem (State.addr b) SS := by
  have hrc : Proof.X448.Arm.RowCtx b s := ⟨hc.r0, by have := hc.fit; omega, hc.wr⟩
  unfold product
  refine WP.seq (WP.mono (Proof.X448.Arm.mulPre_ok (x := SK) (y := SS) hrc h6) fun u hu => ?_)
  refine WP.mono (Proof.X448.Arm.mulLoop_ok (by decide) (by decide) hk hs hu) fun t ht => ?_
  refine ⟨ht.rest, ht.frame, ht.lt, ?_⟩
  have e : val16 (limb t.mem (State.addr b) Impl.X448.Arm.ACC) 56 =
      Proof.X448.Radix16.valN (Proof.X448.Arm.accw t.mem (State.addr b)) (28 + 28) := (VG.Proof.Ed448.Arm.valN_eq _ _).symm
  have e' : Proof.X448.Radix16.valN (Proof.X448.Arm.limbs s.mem (State.addr b) SK) 28 *
      Proof.X448.Arm.fe s.mem (State.addr b) SS = VG.Proof.Ed448.Arm.V28 s.mem (State.addr b) SK * VG.Proof.Ed448.Arm.V28 s.mem (State.addr b) SS := by
    unfold Proof.X448.Arm.fe; rw [VG.Proof.Ed448.Arm.valN_eq, VG.Proof.Ed448.Arm.valN_eq]; rfl
  exact e.trans (ht.val.trans e')

theorem reduceProduct_ok {s : State} (hc : VG.Proof.Ed448.Arm.Ctx8 b s) (h6 : s.gpr .r6 = mask16)
    (hacc : ∀ j < 56, limb s.mem (State.addr b) Impl.X448.Arm.ACC j < 65536) :
    WP isa reduceProduct s fun t => VG.Proof.Ed448.Arm.LoopKeep b RA s t ∧ VG.Proof.Ed448.Arm.Lim28 t.mem (State.addr b) RA ∧
      VG.Proof.Ed448.Arm.V28 t.mem (State.addr b) RA = val16 (limb s.mem (State.addr b) Impl.X448.Arm.ACC) 56 % L := by
  have hA := VG.Proof.Ed448.Arm.ACC_eq
  have hR := VG.Proof.Ed448.Arm.RA_eq
  have hT := VG.Proof.Ed448.Arm.TF_eq
  unfold reduceProduct
  have hinit : WP isa (.block (zeroR RA ++ [.mov .r10 (.imm 224)])) s fun v => VG.Proof.Ed448.Arm.LoopKeep b RA s v ∧
      v.gpr .r10 = BitVec.ofNat 32 (4 * 56) ∧ VG.Proof.Ed448.Arm.Lim28 v.mem (State.addr b) RA ∧
      VG.Proof.Ed448.Arm.V28 v.mem (State.addr b) RA = 0 :=
    WP.append (VG.Proof.Ed448.Arm.zeroR_ok (o := RA) (by decide) hc) fun u ⟨ku, fu, zu⟩ =>
      wp_mov (op2_imm (by decide)) fun v hv => WP.block_nil
        ⟨⟨(ku.mono (by decide)).trans (hv.rest (by decide)), by rw [hv.mem]; exact fu.mono (by simp)⟩,
          hv.gpr, by rw [hv.mem]; exact VG.Proof.Ed448.Arm.Lim28_zero zu, by rw [hv.mem]; exact VG.Proof.Ed448.Arm.V28_zero zu⟩
  refine WP.seq (WP.mono hinit fun v ⟨kv, cv, lv, vv⟩ => ?_)
  have la : ∀ j < 56, limb v.mem (State.addr b) Impl.X448.Arm.ACC j =
      limb s.mem (State.addr b) Impl.X448.Arm.ACC j := fun j hj =>
    wd_frame kv.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by omega)
  refine WP.mono (VG.Proof.Ed448.Arm.limbLoop_ok (hc.of_rest kv.rest (by decide)) ((kv.rest.gpr _ (by decide)).trans h6)
    (fun j hj => by rw [la j hj]; exact hacc j hj) cv lv vv) fun t ⟨kt, lt, vt⟩ =>
    ⟨kv.trans kt, lt, by rw [vt, val16_congr la]⟩

/-! ## The sum -/

theorem addPass_ok {s : State} (hc : VG.Proof.Ed448.Arm.Ctx8 b s) (h6 : s.gpr .r6 = mask16)
    (ha : VG.Proof.Ed448.Arm.Lim28 s.mem (State.addr b) RA) (hr : VG.Proof.Ed448.Arm.Lim28 s.mem (State.addr b) SR)
    (hva : VG.Proof.Ed448.Arm.V28 s.mem (State.addr b) RA < L) (hvr : VG.Proof.Ed448.Arm.V28 s.mem (State.addr b) SR < L) :
    WP isa (.block addPass) s fun t => Rest [.r2, .r3, .r4, .r5] s t ∧
      Frame [VG.Proof.Ed448.Arm.limbsR b TF] s.mem t.mem ∧ VG.Proof.Ed448.Arm.Lim28 t.mem (State.addr b) TF ∧
      VG.Proof.Ed448.Arm.V28 t.mem (State.addr b) TF = VG.Proof.Ed448.Arm.V28 s.mem (State.addr b) RA + VG.Proof.Ed448.Arm.V28 s.mem (State.addr b) SR := by
  have hT := VG.Proof.Ed448.Arm.TF_eq
  have hR := VG.Proof.Ed448.Arm.RA_eq
  have hS := VG.Proof.Ed448.Arm.SR_eq
  unfold addPass
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  have hc1 := hc.of_rest (u1.rest (ws := [.r5]) (by decide)) (by decide)
  have r0 : s1.gpr .r0 = b := hc1.r0
  refine WP.mono (VG.Proof.X448.Arm.carryPass_ok (rb := .r0) (o := TF) (s0 := s1)
    (c := fun k => limb s.mem (State.addr b) RA k + limb s.mem (State.addr b) SR k) (cin := 0)
    (by decide) (by omega) (by rw [r0]; have := hc.fit; omega)
    (fun k hk => by rw [r0]; exact hc1.inW (by omega)) ((u1.other _ (by decide)).trans h6)
    (by rw [u1.gpr]; rfl) (fun k hk => by have := ha k hk; have := hr k hk; omega) (by decide)
    ?_) fun t ht => ?_
  · intro k hk s' hp
    have hc' := hc1.of_rest hp.rest (by decide)
    have hf : Frame [⟨State.addr b + BitVec.ofNat 64 TF, 4 * k⟩] s.mem s'.mem := by
      have := hp.frame; rwa [r0, u1.mem] at this
    have e1 : wd s'.mem (State.addr b) (RA + 4 * k) = limb s.mem (State.addr b) RA k :=
      wd_frame hf fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
    have e2 : wd s'.mem (State.addr b) (SR + 4 * k) = limb s.mem (State.addr b) SR k :=
      wd_frame hf fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
    unfold addSrc
    refine ldr0_ok hc' (d := RA + 4 * k) (by omega) fun v1 w1 => ?_
    refine ldr0_ok (hc'.of_rest (w1.rest (ws := [.r3]) (by decide)) (by decide)) (d := SR + 4 * k)
      (by omega) fun v2 w2 => wp_dp (op2_reg _ _) fun v3 w3 => WP.block_nil ⟨?_,
        (w1.rest (by decide)).trans ((w2.rest (by decide)).trans (w3.rest (by decide))),
        by rw [w3.mem, w2.mem, w1.mem]⟩
    have x1 : (v2.gpr .r3).toNat = limb s.mem (State.addr b) RA k := by
      rw [w2.other _ (by decide), w1.gpr]; exact e1
    have x2 : (v2.gpr .r2).toNat = limb s.mem (State.addr b) SR k := by
      rw [w2.gpr, w1.mem]; exact e2
    rw [w3.gpr]
    show (v2.gpr .r3 + v2.gpr .r2).toNat = _
    rw [toNat_add_lt (by rw [x1, x2]; have := ha k hk; have := hr k hk; omega), x1, x2]
  · generalize hcf : (fun k => limb s.mem (State.addr b) RA k + limb s.mem (State.addr b) SR k) = c at ht
    have outs : ∀ k < 28, limb t.mem (State.addr b) TF k = VG.Proof.X25519.Arm.out c 0 k := by
      intro k hk; have := ht.outs k hk; rwa [r0] at this
    have hval := (chain_val c 0 28).trans (Nat.add_zero _)
    have hcv : val16 c 28 = VG.Proof.Ed448.Arm.V28 s.mem (State.addr b) RA + VG.Proof.Ed448.Arm.V28 s.mem (State.addr b) SR := by
      unfold VG.Proof.Ed448.Arm.V28; rw [← hcf, val16_add]
    rw [hcv] at hval
    have hLM := VG.Proof.Ed448.Arm.two_L_le
    have hV : VG.Proof.Ed448.Arm.V28 t.mem (State.addr b) TF = val16 (VG.Proof.X25519.Arm.out c 0) 28 := val16_congr outs
    refine ⟨(u1.rest (by decide)).trans (ht.rest.mono (by decide)), ?_,
      fun k hk => by rw [outs k hk]; exact out_lt _ _ _, ?_⟩
    · have := ht.frame; rw [r0, u1.mem] at this; exact this
    · rw [hV]
      generalize (2 : Nat) ^ (16 * 28 : Nat) = M at hval hLM
      rcases Nat.eq_zero_or_pos (chain c 0 28) with h | h
      · rw [h, Nat.mul_zero, Nat.add_zero] at hval; exact hval
      · have := Nat.mul_le_mul_left M h
        omega

/-! ## Composing the steps -/

/-- A region of the working space at `b` above its first 64 bytes. -/
def Hi (b : BitVec 32) (r : Region) : Prop :=
  ∃ d n, r = ⟨State.addr b + BitVec.ofNat 64 d, n⟩ ∧ 64 ≤ d ∧ d + n ≤ 8192

theorem hi_of {d n : Nat} (h1 : 64 ≤ d) (h2 : d + n ≤ 8192) :
    VG.Proof.Ed448.Arm.Hi b ⟨State.addr b + BitVec.ofNat 64 d, n⟩ := ⟨d, n, rfl, h1, h2⟩

/-- A word of the first 64 bytes across a frame of regions above them. -/
theorem readW_lo {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (hrs : ∀ r ∈ rs, VG.Proof.Ed448.Arm.Hi b r)
    {e : Nat} (he : e + 4 ≤ 64) :
    m'.readW (State.addr b + BitVec.ofNat 64 e) 32 = m.readW (State.addr b + BitVec.ofNat 64 e) 32 :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    obtain ⟨d, n, rfl, h1, h2⟩ := hrs r hr
    exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (by decide)

theorem Saved.hi {g : Reg → BitVec 32} {m m' : Mem} (hs : VG.Proof.Ed448.Arm.Saved (State.addr b) g m) {rs : List Region}
    (hf : Frame rs m m') (hrs : ∀ r ∈ rs, VG.Proof.Ed448.Arm.Hi b r) : VG.Proof.Ed448.Arm.Saved (State.addr b) g m' := fun i hi => by
  rw [VG.Proof.Ed448.Arm.readW_lo hf hrs (by omega)]; exact hs i hi

theorem Args.hi {g : Reg → BitVec 32} {m m' : Mem} (hs : VG.Proof.Ed448.Arm.Args (State.addr b) g m) {rs : List Region}
    (hf : Frame rs m m') (hrs : ∀ r ∈ rs, VG.Proof.Ed448.Arm.Hi b r) : VG.Proof.Ed448.Arm.Args (State.addr b) g m' := fun i hi => by
  have hO := VG.Proof.Ed448.Arm.OUT_eq
  rw [VG.Proof.Ed448.Arm.readW_lo hf hrs (by omega)]; exact hs i hi

/-- The inputs and their pointers: `g (argReg i)` points to 57 readable bytes
outside the working space. -/
def Input (b : BitVec 32) (s : State) (p : BitVec 32) : Prop :=
  p.toNat + 57 ≤ 2 ^ 32 ∧ (⟨State.addr p, 57⟩ : Region) ∈ s.rd ++ s.wr ∧
    (⟨State.addr p, 57⟩ : Region).Disjoint ⟨State.addr b, 8192⟩

theorem Input.of_rest {s t : State} {ws : List Reg} {p : BitVec 32} (h : VG.Proof.Ed448.Arm.Input b s p) (hr : Rest ws s t) :
    VG.Proof.Ed448.Arm.Input b t p := ⟨h.1, by rw [hr.rd, hr.wr]; exact h.2.1, h.2.2⟩

/-- The bytes of an input across a frame of regions of the working space. -/
theorem Input.bytes {s : State} {p : BitVec 32} (h : VG.Proof.Ed448.Arm.Input b s p) {rs : List Region} {m m' : Mem}
    (hf : Frame rs m m') (hrs : ∀ r ∈ rs, VG.Proof.Ed448.Arm.Hi b r) :
    VG.Spec.Ed448.bytesAt m' (State.addr p) 57 = VG.Spec.Ed448.bytesAt m (State.addr p) 57 :=
  VG.Proof.Ed448.Arm.bytesAt_frame hf (fun r hr => by
    obtain ⟨d, n, rfl, h1, h2⟩ := hrs r hr
    exact h.2.2.sub_right (Offset.sub_base _ h2)) (by decide)

theorem limbs_frame_hi {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {o : Nat}
    (hrs : ∀ r ∈ rs, ∃ d n, r = ⟨State.addr b + BitVec.ofNat 64 d, n⟩ ∧ (d + n ≤ o ∨ o + 112 ≤ d) ∧
      d + n ≤ 8192) (ho : o + 112 ≤ 8192) :
    ∀ k < 28, limb m' (State.addr b) o k = limb m (State.addr b) o k :=
  VG.Proof.Ed448.Arm.limb_frame28 hf fun r hr k hk => by
    obtain ⟨d, n, rfl, h1, h2⟩ := hrs r hr
    exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem inputs_ok {s : State} (hc : VG.Proof.Ed448.Arm.Ctx8 b s) (h6 : s.gpr .r6 = mask16) {g : Reg → BitVec 32}
    (ha : VG.Proof.Ed448.Arm.Args (State.addr b) g s.mem) (hin : ∀ i, 1 ≤ i → i < 4 → VG.Proof.Ed448.Arm.Input b s (g (argReg i))) :
    WP isa inputs s fun t => Rest [.r1, .r2, .r3, .r4, .r5, .r9, .r10, .r11, .r12] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 TF, 624⟩] s.mem t.mem ∧
      VG.Proof.Ed448.Arm.Lim28 t.mem (State.addr b) SK ∧ VG.Proof.Ed448.Arm.Lim28 t.mem (State.addr b) SS ∧ VG.Proof.Ed448.Arm.Lim28 t.mem (State.addr b) SR ∧
      VG.Proof.Ed448.Arm.V28 t.mem (State.addr b) SK = decodeLE (VG.Spec.Ed448.bytesAt s.mem (State.addr (g .r2)) 57) % L ∧
      VG.Proof.Ed448.Arm.V28 t.mem (State.addr b) SS = decodeLE (VG.Spec.Ed448.bytesAt s.mem (State.addr (g .r3)) 57) % L ∧
      VG.Proof.Ed448.Arm.V28 t.mem (State.addr b) SR = decodeLE (VG.Spec.Ed448.bytesAt s.mem (State.addr (g .r1)) 57) % L := by
  have hT := VG.Proof.Ed448.Arm.TF_eq
  have hK := VG.Proof.Ed448.Arm.SK_eq
  have hS := VG.Proof.Ed448.Arm.SS_eq
  have hR := VG.Proof.Ed448.Arm.SR_eq
  have hO := VG.Proof.Ed448.Arm.OUT_eq
  have sub : ∀ o, TF ≤ o → o + 112 ≤ 688 → ∀ r ∈ [VG.Proof.Ed448.Arm.limbsR b TF, VG.Proof.Ed448.Arm.limbsR b o],
      ∃ e ∈ [(⟨State.addr b + BitVec.ofNat 64 TF, 624⟩ : Region)], Region.Sub r e := fun o h1 h2 r hr => by
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub _ (by omega) (by omega)
  have hiTF : ∀ o, TF ≤ o → o + 112 ≤ 4096 → ∀ r ∈ [VG.Proof.Ed448.Arm.limbsR b TF, VG.Proof.Ed448.Arm.limbsR b o], VG.Proof.Ed448.Arm.Hi b r := fun o h1 h2 r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact VG.Proof.Ed448.Arm.hi_of (by omega) (by omega)
  unfold inputs
  -- k
  obtain ⟨k1, k2, k3⟩ := hin 2 (by decide) (by decide)
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.reduceArg_ok (o := SK) ⟨by omega, by omega⟩ (by omega) hc h6 (ha 2 (by decide))
    k1 k2 k3) fun u ⟨ku, fu, lu, vu⟩ => ?_)
  have hcu := hc.of_rest ku (by decide)
  have h6u : u.gpr .r6 = mask16 := (ku.gpr _ (by decide)).trans h6
  have hau := ha.hi fu (hiTF SK (by omega) (by omega))
  -- s
  obtain ⟨s1, s2, s3⟩ := (hin 3 (by decide) (by decide)).of_rest ku
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.reduceArg_ok (o := SS) ⟨by omega, by omega⟩ (by omega) hcu h6u (hau 3 (by decide))
    s1 s2 s3) fun v ⟨kv, fv, lv, vv⟩ => ?_)
  have hcv := hcu.of_rest kv (by decide)
  have h6v : v.gpr .r6 = mask16 := (kv.gpr _ (by decide)).trans h6u
  have hav := hau.hi fv (hiTF SS (by omega) (by omega))
  -- r
  obtain ⟨r1, r2, r3⟩ := ((hin 1 (by decide) (by decide)).of_rest ku).of_rest kv
  refine WP.mono (VG.Proof.Ed448.Arm.reduceArg_ok (o := SR) ⟨by omega, by omega⟩ (by omega) hcv h6v (hav 1 (by decide))
    r1 r2 r3) fun t ⟨kt, ft, lt, vt⟩ => ?_
  have hiW : ∀ r ∈ [(⟨State.addr b + BitVec.ofNat 64 TF, 624⟩ : Region)], VG.Proof.Ed448.Arm.Hi b r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact VG.Proof.Ed448.Arm.hi_of (by omega) (by omega)
  have fu' := fu.sub (sub SK (by omega) (by omega))
  have fv' := fv.sub (sub SS (by omega) (by omega))
  have ft' := ft.sub (sub SR (by omega) (by omega))
  have pr : ∀ {o : Nat} {m m' : Mem}, o + 112 ≤ 4096 → Frame [VG.Proof.Ed448.Arm.limbsR b TF, VG.Proof.Ed448.Arm.limbsR b o] m m' →
      ∀ {o' : Nat}, (o + 112 ≤ o' ∨ o' + 112 ≤ o) → TF + 112 ≤ o' → o' + 112 ≤ 4096 →
      ∀ k < 28, limb m' (State.addr b) o' k = limb m (State.addr b) o' k := fun ho hf o' h1 h2 h3 =>
    VG.Proof.Ed448.Arm.limbs_frame_hi hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, _, rfl, by omega, by omega⟩) (by omega)
  have fK : ∀ k < 28, limb t.mem (State.addr b) SK k = limb u.mem (State.addr b) SK k := fun k hk => by
    rw [pr (o := SR) (by omega) ft (o' := SK) (by omega) (by omega) (by omega) k hk,
      pr (o := SS) (by omega) fv (o' := SK) (by omega) (by omega) (by omega) k hk]
  have fS : ∀ k < 28, limb t.mem (State.addr b) SS k = limb v.mem (State.addr b) SS k :=
    pr (o := SR) (by omega) ft (o' := SS) (by omega) (by omega) (by omega)
  have bS := (hin 3 (by decide) (by decide)).bytes fu' hiW
  have bR := (hin 1 (by decide) (by decide)).bytes (fu'.trans fv') hiW
  refine ⟨(ku.trans kv).trans kt, fu'.trans (fv'.trans ft'), fun k hk => by rw [fK k hk]; exact lu k hk,
    fun k hk => by rw [fS k hk]; exact lv k hk, lt, ?_, ?_, ?_⟩
  · change _ = decodeLE (VG.Spec.Ed448.bytesAt s.mem (State.addr (g (argReg 2))) 57) % L
    rw [← vu]; exact val16_congr fK
  · change _ = decodeLE (VG.Spec.Ed448.bytesAt s.mem (State.addr (g (argReg 3))) 57) % L
    rw [← bS, ← vv]; exact val16_congr fS
  · change _ = decodeLE (VG.Spec.Ed448.bytesAt s.mem (State.addr (g (argReg 1))) 57) % L
    rw [← bR, vt]

end

end VG.Proof.Ed448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.ScalarMulAddMain`. -/
section

/-!
# Ed448 scalar multiply-add on ARMv7: the whole function

`vg_ed448_scalar_mul_add(out = r0, r = r1, k = r2, s = r3, scratch = [sp])`
against a local contract (`scalarMulAddLocal`), the ABI included.
-/

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
  post s t := VG.Spec.Ed448.bytesAt t.mem (State.addr (s.gpr .r0)) 57 =
    Spec.Ed448.scalarMulAdd (VG.Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) 57)
      (VG.Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r2)) 57) (VG.Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r3)) 57)
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

theorem MulAddPre.of {s : State} (h : scalarMulAddLocal.pre s) : VG.Proof.Ed448.Arm.MulAddPre s := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem MulAddPre.input {s : State} (h : VG.Proof.Ed448.Arm.MulAddPre s) {i : Nat} (h1 : 1 ≤ i) (h4 : i < 4) :
    VG.Proof.Ed448.Arm.Input (stackArg s 0) s (s.gpr (argReg i)) := by
  rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
  · exact ⟨h.f1, by rw [h.rd]; simp [argReg], h.r_ws⟩
  · exact ⟨h.f2, by rw [h.rd]; simp [argReg], h.k_ws⟩
  · exact ⟨h.f3, by rw [h.rd]; simp [argReg], h.a_ws⟩

theorem mulAdd_mod (r k s : Nat) : ((k % L * (s % L)) % L + r % L) % L = (r + k * s) % L := by
  rw [← Nat.mul_mod, ← Nat.add_mod, Nat.add_comm]

theorem scalarMulAdd_correct {s : State} (h : VG.Proof.Ed448.Arm.MulAddPre s) :
    WP isa scalarMulAdd s fun t => abiPreserved s t ∧ scalarMulAddLocal.post s t := by
  have hT := VG.Proof.Ed448.Arm.TF_eq
  have hK := VG.Proof.Ed448.Arm.SK_eq
  have hS := VG.Proof.Ed448.Arm.SS_eq
  have hR := VG.Proof.Ed448.Arm.SR_eq
  have hA := VG.Proof.Ed448.Arm.RA_eq
  have hC := VG.Proof.Ed448.Arm.ACC_eq
  have hO := VG.Proof.Ed448.Arm.OUT_eq
  have hw : (⟨State.addr (stackArg s 0), 8192⟩ : Region) ∈ s.wr := by rw [h.wr]; simp
  have ha : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4 :=
    ⟨_, by rw [h.rd]; simp, Region.contains_self _ _⟩
  unfold scalarMulAdd
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.mulAddArgs_ok ha h.fs hw) fun u ⟨hcu, h6u, su, au, ku, fu⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.inputs_ok hcu h6u au fun i h1 h4 => (h.input h1 h4).of_rest ku)
    fun v ⟨kv, fv, lK, lS, lR, vK, vS, vR⟩ => ?_)
  have hcv0 := hcu.of_rest kv (by decide)
  have hiv : ∀ r ∈ [(⟨State.addr (stackArg s 0) + BitVec.ofNat 64 TF, 624⟩ : Region)], VG.Proof.Ed448.Arm.Hi (stackArg s 0) r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact VG.Proof.Ed448.Arm.hi_of (by omega) (by omega)
  have av := au.hi fv hiv
  have hld : WP isa (.block [.ldr .r12 .r0 OUT]) v fun v' =>
      Rest [.r12] v v' ∧ v'.mem = v.mem ∧ v'.gpr .r12 = s.gpr .r0 :=
    ldr0_ok hcv0 (d := OUT) (by omega) fun v' hv' => WP.block_nil ⟨hv'.rest (by decide), hv'.mem,
      by rw [hv'.gpr]; exact av 0 (by decide)⟩
  refine WP.seq (WP.mono hld fun v' ⟨kv', mv', qv'⟩ => ?_)
  have hcv := hcv0.of_rest kv' (by decide)
  have h6v : v'.gpr .r6 = mask16 := (kv'.gpr _ (by decide)).trans ((kv.gpr _ (by decide)).trans h6u)
  rw [← mv'] at lK lS lR vK vS vR fv
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.product_ok hcv h6v lK lS) fun w ⟨kw, fw, aw, vw⟩ => ?_)
  have hcw := hcv.of_rest kw (by decide)
  have h6w : w.gpr .r6 = mask16 := (kw.gpr _ (by decide)).trans h6v
  have hiw : ∀ r ∈ [(⟨State.addr (stackArg s 0) + BitVec.ofNat 64 Impl.X448.Arm.ACC, 224⟩ : Region)], VG.Proof.Ed448.Arm.Hi (stackArg s 0) r :=
    fun r hr => by rw [List.mem_singleton.mp hr]; exact VG.Proof.Ed448.Arm.hi_of (by omega) (by omega)
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.reduceProduct_ok hcw h6w aw) fun x ⟨kx, lx, vx⟩ => ?_)
  have hcx := hcw.of_rest kx.rest (by decide)
  have h6x : x.gpr .r6 = mask16 := (kx.rest.gpr _ (by decide)).trans h6w
  have hix : ∀ r ∈ [VG.Proof.Ed448.Arm.limbsR (stackArg s 0) TF, VG.Proof.Ed448.Arm.limbsR (stackArg s 0) RA], VG.Proof.Ed448.Arm.Hi (stackArg s 0) r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact VG.Proof.Ed448.Arm.hi_of (by omega) (by omega)
  -- The reduced `r` survives the product and its reduction.
  have eR : ∀ k < 28, limb x.mem (State.addr (stackArg s 0)) SR k = limb v'.mem (State.addr (stackArg s 0)) SR k := fun k hk => by
    rw [VG.Proof.Ed448.Arm.limbs_frame_hi kx.frame (o := SR) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, _, rfl, by omega, by omega⟩) (by omega) k hk,
      VG.Proof.Ed448.Arm.limbs_frame_hi fw (o := SR) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, _, rfl, by omega, by omega⟩) (by omega) k hk]
  have lRx : VG.Proof.Ed448.Arm.Lim28 x.mem (State.addr (stackArg s 0)) SR := fun k hk => by rw [eR k hk]; exact lR k hk
  have vRx : VG.Proof.Ed448.Arm.V28 x.mem (State.addr (stackArg s 0)) SR = VG.Proof.Ed448.Arm.V28 v'.mem (State.addr (stackArg s 0)) SR := val16_congr eR
  rw [List.append_assoc]
  refine WP.append (VG.Proof.Ed448.Arm.addPass_ok hcx h6x lx lRx (by rw [vx]; exact Nat.mod_lt _ L_pos)
    (by rw [vRx, vR]; exact Nat.mod_lt _ L_pos)) fun y ⟨ky, fy, ly, vy⟩ => ?_
  have hcy := hcx.of_rest ky (by decide)
  refine WP.append (VG.Proof.Ed448.Arm.reduceT_ok VG.Proof.Ed448.Arm.RA_buf hcy ((ky.gpr _ (by decide)).trans h6x) ly
    (by rw [vy, vx, vRx, vR]; have := Nat.mod_lt (val16 (limb w.mem (State.addr (stackArg s 0)) Impl.X448.Arm.ACC) 56) L_pos
        have := Nat.mod_lt (decodeLE (VG.Spec.Ed448.bytesAt u.mem (State.addr (s.gpr .r1)) 57)) L_pos
        omega)) fun z ⟨kz, fz, lz, vz⟩ => ?_
  have hcz := hcy.of_rest kz (by decide)
  have hiy : ∀ r ∈ [VG.Proof.Ed448.Arm.limbsR (stackArg s 0) TF], VG.Proof.Ed448.Arm.Hi (stackArg s 0) r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact VG.Proof.Ed448.Arm.hi_of (by omega) (by omega)
  have hiz : ∀ r ∈ [VG.Proof.Ed448.Arm.limbsR (stackArg s 0) RA], VG.Proof.Ed448.Arm.Hi (stackArg s 0) r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact VG.Proof.Ed448.Arm.hi_of (by omega) (by omega)
  have sz := ((((su.hi fv hiv).hi fw hiw).hi kx.frame hix).hi fy hiy).hi fz hiz
  have rz' : Rest [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r9, .r10, .r11] w z :=
    (kx.rest.mono (by decide)).trans ((ky.mono (by decide)).trans (kz.mono (by decide)))
  have qz : z.gpr .r12 = s.gpr .r0 := by
    rw [rz'.gpr _ (by decide), kw.gpr _ (by decide), qv']
  have rz : Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r9, .r10, .r11, .r12] s z :=
    (ku.mono (by decide)).trans ((kv.mono (by decide)).trans ((kv'.mono (by decide)).trans
      ((kw.mono (by decide)).trans (rz'.mono (by decide)))))
  refine WP.mono (VG.Proof.Ed448.Arm.output_ok (by decide) hcz lz qz h.f0 (by rw [rz.wr, h.wr]; simp) h.out_ws sz)
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
  · have hu : ∀ i, 1 ≤ i → i < 4 → VG.Spec.Ed448.bytesAt u.mem (State.addr (s.gpr (argReg i))) 57 =
        VG.Spec.Ed448.bytesAt s.mem (State.addr (s.gpr (argReg i))) 57 := fun i h1 h4 =>
      VG.Proof.Ed448.Arm.bytesAt_frame fu (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact (h.input h1 h4).2.2.sub_right (Region.sub_prefix (by decide))) (by decide)
    change VG.Spec.Ed448.bytesAt t.mem _ 57 = encodeLE 57 _
    rw [bt, vz, vy, vx, vw, vRx, vK, vS, vR, VG.Proof.Ed448.Arm.mulAdd_mod]
    rw [show s.gpr .r1 = s.gpr (argReg 1) from rfl, show s.gpr .r2 = s.gpr (argReg 2) from rfl,
      show s.gpr .r3 = s.gpr (argReg 3) from rfl, hu 1 (by decide) (by decide),
      hu 2 (by decide) (by decide), hu 3 (by decide) (by decide)]

end VG.Proof.Ed448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.ScalarVerified`. -/
section

/-!
# Ed448 scalar arithmetic on ARMv7: `Verified`

Correctness includes the ABI. Taint analysis checks that secret input bytes
never determine branches or memory addresses. A concrete witness proves the
signature contract is satisfiable.
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm

def scalarReduceSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 114⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x3000, 8192⟩]

theorem scalarReduce_ok (s : State) (hs : scalarReduceLocal.pre s) :
    ∃ t s', Exec isa scalarReduce s t s' ∧ abiPreserved s s' ∧ scalarReduceLocal.post s s' :=
  VG.Proof.Ed448.Arm.scalarReduce_correct (ReducePre.of hs)

/-- The arguments are public, and so is what the code stores in the working
space (writable region 1, at `r2`): the output's address, at `OUT`. -/
def scalarReduceTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2], flags := false, lens := [57, 8192], bases := [(.r2, 1)] }

theorem scalarReduceTaint_wf {s : State} (h : scalarReduceLocal.pre s) :
    VG.Arm.Taint.Wf VG.Proof.Ed448.Arm.scalarReduceTaint s := by
  have hp := ReducePre.of h
  refine ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.Ed448.Arm.scalarReduceTaint], ?_, ?_⟩, ?_,
    fun h => absurd h (by decide), fun _ h => (List.not_mem_nil h).elim⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact hp.out_ws
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · simpa only [State.addr, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using hp.f0
    · simpa only [State.addr, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)] using hp.f2
  · intro p hm
    simp only [VG.Proof.Ed448.Arm.scalarReduceTaint, List.mem_singleton] at hm
    subst hm
    simp [VG.Arm.Taint.region, hp.wr]

theorem scalarReduce_ct :
    ConstantTime isa scalarReduceLocal.pre scalarReduceLocal.pub scalarReduce := by
  refine VG.Taint.constantTime (A := taint) VG.Proof.Ed448.Arm.scalarReduceTaint ?_ (by taint_decide)
  intro s t hs ht ⟨_, h0, h1, h2⟩
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.Ed448.Arm.scalarReduceTaint_wf hs,
    VG.Proof.Ed448.Arm.scalarReduceTaint_wf ht, fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (by decide), fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  · simp only [VG.Proof.Ed448.Arm.scalarReduceTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
  · rw [(ReducePre.of hs).wr, (ReducePre.of ht).wr, h0, h2]

theorem scalarReduce_verified : Verified Arm.target scalarReduce
    (Spec.Ed448.scalarReduceContract Arm.abi) :=
  Verified.of_correct VG.Proof.Ed448.Arm.scalarReduce_ok VG.Proof.Ed448.Arm.scalarReduce_ct (by
    sig_implies [Spec.Ed448.scalarReduceContract, Spec.Ed448.scalarReduceSig,
      Spec.Ed448.scratchWords, VG.Proof.Ed448.Arm.scalarReduceLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [scalarReduceSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Ed448.Arm.scalarReduceSat)

theorem scalarMulAdd_ok (s : State) (hs : scalarMulAddLocal.pre s) :
    ∃ t s', Exec isa scalarMulAdd s t s' ∧ abiPreserved s s' ∧ scalarMulAddLocal.post s s' :=
  VG.Proof.Ed448.Arm.scalarMulAdd_correct (MulAddPre.of hs)

/-- The arguments are public, and so is what the code stores in the working
space (writable region 1, whose address is the stack argument): the
arguments' addresses, from `OUT`. -/
def scalarMulAddTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [57, 8192],
    argLen := 4, argBases := [(0, 1)] }

theorem scalarMulAddTaint_wf {s : State} (h : scalarMulAddLocal.pre s) :
    VG.Arm.Taint.Wf VG.Proof.Ed448.Arm.scalarMulAddTaint s := by
  have hp := MulAddPre.of h
  refine ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.Ed448.Arm.scalarMulAddTaint], ?_, ?_⟩,
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
    simp only [VG.Proof.Ed448.Arm.scalarMulAddTaint, List.mem_singleton] at hm
    subst hm
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem scalarMulAdd_argByte (s : State) (k : Nat) :
    VG.Arm.Taint.argByte s k = stackArgAddr s 0 + BitVec.ofNat 64 k := by
  simp [VG.Arm.Taint.argByte, stackArgAddr]

theorem scalarMulAdd_ct :
    ConstantTime isa scalarMulAddLocal.pre scalarMulAddLocal.pub scalarMulAdd := by
  refine VG.Taint.constantTime (A := taint) VG.Proof.Ed448.Arm.scalarMulAddTaint ?_ (by taint_decide)
  intro s t hs ht ⟨hsp, h0, h1, h2, h3, ha⟩
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.Ed448.Arm.scalarMulAddTaint_wf hs,
    VG.Proof.Ed448.Arm.scalarMulAddTaint_wf ht, fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => hsp, fun k hk => ?_⟩
  · simp only [VG.Proof.Ed448.Arm.scalarMulAddTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · rw [(MulAddPre.of hs).wr, (MulAddPre.of ht).wr, h0, ha]
  · rw [VG.Proof.Ed448.Arm.scalarMulAdd_argByte, VG.Proof.Ed448.Arm.scalarMulAdd_argByte, Mem.readW_byte s.mem _ hk, Mem.readW_byte t.mem _ hk]
    exact congrArg (fun v : BitVec 32 => v.extractLsb' (8 * k) 8) ha

def scalarMulAddSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x50 else 0
  rd := [⟨0x2000, 57⟩, ⟨0x3000, 57⟩, ⟨0x4000, 57⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x5000, 8192⟩]

theorem scalarMulAdd_verified : Verified Arm.target scalarMulAdd
    (Spec.Ed448.scalarMulAddContract Arm.abi) :=
  Verified.of_correct VG.Proof.Ed448.Arm.scalarMulAdd_ok VG.Proof.Ed448.Arm.scalarMulAdd_ct (by
    sig_implies [Spec.Ed448.scalarMulAddContract, Spec.Ed448.scalarMulAddSig,
      Spec.Ed448.scratchWords, VG.Proof.Ed448.Arm.scalarMulAddLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
      [scalarMulAddSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Ed448.Arm.scalarMulAddSat)

end VG.Proof.Ed448.Arm

end
