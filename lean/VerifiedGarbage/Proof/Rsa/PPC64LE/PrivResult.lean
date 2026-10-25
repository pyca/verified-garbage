module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCmp
public import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

/-!
# `vg_rsa_private_checked` on PPC64LE: the result

From the statuses kept in the frame and the comparison's accumulator,
without a branch: the result and the release mask (`result_ok`), as the
check's logic on every target computes them (`Proof.Rsa.result`,
`Proof.Rsa.relMask`).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv
open VG.Proof.Bignum.PPC64LE (Keep)

theorem eqBit (acc : BitVec 64) (h : acc.toNat < 2 ^ 8) :
    (acc - BitVec.ofNat 64 1) >>> 63 = if acc = 0#64 then 1 else 0 := by
  split
  · next he => subst he; decide
  · next he =>
    apply BitVec.eq_of_toNat_eq
    have h0 : acc.toNat ≠ 0 := fun h' => he (BitVec.eq_of_toNat_eq (by simpa using h'))
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_ofNat]
    have : (0 : BitVec 64).toNat = 0 := rfl
    omega_arith

theorem and1_cases (x : BitVec 64) : x &&& 1 = 0 ∨ x &&& 1 = 1 := by
  have h := Proof.Rsa.and1_toNat x
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h0 | h1
  · exact .inl (BitVec.eq_of_toNat_eq (by rw [h, h0]; rfl))
  · exact .inr (BitVec.eq_of_toNat_eq (by rw [h, h1]; rfl))

theorem res_val (x : BitVec 64) (P : Prop) [Decidable P] :
    (0#64 - (x &&& 1#64) &&& 2#64 - if P then 1 else 0) = Proof.Rsa.result (x &&& 1) (decide P) := by
  unfold Proof.Rsa.result
  rcases and1_cases x with h | h <;> rw [show (1#64 : BitVec 64) = 1 from rfl, h] <;> by_cases hp : P <;>
    simp only [hp, ↓reduceIte, decide_true, decide_false] <;> decide

theorem mask_val (x : BitVec 64) (P : Prop) [Decidable P] :
    0#64 - ((if P then 1 else 0) &&& (x &&& 1#64)) = Proof.Rsa.relMask (x &&& 1) (decide P) := by
  unfold Proof.Rsa.relMask
  rcases and1_cases x with h | h <;> rw [show (1#64 : BitVec 64) = 1 from rfl, h] <;> by_cases hp : P <;>
    simp only [hp, ↓reduceIte, decide_true, decide_false] <;> decide

/-- The result and the release mask. -/
theorem result_ok {s w : State} {cs es acc : BitVec 64} (hsp : w.sp = fb s)
    (iSt : InRegions (w.rd ++ w.wr) (fb s + BitVec.ofNat 64 oSt) 8)
    (iEs : InRegions (w.rd ++ w.wr) (fb s + BitVec.ofNat 64 oEs) 8)
    (hst : w.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = cs)
    (hes : w.mem.readW (fb s + BitVec.ofNat 64 oEs) 64 = es) (h5 : w.gpr .r5 = acc)
    (hacc : acc.toNat < 2 ^ 8) (h24 : w.gpr .r24 = s.gpr .r3) (h26 : w.gpr .r26 = s.gpr .r6) :
    WP isa (.block Impl.Rsa.PPC64LE.Priv.result) w fun u =>
      (u.gpr .r3 = Proof.Rsa.result (cs &&& es &&& 1) (decide (acc = 0#64)) ∧
        u.gpr .r9 = Proof.Rsa.relMask (cs &&& es &&& 1) (decide (acc = 0#64)) ∧
        u.gpr .r6 = s.gpr .r6 ∧ u.gpr .r7 = s.gpr .r3 ∧ u.gpr .r8 = fb s + BitVec.ofNat 64 oM ∧
        u.mem = w.mem) ∧
      Keep [.r12, .r3, .r4, .r5, .r6, .r7, .r8, .r9] w u := by
  have c1 : oSt < 2 ^ 15 := by decide
  have c2 : oSt % 4 = 0 := by decide
  have c3 : oEs < 2 ^ 15 := by decide
  have c4 : oEs % 4 = 0 := by decide
  have c5 : oM < 2 ^ 15 := by decide
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  unfold Impl.Rsa.PPC64LE.Priv.result
  prun [exec_addSp0, hsp, iSt, iEs, hst, hes, h5, h24, h26, c1, c2, c3, c4, c5, BitVec.or_self,
    exec_addi (show Reg.r12 ≠ .r0 by decide) c5, Impl.AesGcm.PPC64LE.mov, eqBit acc hacc]
  exact ⟨res_val _ _, mask_val _ _⟩

theorem write1_ne (m : Mem) {b x : Addr} (v : BitVec (8 * 1)) (h : x ≠ b) : m.write b 1 v x = m x :=
  Mem.write_apply fun h' => h (by bv_omega)

theorem off_ne (p : Addr) {i j : Nat} (h : i ≠ j) (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    p + BitVec.ofNat 64 i ≠ p + BitVec.ofNat 64 j := fun e => h (by
  have := congrArg (fun x => (x - p).toNat) e
  simp only [Mem.sub_ofNat_toNat p hi, Mem.sub_ofNat_toNat p hj] at this
  exact this)

theorem off_ne_of_disjoint {O M : Addr} {k i j : Nat} (hd : Region.Disjoint ⟨O, k⟩ ⟨M, k⟩) (hi : i < k)
    (hj : j < k) (hk : k ≤ 2 ^ 64) : O + BitVec.ofNat 64 i ≠ M + BitVec.ofNat 64 j := fun e =>
  hd _ (Offset.contains_base O (by omega_arith) (by omega_arith)) (e ▸ Offset.contains_base M (by omega_arith) (by omega_arith))

theorem zb_eq (m : Mem) (a : Addr) : zb m a = (m a).setWidth 64 := by
  have h := congrArg BitVec.toNat (Proof.Bignum.PPC64LE.read_one' m a)
  simp only [BitVec.toNat_setWidth] at h
  apply BitVec.eq_of_toNat_eq
  simp only [zb, BitVec.toNat_setWidth]
  have h1 := (m.read a 1).isLt
  have h2 := (m a).isLt
  simp only [Nat.reduceMul, Nat.reducePow] at h1 h2 h ⊢
  omega_arith

/-- The release: `out` := `m` under the mask, `m` := 0. -/
theorem release_ok {s w : State} (h : PreP s) (L : Late s w) {mask : BitVec 64} {c : Prop} [Decidable c]
    (hb : ∀ b : Byte, ((b.setWidth 64) &&& mask).setWidth 8 = if c then b else 0)
    (h6 : w.gpr .r6 = s.gpr .r6) (h7 : w.gpr .r7 = s.gpr .r3) (h8 : w.gpr .r8 = fb s + BitVec.ofNat 64 oM)
    (h9 : w.gpr .r9 = mask) :
    WP isa release w fun u =>
      Spec.Rsa.bytesAt u.mem (s.gpr .r3) (s.gpr .r6).toNat =
        (if c then Spec.Rsa.bytesAt w.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat
          else List.replicate (s.gpr .r6).toNat 0) ∧
      Frame [oR s, mR s] w.mem u.mem ∧ Keep [.r0, .r6, .r7, .r8] w u := by
  have hk := h.k2
  have hk1 := h.k1
  have fbt := fb_toNat h.sp1
  unfold frameBytes at fbt
  have om : Region.Disjoint (oR s) (mR s) :=
    (h.ko.sub_left (frame_sub s (by unfold oM frameBytes; omega_arith))).symm
  have om' : Region.Disjoint ⟨s.gpr .r3, (s.gpr .r6).toNat⟩ (mR s) := by rw [← h.h4] at *; exact om
  let O := s.gpr .r3
  let M := fb s + BitVec.ofNat 64 oM
  let k := (s.gpr .r6).toNat
  let Inv : Nat → State → Prop := fun j u =>
    u.gpr .r7 = O + BitVec.ofNat 64 j ∧ u.gpr .r8 = M + BitVec.ofNat 64 j ∧ Frame [oR s, mR s] w.mem u.mem ∧
      (∀ i < j, u.mem (O + BitVec.ofNat 64 i) = if c then w.mem (M + BitVec.ofNat 64 i) else 0) ∧
      (∀ i, j ≤ i → i < k → u.mem (M + BitVec.ofNat 64 i) = w.mem (M + BitVec.ofNat 64 i)) ∧
      Keep [.r0, .r6, .r7, .r8] w u
  refine WP.mono (Proof.Bignum.PPC64LE.wp_countdown (N := k) (by omega_arith) (by omega_arith) Inv
    (fun j hj u ⟨u7, u8, uf, uo, um, uk⟩ hc => ?_)
    ⟨by rw [h7]; simp [O], by rw [h8]; simp [M], Frame.refl _ _, fun _ h => absurd h (by omega_arith),
      fun _ _ _ => rfl, Keep.refl _ _⟩ (by rw [h6]; simp [k]))
    fun u ⟨_, _, uf, uo, _, uk⟩ => ⟨?_, uf, uk⟩
  · have u9 : u.gpr .r9 = mask := (uk.gpr .r9 (by decide)).trans h9
    have fw : u.wr = fr s :: oR s :: [sR s] := by rw [uk.wr, L.wr, h.hwr]
    have io : InRegions u.wr (O + BitVec.ofNat 64 j) 1 := by
      rw [fw]; exact ⟨oR s, by simp, Offset.contains_base _ (by rw [h.h4]; omega_arith) (by omega_arith)⟩
    have mc : (mR s).Contains (M + BitVec.ofNat 64 j) 1 := Offset.contains_base _ (by omega_arith) (by omega_arith)
    have e : M + BitVec.ofNat 64 j = fb s + BitVec.ofNat 64 (oM + j) := by
      simp only [M]; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    have im : InRegions u.wr (M + BitVec.ofNat 64 j) 1 := by
      rw [fw, e]; exact in_fr s _ (by unfold oM; omega_arith) (by unfold oM frameBytes; omega_arith)
    have imr : InRegions (u.rd ++ u.wr) (M + BitVec.ofNat 64 j) 1 := by
      obtain ⟨r, hr, hc⟩ := im; exact ⟨r, List.mem_append_right _ hr, hc⟩
    refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r0, .r6, .r7, .r8] (Q := fun u' =>
      u'.gpr .r7 = O + BitVec.ofNat 64 (j + 1) ∧ u'.gpr .r8 = M + BitVec.ofNat 64 (j + 1) ∧
        u'.mem = (u.mem.write (O + BitVec.ofNat 64 j) 1 ((zb u.mem (M + BitVec.ofNat 64 j) &&& mask).setWidth 8)).write
          (M + BitVec.ofNat 64 j) 1 ((0#64 : BitVec 64).setWidth 8) ∧
        u'.gpr .r6 = u.gpr .r6 - BitVec.ofNat 64 1) ?_ rfl) fun u' ⟨⟨v7, v8, vm, v6⟩, k'⟩ => ?_
    · prun [u7, u8, u9, io, im, imr, BitVec.add_zero, add_ofNat_one,
        Proof.Bignum.PPC64LE.exec_lbz' (show Reg.r8 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
        exec_stb (show Reg.r7 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
        exec_stb (show Reg.r8 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide)]
    · have hOM : ∀ {i j : Nat}, i < k → j < k → O + BitVec.ofNat 64 i ≠ M + BitVec.ofNat 64 j :=
        fun hi hj => off_ne_of_disjoint om' hi hj (by omega_arith)
      have hMj : u.mem (M + BitVec.ofNat 64 j) = w.mem (M + BitVec.ofNat 64 j) := um j (by omega_arith) hj
      refine ⟨⟨v7, v8, ?_, fun i hi => ?_, fun i hi hi' => ?_, uk.trans k' |>.mono⟩, v6⟩
      · rw [vm]
        refine Frame.write (Frame.write uf (List.mem_cons_self ..) _ ?_) (List.mem_cons_of_mem _
          (List.mem_singleton_self _)) _ mc
        exact Offset.contains_base _ (by rw [h.h4]; omega_arith) (by omega_arith)
      · rw [vm, write1_ne _ _ (hOM (by omega_arith) hj)]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · rw [write1_ne _ _ (off_ne O (by omega_arith) (by omega_arith) (by omega_arith))]; exact uo i hi
        · rw [Proof.Bignum.PPC64LE.write1_self, zb_eq, hMj]; exact hb _
      · rw [vm, write1_ne _ _ (off_ne M (by omega_arith) (by omega_arith) (by omega_arith)),
          write1_ne _ _ (Ne.symm (hOM hj hi'))]
        exact um i (by omega_arith) hi'
  · simp only [Spec.Rsa.bytesAt]
    split
    · exact List.map_congr_left fun i hi => by
        have := uo i (List.mem_range.mp hi); simp only [*, ↓reduceIte] at this; exact this
    · rw [List.eq_replicate_iff]
      refine ⟨by simp, fun b hb => ?_⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
      have := uo i (List.mem_range.mp hi); simp only [*, ↓reduceIte] at this; exact this
