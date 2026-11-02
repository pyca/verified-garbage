module

public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCmp
public import VerifiedGarbage.Proof.Rsa.PrivCheck
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_private_checked` on RISC-V: the result and the release

From the statuses kept in the frame and the comparison's accumulator,
without a branch: the result and the release mask (`result_ok`), as the
check's logic on every target computes them (`Proof.Rsa.result`,
`Proof.Rsa.relMask`); then `out` from `m` under the mask, and `m` cleared
(`release_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Priv

open VG VG.RISCV64 VG.Impl.Rsa.RISCV64.Priv VG.RISCV64.RegUpd

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
    omega

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
theorem result_ok {s w : State} {cs es acc : BitVec 64} (h : PreP s) (hsp : w.sp = fb s)
    (iSt : InRegions (w.rd ++ w.wr) (fb s + BitVec.ofNat 64 152) 8)
    (iEs : InRegions (w.rd ++ w.wr) (fb s + BitVec.ofNat 64 160) 8)
    (hst : w.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = cs)
    (hes : w.mem.readW (fb s + BitVec.ofNat 64 oEs) 64 = es) (h4 : w.gpr .t4 = acc)
    (hacc : acc.toNat < 2 ^ 8) (h1 : w.gpr .s1 = s.gpr .a0) (h3 : w.gpr .s3 = s.gpr .a3) :
    WP isa (.block Impl.Rsa.RISCV64.Priv.result) w fun u =>
      (u.gpr .a0 = Proof.Rsa.result (cs &&& es &&& 1) (decide (acc = 0#64)) ∧
        u.gpr .a3 = Proof.Rsa.relMask (cs &&& es &&& 1) (decide (acc = 0#64)) ∧
        u.gpr .t5 = s.gpr .a3 ∧ u.gpr .t2 = s.gpr .a0 ∧ u.gpr .t3 = fb s + BitVec.ofNat 64 oM ∧
        u.mem = w.mem) ∧
      Keep [.t0, .a0, .a1, .a2, .a3, .t4, .t5, .t2, .t3] w u := by
  have l1 : (fb s + BitVec.ofNat 64 152).toNat % 8 = 0 := fb_al8 h (by decide)
  have l2 : (fb s + BitVec.ofNat 64 160).toNat % 8 = 0 := fb_al8 h (by decide)
  have hst' : w.mem.readW (fb s + BitVec.ofNat 64 152) 64 = cs := hst
  have hes' : w.mem.readW (fb s + BitVec.ofNat 64 160) 64 = es := hes
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [Impl.Rsa.RISCV64.Priv.result, exec_addSp, hsp, BitVec.add_zero, iSt, iEs, l1, l2, hst', hes', h4, h1, h3,
    oSt, oEs, oM, mov, exec_li (d := .a1) (imm := 2) (by decide), exec_li (d := .a2) (imm := 0) (by decide),
    exec_logicImm (op := .and) (imm := 1) (by decide), eqBit acc hacc]
  exact ⟨res_val _ _, mask_val _ _⟩

theorem write1_ne (m : Mem) {b x : Addr} (v : BitVec (8 * 1)) (h : x ≠ b) : m.write b 1 v x = m x :=
  Mem.write_apply fun h' => h (by
    have e : x - b = 0 := BitVec.eq_of_toNat_eq (by show _ = 0; omega)
    rw [← BitVec.sub_add_cancel x b, e]; exact BitVec.zero_add _)

theorem off_ne (p : Addr) {i j : Nat} (h : i ≠ j) (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    p + BitVec.ofNat 64 i ≠ p + BitVec.ofNat 64 j := fun e => h (by
  have := congrArg (fun x => (x - p).toNat) e
  simp only [Mem.sub_ofNat_toNat p hi, Mem.sub_ofNat_toNat p hj] at this
  exact this)

theorem off_ne_of_disjoint {O M : Addr} {k i j : Nat} (hd : Region.Disjoint ⟨O, k⟩ ⟨M, k⟩) (hi : i < k)
    (hj : j < k) (hk : k ≤ 2 ^ 64) : O + BitVec.ofNat 64 i ≠ M + BitVec.ofNat 64 j := fun e =>
  hd _ (Offset.contains_base O (by omega) (by omega)) (e ▸ Offset.contains_base M (by omega) (by omega))

theorem zb_eq (m : Mem) (a : Addr) : zb m a = (m a).setWidth 64 := by
  have h := congrArg BitVec.toNat (Proof.Bignum.RISCV64.read_one' m a)
  simp only [BitVec.toNat_setWidth] at h
  apply BitVec.eq_of_toNat_eq
  simp only [zb, BitVec.toNat_setWidth]
  have h1 := (m.read a 1).isLt
  have h2 := (m a).isLt
  simp only [Nat.reduceMul, Nat.reducePow] at h1 h2 h ⊢
  omega

/-- The release: `out` := `m` under the mask, `m` := 0. -/
theorem release_ok {s w : State} (h : PreP s) (L : Late s w) {mask : BitVec 64} {c : Prop} [Decidable c]
    (hb : ∀ b : Byte, ((b.setWidth 64) &&& mask).setWidth 8 = if c then b else 0)
    (h5 : w.gpr .t5 = s.gpr .a3) (h2 : w.gpr .t2 = s.gpr .a0) (h3 : w.gpr .t3 = fb s + BitVec.ofNat 64 oM)
    (hm : w.gpr .a3 = mask) :
    WP isa release w fun u =>
      Spec.Rsa.bytesAt u.mem (s.gpr .a0) (s.gpr .a3).toNat =
        (if c then Spec.Rsa.bytesAt w.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat
          else List.replicate (s.gpr .a3).toNat 0) ∧
      Frame [oR s, mR s] w.mem u.mem ∧ Keep [.a1, .a2, .t2, .t3, .t5] w u := by
  have hk := h.k2
  have hk1 := h.k1
  have fbt := fb_toNat h.sp1
  unfold frameBytes at fbt
  have om : Region.Disjoint (oR s) (mR s) :=
    (h.ko.sub_left (frame_sub s (by unfold oM frameBytes; omega))).symm
  have om' : Region.Disjoint ⟨s.gpr .a0, (s.gpr .a3).toNat⟩ (mR s) := by rw [← h.h1] at *; exact om
  let O := s.gpr .a0
  let M := fb s + BitVec.ofNat 64 oM
  let k := (s.gpr .a3).toNat
  let Inv : Nat → State → Prop := fun j u =>
    u.gpr .t2 = O + BitVec.ofNat 64 j ∧ u.gpr .t3 = M + BitVec.ofNat 64 j ∧ Frame [oR s, mR s] w.mem u.mem ∧
      (∀ i < j, u.mem (O + BitVec.ofNat 64 i) = if c then w.mem (M + BitVec.ofNat 64 i) else 0) ∧
      (∀ i, j ≤ i → i < k → u.mem (M + BitVec.ofNat 64 i) = w.mem (M + BitVec.ofNat 64 i)) ∧
      Keep [.a1, .a2, .t2, .t3, .t5] w u
  refine WP.mono (Proof.Bignum.RISCV64.wp_countdown (N := k) (by omega) (by omega) Inv
    (fun j hj u ⟨u2, u3, uf, uo, um, uk⟩ hc => ?_)
    ⟨by rw [h2]; simp [O], by rw [h3]; simp [M], Frame.refl _ _, fun _ h => absurd h (by omega),
      fun _ _ _ => rfl, Keep.refl _ _⟩ (by rw [h5]; simp [k]))
    fun u ⟨_, _, uf, uo, _, uk⟩ => ⟨?_, uf, uk⟩
  · have ua3 : u.gpr .a3 = mask := (uk.gpr (by decide)).trans hm
    have fw : u.wr = kR s :: oR s :: [sR s] := by rw [uk.2.2, L.wr, h.hwr]
    have io : InRegions u.wr (O + BitVec.ofNat 64 j) 1 := by
      rw [fw]; exact ⟨oR s, by simp, Offset.contains_base _ (by rw [h.h1]; omega) (by omega)⟩
    have mc : (mR s).Contains (M + BitVec.ofNat 64 j) 1 := Offset.contains_base _ (by omega) (by omega)
    have e : M + BitVec.ofNat 64 j = fb s + BitVec.ofNat 64 (oM + j) := by
      simp only [M]; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    have im : InRegions u.wr (M + BitVec.ofNat 64 j) 1 := by
      rw [fw, e]; exact in_fr s _ (by unfold oM frameBytes; omega)
    have imr : InRegions (u.rd ++ u.wr) (M + BitVec.ofNat 64 j) 1 := by
      obtain ⟨r, hr, hc⟩ := im; exact ⟨r, List.mem_append_right _ hr, hc⟩
    refine WP.mono (WP.keep [.a1, .a2, .t2, .t3, .t5] (Q := fun u' =>
      u'.gpr .t2 = O + BitVec.ofNat 64 (j + 1) ∧ u'.gpr .t3 = M + BitVec.ofNat 64 (j + 1) ∧
        u'.mem = (u.mem.write (O + BitVec.ofNat 64 j) 1 ((zb u.mem (M + BitVec.ofNat 64 j) &&& mask).setWidth 8)).write
          (M + BitVec.ofNat 64 j) 1 ((BitVec.ofNat 64 0).setWidth 8) ∧
        u'.gpr .t5 = u.gpr .t5 - BitVec.ofNat 64 1) ?_ (by rfl) (by rfl)) fun u' ⟨⟨v2, v3, vm, v5⟩, k'⟩ => ?_
    · brun [u2, u3, ua3, io, im, imr, BitVec.add_zero, add_ofNat_one, exec_li (d := .a2) (imm := 0) (by decide)]
    · have hOM : ∀ {i j : Nat}, i < k → j < k → O + BitVec.ofNat 64 i ≠ M + BitVec.ofNat 64 j :=
        fun hi hj => off_ne_of_disjoint om' hi hj (by omega)
      have hMj : u.mem (M + BitVec.ofNat 64 j) = w.mem (M + BitVec.ofNat 64 j) := um j (by omega) hj
      refine ⟨⟨v2, v3, ?_, fun i hi => ?_, fun i hi hi' => ?_, uk.trans k' |>.mono fun r hr =>
        (List.mem_append.mp hr).elim id id⟩, v5⟩
      · rw [vm]
        refine Frame.write (Frame.write uf (List.mem_cons_self ..) _ ?_) (List.mem_cons_of_mem _
          (List.mem_singleton_self _)) _ mc
        exact Offset.contains_base _ (by rw [h.h1]; omega) (by omega)
      · rw [vm, write1_ne _ _ (hOM (by omega) hj)]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · rw [write1_ne _ _ (off_ne O (by omega) (by omega) (by omega))]; exact uo i hi
        · rw [Proof.Bignum.RISCV64.write1_self, zb_eq, hMj]; exact hb _
      · rw [vm, write1_ne _ _ (off_ne M (by omega) (by omega) (by omega)),
          write1_ne _ _ (Ne.symm (hOM hj hi'))]
        exact um i (by omega) hi'
  · simp only [Spec.Rsa.bytesAt]
    split
    · exact List.map_congr_left fun i hi => by
        have := uo i (List.mem_range.mp hi); simp only [*, ↓reduceIte] at this; exact this
    · rw [List.eq_replicate_iff]
      refine ⟨by simp, fun b hb => ?_⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
      have := uo i (List.mem_range.mp hi); simp only [*, ↓reduceIte] at this; exact this

end VG.Proof.Rsa.RISCV64.Priv
