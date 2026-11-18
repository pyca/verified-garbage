module

public import VerifiedGarbage.Proof.X25519.Contract
public import VerifiedGarbage.Proof.X25519.Arm.Invert
public import VerifiedGarbage.Spec.X25519.Contract
public import VerifiedGarbage.Proof.X25519.Arm.Setup
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.X25519.Arm.Mul
public import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.X25519.Arm.AddSub
import VerifiedGarbage.Proof.X25519.Arm.CT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.X25519.Arm.Lit

/-! ### `X25519.Arm.Main`, which only this module used -/

section

/-! ### `X25519.Arm.Bits`, which only this module used -/

section

/-!
# X25519 on 32-bit ARM: the bits of the scalar

`bits` stores bit `t` of the decoded (clamped) scalar at byte `BITS + t` of
the working space, for `t < 255` (`bits_ok`).
-/

@[expose] public section

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P Fe bytesAt)
open VG.Proof.X25519 (bit)

/-- Bit `t` of the scalar's bytes at `SC`, unclamped. -/
def rawBit (m : Mem) (SC : Addr) (t : Nat) : Nat := ((m (SC + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1

theorem getD_bytesAt (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

theorem strb_byte {v : BitVec 32} {x : Nat} (h : v.toNat = x) :
    v.setWidth 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, h, BitVec.toNat_ofNat]

section
variable {b : BitVec 32}

/-- While storing the bits of byte `i`, from `s1` (with the byte in `r4`),
after `j` bits. -/
structure JInv (b : BitVec 32) (i : Nat) (x : Nat) (s1 : State) (j : Nat) (s : State) : Prop where
  rest : Rest [.r5] s1 s
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 (BITS + 8 * i), j⟩] s1.mem s.mem
  bits : ∀ j' < j, s.mem (State.addr b + BitVec.ofNat 64 (BITS + 8 * i + j')) = BitVec.ofNat 8 ((x >>> j') &&& 1)

theorem bitStep_ok {i j : Nat} (hi : i < 32) (hj : j < 8) {x : Nat} {s1 s : State}
    (hc : Ctx b s1) (h4 : (s1.gpr .r4).toNat = x) (h6 : s1.gpr .r6 = b + BitVec.ofNat 32 (8 * i))
    (h : JInv b i x s1 j s) :
    WP isa (.block ((if j = 0 then ([.dp .and .r5 .r4 (.imm 1)] : List Instr)
      else ([.mov .r5 (.shifted .r4 .lsr j), .dp .and .r5 .r5 (.imm 1)] : List Instr)) ++
      ([.strb .r5 .r6 (BITS + j)] : List Instr))) s
      (JInv b i x s1 (j + 1)) := by
  have hB : BITS = 1280 := rfl
  have hfit := hc.fit
  obtain e4 : (s.gpr .r4).toNat = x := by rw [h.rest.gpr _ (by decide), h4]
  -- The bit, into `r5`.
  obtain key : ∀ s2 : State, Rest [.r5] s s2 → s2.mem = s.mem → (s2.gpr .r5).toNat = (x >>> j) &&& 1 →
      WP isa (.block [.strb .r5 .r6 (BITS + j)]) s2 (JInv b i x s1 (j + 1)) := by
    intro s2 hr2 hm2 e5
    obtain e6 : s2.gpr .r6 = b + BitVec.ofNat 32 (8 * i) := by
      rw [hr2.gpr _ (by decide), h.rest.gpr _ (by decide), h6]
    refine wp_strb (a := State.addr b + BitVec.ofNat 64 (BITS + 8 * i + j)) (by omega_using [hj, hB])
      (by rw [e6, ea2 hfit (by omega_using [hi, hj, hB])]; congr 2; omega_using [])
      (by rw [hr2.wr, h.rest.wr]; exact hc.inW (by omega_using [hi, hj, hB])) fun s3 u3 => WP.block_nil ⟨?_, ?_, fun j' hj' => ?_⟩
    · exact h.rest.trans (hr2.trans (u3.rest _))
    · rw [u3.mem, hm2]
      exact (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [])⟩).writeW
        (List.mem_singleton_self _) _ (Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [hi, hj, hB]))
    · rw [u3.mem, VG.WriteBytes.writeW8_apply, hm2]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | rfl
      · rw [iteF (Offset.add_ofNat_ne _ (by omega_arith) (by omega_using [hi, hj, hB]) (by omega_using [hj']))]; exact h.bits j' hj'
      · rw [iteT rfl]; exact strb_byte e5
  by_cases h0 : j = 0
  · subst h0
    simp only [ite_true, List.cons_append, List.nil_append]
    refine wp_dp (op2_imm (by decide)) fun s2 u2 => key s2 (u2.rest (by decide)) u2.mem ?_
    rw [u2.gpr]
    show (s.gpr .r4 &&& 1).toNat = _
    rw [BitVec.toNat_and, e4, Nat.shiftRight_zero]; rfl
  · simp only [h0, ite_false, List.cons_append, List.nil_append]
    refine wp_mov (op2_lsr (by omega_using [hj, h0])) fun s2 u2 => wp_dp (op2_imm (by decide)) fun s3 u3 =>
      key s3 ((u2.rest (by decide)).trans (u3.rest (by decide))) (by rw [u3.mem, u2.mem]) ?_
    rw [u3.gpr]
    show (s2.gpr .r5 &&& 1).toNat = _
    rw [BitVec.toNat_and, u2.gpr, toNat_shr, e4, Nat.shiftRight_eq_div_pow]; rfl

/-- The loop invariant of `bits` from `s0`, before byte `i`. -/
structure BInv (b : BitVec 32) (sc : BitVec 32) (s0 : State) (i : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest [.r1, .r4, .r5, .r6, .r7] s0 s
  r1 : s.gpr .r1 = sc + BitVec.ofNat 32 i
  r6 : s.gpr .r6 = b + BitVec.ofNat 32 (8 * i)
  r7 : s.gpr .r7 = BitVec.ofNat 32 (32 - i)
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 BITS, 8 * i⟩] s0.mem s.mem
  bits : ∀ t < 8 * i, s.mem (State.addr b + BitVec.ofNat 64 (BITS + t)) = BitVec.ofNat 8 (rawBit s0.mem (State.addr sc) t)

theorem bitsBody_ok {sc : BitVec 32} {s0 : State} (hsc : sc.toNat + 32 ≤ 2 ^ 32)
    (hin : (⟨State.addr sc, 32⟩ : Region) ∈ s0.rd ++ s0.wr)
    (hd : Region.Disjoint ⟨State.addr sc, 32⟩ ⟨State.addr b, 4096⟩) {i : Nat} (hi : i < 32) {s : State}
    (h : BInv b sc s0 i s) :
    WP isa (.block bitsBody) s fun s' => BInv b sc s0 (i + 1) s' ∧ s'.z = decide (32 - (i + 1) = 0) := by
  have hB : BITS = 1280 := rfl
  have hfit := h.ctx.fit
  unfold bitsBody
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrb (a := State.addr sc + BitVec.ofNat 64 i) (by decide)
    (by rw [h.r1, BitVec.add_zero]; exact addr_add (by omega_using [hsc, hi]))
    (by rw [h.rest.rd, h.rest.wr]; exact in_base hin (by omega_using [hi]) (by omega_using [hi])) fun s1 u1 => ?_
  obtain hc1 : Ctx b s1 := h.ctx.of_rest (u1.rest (ws := [.r4]) (by decide)) (by decide)
  -- The byte, as in `s0`.
  obtain hx : (s1.gpr .r4).toNat = (s0.mem (State.addr sc + BitVec.ofNat 64 i)).toNat := by
    rw [u1.gpr, toNat_setWidth8]
    congr 1
    refine h.frame _ fun r hr hcon => ?_
    rw [List.mem_singleton.mp hr] at hcon
    exact hd _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))
      ((Offset.sub_base (State.addr b) (d := BITS) (n := 8 * i) (k := 4096) (by omega_using [hi, hB])) _ hcon)
  refine WP.append (wp_range_flatMap (M := isa) (JInv b i (s0.mem (State.addr sc + BitVec.ofNat 64 i)).toNat s1)
    (fun j s' hj h' => bitStep_ok hi hj hc1 hx (by rw [u1.other _ (by decide), h.r6]) h') 8 (Nat.le_refl _) s1
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s2 h2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => wp_dp (op2_imm (by decide)) fun s4 u4 =>
    wp_subs (op2_imm (by decide)) fun s5 u5 hz => WP.block_nil ?_
  obtain hr5 : Rest [.r1, .r4, .r5, .r6, .r7] s s5 :=
    (u1.rest (by decide)).trans ((h2.rest.mono (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide)))))
  obtain hm5 : s5.mem = s2.mem := by rw [u5.mem, u4.mem, u3.mem]
  obtain r7' : s5.gpr .r7 = BitVec.ofNat 32 (32 - (i + 1)) := by
    rw [u5.gpr, u4.other _ (by decide), u3.other _ (by decide), h2.rest.gpr _ (by decide),
      u1.other _ (by decide), h.r7]
    have t1 : (1 : BitVec 32).toNat = 1 := rfl
    apply BitVec.eq_of_toNat_eq
    rw [toNat_sub_le (by rw [toNat_imm (by omega_using []), t1]; omega_using [hi]), toNat_imm (by omega_using []), toNat_imm (by omega_using []), t1]
    omega_using []
  refine ⟨⟨h.ctx.of_rest hr5 (by decide), h.rest.trans hr5, ?_, ?_, r7', ?_, fun t ht => ?_⟩, ?_⟩
  · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr]
    show s2.gpr .r1 + BitVec.ofNat 32 1 = _
    rw [h2.rest.gpr _ (by decide), u1.other _ (by decide), h.r1, Offset.add_add]
  · rw [u5.other _ (by decide), u4.gpr]
    show s3.gpr .r6 + BitVec.ofNat 32 8 = _
    rw [u3.other _ (by decide), h2.rest.gpr _ (by decide), u1.other _ (by decide), h.r6, Offset.add_add,
      Nat.mul_succ]
  · rw [hm5]
    refine (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [])⟩).trans ?_
    rw [← u1.mem]
    exact h2.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_using []) (by omega_using [])⟩
  · rw [hm5]
    rcases Nat.lt_or_ge t (8 * i) with ht' | ht'
    · rw [h2.frame _ fun r hr hcon => by
        rw [List.mem_singleton.mp hr] at hcon
        exact Offset.disjoint (State.addr b) (d := BITS + t) (n := 1) (e := BITS + 8 * i) (k := 8)
          (.inl (by omega_using [ht'])) (by omega_using [hi, hB, ht']) (by omega_using [hi, hB]) _ (Region.contains_self _ _) hcon, u1.mem]
      exact h.bits t ht'
    · have := h2.bits (t - 8 * i) (by omega_using [ht])
      rw [show BITS + 8 * i + (t - 8 * i) = BITS + t by omega_using [ht']] at this
      rw [this]
      simp only [rawBit, show t / 8 = i by omega_using [ht, ht'], show t % 8 = t - 8 * i by omega_using [ht, ht']]
  · rw [hz, ← u5.gpr, r7', ofNat_beq_zero (by omega_using [])]

theorem bits_ok {sc : BitVec 32} {s : State} (hc : Ctx b s) (h1 : s.gpr .r1 = sc)
    (hsc : sc.toNat + 32 ≤ 2 ^ 32) (hin : (⟨State.addr sc, 32⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : Region.Disjoint ⟨State.addr sc, 32⟩ ⟨State.addr b, 4096⟩) :
    WP isa bits s fun s' => Ctx b s' ∧ Rest [.r1, .r4, .r5, .r6, .r7] s s' ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 BITS, 256⟩] s.mem s'.mem ∧
      Bits b (VG.Spec.X25519.decodeScalar25519 (bytesAt s.mem (State.addr sc) 32)) s'.mem := by
  have hB : BITS = 1280 := rfl
  have hfit := hc.fit
  unfold bits
  refine WP.seq (wp_mov (op2_reg _ _) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 => WP.block_nil ?_)
  obtain hr2 : Rest [.r6, .r7] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  obtain hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  obtain h0 : BInv b sc s2 0 s2 :=
    ⟨hc.of_rest hr2 (by decide), Rest.refl _ _, by rw [hr2.gpr _ (by decide), h1]; exact (BitVec.add_zero _).symm,
      by rw [u2.other _ (by decide), u1.gpr, hc.r0]; exact (BitVec.add_zero _).symm, by rw [u2.gpr]; rfl,
      Frame.refl _ _, fun t ht => absurd ht (by omega_using [])⟩
  refine WP.seq (WP.mono (Q := BInv b sc s2 32) (WP.loop (M := isa)
    (fun m s' => ∃ i, m = 32 - i ∧ i < 32 ∧ BInv b sc s2 i s') ?_ 32 s2 ⟨0, rfl, by decide, h0⟩)
    fun s3 h3 => ?_)
  · rintro m s' ⟨i, rfl, hi, hb⟩
    refine WP.mono (bitsBody_ok hsc (by rw [hr2.rd, hr2.wr]; exact hin) hd hi hb) fun s'' ⟨hb', hz⟩ => ?_
    by_cases h32 : i + 1 = 32
    · exact .inl ⟨by rw [eval_ne, hz]; simp [h32], by rw [h32] at hb'; exact hb'⟩
    · exact .inr ⟨by rw [eval_ne, hz]; simp; omega_using [hi, h32], 32 - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, h32], hb'⟩
  -- The clamping.
  have hc3 := h3.ctx
  refine wp_mov (op2_imm (by decide)) fun s4 u4 => ?_
  obtain hc4 : Ctx b s4 := hc3.of_rest (u4.rest (ws := [.r5]) (by decide)) (by decide)
  obtain st : ∀ (t : State), Ctx b t → ∀ d, d < 4096 → State.addr (t.gpr .r0 + BitVec.ofNat 32 d) =
      State.addr b + BitVec.ofNat 64 d := fun t ht d hd => ht.ea hd
  refine wp_strb (a := State.addr b + BitVec.ofNat 64 BITS) (by decide) (st _ hc4 _ (by omega_using [hB]))
    (hc4.inW (by omega_using [hB])) fun s5 u5 => ?_
  obtain hc5 : Ctx b s5 := hc4.of_rest (u5.rest []) (by decide)
  refine wp_strb (a := State.addr b + BitVec.ofNat 64 (BITS + 1)) (by decide) (st _ hc5 _ (by omega_using [hB]))
    (hc5.inW (by omega_using [hB])) fun s6 u6 => ?_
  obtain hc6 : Ctx b s6 := hc5.of_rest (u6.rest []) (by decide)
  refine wp_strb (a := State.addr b + BitVec.ofNat 64 (BITS + 2)) (by decide) (st _ hc6 _ (by omega_using [hB]))
    (hc6.inW (by omega_using [hB])) fun s7 u7 => ?_
  obtain hc7 : Ctx b s7 := hc6.of_rest (u7.rest []) (by decide)
  refine wp_mov (op2_imm (by decide)) fun s8 u8 => ?_
  obtain hc8 : Ctx b s8 := hc7.of_rest (u8.rest (ws := [.r5]) (by decide)) (by decide)
  refine wp_strb (a := State.addr b + BitVec.ofNat 64 (BITS + 254)) (by decide) (st _ hc8 _ (by omega_using [hB]))
    (hc8.inW (by omega_using [hB])) fun s9 u9 => WP.block_nil ?_
  obtain v0 : (s4.gpr .r5).setWidth 8 = 0 := by rw [u4.gpr]; rfl
  obtain v1 : (s8.gpr .r5).setWidth 8 = 1 := by rw [u8.gpr]; rfl
  obtain hm9 : s9.mem = (((s3.mem.writeW (State.addr b + BitVec.ofNat 64 BITS) (0 : BitVec 8)).writeW
      (State.addr b + BitVec.ofNat 64 (BITS + 1)) (0 : BitVec 8)).writeW
      (State.addr b + BitVec.ofNat 64 (BITS + 2)) (0 : BitVec 8)).writeW
      (State.addr b + BitVec.ofNat 64 (BITS + 254)) (1 : BitVec 8) := by
    rw [u9.mem, v1, u8.mem, u7.mem, u6.gpr, u5.gpr, v0, u6.mem, u5.gpr, v0, u5.mem, v0, u4.mem]
  obtain ne : ∀ a c : Nat, a < 256 → c < 256 → a ≠ c →
      State.addr b + BitVec.ofNat 64 (BITS + a) ≠ State.addr b + BitVec.ofNat 64 (BITS + c) :=
    fun a c ha hc' hac => Offset.add_ofNat_ne _ (by omega_using [hB, ha]) (by omega_using [hB, hc']) (by omega_using [hac])
  obtain hr9 : Rest [.r1, .r4, .r5, .r6, .r7] s s9 :=
    (hr2.mono (by decide)).trans ((h3.rest).trans ((u4.rest (by decide)).trans ((u5.rest _).trans
      ((u6.rest _).trans ((u7.rest _).trans ((u8.rest (by decide)).trans (u9.rest _)))))))
  refine ⟨hc3.of_rest ((u4.rest (ws := [.r5]) (by decide)).trans ((u5.rest _).trans ((u6.rest _).trans
    ((u7.rest _).trans ((u8.rest (by decide)).trans (u9.rest _)))))) (by decide), hr9, ?_, fun t ht => ?_⟩
  · rw [hm9, ← hm2]
    obtain m := List.mem_singleton_self (⟨State.addr b + BitVec.ofNat 64 BITS, 256⟩ : Region)
    refine ((((h3.frame.sub fun r hr => ⟨_, m, by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [])⟩).writeW m _ ?_).writeW m _ ?_).writeW m _ ?_).writeW
      m _ ?_ <;> exact Offset.contains _ (n := 1) (by omega_using []) (by omega_using []) (by omega_using [hB])
  · have hbit := VG.Proof.X25519.scalar_bit (length_bytesAt s.mem (State.addr sc) 32) ht
    rw [getD_bytesAt _ _ (by omega_using [ht])] at hbit
    rw [hbit, hm9]
    simp only [VG.WriteBytes.writeW8_apply]
    by_cases t254 : t = 254
    · subst t254; rw [iteT rfl]; rfl
    rw [iteF (ne _ _ (by omega_using [ht]) (by omega_using []) t254)]
    by_cases t2 : t = 2
    · subst t2; rw [iteT rfl]; rfl
    rw [iteF (ne _ _ (by omega_using [ht]) (by omega_using []) t2)]
    by_cases t1 : t = 1
    · subst t1; rw [iteT rfl]; rfl
    rw [iteF (ne _ _ (by omega_using [ht]) (by omega_using []) t1)]
    by_cases t0 : t = 0
    · subst t0; rw [iteT (by rfl)]; rfl
    rw [iteF (show State.addr b + BitVec.ofNat 64 (BITS + t) ≠ State.addr b + BitVec.ofNat 64 BITS from
      fun e => ne t 0 (by omega_using [ht]) (by omega_using []) t0 (by rw [e]; rfl)), h3.bits t (by omega_using [ht]), hm2,
      iteF (show ¬ t < 3 by omega_using [t2, t1, t0]), iteF t254]
    rfl

end

end VG.Proof.X25519.Arm

end

end

/-! ### `X25519.Arm.Freeze`, which only this module used -/

section

/-!
# X25519 on 32-bit ARM: the final reduction and the output

`freeze` stores the 32 bytes of the element at `X2`, reduced fully modulo `p`,
at `out` (`freeze_ok`).
-/

@[expose] public section

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P Fe bytesAt)
open VG.Proof.X25519 (leBytes)

theorem low15_val (x : BitVec 32) : ((x <<< 17) >>> 17).toNat = x.toNat % 32768 := by
  rw [toNat_shr, toNat_shl, show (2 : Nat) ^ 32 = 32768 * 2 ^ 17 from rfl, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

theorem sel0r (a c : BitVec 32) : a ^^^ ((c ^^^ a) &&& (0 - BitVec.ofNat 32 0)) = a := by simp

theorem sel1r (a c : BitVec 32) : a ^^^ ((c ^^^ a) &&& (0 - BitVec.ofNat 32 1)) = c := by
  have : (0 : BitVec 32) - BitVec.ofNat 32 1 = BitVec.allOnes 32 := by decide
  rw [this, BitVec.and_allOnes, BitVec.xor_comm c, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem byte_eq {v : BitVec 32} {n : Nat} (h : v.toNat = n) : v.setWidth 8 = BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, h]

theorem ofNat8_eq {a c : Nat} (h : a % 256 = c % 256) : BitVec.ofNat 8 a = BitVec.ofNat 8 c := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]; exact h

/-- The bytes at `O` are those of `X`, if the bytes `2k` and `2k + 1` are those
of limb `k`. -/
theorem bytesAt_limbs {m : Mem} {O : Addr} {r : Nat → Nat} (hr : ∀ k < 16, r k < 65536)
    (h0 : ∀ k < 16, m (O + BitVec.ofNat 64 (2 * k)) = BitVec.ofNat 8 (r k))
    (h1 : ∀ k < 16, m (O + BitVec.ofNat 64 (2 * k + 1)) = BitVec.ofNat 8 (r k / 256)) :
    bytesAt m O 32 = leBytes 32 (val16 r 16) := by
  simp only [bytesAt, leBytes]
  refine List.map_congr_left fun i hi => ?_
  obtain hi := List.mem_range.mp hi
  obtain hk : i / 2 < 16 := by omega_arith
  obtain ⟨b0, b1⟩ := bytes_of_limbs hr hk
  rcases Nat.mod_two_eq_zero_or_one i with he | ho
  · rw [show i = 2 * (i / 2) by omega_using [he], h0 _ hk]
    exact ofNat8_eq b0.symm
  · rw [show i = 2 * (i / 2) + 1 by omega_using [ho], h1 _ hk]
    refine ofNat8_eq ?_
    rw [b1, Nat.mod_eq_of_lt (by have := hr _ hk; omega_using [this])]

section
variable {b : BitVec 32}

/-- The start of `freeze`: bit 255 of `[X2]` cleared, 19 times it in `r5`. -/
theorem freezeA_ok {s : State} (hc : Ctx b s) (hl : Lim s.mem (State.addr b) X2) :
    WP isa (.block freezeA) s fun s' =>
      s'.gpr .r6 = mask16 ∧ (s'.gpr .r5).toNat = 19 * (limb s.mem (State.addr b) X2 15 / 32768) ∧
      (∀ k < 16, limb s'.mem (State.addr b) X2 k = mask15 (limb s.mem (State.addr b) X2) k) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 X2, 64⟩] s.mem s'.mem ∧
      Rest [.r2, .r3, .r5, .r6] s s' := by
  have hX : X2 = 128 := rfl
  simp only [freezeA, low15, List.cons_append, List.nil_append]
  refine wp_movw fun s1 u1 => ?_
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := [.r6]) (by decide)) (by decide)
  refine ldr0_ok hc1 (d := X2 + 60) (by decide) fun s2 u2 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s3 u3 => wp_mov (op2_lsl (by decide)) fun s4 u4 =>
    wp_mov (op2_lsr (by decide)) fun s5 u5 => ?_
  have hr5 : Rest [.r3, .r5, .r6] s s5 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide)))))
  have hc5 : Ctx b s5 := hc.of_rest hr5 (by decide)
  refine str0_ok hc5 (d := X2 + 60) (by decide) fun s6 u6 => ?_
  refine wp_mov (op2_imm (by decide)) fun s7 u7 => wp_mul fun s8 u8 => WP.block_nil ?_
  have hl15 := hl 15 (by decide)
  have e2 : (s2.gpr .r3).toNat = limb s.mem (State.addr b) X2 15 := by rw [u2.gpr, u1.mem]; rfl
  have e5 : (s5.gpr .r3).toNat = limb s.mem (State.addr b) X2 15 % 32768 := by
    rw [u5.gpr, u4.gpr, low15_val, u3.other .r3 (by decide), e2]
  have e3 : (s3.gpr .r5).toNat = limb s.mem (State.addr b) X2 15 / 32768 := by
    rw [u3.gpr, toNat_shr, e2]
  have hm6 : s6.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (X2 + 60)) (s5.gpr .r3) := by
    rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨?_, ?_, fun k hk => ?_, ?_, ?_⟩
  · rw [u8.other _ (by decide), u7.other _ (by decide), u6.gpr, u5.other .r6 (by decide),
      u4.other .r6 (by decide), u3.other .r6 (by decide), u2.other .r6 (by decide), u1.gpr]
  · rw [u8.gpr, u7.other _ (by decide), u7.gpr, u6.gpr, u5.other _ (by decide), u4.other _ (by decide),
      toNat_mul_lt (by rw [e3]; show _ * 19 < _; omega_using [e2]), e3]
    show _ * 19 = _
    omega_using []
  · rw [limb, u8.mem, u7.mem, hm6]
    rcases Nat.lt_or_ge k 15 with h | h
    · rw [wd_write_other _ _ _ (by omega_using [h]) (by omega_using [hX, h]) (by omega_using [hX])]
      simp only [mask15, show k ≠ 15 by omega_using [h], ite_false]; rfl
    · rw [show X2 + 4 * k = X2 + 60 by omega_using [hk, h], wd_write_self, e5, show k = 15 by omega_using [hk, h]]; rfl
  · rw [u8.mem, u7.mem, hm6]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (d := X2 + 60) (n := 4) (Nat.le_add_right _ _) (by omega_using []) (by omega_using [hX]))
  · exact (hr5.mono (by decide)).trans ((u6.rest _).trans ((u7.rest (by decide)).trans (u8.rest (by decide))))

/-- `freezeB`: the mask `-(bit 255 of [Y])` in `r9`, and bit 255 of `[Y]` cleared. -/
theorem freezeB_ok {s : State} (hc : Ctx b s) :
    WP isa (.block freezeB) s fun s' =>
      s'.gpr .r9 = 0 - BitVec.ofNat 32 (limb s.mem (State.addr b) Y 15 / 32768) ∧
      (∀ k < 16, limb s'.mem (State.addr b) Y k = mask15 (limb s.mem (State.addr b) Y) k) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 Y, 64⟩] s.mem s'.mem ∧ Rest [.r1, .r3, .r9] s s' := by
  have hY : Y = 1088 := rfl
  simp only [freezeB, low15, List.cons_append, List.nil_append]
  refine ldr0_ok hc (d := Y + 60) (by decide) fun s1 u1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => wp_mov (op2_imm (by decide)) fun s3 u3 =>
    wp_dp (op2_reg _ _) fun s4 u4 => wp_mov (op2_lsl (by decide)) fun s5 u5 =>
    wp_mov (op2_lsr (by decide)) fun s6 u6 => ?_
  obtain hr6 : Rest [.r1, .r3, .r9] s s6 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  refine str0_ok (hc.of_rest hr6 (by decide)) (d := Y + 60) (by decide) fun s7 u7 => WP.block_nil ?_
  obtain e1 : (s1.gpr .r3).toNat = limb s.mem (State.addr b) Y 15 := by rw [u1.gpr]; rfl
  obtain hm7 : s7.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (Y + 60)) (s6.gpr .r3) := by
    rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨?_, fun k hk => ?_, ?_, hr6.trans (u7.rest _)⟩
  · rw [u7.gpr, u6.other _ (by decide), u5.other _ (by decide), u4.gpr]
    show s3.gpr .r1 - s3.gpr .r9 = _
    rw [u3.gpr, u3.other _ (by decide), u2.gpr]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [toNat_shr, e1, toNat_imm (by have := wd_lt s.mem (State.addr b) (Y + 4 * 15); unfold limb; omega_using [this])]
  · rw [limb, hm7]
    rcases Nat.lt_or_ge k 15 with h | h
    · rw [wd_write_other _ _ _ (by omega_using [h]) (by omega_using [hY, h]) (by omega_using [hY])]
      simp only [mask15, show k ≠ 15 by omega_using [h], ite_false]; rfl
    · rw [show Y + 4 * k = Y + 60 by omega_using [hk, h], wd_write_self, u6.gpr, u5.gpr, low15_val, u4.other .r3 (by decide),
        u3.other .r3 (by decide), u2.other .r3 (by decide), e1, show k = 15 by omega_using [hk, h]]; rfl
  · rw [hm7]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (d := Y + 60) (n := 4) (Nat.le_add_right _ _) (by omega_using []) (by omega_using [hY]))

/-- The output of `freeze` from `s0`, after `j` limbs. -/
structure OutInv (O : Addr) (r : Nat → Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  rest : Rest [.r2, .r3] s0 s
  frame : Frame [⟨O, 2 * j⟩] s0.mem s.mem
  b0 : ∀ i < j, s.mem (O + BitVec.ofNat 64 (2 * i)) = BitVec.ofNat 8 (r i)
  b1 : ∀ i < j, s.mem (O + BitVec.ofNat 64 (2 * i + 1)) = BitVec.ofNat 8 (r i / 256)

theorem out_ok {s0 : State} (hc : Ctx b s0) {o : BitVec 32} (h12 : s0.gpr .r12 = o)
    (hout : (⟨State.addr o, 32⟩ : Region) ∈ s0.wr) (hofit : o.toNat + 32 ≤ 2 ^ 32)
    (hdisj : Region.Disjoint ⟨State.addr b, 4096⟩ ⟨State.addr o, 32⟩) {sw : Nat} (hsw : sw ≤ 1)
    (h9 : s0.gpr .r9 = 0 - BitVec.ofNat 32 sw) :
    WP isa (.block ((List.range 16).flatMap outStep)) s0
      (OutInv (State.addr o) (fun k => sel sw (limb s0.mem (State.addr b) X2 k)
        (limb s0.mem (State.addr b) Y k)) s0 16) := by
  have hX : X2 = 128 := rfl
  have hY : Y = 1088 := rfl
  refine wp_range_flatMap (M := isa) _ (fun k s hk h => ?_) 16 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain hcs : Ctx b s := hc.of_rest h.rest (by decide)
  -- The words of the working space are as in `s0`.
  obtain hw : ∀ d, d + 4 ≤ 4096 → wd s.mem (State.addr b) d = wd s0.mem (State.addr b) d := fun d hd =>
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (hdisj.sub_left (Offset.sub_base _ hd)).sub_right (Region.sub_prefix (by omega_using [hk]))
  unfold outStep
  refine ldr0_ok hcs (d := X2 + 4 * k) (by omega_using [hX, hk]) fun t1 v1 => ?_
  refine ldr0_ok (hcs.of_rest (v1.rest (ws := [.r2]) (by decide)) (by decide)) (d := Y + 4 * k) (by omega_using [hY, hk])
    fun t2 v2 => ?_
  refine wp_dp (op2_reg _ _) fun t3 v3 => wp_dp (op2_reg _ _) fun t4 v4 =>
    wp_dp (op2_reg _ _) fun t5 v5 => ?_
  obtain hr5 : Rest [.r2, .r3] s t5 :=
    (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans (v5.rest (by decide)))))
  obtain e12 : t5.gpr .r12 = o := by rw [hr5.gpr _ (by decide), h.rest.gpr _ (by decide), h12]
  obtain hwr : t5.wr = s0.wr := by rw [hr5.wr, h.rest.wr]
  refine wp_strb (a := State.addr o + BitVec.ofNat 64 (2 * k)) (by omega_using [hk])
    (by rw [e12]; exact addr_add (by omega_using [hofit, hk])) (by rw [hwr]; exact in_base hout (by omega_using [hk]) (by omega_using [hk]))
    fun t6 v6 => ?_
  refine wp_mov (op2_lsr (by decide)) fun t7 v7 => ?_
  refine wp_strb (a := State.addr o + BitVec.ofNat 64 (2 * k + 1)) (by omega_using [hk])
    (by rw [v7.other _ (by decide), v6.gpr, e12]; exact addr_add (by omega_using [hofit, hk]))
    (by rw [v7.wr, v6.wr, hwr]; exact in_base hout (by omega_using [hk]) (by omega_using [hk])) fun t8 v8 => WP.block_nil ?_
  -- The limb selected.
  obtain ev : (t5.gpr .r2).toNat = sel sw (limb s0.mem (State.addr b) X2 k) (limb s0.mem (State.addr b) Y k) := by
    obtain ex : t2.gpr .r2 = s.mem.readW (State.addr b + BitVec.ofNat 64 (X2 + 4 * k)) 32 := by
      rw [v2.other _ (by decide), v1.gpr]
    obtain ey : t2.gpr .r3 = s.mem.readW (State.addr b + BitVec.ofNat 64 (Y + 4 * k)) 32 := by
      rw [v2.gpr, v1.mem]
    obtain em : t3.gpr .r9 = 0 - BitVec.ofNat 32 sw := by
      rw [v3.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide), h.rest.gpr _ (by decide), h9]
    rw [v5.gpr]
    show (t4.gpr .r2 ^^^ t4.gpr .r3).toNat = _
    rw [v4.other .r2 (by decide), v4.gpr]
    show (t3.gpr .r2 ^^^ (t3.gpr .r3 &&& t3.gpr .r9)).toNat = _
    rw [v3.other .r2 (by decide), v3.gpr, em]
    show (t2.gpr .r2 ^^^ ((t2.gpr .r3 ^^^ t2.gpr .r2) &&& _)).toNat = _
    rw [ex, ey]
    obtain hx := hw (X2 + 4 * k) (by omega_using [hX, hk])
    obtain hy := hw (Y + 4 * k) (by omega_using [hY, hk])
    unfold wd at hx hy
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
    · rw [sel0r, hx]; rfl
    · rw [sel1r, hy]; rfl
  obtain hm8 : t8.mem = (s.mem.writeW (State.addr o + BitVec.ofNat 64 (2 * k)) ((t5.gpr .r2).setWidth 8)).writeW
      (State.addr o + BitVec.ofNat 64 (2 * k + 1)) ((t5.gpr .r2 >>> 8).setWidth 8) := by
    rw [v8.mem, v7.gpr, v7.mem, v6.gpr, v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
  obtain ne : ∀ a c : Nat, a < 32 → c < 32 → a ≠ c →
      State.addr o + BitVec.ofNat 64 a ≠ State.addr o + BitVec.ofNat 64 c :=
    fun a c ha hc' hac => Offset.add_ofNat_ne _ (by omega_using [ha]) (by omega_using [hc']) hac
  refine ⟨h.rest.trans (hr5.trans ((v6.rest _).trans ((v7.rest (by decide)).trans (v8.rest _)))), ?_,
    fun i hi => ?_, fun i hi => ?_⟩
  · rw [hm8]
    refine ((h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [])⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using []) (by omega_using [hk]))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using []) (by omega_using [hk]))
  · rw [hm8, VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply,
      iteF (ne _ _ (by omega_using [hk, hi]) (by omega_using [hk]) (by omega_using []))]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [iteF (ne _ _ (by omega_arith) (by omega_using [hk]) (by omega_arith))]; exact h.b0 i hi
    · rw [iteT rfl]; exact byte_eq ev
  · rw [hm8, VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [iteF (ne _ _ (by omega_arith) (by omega_using [hk]) (by omega_arith)), iteF (ne _ _ (by omega_arith) (by omega_using [hk]) (by omega_using []))]
      exact h.b1 i hi
    · rw [iteT rfl]
      exact byte_eq (by rw [toNat_shr, ev])

theorem frame_sub1 {m m' : Mem} {r r' : Region} {rs : List Region} (h : Frame [r] m m') (hs : Region.Sub r r')
    (hr : r' ∈ rs) : Frame rs m m' :=
  h.sub fun x hx => ⟨r', hr, by rw [List.mem_singleton.mp hx]; exact hs⟩

theorem freeze_ok {s : State} (hc : Ctx b s) (hl : Lim s.mem (State.addr b) X2) {o : BitVec 32}
    (h12 : s.gpr .r12 = o) (hout : (⟨State.addr o, 32⟩ : Region) ∈ s.wr) (hofit : o.toNat + 32 ≤ 2 ^ 32)
    (hdisj : Region.Disjoint ⟨State.addr b, 4096⟩ ⟨State.addr o, 32⟩) :
    WP isa (.block freeze) s fun s' =>
      bytesAt s'.mem (State.addr o) 32 = leBytes 32 (V s.mem (State.addr b) X2 % P) ∧ Rest clob s s' ∧
      Frame [FA ACC b, ⟨State.addr o, 32⟩] s.mem s'.mem := by
  have hX : X2 = 128 := rfl
  have hY : Y = 1088 := rfl
  obtain ⟨tA, tY, hS, hR, hv⟩ := freeze_facts hl
  obtain ⟨-, -, lm, c1⟩ := mask15_facts hl
  simp only [freeze, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (freezeA_ok hc hl) fun s1 ⟨h6, h5, hl1, hf1, hr1⟩ => ?_
  obtain hc1 : Ctx b s1 := hc.of_rest hr1 (by decide)
  refine WP.append (pass_ok (rb := .r0) (o := X2) (s0 := s1) (c := mask15 (limb s.mem (State.addr b) X2))
    (cin := 19 * (limb s.mem (State.addr b) X2 15 / 32768)) (by decide) (by decide)
    (by rw [hc1.r0]; have := hc.fit; omega_using [hX, this]) (fun k hk => by rw [hc1.r0]; exact hc1.inW (by omega_using [hX, hk])) h6 h5
    (fun k hk => by have := lm k hk; omega_using [this]) (by omega_using [c1]) ?_) fun s2 hp2 => ?_
  · intro k hk s' hp
    refine WP.mono (ldSrc_ok (hc1.of_rest hp.rest (by decide)) (o := X2) (k := k) (by omega_using [hX, hk])) fun t ht => ⟨?_, ht.2.1.mono (by decide), ht.2.2⟩
    rw [ht.1, wd_pass hc1 hp.frame (by omega_using []) (by omega_using [hX, hk]) (by omega_using [hX, hk])]
    exact hl1 k hk
  obtain hc2 : Ctx b s2 := hc1.of_rest hp2.rest (by decide)
  obtain hpo2 : ∀ j < 16, wd s2.mem (State.addr b) (X2 + 4 * j) = frA (limb s.mem (State.addr b) X2) j :=
    fun j hj => by have := hp2.outs j hj; rwa [hc1.r0] at this
  obtain hpf2 : Frame [⟨State.addr b + BitVec.ofNat 64 X2, 64⟩] s1.mem s2.mem := by
    have := hp2.frame; rwa [hc1.r0] at this
  refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  obtain hc3 : Ctx b s3 := hc2.of_rest (u3.rest (ws := [.r5]) (by decide)) (by decide)
  refine WP.append (pass_ok (rb := .r0) (o := Y) (s0 := s3) (c := frA (limb s.mem (State.addr b) X2))
    (cin := 19) (by decide) (by decide)
    (by rw [hc3.r0]; have := hc.fit; omega_using [hY, this]) (fun k hk => by rw [hc3.r0]; exact hc3.inW (by omega_using [hY, hk]))
    (by rw [u3.other _ (by decide), hp2.rest.gpr _ (by decide)]; exact h6)
    (by rw [u3.gpr]; rfl) (fun k hk => by have := out_lt (mask15 (limb s.mem (State.addr b) X2)) (19 * (limb s.mem (State.addr b) X2 15 / 32768)) k; unfold frA; omega_using [this]) (by decide) ?_) fun s4 hp4 => ?_
  · intro k hk s' hp
    refine WP.mono (ldSrc_ok (hc3.of_rest hp.rest (by decide)) (o := X2) (k := k) (by omega_using [hX, hk])) fun t ht => ⟨?_, ht.2.1.mono (by decide), ht.2.2⟩
    rw [ht.1, wd_pass hc3 hp.frame (by omega_using [hX, hY, hk]) (by omega_using [hX, hk]) (by omega_using [hY, hk]), u3.mem]
    exact hpo2 k hk
  obtain hc4 : Ctx b s4 := hc3.of_rest hp4.rest (by decide)
  obtain hpo4 : ∀ j < 16, wd s4.mem (State.addr b) (Y + 4 * j) = frY (limb s.mem (State.addr b) X2) j :=
    fun j hj => by have := hp4.outs j hj; rwa [hc3.r0] at this
  obtain hpf4 : Frame [⟨State.addr b + BitVec.ofNat 64 Y, 64⟩] s3.mem s4.mem := by
    have := hp4.frame; rwa [hc3.r0] at this
  obtain hx4 : ∀ k < 16, limb s4.mem (State.addr b) X2 k = frA (limb s.mem (State.addr b) X2) k := by
    intro k hk
    rw [limb, wd_frame hpf4 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [hX, hY, hk])) (by omega_using [hX, hk]) (by omega_using [hY]),
      u3.mem, hpo2 k hk]
  refine WP.append (freezeB_ok hc4) fun s5 ⟨h9, hy5, hf5, hr5⟩ => ?_
  obtain hc5 : Ctx b s5 := hc4.of_rest hr5 (by decide)
  obtain hx5 : ∀ k < 16, limb s5.mem (State.addr b) X2 k = frA (limb s.mem (State.addr b) X2) k := by
    intro k hk
    rw [limb, wd_frame hf5 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [hX, hY, hk])) (by omega_using [hX, hk]) (by omega_using [hY])]
    exact hx4 k hk
  obtain hy5' : ∀ k < 16, limb s5.mem (State.addr b) Y k = mask15 (frY (limb s.mem (State.addr b) X2)) k := by
    intro k hk
    rw [hy5 k hk]
    simp only [mask15]
    split
    · rename_i h; subst h; rw [limb, hpo4 15 (by decide)]
    · rw [limb, hpo4 k hk]
  obtain h9' : s5.gpr .r9 = 0 - BitVec.ofNat 32 (frS (limb s.mem (State.addr b) X2)) := by
    rw [h9, limb, hpo4 15 (by decide)]; rfl
  obtain hr45 : Rest [.r1, .r2, .r3, .r4, .r5, .r6, .r9] s s5 :=
    (hr1.mono (by decide)).trans ((hp2.rest.mono (by decide)).trans ((u3.rest (by decide)).trans
      ((hp4.rest.mono (by decide)).trans (hr5.mono (by decide)))))
  refine WP.mono (out_ok hc5 (o := o) (by rw [hr45.gpr _ (by decide), h12]) (by rw [hr45.wr]; exact hout) hofit
    hdisj hS h9') fun s6 h6' => ⟨?_, ?_, ?_⟩
  · have hr : ∀ k < 16, sel (frS (limb s.mem (State.addr b) X2)) (limb s5.mem (State.addr b) X2 k)
        (limb s5.mem (State.addr b) Y k) = frR (limb s.mem (State.addr b) X2) k := fun k hk => by
      rw [hx5 k hk, hy5' k hk]; rfl
    rw [V, ← hv]
    exact bytesAt_limbs hR (fun k hk => by rw [h6'.b0 k hk, hr k hk]) (fun k hk => by rw [h6'.b1 k hk, hr k hk])
  · exact (hr45.mono (by decide)).trans (h6'.rest.mono (by decide))
  · have hfa : ∀ z, z + 64 ≤ 1280 → 64 ≤ z → Region.Sub ⟨State.addr b + BitVec.ofNat 64 z, 64⟩ (FA ACC b) :=
      fun z h1 h2 => Offset.sub _ (by omega_using [h2]) (by rw [ACC_eq]; omega_using [h1])
    refine (frame_sub1 hf1 (hfa X2 (by omega_using [hX]) (by omega_using [hX])) (List.mem_cons_self ..)).trans ?_
    refine (frame_sub1 hpf2 (hfa X2 (by omega_using [hX]) (by omega_using [hX])) (List.mem_cons_self ..)).trans ?_
    rw [← u3.mem]
    refine (frame_sub1 hpf4 (hfa Y (by omega_using [hY]) (by omega_using [hY])) (List.mem_cons_self ..)).trans ?_
    refine (frame_sub1 hf5 (hfa Y (by omega_using [hY]) (by omega_using [hY])) (List.mem_cons_self ..)).trans ?_
    exact frame_sub1 h6'.frame (Region.sub_prefix (by omega_using [])) (List.mem_cons_of_mem _ (List.mem_singleton_self _))

end

end VG.Proof.X25519.Arm

end

end


/-!
# X25519 on 32-bit ARM: the whole function

`vg_x25519` writes `X25519(k, u)` to `out` (`x25519_correct`, for any
multiplication that meets `mul_ok`'s statement, `MulOk`), restoring the
callee-saved registers.
-/

@[expose] public section

namespace VG.Proof.X25519.Arm

open VG VG.Arm VG.Impl.X25519.Arm
open VG.Spec.X25519 (P Fe bytesAt)
open VG.Proof.X25519 (leBytes toFe ladderAfter ladderAfter_swap_le)

/-- `vg_x25519(out = r0, scalar = r1, point = r2, scratch = r3)`. -/
def x25519Arm : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 32⟩
    let sc : Region := ⟨State.addr (s.gpr .r1), 32⟩
    let pt : Region := ⟨State.addr (s.gpr .r2), 32⟩
    let ws : Region := ⟨State.addr (s.gpr .r3), 4096⟩
    s.rd = [sc, pt] ∧ s.wr = [out, ws] ∧ out.Disjoint sc ∧ out.Disjoint pt ∧ out.Disjoint ws ∧
      sc.Disjoint ws ∧ pt.Disjoint ws ∧ (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 4096 ≤ 2 ^ 32
  post s s' := bytesAt s'.mem (State.addr (s.gpr .r0)) 32 =
    VG.Spec.X25519.x25519 (bytesAt s.mem (State.addr (s.gpr .r1)) 32) (bytesAt s.mem (State.addr (s.gpr .r2)) 32)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

theorem XPre.of {s : State} (h : x25519Arm.pre s) : XPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

section
variable {b : BitVec 32}

theorem lastSwap_ok {s : State} (hc : Ctx b s) {sw : Nat} (hsw : sw ≤ 1)
    (h10 : s.gpr .r10 = BitVec.ofNat 32 sw) {v : Nat → Fe} (hS : SlotsOk s.mem (State.addr b) LQ v) :
    WP isa (.block lastSwap) s fun s' => Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem (State.addr b) LQ (swapV Z2 Z3 sw (swapV X2 X3 sw v)) := by
  simp only [lastSwap, mask, List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => wp_dp (op2_reg _ _) fun s2 u2 => ?_
  obtain hr2 : Rest [.r9] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  obtain hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  obtain e9 : s2.gpr .r9 = 0 - BitVec.ofNat 32 sw := by
    rw [u2.gpr]; show s1.gpr .r9 - s1.gpr .r10 = _
    rw [u1.gpr, u1.other _ (by decide), h10]
  obtain hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  refine WP.append (cswapS (acc := ACC) (qs := LQ) (v := v) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hc2
    hsw e9 (by rw [hm2]; exact hS)) fun s3 ⟨hr3, hf3, hS3⟩ => ?_
  obtain hc3 : Ctx b s3 := hc2.of_rest hr3 (by decide)
  refine WP.mono (cswapS (acc := ACC) (qs := LQ) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hc3 hsw
    (by rw [hr3.gpr _ (by decide), e9]) hS3) fun s4 ⟨hr4, hf4, hS4⟩ =>
    ⟨⟨(hr2.mono (by decide)).trans ((hr3.mono (by decide)).trans (hr4.mono (by decide))),
      by rw [← hm2]; exact hf3.trans hf4⟩, hc3.of_rest hr4 (by decide), hS4⟩

theorem restore_ok {s : State} (hc : Ctx b s) {g : Reg → BitVec 32} (hs : Saved (State.addr b) g s.mem) :
    WP isa (.block restore) s fun s' => (∀ i < 8, s'.gpr (savedReg i) = g (savedReg i)) ∧
      Rest [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s' ∧ s'.mem = s.mem := by
  obtain hsr : ∀ i < 8, savedReg i ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] := by decide
  obtain hinj : ∀ i < 8, ∀ j < 8, savedReg i = savedReg j → i = j := by decide
  obtain h0 : ∀ i < 8, savedReg i ≠ .r0 := by decide
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.gpr (savedReg i) = g (savedReg i)) ∧
      Rest [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s' ∧ s'.mem = s.mem)
    (fun n s' hn ⟨hl, hr, hm⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Rest.refl _ _, rfl⟩) fun s' h => h
  refine ldr0_ok (hc.of_rest hr (by decide)) (d := 4 * n) (by omega_using [hn]) fun s1 u1 =>
    WP.block_nil ⟨fun i hi => ?_, hr.trans (u1.rest (hsr n hn)), by rw [u1.mem, hm]⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
  · rw [u1.other _ (fun e => absurd (hinj _ (by omega_using [hn, hi]) _ hn e) (by omega_using [h']))]; exact hl i h'
  · rw [u1.gpr, hm, hs i hn]

/-- The saved registers stay where no code writes. -/
theorem Saved.frame {g : Reg → BitVec 32} {m m' : Mem} (hs : Saved (State.addr b) g m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, ∀ i < 8, Region.Disjoint ⟨State.addr b + BitVec.ofNat 64 (4 * i), 4⟩ r) :
    Saved (State.addr b) g m' := fun i hi => by
  rw [hf.readW (Region.contains_self _ _) (fun r hr => hd r hr i hi) (by decide)]; exact hs i hi

theorem FA_saved (i : Nat) (hi : i < 8) :
    Region.Disjoint ⟨State.addr b + BitVec.ofNat 64 (4 * i), 4⟩ (FA ACC b) :=
  Offset.disjoint _ (.inl (by omega_using [hi])) (by omega_using [hi]) (by rw [ACC_eq]; omega_using [])

/-- The slots stay through a write of `BITS`. -/
theorem SlotsOk.bits {m m' : Mem} {qs : List Nat} {v : Nat → Fe} (hS : SlotsOk m (State.addr b) qs v)
    (hq : (qs.all fun q => q + 64 ≤ BITS) = true)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 BITS, 256⟩] m m') : SlotsOk m' (State.addr b) qs v := by
  intro q hq'
  obtain h := List.all_eq_true.mp hq q hq'
  simp only [decide_eq_true_eq] at h
  have hB : BITS = 1280 := rfl
  obtain e := limb_frame (o := q) hf fun r hr k hk => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [h, hk])) (by omega_using [h, hB, hk]) (by omega_using [hB])
  exact ⟨fun k hk => by rw [e k hk]; exact (hS q hq').1 k hk, by rw [FS, V, val16_congr e]; exact (hS q hq').2⟩

end

theorem bytesAt_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 32⟩ r) : bytesAt m' p 32 = bytesAt m p 32 := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  obtain hi := List.mem_range.mp hi
  exact hf _ fun r hr hc => hd r hr _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) hc

/-- `x25519With M`, for a multiplication `M`, writes `X25519(k, u)` to `out`. -/
theorem x25519_correct {M : Nat → Nat → Nat → Prog isa} (hM : MulOk ACC M) {s : State} (hp : XPre s) :
    WP isa (x25519With M) s fun s' => abiPreserved s s' ∧ x25519Arm.post s s' := by
  have hfit := hp.f3
  have hB : BITS = 1280 := rfl
  obtain hsc_in : (⟨State.addr (s.gpr .r1), 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [hp.rd]; simp
  unfold x25519With
  refine WP.seq (WP.mono (setup_ok hp) fun s1 ⟨hc1, h12, h1, hsv1, hf1, hS1, hr1⟩ => ?_)
  refine WP.seq (WP.mono (bits_ok hc1 h1 hp.f1 (by rw [hr1.rd, hr1.wr]; exact hsc_in) hp.sc_ws)
    fun s2 ⟨hc2, hr2, hf2, hb2⟩ => ?_)
  obtain hS2 := hS1.bits (by decide) hf2
  refine WP.seq (WP.mono (ladder_ok hM hc2 hb2 hS2) fun s3 ⟨hst3, hc3, h10, hS3⟩ => ?_)
  refine WP.seq (WP.mono (lastSwap_ok hc3 (ladderAfter_swap_le _ _ (by decide)) h10 hS3)
    fun s4 ⟨hst4, hc4, hS4⟩ => ?_)
  refine WP.seq (WP.mono (invert_ok hM hc4 (hS4.mono (by decide)) rfl) fun s5 ⟨hst5, hc5, hS5⟩ => ?_)
  refine WP.seq (WP.mono (mulS (acc := ACC) (o := X2) (x := X2) (y := R) (by decide) hM (by decide) (by decide)
    (by decide) (by decide) hc5 hS5)
    fun s6 ⟨hr6, hf6, hS6⟩ => ?_)
  -- The registers and regions along the way.
  obtain hst6 : Stp (s.gpr .r3) s2 s6 := hst3.trans (hst4.trans (hst5.trans ⟨hr6.mono (by decide), hf6⟩))
  obtain h12' : s6.gpr .r12 = s.gpr .r0 := by
    rw [hst6.rest.gpr _ (by decide), hr2.gpr _ (by decide), h12]
  obtain hwr6 : s6.wr = s.wr := by rw [hst6.rest.wr, hr2.wr, hr1.wr]
  obtain hc6 : Ctx (s.gpr .r3) s6 := hc5.of_rest hr6 (by decide)
  refine WP.append (freeze_ok hc6 (hS6 X2 (by decide)).1 h12' (by rw [hwr6, hp.wr]; simp) hp.f0
    hp.out_ws.symm) fun s7 ⟨hbytes, hr7, hf7⟩ => ?_
  obtain hc7 : Ctx (s.gpr .r3) s7 := hc6.of_rest hr7 (by decide)
  -- The saved registers.
  obtain hsv7 : Saved (State.addr (s.gpr .r3)) s.gpr s7.mem := by
    refine ((hsv1.frame hf2 fun r hr i hi => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [hB, hi])) (by omega_using [hi]) (by decide)).frame
      hst6.frame fun r hr i hi => by rw [List.mem_singleton.mp hr]; exact FA_saved i hi).frame hf7 fun r hr i hi => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact FA_saved i hi
    · exact (hp.out_ws.symm.sub_left (Offset.sub_base _ (by omega_using [hi]))).symm.symm
  refine WP.mono (restore_ok hc7 hsv7) fun s8 ⟨hg8, hr8, hm8⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg8 0 (by decide)
    · exact hg8 1 (by decide)
    · exact hg8 2 (by decide)
    · exact hg8 3 (by decide)
    · exact hg8 4 (by decide)
    · exact hg8 5 (by decide)
    · exact hg8 6 (by decide)
    · exact hg8 7 (by decide)
    · rw [hr8.gpr _ (by decide), hr7.gpr _ (by decide), hst6.rest.gpr _ (by decide), hr2.gpr _ (by decide),
        hr1.gpr _ (by decide)]
  · rw [hr8.sp, hr7.sp, hst6.rest.sp, hr2.sp, hr1.sp]
  · -- The result.
    show bytesAt s8.mem _ 32 = _
    rw [hm8, hbytes, VG.Proof.X25519.x25519_eq]
    -- The scalar and the u-coordinate, as read by `bits` and `setup`.
    obtain hk : bytesAt s1.mem (State.addr (s.gpr .r1)) 32 = bytesAt s.mem (State.addr (s.gpr .r1)) 32 :=
      bytesAt_frame hf1 fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.sc_ws
    rw [hk] at hS3 h10 hS4 hS5 hS6
    obtain e6 : FS s6.mem (State.addr (s.gpr .r3)) X2 = _ := (hS6 X2 (by decide)).2
    rw [← VG.Proof.X25519.toFe_val, ← VG.Proof.X25519.encodeUCoordinate_eq]
    change VG.Spec.X25519.encodeUCoordinate (FS s6.mem (State.addr (s.gpr .r3)) X2) = _
    rw [e6]
    simp only [upd, swapV, ladV, sel, iteT, VG.Proof.X25519.invert_eq, VG.Proof.X25519.pow_pw, cswap_fst,
      uOf, X1, X2, Z2, X3, Z3, R, Nat.reduceEqDiff, ite_false]

end VG.Proof.X25519.Arm

end

end


/-!
# X25519 on 32-bit ARM: verified

`vg_x25519` meets the shared contract of `Spec/X25519/Contract.lean`: the
proof against `x25519Arm`, which it implies, and a state satisfying it.
-/

@[expose] public section

namespace VG.Proof.X25519.Arm

open VG VG.Arm

theorem x25519_ok (s : State) (hs : x25519Arm.pre s) :
    ∃ t s', Exec isa Impl.X25519.Arm.x25519 s t s' ∧ abiPreserved s s' ∧ x25519Arm.post s s' :=
  x25519_correct (mulAt_mulOk (by decide)) (XPre.of hs)

theorem x25519_ct' : ConstantTime isa x25519Arm.pre x25519Arm.pub Impl.X25519.Arm.x25519 :=
  x25519_ct fun _ _ _ _ ⟨_, h0, h1, h2, h3⟩ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition. -/
def x25519Sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x10000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 4096⟩]

theorem x25519_verified :
    Verified Arm.target Impl.X25519.Arm.x25519 (Proof.X25519.x25519Contract Arm.abi) :=
  Verified.of_correct x25519_ok x25519_ct' (by
    sig_implies [Proof.X25519.x25519Contract, Proof.X25519.x25519Sig, Proof.X25519.Arm.x25519Arm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [Proof.X25519.Arm.x25519Sat,
      Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.X25519.Arm.x25519Sat)

end VG.Proof.X25519.Arm
