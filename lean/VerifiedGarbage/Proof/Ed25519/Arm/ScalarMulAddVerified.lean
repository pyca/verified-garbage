import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Impl.Ed25519.Arm.Scalar
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseVerified
import VerifiedGarbage.Proof.X25519.Arm.Verified
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Impl.Ed25519.Arm.ScalarMulAdd
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseVerified
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.ScalarPass`. -/
section

/-! Merged from `Proof.Ed25519.Arm.ScalarNat`. -/
section
/-! Radix-65536 arithmetic for subgroup-order reduction. -/
namespace VG.Proof.Ed25519.Arm
open VG.Proof.X25519.Arm VG.Spec.Ed25519 VG.Impl.Ed25519.Arm

theorem scalarComplement_lt (k : Nat) : scalarComplement k < 65536 := by
  unfold scalarComplement; omega

theorem scalarComplement_val : val16 scalarComplement 16 + L + 1 = 2 ^ 256 := by decide

theorem scalarDouble_val {f : Nat → Nat} {bit : Nat}
    (hf : val16 f 16 < L) (hb : bit < 2) :
    val16 (VG.Proof.X25519.Arm.out (fun k => 2 * f k) bit) 16 = 2 * val16 f 16 + bit := by
  have h := chain_val (fun k => 2 * f k) bit 16
  rw [val16_cmul] at h
  have bound := order_bound
  have hc : chain (fun k => 2 * f k) bit 16 = 0 := by
    rcases Nat.eq_zero_or_pos (chain (fun k => 2 * f k) bit 16) with hz | hp
    · exact hz
    · have := Nat.le_mul_of_pos_right (2 ^ 256) hp
      change _ + 2 ^ 256 * _ = _ at h
      omega
  rw [hc, Nat.mul_zero, Nat.add_zero] at h
  exact h

theorem scalarSubtract_facts {f : Nat → Nat} (hf : val16 f 16 < 2 * L) :
    chain (fun k => f k + scalarComplement k) 1 16 ≤ 1 ∧
    val16 (fun k => sel (chain (fun j => f j + scalarComplement j) 1 16)
      (f k) (VG.Proof.X25519.Arm.out (fun j => f j + scalarComplement j) 1 k)) 16 = val16 f 16 % L := by
  have hv := chain_val (fun k => f k + scalarComplement k) 1 16
  rw [val16_add] at hv
  have hc := VG.Proof.Ed25519.Arm.scalarComplement_val
  have hL := order_pos
  have hB := order_bound
  have hout := val16_lt (f := VG.Proof.X25519.Arm.out (fun k => f k + scalarComplement k) 1) (n := 16)
    fun _ _ => out_lt _ _ _
  have hcarry : chain (fun k => f k + scalarComplement k) 1 16 ≤ 1 := by
    have : 2 ^ 256 * chain (fun k => f k + scalarComplement k) 1 16 < 2 ^ 256 * 2 := by omega
    exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_left this)
  refine ⟨hcarry, ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcarry with hz | ho
  · have he : val16 (fun k => sel (chain (fun j => f j + scalarComplement j) 1 16)
        (f k) (VG.Proof.X25519.Arm.out (fun j => f j + scalarComplement j) 1 k)) 16 = val16 f 16 :=
      val16_congr fun _ _ => by rw [hz]; rfl
    rw [he, Nat.mod_eq_of_lt (by rw [hz] at hv; omega)]
  · have he : val16 (fun k => sel (chain (fun j => f j + scalarComplement j) 1 16)
        (f k) (VG.Proof.X25519.Arm.out (fun j => f j + scalarComplement j) 1 k)) 16 =
        val16 (VG.Proof.X25519.Arm.out (fun j => f j + scalarComplement j) 1) 16 :=
      val16_congr fun _ _ => by rw [ho]; rfl
    rw [he]
    have heq : val16 f 16 = val16 (VG.Proof.X25519.Arm.out (fun j => f j + scalarComplement j) 1) 16 + L := by
      rw [ho] at hv; omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem scalarCompare_carry {f : Nat → Nat} (hf : val16 f 16 < 2 ^ 256) :
    chain (fun k => f k + scalarComplement k) 1 16 = if val16 f 16 < L then 0 else 1 := by
  have hv := chain_val (fun k => f k + scalarComplement k) 1 16
  rw [val16_add] at hv
  have hc := VG.Proof.Ed25519.Arm.scalarComplement_val
  have hl := order_pos
  have hout := val16_lt (f := VG.Proof.X25519.Arm.out (fun k => f k + scalarComplement k) 1) (n := 16)
    fun _ _ => out_lt _ _ _
  split <;> omega

/-- Consume the low n bits of a word, in descending order. -/
def scalarConsumeBits (v n r : Nat) : Nat :=
  (List.range n).reverse.foldl (fun a j => (2 * a + v / 2 ^ j % 2) % L) r

theorem scalarConsumeBits_succ (v n r : Nat) :
    VG.Proof.Ed25519.Arm.scalarConsumeBits v (n + 1) r = VG.Proof.Ed25519.Arm.scalarConsumeBits v n ((2 * r + v / 2 ^ n % 2) % L) := by
  simp only [VG.Proof.Ed25519.Arm.scalarConsumeBits, List.range_succ, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem scalarConsumeBits_eq (v n r : Nat) (hr : r < L) :
    VG.Proof.Ed25519.Arm.scalarConsumeBits v n r = (2 ^ n * r + v % 2 ^ n) % L := by
  induction n generalizing r with
  | zero => simp only [VG.Proof.Ed25519.Arm.scalarConsumeBits, List.range_zero, List.reverse_nil, List.foldl_nil,
      Nat.pow_zero, Nat.one_mul, Nat.mod_one, Nat.add_zero, Nat.mod_eq_of_lt hr]
  | succ n ih =>
    rw [VG.Proof.Ed25519.Arm.scalarConsumeBits_succ, ih _ (Nat.mod_lt _ order_pos)]
    have hmod (a x z : Nat) : (a * (x % L) + z) % L = (a * x + z) % L := by
      rw [Nat.add_mod, Nat.mul_mod_mod, ← Nat.add_mod]
    rw [hmod, Nat.pow_succ, Nat.mod_mul]
    simp only [Nat.mul_add, Nat.mul_assoc]
    congr 1
    omega

end VG.Proof.Ed25519.Arm
end

/-! Carry passes for doubling a remainder and subtracting the subgroup order. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

variable {b : BitVec 32}

theorem scalarDoublePass_ok {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : Lim s.mem (State.addr b) SR)
    {bit : Nat} (hb : bit < 2) (h5 : (s.gpr .r5).toNat = bit) (h6 : s.gpr .r6 = mask16) :
    WP isa (.block (pass .r0 SR scalarDoubleSrc)) s
      (PassInv .r0 SR s (fun k => 2 * limb s.mem (State.addr b) SR k) bit 16) := by
  have hR : SR = 256 := rfl
  refine pass_ok (by decide) (by decide) (by rw [hc.r0]; have := hc.fit; omega)
    (fun k hk => by rw [hc.r0]; exact hc.inW (by omega)) h6 h5
    (fun k hk => by have := hl k hk; omega) (by omega) ?_
  intro k hk t ht
  have hct := hc.of_rest ht.rest (by decide)
  unfold scalarDoubleSrc
  refine ldr0_ok hct (by omega) fun u hu => wp_dp (op2_reg _ _) fun v hv => WP.block_nil ?_
  have he : (u.gpr .r3).toNat = limb s.mem (State.addr b) SR k := by
    rw [hu.gpr]
    exact wd_frame ht.frame fun r hr => by
      rw [List.mem_singleton.mp hr, hc.r0]
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  refine ⟨?_, (hu.rest (by decide)).trans (hv.rest (by decide)), by rw [hv.mem, hu.mem]⟩
  rw [hv.gpr]
  show (u.gpr .r3 + u.gpr .r3).toNat = _
  rw [toNat_add_lt (by rw [he]; have := hl k hk; omega), he]
  omega

theorem scalarSubtractPass_ok {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : Lim s.mem (State.addr b) SR)
    (h5 : (s.gpr .r5).toNat = 1) (h6 : s.gpr .r6 = mask16) :
    WP isa (.block (pass .r0 SD scalarSubtractSrc)) s
      (PassInv .r0 SD s (fun k => limb s.mem (State.addr b) SR k + scalarComplement k) 1 16) := by
  have hR : SR = 256 := rfl
  have hT : SD = 320 := rfl
  refine pass_ok (by decide) (by decide) (by rw [hc.r0]; have := hc.fit; omega)
    (fun k hk => by rw [hc.r0]; exact hc.inW (by omega)) h6 h5
    (fun k hk => by have := hl k hk; have := VG.Proof.Ed25519.Arm.scalarComplement_lt k; omega) (by decide) ?_
  intro k hk t ht
  have hct := hc.of_rest ht.rest (by decide)
  unfold scalarSubtractSrc
  refine ldr0_ok hct (by omega) fun u hu => wp_movw fun v hv =>
    wp_dp (op2_reg _ _) fun w hw => WP.block_nil ?_
  have he : (u.gpr .r3).toNat = limb s.mem (State.addr b) SR k := by
    rw [hu.gpr]
    exact wd_frame ht.frame fun r hr => by
      rw [List.mem_singleton.mp hr, hc.r0]
      exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  have hc2 : (v.gpr .r2).toNat = scalarComplement k := by
    rw [hv.gpr, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (VG.Proof.Ed25519.Arm.scalarComplement_lt k)]
    exact Nat.mod_eq_of_lt (by have := VG.Proof.Ed25519.Arm.scalarComplement_lt k; omega)
  refine ⟨?_, (hu.rest (by decide)).trans ((hv.rest (by decide)).trans (hw.rest (by decide))), by
    rw [hw.mem, hv.mem, hu.mem]⟩
  rw [hw.gpr]
  show (v.gpr .r3 + v.gpr .r2).toNat = _
  rw [hv.other .r3 (by decide), toNat_add_lt (by rw [he, hc2]; have := hl k hk; have := VG.Proof.Ed25519.Arm.scalarComplement_lt k; omega), he, hc2]

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.ScalarLoop`. -/
section

/-! Merged from `Proof.Ed25519.Arm.ScalarByte`. -/
section
/-! Merged from `Proof.Ed25519.Arm.ScalarStep`. -/
section
/-! One fixed binary-reduction step modulo L. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Spec.Ed25519 (L)

abbrev scalarClob : List Reg := [.r2, .r3, .r4, .r5, .r6, .r9]
def scalarRegions (b : BitVec 32) : List Region :=
  [⟨State.addr b + BitVec.ofNat 64 SR, 64⟩, ⟨State.addr b + BitVec.ofNat 64 SD, 64⟩]

structure ScalarKeep (b : BitVec 32) (s t : State) : Prop where
  rest : Rest VG.Proof.Ed25519.Arm.scalarClob s t
  frame : Frame (VG.Proof.Ed25519.Arm.scalarRegions b) s.mem t.mem

theorem ScalarKeep.ctx {b : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.Arm.ScalarKeep b s t) (hc : VG.Proof.Ed25519.Arm.Ctx b s) : VG.Proof.Ed25519.Arm.Ctx b t :=
  hc.of_rest h.rest (by decide)

theorem ScalarKeep.trans {b : BitVec 32} {s t u : State} (h : VG.Proof.Ed25519.Arm.ScalarKeep b s t)
    (h' : VG.Proof.Ed25519.Arm.ScalarKeep b t u) : VG.Proof.Ed25519.Arm.ScalarKeep b s u := ⟨h.rest.trans h'.rest, h.frame.trans h'.frame⟩

theorem scalarBitSource_eval {s : State} {j : Nat} (hj : j < 8) :
    (scalarBitSource j).eval s = some (s.gpr .r11 >>> j) := by
  unfold scalarBitSource
  by_cases hz : j = 0
  · subst hz; simp only [ite_true, BitVec.ushiftRight_zero]; rfl
  · rw [ite_eq_right_iff.mpr (fun h => False.elim (hz h))]
    exact op2_lsr (by omega)

theorem scalarBitHead_ok {s : State} {j : Nat} (hj : j < 8) :
    WP isa (.block [.mov .r5 (scalarBitSource j), .dp .and .r5 .r5 (.imm 1), .movw .r6 65535]) s
      fun t => (t.gpr .r5).toNat = (s.gpr .r11).toNat / 2 ^ j % 2 ∧
        t.gpr .r6 = mask16 ∧ Rest [.r5, .r6] s t ∧ t.mem = s.mem := by
  refine wp_mov (VG.Proof.Ed25519.Arm.scalarBitSource_eval hj) fun u hu => wp_dp (op2_imm (by decide)) fun v hv =>
    wp_movw fun w hw => WP.block_nil ⟨?_, hw.gpr, ?_, by rw [hw.mem, hv.mem, hu.mem]⟩
  · rw [hw.other _ (by decide), hv.gpr]
    show (u.gpr .r5 &&& (1 : BitVec 32)).toNat = _
    rw [hu.gpr, BitVec.toNat_and, toNat_shr]
    exact Nat.and_two_pow_sub_one_eq_mod _ 1
  · exact (hu.rest (by decide)).trans ((hv.rest (by decide)).trans (hw.rest (by decide)))

theorem scalarBit_ok {b : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) {j : Nat} (hj : j < 8)
    (hl : Lim s.mem (State.addr b) SR) (hr : V s.mem (State.addr b) SR < L) :
    WP isa (.block (VG.Impl.Ed25519.Arm.scalarBit j)) s fun t => VG.Proof.Ed25519.Arm.ScalarKeep b s t ∧
      Lim t.mem (State.addr b) SR ∧
      V t.mem (State.addr b) SR =
        (2 * V s.mem (State.addr b) SR + (s.gpr .r11).toNat / 2 ^ j % 2) % L := by
  let bit := (s.gpr .r11).toNat / 2 ^ j % 2
  have hb : bit < 2 := Nat.mod_lt _ (by decide)
  have hR : SR = 256 := rfl
  have hD : SD = 320 := rfl
  rw [VG.Impl.Ed25519.Arm.scalarBit, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
  refine WP.append (VG.Proof.Ed25519.Arm.scalarBitHead_ok hj) fun s1 ⟨h5, h6, k1, m1⟩ => ?_
  have hc1 := hc.of_rest k1 (by decide)
  refine WP.append (VG.Proof.Ed25519.Arm.scalarDoublePass_ok hc1 (m1 ▸ hl) hb h5 h6) fun s2 h2 => ?_
  have hc2 := hc1.of_rest h2.rest (by decide)
  have f2 : Frame [⟨State.addr b + BitVec.ofNat 64 SR, 64⟩] s.mem s2.mem := by
    have hf := h2.frame; rw [hc1.r0, m1] at hf; exact hf
  have l2 : Lim s2.mem (State.addr b) SR := by
    intro k hk; have he := h2.outs k hk; rw [hc1.r0] at he
    rw [limb, he]; exact out_lt _ _ _
  have v2 : V s2.mem (State.addr b) SR = 2 * V s.mem (State.addr b) SR + bit := by
    have he : ∀ k < 16, limb s2.mem (State.addr b) SR k =
        VG.Proof.X25519.Arm.out (fun k => 2 * limb s.mem (State.addr b) SR k) bit k := by
      intro k hk
      have he := h2.outs k hk
      rwa [hc1.r0, m1] at he
    exact (val16_congr he).trans (VG.Proof.Ed25519.Arm.scalarDouble_val hr hb)
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  have k3 : Rest [.r2, .r3, .r4, .r5, .r6] s s3 :=
    (k1.mono (by decide)).trans ((h2.rest.mono (by decide)).trans (u3.rest (by decide)))
  have hc3 := hc.of_rest k3 (by decide)
  refine WP.append (VG.Proof.Ed25519.Arm.scalarSubtractPass_ok hc3 (u3.mem ▸ l2) (by rw [u3.gpr]; rfl)
    (by rw [u3.other _ (by decide), h2.rest.gpr _ (by decide), h6])) fun s4 h4 => ?_
  have subf := VG.Proof.Ed25519.Arm.scalarSubtract_facts (f := limb s3.mem (State.addr b) SR)
    (by change V s3.mem (State.addr b) SR < _; rw [u3.mem, v2]; omega)
  have hc4 := hc3.of_rest h4.rest (by decide)
  have f4 : Frame [⟨State.addr b + BitVec.ofNat 64 SD, 64⟩] s3.mem s4.mem := by
    have hf := h4.frame; rwa [hc3.r0] at hf
  have lr4 : ∀ k < 16, limb s4.mem (State.addr b) SR k = limb s3.mem (State.addr b) SR k :=
    limb_frame f4 fun r hr k hk => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  have ld4 : ∀ k < 16, limb s4.mem (State.addr b) SD k =
      VG.Proof.X25519.Arm.out (fun k => limb s3.mem (State.addr b) SR k + scalarComplement k) 1 k := by
    intro k hk; have he := h4.outs k hk; rwa [hc3.r0] at he
  refine wp_mov (op2_imm (by decide)) fun s5 u5 => wp_dp (op2_reg _ _) fun s6 u6 => ?_
  have k6 : Rest VG.Proof.Ed25519.Arm.scalarClob s s6 := (k3.mono (by decide)).trans
    ((h4.rest.mono (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))
  have m6 : s6.mem = s4.mem := by rw [u6.mem, u5.mem]
  have mask6 : s6.gpr .r9 = 0 - BitVec.ofNat 32
      (chain (fun k => limb s3.mem (State.addr b) SR k + scalarComplement k) 1 16) := by
    rw [u6.gpr]
    show s5.gpr .r9 - s5.gpr .r5 = _
    rw [u5.gpr, u5.other _ (by decide)]
    apply congrArg (fun x : BitVec 32 => 0 - x)
    apply BitVec.eq_of_toNat_eq
    rw [toNat_imm (by have := subf.1; omega), h4.r5]
  refine WP.mono (cswap_ok (by decide) (by decide) (Or.inl (by decide))
    (hc.of_rest k6 (by decide)) subf.1 mask6) fun t ht => ?_
  have ltout : ∀ k < 16, limb t.mem (State.addr b) SR k =
      sel (chain (fun j => limb s3.mem (State.addr b) SR j + scalarComplement j) 1 16)
        (limb s3.mem (State.addr b) SR k)
        (VG.Proof.X25519.Arm.out (fun j => limb s3.mem (State.addr b) SR j + scalarComplement j) 1 k) := by
    intro k hk
    rw [ht.lx k hk, m6, lr4 k hk, ld4 k hk]
  refine ⟨⟨k6.trans (ht.rest.mono (by decide)), ?_⟩, ?_, ?_⟩
  · have fa : Frame (VG.Proof.Ed25519.Arm.scalarRegions b) s.mem s2.mem := f2.mono fun r hr => by
      simp only [VG.Proof.Ed25519.Arm.scalarRegions, List.mem_cons, List.mem_singleton.mp hr, true_or]
    have fb : Frame (VG.Proof.Ed25519.Arm.scalarRegions b) s2.mem s4.mem := by
      rw [← u3.mem]; exact f4.mono fun r hr => by
        exact List.mem_cons_of_mem _ hr
    have fc : Frame (VG.Proof.Ed25519.Arm.scalarRegions b) s4.mem t.mem := by rw [← m6]; exact ht.frame
    exact (fa.trans fb).trans fc
  · intro k hk
    rw [ltout k hk]; unfold sel
    split
    · exact out_lt _ _ _
    · rw [u3.mem]; exact l2 k hk
  · unfold V
    rw [val16_congr ltout, subf.2]
    change V s3.mem (State.addr b) SR % L = _
    rw [u3.mem, v2]
    rfl

end VG.Proof.Ed25519.Arm
end

/-! Eight reduction steps consume a byte from high bit to low bit. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Spec.Ed25519 (L)

theorem scalarBits_ok {b : BitVec 32} (js : List Nat) (hj : ∀ j ∈ js, j < 8)
    {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) (hl : Lim s.mem (State.addr b) SR)
    (hr : V s.mem (State.addr b) SR < L) :
    WP isa (.block (js.flatMap VG.Impl.Ed25519.Arm.scalarBit)) s fun t => VG.Proof.Ed25519.Arm.ScalarKeep b s t ∧
      Lim t.mem (State.addr b) SR ∧ V t.mem (State.addr b) SR =
        js.foldl (fun v j => (2 * v + (s.gpr .r11).toNat / 2 ^ j % 2) % L)
          (V s.mem (State.addr b) SR) := by
  induction js generalizing s with
  | nil => exact WP.block_nil ⟨⟨Rest.refl _ _, Frame.refl _ _⟩, hl, rfl⟩
  | cons j js ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed25519.Arm.scalarBit_ok hc (hj j (by simp)) hl hr) fun t ⟨kt, lt, vt⟩ => ?_
    refine WP.mono (ih (fun i hi => hj i (List.mem_cons_of_mem _ hi)) (kt.ctx hc) lt
      (by rw [vt]; exact Nat.mod_lt _ order_pos)) fun u ⟨ku, lu, vu⟩ => ?_
    refine ⟨kt.trans ku, lu, ?_⟩
    rw [vu, kt.rest.gpr .r11 (by decide), vt]
    rfl

theorem scalarEight_ok {b : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s)
    (hl : Lim s.mem (State.addr b) SR) (hr : V s.mem (State.addr b) SR < L)
    (hb : (s.gpr .r11).toNat < 256) :
    WP isa (.block ((List.range 8).reverse.flatMap VG.Impl.Ed25519.Arm.scalarBit)) s fun t =>
      VG.Proof.Ed25519.Arm.ScalarKeep b s t ∧ Lim t.mem (State.addr b) SR ∧
      V t.mem (State.addr b) SR = (256 * V s.mem (State.addr b) SR + (s.gpr .r11).toNat) % L := by
  refine WP.mono (VG.Proof.Ed25519.Arm.scalarBits_ok _ (by intro j hj; simpa only [List.mem_reverse, List.mem_range] using hj)
    hc hl hr) fun t ⟨kt, lt, vt⟩ => ?_
  change V t.mem (State.addr b) SR = VG.Proof.Ed25519.Arm.scalarConsumeBits _ 8 _ at vt
  rw [VG.Proof.Ed25519.Arm.scalarConsumeBits_eq _ _ _ hr, show 2 ^ 8 = 256 from rfl, Nat.mod_eq_of_lt hb] at vt
  exact ⟨kt, lt, vt⟩

theorem scalarRead_ok {s : State} {p : BitVec 32} {n : Nat} (hn : n < 64)
    (hp : s.gpr .r12 = p) (hfit : p.toNat + 64 ≤ 2 ^ 32)
    (h10 : s.gpr .r10 = BitVec.ofNat 32 (n + 1))
    (hr : InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 n) 1) :
    WP isa (.block scalarRead) s fun t =>
      Rest [.r2, .r10, .r11] s t ∧ t.mem = s.mem ∧
      t.gpr .r10 = BitVec.ofNat 32 n ∧
      (t.gpr .r11).toNat = (s.mem (State.addr p + BitVec.ofNat 64 n)).toNat := by
  unfold scalarRead
  refine wp_dp (op2_imm (by decide)) fun u hu => wp_dp (op2_reg _ _) fun v hv => ?_
  have he : u.gpr .r10 = BitVec.ofNat 32 n := by
    rw [hu.gpr]
    change s.gpr .r10 - BitVec.ofNat 32 1 = _
    rw [h10, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have hpv : v.gpr .r2 = p + BitVec.ofNat 32 n := by
    rw [hv.gpr]; change u.gpr .r12 + u.gpr .r10 = _
    rw [hu.other _ (by decide), hp, he]
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 n) (by decide)
    (by rw [hpv, BitVec.add_zero]; exact addr_add (by omega))
    (by rw [hv.rd, hv.wr, hu.rd, hu.wr]; exact hr) fun w hw => WP.block_nil ?_
  refine ⟨(hu.rest (by decide)).trans ((hv.rest (by decide)).trans (hw.rest (by decide))),
    by rw [hw.mem, hv.mem, hu.mem], by rw [hw.other _ (by decide), hv.other _ (by decide), he], ?_⟩
  rw [hw.gpr, BitVec.toNat_setWidth_of_le (by decide), hv.mem, hu.mem]

abbrev scalarBodyClob : List Reg := [.r2, .r3, .r4, .r5, .r6, .r9, .r10, .r11]

structure ScalarBodyKeep (b : BitVec 32) (s t : State) : Prop where
  rest : Rest VG.Proof.Ed25519.Arm.scalarBodyClob s t
  frame : Frame (VG.Proof.Ed25519.Arm.scalarRegions b) s.mem t.mem

theorem ScalarBodyKeep.ctx {b : BitVec 32} {s t : State} (h : VG.Proof.Ed25519.Arm.ScalarBodyKeep b s t)
    (hc : VG.Proof.Ed25519.Arm.Ctx b s) : VG.Proof.Ed25519.Arm.Ctx b t := hc.of_rest h.rest (by decide)

theorem ScalarBodyKeep.trans {b : BitVec 32} {s t u : State} (h : VG.Proof.Ed25519.Arm.ScalarBodyKeep b s t)
    (h' : VG.Proof.Ed25519.Arm.ScalarBodyKeep b t u) : VG.Proof.Ed25519.Arm.ScalarBodyKeep b s u :=
  ⟨h.rest.trans h'.rest, h.frame.trans h'.frame⟩

theorem scalarByte_ok {b p : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s)
    {n : Nat} (hn : n < 64) (hp : s.gpr .r12 = p) (hfit : p.toNat + 64 ≤ 2 ^ 32)
    (h10 : s.gpr .r10 = BitVec.ofNat 32 (n + 1))
    (hread : InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 n) 1)
    (hl : Lim s.mem (State.addr b) SR) (hr : V s.mem (State.addr b) SR < L) :
    WP isa (.block scalarByte) s fun t =>
      VG.Proof.Ed25519.Arm.ScalarBodyKeep b s t ∧ Lim t.mem (State.addr b) SR ∧
      V t.mem (State.addr b) SR =
        (256 * V s.mem (State.addr b) SR + (s.mem (State.addr p + BitVec.ofNat 64 n)).toNat) % L ∧
      t.gpr .r10 = BitVec.ofNat 32 n ∧ t.z = decide (n = 0) := by
  rw [scalarByte, List.append_assoc]
  refine WP.append (VG.Proof.Ed25519.Arm.scalarRead_ok hn hp hfit h10 hread) fun u ⟨ku, mu, eu, bu⟩ => ?_
  have hcu := hc.of_rest ku (by decide)
  refine WP.append (VG.Proof.Ed25519.Arm.scalarEight_ok hcu (mu ▸ hl) (mu ▸ hr) (by rw [bu]; exact BitVec.isLt _))
    fun v ⟨kv, lv, vv⟩ => ?_
  refine wp_cmp (op2_imm (by decide)) fun w hw hz => WP.block_nil ?_
  have ev : v.gpr .r10 = BitVec.ofNat 32 n := (kv.rest.gpr _ (by decide)).trans eu
  refine ⟨⟨(ku.mono (by decide)).trans ((kv.rest.mono (by decide)).trans (hw.rest _)), ?_⟩,
    hw.mem ▸ lv, ?_, by rw [hw.gpr, ev], ?_⟩
  · rw [hw.mem, ← mu]; exact kv.frame
  · rw [hw.mem, vv, mu, bu]
  · rw [hz, ev]
    have he : BitVec.ofNat 32 n - (0 : BitVec 32) = BitVec.ofNat 32 n := BitVec.sub_zero _
    rw [he, ofNat_beq_zero (by omega)]

end VG.Proof.Ed25519.Arm
end

/-! The fixed 64-byte reduction loop, with an exact suffix invariant. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Spec.Ed25519 (L bytesAt decodeLE)

theorem scalar_bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (VG.Spec.Ed25519.bytesAt m p n).length = n := by
  simp only [VG.Spec.Ed25519.bytesAt, List.length_map, List.length_range]

theorem scalar_suffix_step (m : Mem) (p : Addr) (n : Nat) (hn : n < 64) :
    decodeLE ((VG.Spec.Ed25519.bytesAt m p 64).drop n) % L =
      (256 * (decodeLE ((VG.Spec.Ed25519.bytesAt m p 64).drop (n + 1)) % L) +
        (m (p + BitVec.ofNat 64 n)).toNat) % L := by
  rw [List.drop_eq_getElem_cons (by rw [VG.Proof.Ed25519.Arm.scalar_bytesAt_length]; exact hn), reduce_cons]
  simp only [VG.Spec.Ed25519.bytesAt, List.getElem_map, List.getElem_range]

structure ScalarInv (b : BitVec 32) (p : Addr) (s0 : State) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 64
  counter : s.gpr .r10 = BitVec.ofNat 32 n
  limbs : Lim s.mem (State.addr b) SR
  value : V s.mem (State.addr b) SR = decodeLE ((VG.Spec.Ed25519.bytesAt s0.mem p 64).drop n) % L
  keeps : VG.Proof.Ed25519.Arm.ScalarBodyKeep b s0 s

theorem scalarLoop_ok {b p : BitVec 32} {s0 : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s0)
    (hp : s0.gpr .r12 = p) (hfit : p.toNat + 64 ≤ 2 ^ 32)
    (hread : ∀ n < 64, InRegions (s0.rd ++ s0.wr) (State.addr p + BitVec.ofNat 64 n) 1)
    (hsep : ∀ r ∈ VG.Proof.Ed25519.Arm.scalarRegions b, (⟨State.addr p, 64⟩ : Region).Disjoint r)
    (h10 : s0.gpr .r10 = 64) (hl : Lim s0.mem (State.addr b) SR)
    (hz : V s0.mem (State.addr b) SR = 0) :
    WP isa (.loop (.block scalarByte) .ne) s0 fun t => VG.Proof.Ed25519.Arm.ScalarBodyKeep b s0 t ∧
      Lim t.mem (State.addr b) SR ∧
      V t.mem (State.addr b) SR = decodeLE (VG.Spec.Ed25519.bytesAt s0.mem (State.addr p) 64) % L := by
  apply WP.loop (VG.Proof.Ed25519.Arm.ScalarInv b (State.addr p) s0) (n := 64)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega : n ≠ 0)
    have hk : k < 64 := by have := hi.bound; omega
    have hps : s.gpr .r12 = p := (hi.keeps.rest.gpr _ (by decide)).trans hp
    have hrs : InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 k) 1 := by
      rw [hi.keeps.rest.rd, hi.keeps.rest.wr]; exact hread k hk
    refine WP.mono (VG.Proof.Ed25519.Arm.scalarByte_ok (hi.keeps.ctx hc) hk hps hfit hi.counter hrs hi.limbs
      (by rw [hi.value]; exact Nat.mod_lt _ order_pos)) fun t ⟨kt, lt, vt, et, zt⟩ => ?_
    have km := hi.keeps.trans kt
    have mb : s.mem (State.addr p + BitVec.ofNat 64 k) = s0.mem (State.addr p + BitVec.ofNat 64 k) :=
      hi.keeps.frame.bytes hsep (by decide : 64 ≤ 2 ^ 64) hk
    have val : V t.mem (State.addr b) SR = decodeLE ((VG.Spec.Ed25519.bytesAt s0.mem (State.addr p) 64).drop k) % L := by
      rw [vt, hi.value, mb, VG.Proof.Ed25519.Arm.scalar_suffix_step _ _ _ hk]
    by_cases hk0 : k = 0
    · subst hk0
      refine .inl ⟨by rw [eval_ne, zt]; rfl, km, lt, ?_⟩
      simpa only [List.drop_zero] using val
    · refine .inr ⟨by rw [eval_ne, zt]; simp only [hk0, decide_false, Bool.not_false],
        k, by omega, ?_⟩
      exact ⟨by omega, by omega, et, lt, val, km⟩
  · refine ⟨by decide, by decide, h10, hl, ?_, ⟨Rest.refl _ _, Frame.refl _ _⟩⟩
    rw [hz, List.drop_eq_nil_of_le (by rw [VG.Proof.Ed25519.Arm.scalar_bytesAt_length])]
    rfl

theorem scalarInit_ok {b : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s) :
    WP isa (.block scalarInit) s fun t => VG.Proof.Ed25519.Arm.ScalarBodyKeep b s t ∧
      t.gpr .r10 = 64 ∧ Lim t.mem (State.addr b) SR ∧ V t.mem (State.addr b) SR = 0 := by
  rw [scalarInit, List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun u hu => ?_
  refine WP.append (VG.Proof.Ed25519.Arm.stores_ok (by decide) (hc.of_rest (hu.rest (ws := [.r3]) (by decide)) (by decide)))
    fun v ⟨out, frame, _, kv⟩ => ?_
  refine wp_mov (op2_imm (by decide)) fun t ht => WP.block_nil ?_
  have he : ∀ k < 16, limb t.mem (State.addr b) SR k = 0 := by
    intro k hk; rw [ht.mem]; have h := out k hk; rw [hu.gpr] at h; exact h
  refine ⟨⟨(hu.rest (by decide)).trans ((kv.mono (by decide)).trans (ht.rest (by decide))), ?_⟩,
    ht.gpr, fun k hk => by rw [he k hk]; decide, ?_⟩
  · rw [ht.mem, ← hu.mem]
    exact frame.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_cons_self
  · exact (val16_congr he).trans (val16_zero_fn _)

theorem scalarReduceEngine_ok {b p : BitVec 32} {s : State} (hc : VG.Proof.Ed25519.Arm.Ctx b s)
    (hp : s.gpr .r12 = p) (hfit : p.toNat + 64 ≤ 2 ^ 32)
    (hread : ∀ n < 64, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 n) 1)
    (hsep : ∀ r ∈ VG.Proof.Ed25519.Arm.scalarRegions b, (⟨State.addr p, 64⟩ : Region).Disjoint r) :
    WP isa scalarReduceEngine s fun t => VG.Proof.Ed25519.Arm.ScalarBodyKeep b s t ∧
      Lim t.mem (State.addr b) SR ∧
      V t.mem (State.addr b) SR = decodeLE (VG.Spec.Ed25519.bytesAt s.mem (State.addr p) 64) % L := by
  unfold scalarReduceEngine
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.scalarInit_ok hc) fun u ⟨ku, eu, lu, vu⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.Arm.scalarLoop_ok (ku.ctx hc) ((ku.rest.gpr _ (by decide)).trans hp) hfit
    (fun n hn => by rw [ku.rest.rd, ku.rest.wr]; exact hread n hn) hsep eu lu vu)
    fun t ⟨kt, lt, vt⟩ => ⟨ku.trans kt, lt, ?_⟩
  have bytes : VG.Spec.Ed25519.bytesAt u.mem (State.addr p) 64 = VG.Spec.Ed25519.bytesAt s.mem (State.addr p) 64 := by
    unfold VG.Spec.Ed25519.bytesAt; apply List.map_congr_left
    intro n hn
    exact ku.frame.bytes hsep (by decide : 64 ≤ 2 ^ 64) (List.mem_range.mp hn)
  rw [vt, bytes]

end VG.Proof.Ed25519.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed25519.Arm.ScalarMulAddVerified`. -/
section

/-! Merged from `Proof.Ed25519.Arm.ScalarMulAddEngine`. -/
section
/-! Merged from `Proof.Ed25519.Arm.ScalarWideAdd`. -/
section
/-! Merged from `Proof.Ed25519.Arm.ScalarWide`. -/
section
/-! Exact multiplication uses the field multiplier's checked row loop,
but stops before folding the high 256 bits modulo the field prime. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarWideMul_ok {b : BitVec 32} {x y : Nat}
    (hx : x + 64 ≤ ACC) (hy : y + 64 ≤ ACC) {s : State}
    (hc : Ctx b s) (hlx : Lim s.mem (State.addr b) x) (hly : Lim s.mem (State.addr b) y) :
    WP isa (scalarWideMul x y) s fun t =>
      Rest clob s t ∧ Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s.mem t.mem ∧
      (∀ k < 32, accw ACC t.mem (State.addr b) k < 65536) ∧
      val16 (accw ACC t.mem (State.addr b)) 32 = V s.mem (State.addr b) x * V s.mem (State.addr b) y := by
  unfold scalarWideMul
  refine WP.seq (WP.mono (mulPre_ok (by decide) (x := x) (y := y) hc) fun s1 h1 => ?_)
  refine WP.mono (Q := RowInv 4096 ACC b x y s 16) (WP.loop (M := isa)
    (fun n t => ∃ i, n = 16 - i ∧ i < 16 ∧ RowInv 4096 ACC b x y s i t) ?_ 16 s1
    ⟨0, rfl, by decide, h1⟩) fun t ht => ⟨ht.rest, ht.frame, ht.lt, ht.val⟩
  rintro n t ⟨i, rfl, hi, ht⟩
  refine WP.mono (row_ok (by decide) hx hy hlx hly hi ht) fun u ⟨hu, hz⟩ => ?_
  by_cases h16 : i + 1 = 16
  · refine .inl ⟨by rw [eval_ne, hz]; simp [h16], ?_⟩
    rw [h16] at hu; exact hu
  · exact .inr ⟨by rw [eval_ne, hz]; simp; omega, 16 - (i + 1), by omega,
      i + 1, rfl, by omega, hu⟩

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarAddPass`. -/
section
/-! Exact full-width addition, without the field multiplier's modulo-p tail. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

variable {b : BitVec 32}

theorem scalarAddPass_ok {x y : Nat} (hx : x + 64 ≤ 4096) (hy : y + 64 ≤ 4096)
    (hxy : x = y ∨ x + 64 ≤ y ∨ y + 64 ≤ x)
    {s : State} (hc : Ctx b s) (hlx : Lim s.mem (State.addr b) x) (hly : Lim s.mem (State.addr b) y)
    {cin : Nat} (hcin : cin < 65536) (h5 : (s.gpr .r5).toNat = cin) (h6 : s.gpr .r6 = mask16) :
    WP isa (.block (pass .r0 x (addSrc x y))) s
      (PassInv .r0 x s (fun k => limb s.mem (State.addr b) x k + limb s.mem (State.addr b) y k) cin 16) := by
  refine pass_ok (by decide) hx (by rw [hc.r0]; have := hc.fit; omega)
    (fun k hk => by rw [hc.r0]; exact hc.inW (by omega)) h6 h5
    (fun k hk => by have := hlx k hk; have := hly k hk; omega) hcin ?_
  intro k hk t ht
  have hct := hc.of_rest ht.rest (by decide)
  unfold addSrc
  refine ldr0_ok hct (d := x + 4 * k) (by omega) fun u hu => ?_
  refine ldr0_ok (hct.of_rest (hu.rest (ws := [.r3]) (by decide)) (by decide))
    (d := y + 4 * k) (by omega) fun v hv => ?_
  refine wp_dp (op2_reg _ _) fun w hw => WP.block_nil ?_
  have ex : (u.gpr .r3).toNat = limb s.mem (State.addr b) x k := by
    rw [hu.gpr]; exact wd_pass hc ht.frame (Or.inr (by omega)) (by omega) (by omega)
  have ey : (v.gpr .r2).toNat = limb s.mem (State.addr b) y k := by
    rw [hv.gpr, hu.mem]; exact wd_pass hc ht.frame (by omega) (by omega) (by omega)
  refine ⟨?_, (hu.rest (by decide)).trans ((hv.rest (by decide)).trans (hw.rest (by decide))),
    by rw [hw.mem, hv.mem, hu.mem]⟩
  rw [hw.gpr]
  show (v.gpr .r3 + v.gpr .r2).toNat = _
  rw [hv.other _ (by decide), toNat_add_lt (by rw [ex, ey]; have := hlx k hk; have := hly k hk; omega), ex, ey]

theorem scalarCarryPass_ok {x : Nat} (hx : x + 64 ≤ 4096)
    {s : State} (hc : Ctx b s) (hl : Lim s.mem (State.addr b) x)
    {cin : Nat} (hcin : cin < 65536) (h5 : (s.gpr .r5).toNat = cin) (h6 : s.gpr .r6 = mask16) :
    WP isa (.block (pass .r0 x (ldSrc x))) s
      (PassInv .r0 x s (limb s.mem (State.addr b) x) cin 16) := by
  refine pass_ok (by decide) hx (by rw [hc.r0]; have := hc.fit; omega)
    (fun k hk => by rw [hc.r0]; exact hc.inW (by omega)) h6 h5
    (fun k hk => by have := hl k hk; omega) hcin ?_
  intro k hk t ht
  refine WP.mono (ldSrc_ok (hc.of_rest ht.rest (by decide)) (by omega)) fun u ⟨e, ku, mu⟩ => ?_
  exact ⟨e.trans (wd_pass hc ht.frame (Or.inr (by omega)) (by omega) (by omega)), ku.mono (by decide), mu⟩

theorem scalarPass_result {x : Nat} {s t : State} {f : Nat → Nat} {cin : Nat}
    (hc : Ctx b s) (hp : PassInv .r0 x s f cin 16 t) :
    Frame [⟨State.addr b + BitVec.ofNat 64 x, 64⟩] s.mem t.mem ∧
    Lim t.mem (State.addr b) x ∧
    V t.mem (State.addr b) x + 2 ^ 256 * (t.gpr .r5).toNat = val16 f 16 + cin := by
  have outs : ∀ k < 16, limb t.mem (State.addr b) x k = VG.Proof.X25519.Arm.out f cin k := by
    intro k hk; have he := hp.outs k hk; rwa [hc.r0] at he
  refine ⟨by have hf := hp.frame; rwa [hc.r0] at hf,
    fun k hk => by rw [outs k hk]; exact out_lt _ _ _, ?_⟩
  change val16 _ _ + _ = _
  rw [val16_congr outs, hp.r5]
  exact chain_val f cin 16

end VG.Proof.Ed25519.Arm
end

/-! Add the 256-bit scalar to all 512 product bits, carrying across both halves. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarWide_split (m : Mem) (b : BitVec 32) :
    val16 (accw ACC m (State.addr b)) 32 = V m (State.addr b) ACC + 2 ^ 256 * V m (State.addr b) (ACC + 64) := by
  rw [show (32 : Nat) = 16 + 16 from rfl, val16_append]
  have he : val16 (fun k => accw ACC m (State.addr b) (16 + k)) 16 = V m (State.addr b) (ACC + 64) := by
    apply val16_congr
    intro k _
    unfold accw limb
    rw [show ACC + 4 * (16 + k) = ACC + 64 + 4 * k by omega]
  rw [he]
  rfl

theorem scalarWideAdd_ok {b : BitVec 32} {r : Nat} (hr : r + 64 ≤ ACC) {s : State}
    (hc : Ctx b s) (lr : Lim s.mem (State.addr b) r)
    (la : ∀ k < 32, accw ACC s.mem (State.addr b) k < 65536) :
    WP isa (.block (scalarWideAdd r)) s fun t =>
      Rest [.r2, .r3, .r4, .r5, .r6] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s.mem t.mem ∧
      (∀ k < 32, accw ACC t.mem (State.addr b) k < 65536) ∧
      val16 (accw ACC t.mem (State.addr b)) 32 + 2 ^ 512 * (t.gpr .r5).toNat =
        val16 (accw ACC s.mem (State.addr b)) 32 + V s.mem (State.addr b) r := by
  have hA : ACC = 1472 := rfl
  have ll : Lim s.mem (State.addr b) ACC := fun k hk => la k (by omega)
  have lh : Lim s.mem (State.addr b) (ACC + 64) := by
    intro k hk
    have he : limb s.mem (State.addr b) (ACC + 64) k = accw ACC s.mem (State.addr b) (16 + k) := by
      unfold limb accw; rw [show ACC + 64 + 4 * k = ACC + 4 * (16 + k) by omega]
    rw [he]; exact la _ (by omega)
  rw [scalarWideAdd, List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine wp_movw fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  have k2 : Rest [.r5, .r6] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have m2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have hc2 := hc.of_rest k2 (by decide)
  refine WP.append (VG.Proof.Ed25519.Arm.scalarAddPass_ok (x := ACC) (y := r) (by decide) (by omega) (Or.inr (Or.inr hr))
    hc2 (m2 ▸ ll) (m2 ▸ lr) (by decide : 0 < 65536) (by rw [u2.gpr]; rfl)
    (by rw [u2.other _ (by decide), u1.gpr])) fun s3 h3 => ?_
  obtain ⟨f3, l3, v3⟩ := VG.Proof.Ed25519.Arm.scalarPass_result hc2 h3
  have hc3 := hc2.of_rest h3.rest (by decide)
  have hs3 : Lim s3.mem (State.addr b) (ACC + 64) :=
    fun k hk => by
      rw [limb_frame f3 (fun z hz j hj => by
        rw [List.mem_singleton.mp hz]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) k hk, m2]
      exact lh k hk
  have hi3 : V s3.mem (State.addr b) (ACC + 64) = V s.mem (State.addr b) (ACC + 64) := by
    apply val16_congr
    intro k hk
    rw [limb_frame f3 (fun z hz j hj => by
      rw [List.mem_singleton.mp hz]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) k hk, m2]
  have carry3 : (s3.gpr .r5).toNat < 65536 := by
    rw [h3.r5]
    exact chain_lt (fun k hk => by have := ll k hk; have := lr k hk; rw [m2]; omega)
      (by decide) 16 (Nat.le_refl _)
  refine WP.mono (VG.Proof.Ed25519.Arm.scalarCarryPass_ok (x := ACC + 64) (by decide) hc3 hs3 carry3 rfl
    (by rw [h3.rest.gpr _ (by decide), u2.other _ (by decide), u1.gpr])) fun t ht => ?_
  obtain ⟨ft, lt, vt⟩ := VG.Proof.Ed25519.Arm.scalarPass_result hc3 ht
  have lrt : ∀ k < 16, limb t.mem (State.addr b) ACC k = limb s3.mem (State.addr b) ACC k :=
    limb_frame ft fun z hz j hj => by
      rw [List.mem_singleton.mp hz]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  have vlo : V t.mem (State.addr b) ACC = V s3.mem (State.addr b) ACC := val16_congr lrt
  refine ⟨(k2.mono (by decide)).trans ((h3.rest.mono (by decide)).trans (ht.rest.mono (by decide))), ?_, ?_, ?_⟩
  · have f3' : Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s.mem s3.mem := by
      rw [← m2]
      exact f3.sub fun z hz => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hz]; exact Region.sub_prefix (by decide)⟩
    exact f3'.trans (ft.sub fun z hz => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hz]; exact Offset.sub _ (by decide) (by decide)⟩)
  · intro k hk
    rcases Nat.lt_or_ge k 16 with hk16 | hk16
    · rw [show accw ACC t.mem (State.addr b) k = limb t.mem (State.addr b) ACC k from rfl, lrt k hk16]
      exact l3 k hk16
    · have he : accw ACC t.mem (State.addr b) k = limb t.mem (State.addr b) (ACC + 64) (k - 16) := by
        unfold accw limb; rw [show ACC + 4 * k = ACC + 64 + 4 * (k - 16) by omega]
      rw [he]; exact lt _ (by omega)
  · rw [val16_add, Nat.add_zero, m2] at v3
    change V s3.mem (State.addr b) ACC + _ = V s.mem (State.addr b) ACC + V s.mem (State.addr b) r at v3
    change V t.mem (State.addr b) (ACC + 64) + _ = V s3.mem (State.addr b) (ACC + 64) + _ at vt
    rw [hi3] at vt
    rw [VG.Proof.Ed25519.Arm.scalarWide_split, VG.Proof.Ed25519.Arm.scalarWide_split, vlo]
    omega

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarPackWide`. -/
section
/-! Serialize all 512 product bits for the same checked reduction engine. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarPackWide_ok {b : BitVec 32} {s : State} (hc : Ctx b s)
    (la : ∀ k < 32, accw ACC s.mem (State.addr b) k < 65536) :
    WP isa (.block scalarPackWide) s fun t =>
      Rest [.r3, .r12] s t ∧ Frame [⟨State.addr b + BitVec.ofNat 64 512, 64⟩] s.mem t.mem ∧
      t.gpr .r12 = b + BitVec.ofNat 32 512 ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem (State.addr b + BitVec.ofNat 64 512) 64) =
        val16 (accw ACC s.mem (State.addr b)) 32 := by
  have hA : ACC = 1472 := rfl
  have ll : Lim s.mem (State.addr b) ACC := fun k hk => la k (by omega)
  have lh : Lim s.mem (State.addr b) (ACC + 64) := by
    intro k hk
    change wd s.mem (State.addr b) (ACC + 64 + 4 * k) < _
    rw [show ACC + 64 + 4 * k = ACC + 4 * (16 + k) by omega]
    exact la _ (by omega)
  have afit := hc.fit
  have ep : State.addr (b + BitVec.ofNat 32 512) = State.addr b + BitVec.ofNat 64 512 :=
    addr_add (by omega)
  have pf : (b + BitVec.ofNat 32 512).toNat = b.toNat + 512 := by
    rw [toNat_add_lt (by rw [toNat_imm (by decide)]; omega), toNat_imm (by decide)]
  rw [scalarPackWide, List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine wp_dp (op2_imm (by decide)) fun u hu => ?_
  have hcu := hc.of_rest (hu.rest (ws := [.r12]) (by decide)) (by decide)
  have pu : u.gpr .r12 = b + BitVec.ofNat 32 512 := by rw [hu.gpr]; change s.gpr .r0 + _ = _; rw [hc.r0]; rfl
  refine WP.append (packField_ok (p := b + BitVec.ofNat 32 512) (a := ACC) (dst := 0) hcu
    (by decide) (hu.mem ▸ ll) (by decide) pu (by rw [pf]; omega)
    (fun i hi => by rw [ep, Offset.add_add]; exact hcu.inW (by omega))
    (by rw [ep, BitVec.add_zero]; exact Offset.disjoint _ (Or.inr (by decide)) (by decide) (by decide)))
    fun v ⟨kv, fv, vv⟩ => ?_
  have hcv := hcu.of_rest kv (by decide)
  have fv' : Frame [⟨State.addr b + BitVec.ofNat 64 512, 32⟩] s.mem v.mem := by
    simpa only [ep, BitVec.add_zero, hu.mem] using fv
  have hvh : ∀ k < 16, limb v.mem (State.addr b) (ACC + 64) k = limb s.mem (State.addr b) (ACC + 64) k :=
    limb_frame fv' fun r hr k hk => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (Or.inr (by omega)) (by omega) (by decide)
  have lvh : Lim v.mem (State.addr b) (ACC + 64) := fun k hk => by rw [hvh k hk]; exact lh k hk
  refine WP.mono (packField_ok (p := b + BitVec.ofNat 32 512) (a := ACC + 64) (dst := 32) hcv
    (by decide) lvh (by decide) ((kv.gpr _ (by decide)).trans pu) (by rw [pf]; omega)
    (fun i hi => by rw [ep, Offset.add_add]; exact hcv.inW (by omega))
    (by rw [ep, Offset.add_add]; exact Offset.disjoint _ (Or.inr (by decide)) (by decide) (by decide)))
    fun t ⟨kt, ft, vt⟩ => ?_
  have ft' : Frame [⟨State.addr b + BitVec.ofNat 64 544, 32⟩] v.mem t.mem := by
    simpa only [ep, Offset.add_add] using ft
  have vlo : packedV t.mem (State.addr b + BitVec.ofNat 64 512) = V s.mem (State.addr b) ACC := by
    rw [packedV_frame ft' (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (Or.inl (by decide)) (by decide) (by decide))]
    simpa only [ep, BitVec.add_zero, hu.mem] using vv
  have vhi : packedV t.mem (State.addr b + BitVec.ofNat 64 544) = V s.mem (State.addr b) (ACC + 64) := by
    have ve : V v.mem (State.addr b) (ACC + 64) = V s.mem (State.addr b) (ACC + 64) := val16_congr hvh
    simpa only [ep, Offset.add_add, ve] using vt
  refine ⟨(hu.rest (by decide)).trans ((kv.mono (by decide)).trans (kt.mono (by decide))), ?_,
    (kt.gpr _ (by decide)).trans ((kv.gpr _ (by decide)).trans pu), ?_⟩
  · exact (fv'.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩).trans
      (ft'.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩)
  · change Spec.Ed25519.decodeLE (Spec.X25519.bytesAt t.mem _ (32 + 32)) = _
    rw [VG.Proof.X25519.bytesAt_add, decodeLE_append, VG.Proof.X25519.length_bytesAt]
    change Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem _ 32) +
      256 ^ 32 * Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem _ 32) = _
    rw [scalar_packed_decode, scalar_packed_decode, Offset.add_add, vlo, vhi, VG.Proof.Ed25519.Arm.scalarWide_split]

end VG.Proof.Ed25519.Arm
end

/-! Full-width product plus addend, serialized and reduced modulo L. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

abbrev scalarEngineClob : List Reg := [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]
def scalarWork (b : BitVec 32) : Region := ⟨State.addr b + BitVec.ofNat 64 64, 1536⟩

theorem scalarWork_sub {b : BitVec 32} {o n : Nat} (ho : 64 ≤ o) (hn : o + n ≤ 1600) :
    (⟨State.addr b + BitVec.ofNat 64 o, n⟩ : Region).Sub (VG.Proof.Ed25519.Arm.scalarWork b) :=
  Offset.sub _ ho (by omega)

theorem scalar_muladd_bound {r k a : Nat} (hr : r < 2 ^ 256) (hk : k < 2 ^ 256) (ha : a < 2 ^ 256) :
    k * a + r < 2 ^ 512 := by
  have hm : k * a ≤ (2 ^ 256 - 1) * (2 ^ 256 - 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem scalar_zero_carry {n c x y : Nat} (h : x + n * c = y) (hc : c = 0) : x = y := by
  rw [hc, Nat.mul_zero, Nat.add_zero] at h
  exact h

theorem scalarMulAddEngine_ok {b : BitVec 32} {s : State} (hc : Ctx b s)
    (lr : Lim s.mem (State.addr b) 64) (lk : Lim s.mem (State.addr b) 128)
    (la : Lim s.mem (State.addr b) 192) :
    WP isa scalarMulAddEngine s fun t =>
      Rest VG.Proof.Ed25519.Arm.scalarEngineClob s t ∧ Frame [VG.Proof.Ed25519.Arm.scalarWork b] s.mem t.mem ∧
      Lim t.mem (State.addr b) SR ∧ V t.mem (State.addr b) SR =
        (V s.mem (State.addr b) 64 + V s.mem (State.addr b) 128 * V s.mem (State.addr b) 192) %
          Spec.Ed25519.L ∧ t.gpr .r8 = s.gpr .r10 := by
  have hA : ACC = 1472 := rfl
  unfold scalarMulAddEngine
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.scalarWideMul_ok (by decide) (by decide) hc lk la)
    fun u ⟨ku, fu, lu, vu⟩ => ?_)
  have hcu := hc.of_rest ku (by decide)
  have ur : ∀ k < 16, limb u.mem (State.addr b) 64 k = limb s.mem (State.addr b) 64 k :=
    limb_frame fu fun z hz k hk => by
      rw [List.mem_singleton.mp hz]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  have lru : Lim u.mem (State.addr b) 64 := fun k hk => by rw [ur k hk]; exact lr k hk
  refine WP.seq (WP.append (VG.Proof.Ed25519.Arm.scalarWideAdd_ok (by decide) hcu lru lu) fun v ⟨kv, fv, lv, vv⟩ => ?_)
  have hcv := hcu.of_rest kv (by decide)
  have vr : V u.mem (State.addr b) 64 = V s.mem (State.addr b) 64 := val16_congr ur
  have sum : val16 (accw ACC v.mem (State.addr b)) 32 =
      V s.mem (State.addr b) 128 * V s.mem (State.addr b) 192 + V s.mem (State.addr b) 64 := by
    rw [vu, vr] at vv
    have bound := VG.Proof.Ed25519.Arm.scalar_muladd_bound (V_lt lr) (V_lt lk) (V_lt la)
    have zero : (v.gpr .r5).toNat = 0 := by
      rcases Nat.eq_zero_or_pos (v.gpr .r5).toNat with hz | hp
      · exact hz
      · have := Nat.le_mul_of_pos_right (2 ^ 512) hp; omega
    exact VG.Proof.Ed25519.Arm.scalar_zero_carry vv zero
  refine WP.mono (VG.Proof.Ed25519.Arm.scalarPackWide_ok hcv lv) fun w ⟨kw, fw, pw, vw⟩ => ?_
  have kr : Rest VG.Proof.Ed25519.Arm.scalarEngineClob s w :=
    (ku.mono (by decide)).trans ((kv.mono (by decide)).trans (kw.mono (by decide)))
  have hcw := hc.of_rest kr (by decide)
  have pf : (b + BitVec.ofNat 32 512).toNat + 64 ≤ 2 ^ 32 := by
    rw [toNat_add_lt (by rw [toNat_imm (by decide)]; have := hc.fit; omega), toNat_imm (by decide)]
    have := hc.fit; omega
  have ep : State.addr (b + BitVec.ofNat 32 512) = State.addr b + BitVec.ofNat 64 512 :=
    addr_add (by have := hc.fit; omega)
  refine WP.seq ?_
  refine wp_mov (op2_reg _ _) fun x hx => WP.block_nil ?_
  have hcx := hcw.of_rest (hx.rest (ws := [.r8]) (by decide)) (by decide)
  refine WP.mono (VG.Proof.Ed25519.Arm.scalarReduceEngine_ok hcx ((hx.other _ (by decide)).trans pw) pf
    (fun n hn => by rw [ep, Offset.add_add]; exact hcx.inR (by omega))
    (fun z hz => by
      rw [ep]
      simp only [VG.Proof.Ed25519.Arm.scalarRegions, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl <;> exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)))
    fun t ⟨kt, lt, vt⟩ => ?_
  refine ⟨kr.trans ((hx.rest (by decide)).trans (kt.rest.mono (by decide))), ?_, lt, ?_, ?_⟩
  · have fu' : Frame [VG.Proof.Ed25519.Arm.scalarWork b] s.mem u.mem := fu.sub fun z hz => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hz]; exact VG.Proof.Ed25519.Arm.scalarWork_sub (by decide) (by decide)⟩
    have fv' : Frame [VG.Proof.Ed25519.Arm.scalarWork b] u.mem v.mem := fv.sub fun z hz => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hz]; exact VG.Proof.Ed25519.Arm.scalarWork_sub (by decide) (by decide)⟩
    have fw' : Frame [VG.Proof.Ed25519.Arm.scalarWork b] v.mem w.mem := fw.sub fun z hz => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hz]; exact VG.Proof.Ed25519.Arm.scalarWork_sub (by decide) (by decide)⟩
    have ft' : Frame [VG.Proof.Ed25519.Arm.scalarWork b] w.mem t.mem := by
      rw [← hx.mem]
      exact kt.frame.sub fun z hz => ⟨_, List.mem_singleton_self _, by
        simp only [VG.Proof.Ed25519.Arm.scalarRegions, List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl <;> exact VG.Proof.Ed25519.Arm.scalarWork_sub (by decide) (by decide)⟩
    exact fu'.trans (fv'.trans (fw'.trans ft'))
  · rw [vt, ep, hx.mem, vw, sum, Nat.add_comm]
  · rw [kt.rest.gpr _ (by decide), hx.gpr, kw.gpr _ (by decide), kv.gpr _ (by decide), ku.gpr _ (by decide)]

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarMulAddMain`. -/
section
/-! Merged from `Proof.Ed25519.Arm.ScalarMulAddArgs`. -/
section
/-! Preserve the input pointers and callee-saved registers before arithmetic. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def ScalarArgs (b : BitVec 32) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  ∀ i < 4, m.readW (State.addr b + BitVec.ofNat 64 (32 + 4 * i)) 32 = g (scalarArgReg i)

theorem scalarStoreArgs_ok {b : BitVec 32} {s : State} (hp : s.gpr .r12 = b)
    (hfit : b.toNat + 8192 ≤ 2 ^ 32) (hw : (⟨State.addr b, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block scalarStoreArgs) s fun t => VG.Proof.Ed25519.Arm.ScalarArgs b s.gpr t.mem ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 32, 16⟩] s.mem t.mem ∧ t.gpr = s.gpr ∧ Rest [] s t := by
  refine wp_range_flatMap (M := isa)
    (fun n t => (∀ i < n, t.mem.readW (State.addr b + BitVec.ofNat 64 (32 + 4 * i)) 32 =
      s.gpr (scalarArgReg i)) ∧ Frame [⟨State.addr b + BitVec.ofNat 64 32, 4 * n⟩] s.mem t.mem ∧
      t.gpr = s.gpr ∧ Rest [] s t)
    (fun n t hn ⟨hval, hf, hg, hk⟩ => ?_) 4 (Nat.le_refl _) s
    ⟨fun _ h => by omega, Frame.refl _ _, rfl, Rest.refl _ _⟩
  refine wp_str (a := State.addr b + BitVec.ofNat 64 (32 + 4 * n)) (by omega)
    (by rw [hg, hp]; exact addr_add (by omega))
    (by rw [hk.wr]; exact in_base hw (by omega) (by omega)) fun u hu => WP.block_nil ?_
  refine ⟨fun i hi => ?_, ?_, by rw [hu.gpr, hg], hk.trans (hu.rest _)⟩
  · rw [hu.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact hval i hi
    · rw [Mem.readW_writeW_self32, hg]
  · rw [hu.mem]
    exact (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))

theorem scalar_ldrSp {s : State} {is : List Instr} {Q : State → Prop}
    (hr : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (k : ∀ t, Upd s t .r12 (stackArg s 0) → WP isa (.block is) t Q) :
    WP isa (.block (.ldrSp .r12 0 :: is)) s Q := by
  refine WP.cons (s' := s.setReg .r12 (stackArg s 0)) ?_ (k _ (Upd.setReg _ _ _))
  simp only [exec, show (0 : Nat) < 4096 from by decide, ite_true, State.load32,
    BitVec.add_zero, hr, Option.map_some]
  simp [stackArg, stackArgAddr]

theorem scalarMulAddArgs_ok {s : State}
    (hr : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (hfit : (stackArg s 0).toNat + 8192 ≤ 2 ^ 32)
    (hw : (⟨State.addr (stackArg s 0), 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block scalarMulAddArgs) s fun t =>
      Ctx (stackArg s 0) t ∧ ScalarSaved (State.addr (stackArg s 0)) s.gpr t.mem ∧
      VG.Proof.Ed25519.Arm.ScalarArgs (stackArg s 0) s.gpr t.mem ∧ Rest [.r0, .r12] s t ∧
      Frame [⟨State.addr (stackArg s 0), 48⟩] s.mem t.mem := by
  rw [scalarMulAddArgs, List.append_assoc, List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine VG.Proof.Ed25519.Arm.scalar_ldrSp hr fun u hu => ?_
  refine WP.append (scalarSave_ok hu.gpr hfit (hu.wr ▸ hw)) fun v ⟨sv, fv, gv, kv⟩ => ?_
  refine WP.append (VG.Proof.Ed25519.Arm.scalarStoreArgs_ok (by rw [gv]; exact hu.gpr) hfit
    (by rw [kv.wr, hu.wr]; exact hw)) fun w ⟨aw, fw, gw, kw⟩ => ?_
  refine wp_mov (op2_reg _ _) fun t ht => WP.block_nil ?_
  have kt : Rest [.r0, .r12] s t := (hu.rest (by decide)).trans
    ((kv.mono (by decide)).trans ((kw.mono (by decide)).trans (ht.rest (by decide))))
  refine ⟨⟨?_, hfit, by rw [kt.wr]; exact hw⟩, ?_, ?_, kt, ?_⟩
  · rw [ht.gpr, gw, gv, hu.gpr]
  · have sn : ∀ i < 8, scalarSavedReg i ≠ .r12 := by decide
    intro i hi
    rw [ht.mem, fw.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), sv i hi]
    · exact hu.other _ (sn i hi)
    · rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  · have an : ∀ i < 4, scalarArgReg i ≠ .r12 := by decide
    intro i hi
    rw [ht.mem, aw i hi, gv]
    exact hu.other _ (an i hi)
  · rw [ht.mem, ← hu.mem]
    exact (fv.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩).trans
      (fw.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by decide)⟩)

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarMulAddInputs`. -/
section
/-! Merged from `Proof.Ed25519.Arm.ScalarLoadInput`. -/
section
/-! Load a scalar using a saved public input pointer. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarLoadInput_ok {b p : BitVec 32} {o ptrOff : Nat} {s : State} (hc : Ctx b s)
    (ho : o + 64 ≤ 4096) (hm : ptrOff + 4 ≤ 4096)
    (hp : s.mem.readW (State.addr b + BitVec.ofNat 64 ptrOff) 32 = p)
    (hfit : p.toNat + 32 ≤ 2 ^ 32)
    (hr : (⟨State.addr p, 32⟩ : Region) ∈ s.rd ++ s.wr)
    (hsep : (⟨State.addr p, 32⟩ : Region).Disjoint ⟨State.addr b, 8192⟩) :
    WP isa (.block (scalarLoadInput o ptrOff)) s fun t =>
      Rest [.r2, .r3, .r12] s t ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] s.mem t.mem ∧
      Lim t.mem (State.addr b) o ∧ V t.mem (State.addr b) o =
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr p) 32) := by
  unfold scalarLoadInput
  simp only [List.cons_append, List.nil_append]
  refine ldr0_ok hc hm fun u hu => ?_
  have hcu := hc.of_rest (hu.rest (ws := [.r12]) (by decide)) (by decide)
  refine WP.mono (unpackField_ok (p := p) (src := 0) hcu ho (by decide) (hu.gpr.trans hp) (by omega)
    (fun i hi => by rw [hu.rd, hu.wr]; simpa only [Nat.zero_add] using in_base hr (by omega) (by omega))
    (by simpa only [BitVec.add_zero] using hsep.sub_right (Offset.sub_base _ (by omega))))
    fun t ⟨kt, ft, lt, vt⟩ => ?_
  refine ⟨(hu.rest (by decide)).trans (kt.mono (by decide)), ?_, lt, ?_⟩
  · rw [← hu.mem]; exact ft
  · rw [vt, hu.mem, BitVec.add_zero, scalar_packed_decode]

end VG.Proof.Ed25519.Arm
end

/-! Prepare the three arbitrary, unreduced 256-bit scalar inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def ScalarInputs (b : BitVec 32) (m : Mem) (p : Nat → BitVec 32) (n : Nat) (t : State) : Prop :=
  ∀ i < n, Lim t.mem (State.addr b) (64 + 64 * i) ∧
    V t.mem (State.addr b) (64 + 64 * i) =
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr (p i)) 32)

structure ScalarInputsInv (b : BitVec 32) (s0 : State) (p : Nat → BitVec 32) (n : Nat) (t : State) : Prop where
  rest : Rest [.r2, .r3, .r12] s0 t
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 64, 64 * n⟩] s0.mem t.mem
  values : VG.Proof.Ed25519.Arm.ScalarInputs b s0.mem p n t

theorem scalarInputsLoop_ok {b : BitVec 32} {s : State} (hc : Ctx b s)
    {p : Nat → BitVec 32}
    (hp : ∀ i < 3, s.mem.readW (State.addr b + BitVec.ofNat 64 (36 + 4 * i)) 32 = p i)
    (hfit : ∀ i < 3, (p i).toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ i < 3, (⟨State.addr (p i), 32⟩ : Region) ∈ s.rd ++ s.wr)
    (hsep : ∀ i < 3, (⟨State.addr (p i), 32⟩ : Region).Disjoint ⟨State.addr b, 8192⟩) :
    WP isa (.block ((List.range 3).flatMap fun i => scalarLoadInput (64 + 64 * i) (36 + 4 * i))) s
      (VG.Proof.Ed25519.Arm.ScalarInputsInv b s p 3) := by
  refine wp_range_flatMap (M := isa) (VG.Proof.Ed25519.Arm.ScalarInputsInv b s p)
    (fun n t hn ht => ?_) 3 (Nat.le_refl _) s
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => by omega⟩
  have hct := hc.of_rest ht.rest (by decide)
  have ptr : t.mem.readW (State.addr b + BitVec.ofNat 64 (36 + 4 * n)) 32 = p n := by
    rw [ht.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), hp n hn]
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  refine WP.mono (VG.Proof.Ed25519.Arm.scalarLoadInput_ok hct (by omega) (by omega) ptr (hfit n hn)
    (by rw [ht.rest.rd, ht.rest.wr]; exact hr n hn) (hsep n hn)) fun u ⟨ku, fu, lu, vu⟩ => ?_
  refine ⟨ht.rest.trans ku, ?_, fun i hi => ?_⟩
  · exact (ht.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).trans
      (fu.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)⟩)
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have eq : ∀ k < 16, limb u.mem (State.addr b) (64 + 64 * i) k =
          limb t.mem (State.addr b) (64 + 64 * i) k :=
        limb_frame fu fun r hr k hk => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
      exact ⟨fun k hk => by rw [eq k hk]; exact (ht.values i hi).1 k hk,
        (val16_congr eq).trans (ht.values i hi).2⟩
    · refine ⟨lu, ?_⟩
      rw [vu]
      apply congrArg Spec.Ed25519.decodeLE
      unfold Spec.Ed25519.bytesAt
      refine List.map_congr_left fun k hk => ht.frame.bytes
        (R := ⟨State.addr (p i), 32⟩) (fun r hr => ?_) (by decide : 32 ≤ 2 ^ 64) (List.mem_range.mp hk)
      rw [List.mem_singleton.mp hr]
      exact (hsep i hn).sub_right (Offset.sub_base _ (by omega))

theorem scalarMulAddInputs_ok {b q : BitVec 32} {s : State} (hc : Ctx b s)
    {p : Nat → BitVec 32}
    (hp : ∀ i < 3, s.mem.readW (State.addr b + BitVec.ofNat 64 (36 + 4 * i)) 32 = p i)
    (hfit : ∀ i < 3, (p i).toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ i < 3, (⟨State.addr (p i), 32⟩ : Region) ∈ s.rd ++ s.wr)
    (hsep : ∀ i < 3, (⟨State.addr (p i), 32⟩ : Region).Disjoint ⟨State.addr b, 8192⟩)
    (hout : s.mem.readW (State.addr b + BitVec.ofNat 64 32) 32 = q) :
    WP isa (.block scalarMulAddInputs) s fun t =>
      Rest [.r2, .r3, .r10, .r12] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 64, 192⟩] s.mem t.mem ∧
      VG.Proof.Ed25519.Arm.ScalarInputs b s.mem p 3 t ∧ t.gpr .r10 = q := by
  unfold scalarMulAddInputs
  refine WP.append (VG.Proof.Ed25519.Arm.scalarInputsLoop_ok hc hp hfit hr hsep) fun u hu => ?_
  refine ldr0_ok (hc.of_rest hu.rest (by decide)) (by decide) fun t ht => WP.block_nil ?_
  refine ⟨(hu.rest.mono (by decide)).trans (ht.rest (by decide)), by rw [ht.mem]; exact hu.frame,
    fun i hi => by rw [show t.mem = u.mem from ht.mem]; exact hu.values i hi, ?_⟩
  rw [ht.gpr, hu.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), hout]
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarMulAddFinish`. -/
section
/-! Encode the scalar using the output pointer kept public across arithmetic. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarMulAddFinish_ok {b p : BitVec 32} {s : State} (hc : Ctx b s)
    (hl : Lim s.mem (State.addr b) SR) (hp : s.gpr .r8 = p)
    (hfit : p.toNat + 32 ≤ 2 ^ 32) (hw : (⟨State.addr p, 32⟩ : Region) ∈ s.wr)
    (hsep : (⟨State.addr p, 32⟩ : Region).Disjoint ⟨State.addr b, 8192⟩)
    {g : Reg → BitVec 32} (hs : ScalarSaved (State.addr b) g s.mem) :
    WP isa (.block scalarMulAddFinish) s fun t =>
      (∀ i < 8, t.gpr (scalarSavedReg i) = g (scalarSavedReg i)) ∧ Rest scalarFinishClob s t ∧
      Frame [⟨State.addr p, 32⟩] s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr p) 32 = Spec.Ed25519.encodeLE 32 (V s.mem (State.addr b) SR) := by
  rw [scalarMulAddFinish, List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun u hu => ?_
  have hcu := hc.of_rest (hu.rest (ws := [.r12]) (by decide)) (by decide)
  refine WP.append (packField_ok (p := p) (a := SR) (dst := 0) hcu (by decide) (hu.mem ▸ hl) (by decide)
    (hu.gpr.trans hp) (by omega)
    (fun i hi => by rw [hu.wr]; simpa only [Nat.zero_add] using in_base hw (by omega) (by omega))
    (by simpa only [BitVec.add_zero] using
      hsep.symm.sub_left (Offset.sub_base _ (by decide : SR + 64 ≤ 8192))))
    fun v ⟨kv, fv, vv⟩ => ?_
  have hcv := hcu.of_rest kv (by decide)
  have hs' : ScalarSaved (State.addr b) g v.mem :=
    (hu.mem ▸ hs).frame fv fun r hr i hi => by
      rw [List.mem_singleton.mp hr, BitVec.add_zero]
      exact hsep.symm.sub_left (Offset.sub_base _ (by omega))
  refine WP.mono (scalarRestore_ok hcv hs') fun t ⟨saved, kt, mt⟩ => ?_
  refine ⟨saved, (hu.rest (by decide)).trans ((kv.mono (by decide)).trans (kt.mono (by decide))), ?_, ?_⟩
  · rw [mt, ← hu.mem]; simpa only [BitVec.add_zero] using fv
  · rw [mt, scalar_packed_encode, ← hu.mem]
    have e : packedV v.mem (State.addr p) = V u.mem (State.addr b) SR := by
      simpa only [BitVec.add_zero] using vv
    exact congrArg (Spec.Ed25519.encodeLE 32) e

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarMulAddContract`. -/
section
/-! A local contract for the five-argument scalar multiply-add ABI. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def scalarMulAddLocal : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 32⟩
    let r : Region := ⟨State.addr (s.gpr .r1), 32⟩
    let k : Region := ⟨State.addr (s.gpr .r2), 32⟩
    let a : Region := ⟨State.addr (s.gpr .r3), 32⟩
    let ws : Region := ⟨State.addr (stackArg s 0), 8192⟩
    let args : Region := ⟨State.addr s.sp, 4⟩
    s.rd = [r, k, a, args] ∧ s.wr = [out, ws] ∧
      out.Disjoint ws ∧ r.Disjoint ws ∧ k.Disjoint ws ∧ a.Disjoint ws ∧
      out.Disjoint args ∧ ws.Disjoint args ∧
      (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + 32 ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + 8192 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32
  post s t := Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r0)) 32 =
    Spec.Ed25519.scalarMulAdd (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 32)
      (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r2)) 32)
      (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r3)) 32)
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧
    s.gpr .r2 = t.gpr .r2 ∧ s.gpr .r3 = t.gpr .r3 ∧ stackArg s 0 = stackArg t 0

structure ScalarMulAddPre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r1), 32⟩, ⟨State.addr (s.gpr .r2), 32⟩,
    ⟨State.addr (s.gpr .r3), 32⟩, ⟨State.addr s.sp, 4⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r0), 32⟩, ⟨State.addr (stackArg s 0), 8192⟩]
  out_ws : (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 8192⟩
  r_ws : (⟨State.addr (s.gpr .r1), 32⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 8192⟩
  k_ws : (⟨State.addr (s.gpr .r2), 32⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 8192⟩
  a_ws : (⟨State.addr (s.gpr .r3), 32⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 8192⟩
  out_args : (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr s.sp, 4⟩
  ws_args : (⟨State.addr (stackArg s 0), 8192⟩ : Region).Disjoint ⟨State.addr s.sp, 4⟩
  f0 : (s.gpr .r0).toNat + 32 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 32 ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 32 ≤ 2 ^ 32
  f3 : (s.gpr .r3).toNat + 32 ≤ 2 ^ 32
  fs : (stackArg s 0).toNat + 8192 ≤ 2 ^ 32
  fsp : s.sp.toNat + 4 ≤ 2 ^ 32

theorem ScalarMulAddPre.of {s : State} (h : scalarMulAddLocal.pre s) : VG.Proof.Ed25519.Arm.ScalarMulAddPre s := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem ScalarMulAddPre.input {s : State} (h : VG.Proof.Ed25519.Arm.ScalarMulAddPre s) {i : Nat} (hi : i < 3) :
    (s.gpr (scalarArgReg (i + 1))).toNat + 32 ≤ 2 ^ 32 ∧
    (⟨State.addr (s.gpr (scalarArgReg (i + 1))), 32⟩ : Region) ∈ s.rd ++ s.wr ∧
    (⟨State.addr (s.gpr (scalarArgReg (i + 1))), 32⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 8192⟩ := by
  have hc : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · exact ⟨h.f1, by rw [h.rd]; simp [scalarArgReg], h.r_ws⟩
  · exact ⟨h.f2, by rw [h.rd]; simp [scalarArgReg], h.k_ws⟩
  · exact ⟨h.f3, by rw [h.rd]; simp [scalarArgReg], h.a_ws⟩

end VG.Proof.Ed25519.Arm
end

/-! The complete scalar multiply-add function and ARM calling convention. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarMulAdd_correct {s : State} (h : VG.Proof.Ed25519.Arm.ScalarMulAddPre s) :
    WP isa scalarMulAdd s fun t => abiPreserved s t ∧ scalarMulAddLocal.post s t := by
  let b := stackArg s 0
  let ptr := fun i => s.gpr (scalarArgReg (i + 1))
  have hw : (⟨State.addr b, 8192⟩ : Region) ∈ s.wr := by rw [h.wr]; simp [b]
  have ha : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4 :=
    ⟨_, by rw [h.rd]; simp, Region.contains_self _ _⟩
  unfold scalarMulAdd
  refine WP.seq (WP.append (VG.Proof.Ed25519.Arm.scalarMulAddArgs_ok ha h.fs hw) fun u ⟨hcu, su, au, ku, fu⟩ => ?_)
  refine WP.mono (VG.Proof.Ed25519.Arm.scalarMulAddInputs_ok (p := ptr) (q := s.gpr .r0) hcu
    (fun i hi => by
      have e := au (i + 1) (by omega)
      rw [show 32 + 4 * (i + 1) = 36 + 4 * i by omega] at e
      exact e)
    (fun i hi => (h.input hi).1)
    (fun i hi => by rw [ku.rd, ku.wr]; exact (h.input hi).2.1)
    (fun i hi => (h.input hi).2.2) (au 0 (by decide))) fun v ⟨kv, fv, iv, ov⟩ => ?_
  have hcv := hcu.of_rest kv (by decide)
  refine WP.seq (WP.mono (VG.Proof.Ed25519.Arm.scalarMulAddEngine_ok hcv (iv 0 (by decide)).1
    (iv 1 (by decide)).1 (iv 2 (by decide)).1) fun w ⟨kw, fw, lw, vw, ow⟩ => ?_)
  have sw : ScalarSaved (State.addr b) s.gpr w.mem :=
    (su.frame fv fun r hr i hi => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)).frame
      fw fun r hr i hi => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  refine WP.mono (VG.Proof.Ed25519.Arm.scalarMulAddFinish_ok (hcv.of_rest kw (by decide)) lw (ow.trans ov) h.f0
    (by rw [kw.wr, kv.wr, ku.wr, h.wr]; simp) h.out_ws sw) fun t ⟨gt, kt, _, bt⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [kt.sp, kw.sp, kv.sp, ku.sp]⟩, ?_⟩
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
    · rw [kt.gpr _ (by decide), kw.gpr _ (by decide), kv.gpr _ (by decide), ku.gpr _ (by decide)]
  · have inputs : ∀ i < 3, V v.mem (State.addr b) (64 + 64 * i) =
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr (ptr i)) 32) := by
      intro i hi
      rw [(iv i hi).2]
      apply congrArg Spec.Ed25519.decodeLE
      unfold Spec.Ed25519.bytesAt
      refine List.map_congr_left fun k hk => fu.bytes (R := ⟨State.addr (ptr i), 32⟩)
        (fun r hr => ?_) (by decide : 32 ≤ 2 ^ 64) (List.mem_range.mp hk)
      rw [List.mem_singleton.mp hr]
      exact (h.input hi).2.2.sub_right (Region.sub_prefix (by decide))
    change Spec.Ed25519.bytesAt t.mem _ 32 = Spec.Ed25519.encodeLE 32 _
    rw [bt, vw, inputs 0 (by decide), inputs 1 (by decide), inputs 2 (by decide)]
    rfl

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarMulAddLit`. -/
section
namespace VG.Impl.Ed25519.Arm
materialize_code scalarMulAdd
end VG.Impl.Ed25519.Arm
end

/-! The complete multiply-add primitive satisfies the reviewed contract. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def scalarMulAddTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [32, 8192],
    argLen := 4, argBases := [(0, 1)] }

theorem scalarMulAddTaint_wf {s : State} (h : scalarMulAddLocal.pre s) :
    VG.Arm.Taint.Wf VG.Proof.Ed25519.Arm.scalarMulAddTaint s := by
  have hp := ScalarMulAddPre.of h
  refine ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.Ed25519.Arm.scalarMulAddTaint], ?_, ?_⟩,
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
    simp only [VG.Proof.Ed25519.Arm.scalarMulAddTaint, List.mem_singleton] at hm
    subst hm
    refine ⟨by decide, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem scalarMulAdd_argByte (s : State) (k : Nat) :
    VG.Arm.Taint.argByte s k = stackArgAddr s 0 + BitVec.ofNat 64 k := by
  simp [VG.Arm.Taint.argByte, stackArgAddr]

theorem scalarMulAdd_ct : ConstantTime isa scalarMulAddLocal.pre scalarMulAddLocal.pub scalarMulAdd := by
  refine VG.Taint.constantTime (A := VG.Arm.taint) VG.Proof.Ed25519.Arm.scalarMulAddTaint ?_ (by taint_decide)
  intro s t hs ht ⟨hsp, h0, h1, h2, h3, ha⟩
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.Ed25519.Arm.scalarMulAddTaint_wf hs, VG.Proof.Ed25519.Arm.scalarMulAddTaint_wf ht,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => hsp, fun k hk => ?_⟩
  · simp only [VG.Proof.Ed25519.Arm.scalarMulAddTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · rw [(ScalarMulAddPre.of hs).wr, (ScalarMulAddPre.of ht).wr, h0, ha]
  · rw [VG.Proof.Ed25519.Arm.scalarMulAdd_argByte, VG.Proof.Ed25519.Arm.scalarMulAdd_argByte, Mem.readW_byte s.mem _ hk, Mem.readW_byte t.mem _ hk]
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
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 32⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x5000, 8192⟩]

theorem scalarMulAdd_ok (s : State) (hs : scalarMulAddLocal.pre s) :
    ∃ t s', Exec isa scalarMulAdd s t s' ∧ abiPreserved s s' ∧ scalarMulAddLocal.post s s' :=
  VG.Proof.Ed25519.Arm.scalarMulAdd_correct (ScalarMulAddPre.of hs)

theorem scalarMulAdd_verified : Verified Arm.target scalarMulAdd
    (Spec.Ed25519.scalarMulAddContract Arm.abi) :=
  Verified.of_correct VG.Proof.Ed25519.Arm.scalarMulAdd_ok VG.Proof.Ed25519.Arm.scalarMulAdd_ct (by
    sig_implies [Spec.Ed25519.scalarMulAddContract, Spec.Ed25519.scalarMulAddSig,
      Spec.Ed25519.scratchWords, VG.Proof.Ed25519.Arm.scalarMulAddLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
      [scalarMulAddSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Ed25519.Arm.scalarMulAddSat)

end VG.Proof.Ed25519.Arm

end
