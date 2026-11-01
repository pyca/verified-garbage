module

public import VerifiedGarbage.Impl.Ed25519.RISCV64.MulFn
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
public import VerifiedGarbage.Proof.X25519.Field32Contract
import VerifiedGarbage.Proof.X25519.RISCV64.R64.Reduce
import VerifiedGarbage.Proof.Ed25519.RISCV64.Packed
import VerifiedGarbage.Proof.Ed25519.RISCV64.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_gf25519_r32_mul` on RISC-V: correctness

For a working space `ws` whose address is a multiple of 8 (`hal`, which the
contract does not state yet), the function copies `a` and `b` to its own
working space (`unpackField_ok`), multiplies them there (`mulAt_ok`, X25519's
product with 64-bit limbs) and copies the product to `o` (`packField_ok`): the result is
congruent to `a b`, and it writes only its own working space and `o`
(`mulFn_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Spec.X25519 (P)
open VG.Proof.X25519.Field32 (valAt Fits Keeps)
open VG.Proof.X25519 (val32_congr)

/-- An offset argument, the low word of its register. -/
abbrev offArg (s : State) (r : Reg) : BitVec 32 := (s.gpr r).setWidth 32

/-- A register zero-extended from its low word by two shifts. -/
theorem zext_shifts (x : BitVec 64) : (x <<< 32) >>> 32 = BitVec.ofNat 64 (x.setWidth 32).toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_shr, toNat_shl, show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 from rfl, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (Nat.two_pow_pos _), BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))]

/-- The element at `o` of `ws`, as read by `valAt`. -/
theorem valAt_eq (m : Mem) (ws : Addr) (o : BitVec 32) : valAt m ws o = V m (ws + BitVec.ofNat 64 o.toNat) 0 := by
  rw [valAt, ← read_V, BitVec.add_zero]; rfl

/-- What `mul` writes: its own working space and the result. -/
abbrev mulW (ws : Addr) (o : Nat) : List Region := [⟨ws + BitVec.ofNat 64 768, 256⟩, ⟨ws + BitVec.ofNat 64 o, 32⟩]

/-- A byte of `ws` outside a range of it. -/
theorem byte_out {b : Addr} {i e k : Nat} (hi : i + 1 ≤ 4096) (he : e + k ≤ 4096) (h : i < e ∨ e + k ≤ i) :
    ¬ (⟨b + BitVec.ofNat 64 e, k⟩ : Region).Contains (b + BitVec.ofNat 64 i) 1 := fun hc =>
  Offset.disjoint b (d := i) (n := 1) (e := e) (k := k) (by omega) (by omega) (by omega) _ (Region.contains_self _ _) hc

theorem keeps_mul {ws : Addr} {o : BitVec 32} (ho : o.toNat + 32 ≤ 768) {m m' : Mem}
    (hf : Frame (mulW ws o.toNat) m m') : Keeps ws o m m' := by
  intro i hi hown hoi
  simp only [Proof.X25519.Field32.wsBytes, Proof.X25519.Field32.ownAt, Proof.X25519.Field32.ownEnd,
    Proof.X25519.Field32.elemBytes] at hi hown hoi
  refine hf _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact byte_out (by omega) (by omega) (by omega)
  · exact byte_out (by omega) (by omega) hoi

theorem mulFn_ok {s : State} (hrd : s.rd = []) (hwr : s.wr = [⟨s.gpr .a0, 4096⟩])
    (hO : Fits (offArg s .a1)) (hA : Fits (offArg s .a2)) (hB : Fits (offArg s .a3))
    (hal : (s.gpr .a0).toNat % 8 = 0) :
    WP isa mulFn s fun t =>
      valAt t.mem (s.gpr .a0) (offArg s .a1) % P =
        valAt s.mem (s.gpr .a0) (offArg s .a2) * valAt s.mem (s.gpr .a0) (offArg s .a3) % P ∧
      Frame (mulW (s.gpr .a0) (offArg s .a1).toNat) s.mem t.mem := by
  simp only [Fits, Proof.X25519.Field32.elemBytes, Proof.X25519.Field32.ownAt] at hO hA hB
  obtain ⟨ws, hws⟩ : ∃ ws, ws = s.gpr .a0 := ⟨_, rfl⟩
  rw [← hws] at hal hwr ⊢
  obtain ⟨O, hO'⟩ : ∃ O, O = (offArg s .a1).toNat := ⟨_, rfl⟩
  obtain ⟨A, hA'⟩ : ∃ A, A = (offArg s .a2).toNat := ⟨_, rfl⟩
  obtain ⟨B, hB'⟩ : ∃ B, B = (offArg s .a3).toNat := ⟨_, rfl⟩
  rw [← hO'] at hO ⊢
  rw [← hA'] at hA
  rw [← hB'] at hB
  have hMA : MA = 768 := rfl
  have hMB : MB = 800 := rfl
  have hMO : MO = 832 := rfl
  have hC : ACC = 864 := rfl
  have hin : (⟨ws, 4096⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  unfold mulFn mulZext mulPtrs mulIn
  simp only [List.cons_append, List.nil_append]
  refine WP.seq ?_
  refine wp_sll (by decide) fun s1 u1 => wp_srl (by decide) fun s2 u2 => wp_sll (by decide) fun s3 u3 =>
    wp_srl (by decide) fun s4 u4 => wp_sll (by decide) fun s5 u5 => wp_srl (by decide) fun s6 u6 =>
    WP.block_nil ?_
  refine WP.seq ?_
  refine wp_add fun s7 u7 => wp_add fun s8 u8 => wp_add fun s9 u9 => wp_mv fun s10 u10 => ?_
  have hr10 : Rest [.a1, .a2, .a3, .t2, .t4, .t5] s s10 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans
      ((u7.rest (by decide)).trans ((u8.rest (by decide)).trans ((u9.rest (by decide)).trans
      (u10.rest (by decide))))))))))
  have hm10 : s10.mem = s.mem := by
    rw [u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have g0 : ∀ t : State, Rest [.a1, .a2, .a3, .t2, .t4, .t5] s t → t.gpr .a0 = ws := fun t h => by
    rw [h.gpr _ (by decide), hws]
  have e1 : s6.gpr .a1 = BitVec.ofNat 64 O := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      u2.gpr, u1.gpr, zext_shifts, hO']
  have e2 : s6.gpr .a2 = BitVec.ofNat 64 A := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.gpr, u2.other _ (by decide),
      u1.other _ (by decide), zext_shifts, hA']
  have e3 : s6.gpr .a3 = BitVec.ofNat 64 B := by
    rw [u6.gpr, u5.gpr, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide), zext_shifts, hB']
  have e0 : s6.gpr .a0 = ws := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      u2.other _ (by decide), u1.other _ (by decide), hws]
  have p3 : s10.gpr .t2 = ws + BitVec.ofNat 64 O := by
    rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.gpr, e0, e1]
  have p4 : s10.gpr .t4 = ws + BitVec.ofNat 64 A := by
    rw [u10.other _ (by decide), u9.other _ (by decide), u8.gpr, u7.other .a0 (by decide), u7.other .a2 (by decide),
      e0, e2]
  have p5 : s10.gpr .t5 = ws + BitVec.ofNat 64 B := by
    rw [u10.other _ (by decide), u9.gpr, u8.other .a0 (by decide), u8.other .a3 (by decide),
      u7.other .a0 (by decide), u7.other .a3 (by decide), e0, e3]
  have h9 : Rest [.a1, .a2, .a3, .t2, .t4, .t5] s s9 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans
      ((u7.rest (by decide)).trans ((u8.rest (by decide)).trans (u9.rest (by decide)))))))))
  have e10 : s10.gpr .a3 = ws := by rw [u10.gpr, g0 s9 h9]
  have hc10 : Ctx ws s10 :=
    ⟨e10, hal, fun d n hd => by rw [hr10.wr]; exact in_base hin (by omega) (by omega)⟩
  have hrd10 : s10.rd ++ s10.wr = s.wr := by rw [hr10.rd, hr10.wr, hrd, List.nil_append]
  -- The operands into the own working space.
  refine WP.append (unpackField_ok hc10 (p := .t4) (by decide) p4 (o := MA) (src := 0) (by omega) (by decide)
    (by decide) (fun k hk => by rw [hrd10, Offset.add_add]; exact in_base hin (by omega) (by omega))
    (by rw [BitVec.add_zero]; exact Offset.disjoint _ (by omega) (by omega) (by omega)))
    fun s11 ⟨r11, f11, l11⟩ => ?_
  have hc11 : Ctx ws s11 := hc10.of_rest r11 (by decide)
  refine WP.mono (unpackField_ok hc11 (p := .t5) (q := ws + BitVec.ofNat 64 B) (by decide)
    (by rw [r11.gpr _ (by decide), p5])
    (o := MB) (src := 0) (by omega) (by decide) (by decide)
    (fun k hk => by rw [r11.rd, r11.wr, hrd10, Offset.add_add]; exact in_base hin (by omega) (by omega))
    (by rw [BitVec.add_zero]; exact Offset.disjoint _ (by omega) (by omega) (by omega)))
    fun s12 ⟨r12, f12, l12⟩ => ?_
  have hc12 : Ctx ws s12 := hc11.of_rest r12 (by decide)
  -- The operands' values.
  have va : V s12.mem ws MA = valAt s.mem ws (offArg s .a2) := by
    rw [V, val32_congr (limb_frame f12 fun r hr k hk => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega) (by omega) (by omega)),
      val32_congr l11, valAt_eq, ← hA', V, hm10]
    exact val32_congr fun k hk => by rw [limb, Nat.zero_add]
  have vb : V s12.mem ws MB = valAt s.mem ws (offArg s .a3) := by
    have hb11 : ∀ k < 8, wd s11.mem (ws + BitVec.ofNat 64 B) (4 * k) = wd s.mem (ws + BitVec.ofNat 64 B) (4 * k) :=
      fun k hk => by
        rw [wd_shift, wd_shift, wd_frame f11 fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega) (by omega) (by omega), hm10]
    rw [V, val32_congr l12, valAt_eq, ← hB', V]
    exact val32_congr fun k hk => by rw [Nat.zero_add, hb11 k hk, limb, Nat.zero_add]
  -- The product, and the copy to `o`.
  refine WP.seq (WP.mono (R64.mulAt_ok (acc := ACC) (o := MO) (x := MA) (y := MB) (by omega) (by decide)
    (by omega) (by omega) (by omega) (by decide) (by decide) (by decide) hc12) fun s13 ⟨r13, f13, v13⟩ => ?_)
  have hc13 : Ctx ws s13 := hc12.of_rest r13 (by decide)
  refine WP.mono (packField_ok hc13 (p := .t2) (by decide)
    (by rw [r13.gpr _ (by decide), r12.gpr _ (by decide), r11.gpr _ (by decide), p3])
    (a := MO) (dst := 0) (by omega) (by decide) (by decide)
    (fun k hk => by rw [r13.wr, r12.wr, r11.wr, hr10.wr, Offset.add_add]; exact in_base hin (by omega) (by omega))
    (by rw [BitVec.add_zero]; exact Offset.disjoint _ (by omega) (by omega) (by omega)))
    fun t ht => ⟨?_, ?_⟩
  · rw [valAt_eq, ← hO', V, val32_congr (g := limb s13.mem ws MO) fun k hk => by
      rw [limb, ← ht.outs k hk, Nat.zero_add], ← V, v13, va, vb]
  · -- Every write is in the own working space or at `o`.
    have sub_own : ∀ d n, 768 ≤ d → d + n ≤ 1024 →
        ∀ r ∈ ([⟨ws + BitVec.ofNat 64 d, n⟩] : List Region), ∃ r' ∈ mulW ws O, r.Sub r' :=
      fun d n h1 h2 r hr => ⟨_, List.mem_cons_self .., by
        rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)⟩
    have f13' : Frame (mulW ws O) s12.mem s13.mem := f13.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by omega) (by omega)⟩
      · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by omega) (by omega)⟩
    have ft : Frame (mulW ws O) s13.mem t.mem := ht.frame.sub fun r hr => ⟨_, List.mem_cons_of_mem _
      (List.mem_singleton_self _), by rw [List.mem_singleton.mp hr, BitVec.add_zero]; exact Region.sub_prefix (by omega)⟩
    rw [← hm10]
    exact ((f11.sub (sub_own MA 32 (by omega) (by omega))).trans (f12.sub (sub_own MB 32 (by omega) (by omega)))).trans
      (f13'.trans ft)

end VG.Proof.Ed25519.RISCV64
