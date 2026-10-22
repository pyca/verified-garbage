module

public import VerifiedGarbage.Impl.Rsa.X86.KeyRt.CountEven
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Word
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
public import VerifiedGarbage.Proof.Rsa.KeyBits32
public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! Reuse RSA's parity counter while preparing a primality exponent. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Keep num slot)
open VG.Impl.Rsa.X86.KeyRt (Lay)

theorem count_even {L : Lay} {s : State} {base : Addr} {bytes len count j : Nat}
    (h : RtWs L s base bytes len count) (hj : j < count) (bound : slot s.mem base 20 ≤ 16384) :
    WP isa (.block (Impl.Rsa.X86.KeyRt.countEven L 28 20 j)) s fun t =>
      RtWs L t base bytes len count ∧ Keep base (kw len) [] [28, 20] s.mem t.mem ∧
      slot t.mem base 28 = 1 - num s.mem base (kw len) j % 2 ∧
      slot t.mem base 20 = slot s.mem base 20 + (1 - num s.mem base (kw len) j % 2) ∧
      Keeps [.eax, .edx] s t := by
  unfold Impl.Rsa.X86.KeyRt.countEven
  refine WP.block_append (WP.mono (bitOf_ok h hj (by decide : 28 + 4 ≤ Impl.Rsa.X86.Keys.hdr)) ?_)
  rintro u ⟨hu, F, parity, K⟩
  have head : 160 ≤ bytes := hu.ws.hdr_le
  refine wp_movS (readSrc_sc hu.ws.workspace (d := 28) (by omega)) fun v V _ =>
    wp_logicS (Or.inr rfl) rfl fun w W => ?_
  have even : (w.gpr .eax).toNat = 1 - num s.mem base (kw len) j % 2 := by
    rw [W.gpr, ite_eq_right (by decide), V.gpr]
    rw [VG.Proof.Rsa.KeyBits32.bv_xor_bits (by change slot u.mem base 28 ≤ 1; omega) (by decide)]
    change (slot u.mem base 28 + 1) % 2 = _
    rw [parity]
    omega
  have Kw : Keeps [.eax, .edx] s w := (K.trans (V.keeps.mono (by decide))).trans (W.keeps.mono (by decide))
  have hw := hu.keep (V.keeps.trans W.keeps) (by decide) (by decide)
    (by rw [W.mem, V.mem]; exact Outside.refl _ _ _ _)
  refine WP.block_append (WP.mono (storeSlot_ok hw (by decide : 28 + 4 ≤ Impl.Rsa.X86.Keys.hdr) .eax) ?_)
  rintro x ⟨hx, Fx, bit, Kx⟩
  rw [even] at bit
  rw [W.mem, V.mem] at Fx
  have FF : Keep base (kw len) [] [28, 20] s.mem x.mem := F.join Fx
  have counter' : slot x.mem base 20 = slot s.mem base 20 :=
    (Fx.slot (by decide) (by simp)).trans (F.slot (by decide) (by simp))
  have headx : 160 ≤ bytes := hx.ws.hdr_le
  refine wp_movS (readSrc_sc hx.ws.workspace (d := 20) (by omega)) fun y Y _ =>
    wp_addS rfl fun z Z _ => ?_
  have total : (z.gpr .edx).toNat = slot s.mem base 20 + (1 - num s.mem base (kw len) j % 2) := by
    rw [Z.gpr, BitVec.toNat_add, Y.gpr, Y.other .eax (by decide), Kx.1 .eax (by simp), even]
    change (slot x.mem base 20 + _) % 2 ^ 32 = _
    rw [counter', Nat.mod_eq_of_lt (by omega)]
  have hz := hx.keep (Y.keeps.mono (rs' := [.edx]) (by decide) |>.trans Z.keeps) (by decide) (by decide)
    (by rw [Z.mem, Y.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (storeSlot_ok hz (by decide : 20 + 4 ≤ Impl.Rsa.X86.Keys.hdr) .edx) ?_
  rintro t ⟨ht, Ft, value, Kt⟩
  rw [total] at value
  rw [Z.mem, Y.mem] at Ft
  exact ⟨ht, FF.join Ft, (Ft.slot (by decide) (by simp)).trans bit, value,
    (((Kw.trans (Kx.mono (by simp))).trans (Y.keeps.mono (by decide))).trans
      (Z.keeps.mono (by decide))).trans (Kt.mono (by simp))⟩

end VG.Proof.Dsa.X86.Generation
