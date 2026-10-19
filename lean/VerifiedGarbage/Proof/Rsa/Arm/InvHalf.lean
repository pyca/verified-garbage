module
public import VerifiedGarbage.Impl.Rsa.Arm.Inverse
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
public import VerifiedGarbage.Proof.Rsa.KeyMath

import VerifiedGarbage.Proof.Rsa.Arm.InvParts
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits

/-! # `inverse` on ARMv7: the halving modulo `m` at the end of a step -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm
open VG.Proof.Rsa (subMod halfMod)

/-- The halving of `[aT3]` modulo `m` into `[o]`. -/
def halfModP (o : Nat) : List (Prog isa) := [
  .block (bitOf sB aT3), sel aT4 aZero aNM sB, sub3 o aT3 aT4,
  .block [.ldr .r1 .r8 sB, .dp .eor .r11 .r11 (.reg .r1)], half o]

theorem halfModP_ok {s : State} {B : BitVec 32} {Z w N o : Nat} (h : Ws s B Z w N)
    (hN15 : 15 ≤ N) (hN : N ≤ 256) (ho : o < N) (hoT3 : o ≠ aT3) (hoT4 : o ≠ aT4) :
    WP isa (seqs (halfModP o)) s fun t => Ws t B Z w N ∧ Keep B w [aT4, o] [sB] s.mem t.mem ∧
      (num s.mem B w aNM + num s.mem B w aM = 2 ^ (32 * w) → num s.mem B w aZero = 0 →
        num t.mem B w o = halfMod (num s.mem B w aM) (num s.mem B w aT3)) ∧
      Rest opRegs s t := by
  have hsB : sB + 4 ≤ hdr := by decide
  simp only [aT3, aT4] at hoT3 hoT4
  unfold halfModP
  rw [wp_seqs_cons (List.cons_ne_nil _ _), ← List.append_nil (bitOf sB aT3)]
  refine bitOf_ok h (by idx) hN hsB fun t1 h1 k1 s1 r1 => WP.block_nil ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have b1 : slot t1.mem B sB ≤ 1 := by rw [s1]; omega
  refine WP.mono (sel_ok h1 (by idx) (by idx) (by idx) hN (by idx) (by idx) hsB b1)
    fun t2 ⟨h2, k2, v2, r2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h2 ho (by idx) (by idx) hN hoT3 hoT4) fun t3 ⟨h3, k3, v3, b3, r3⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine wp_ldrSlot h3 hsB fun s4 u4 => ?_
  have h4 := h3.of_upd u4 (by decide) (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun t4 u5 => WP.block_nil ?_
  have h5 := h4.of_upd u5 (by decide) (by decide) (by decide)
  have sB3 : slot t3.mem B sB = slot t1.mem B sB := by
    rw [k3.slot hsB (by simp), k2.slot hsB (by simp)]
  have c4 : (t4.gpr .r11).toNat = ((t3.gpr .r11).toNat + num s.mem B w aT3 % 2) % 2 := by
    rw [u5.gpr, dpVal, u4.gpr, u4.other .r11 (by decide)]
    have e : (t3.mem.readW (off (State.addr B) sB) 32).toNat = num s.mem B w aT3 % 2 := by
      change slot t3.mem B sB = _; rw [sB3, s1]
    rw [bv_xor_bits b3 (by rw [e]; omega), e]
  refine WP.mono (half_ok h5 ho hN (by rw [c4]; omega)) fun t ⟨h6, k6, v6, r6⟩ => ?_
  have m4 : t4.mem = t3.mem := u5.mem.trans u4.mem
  rw [m4] at k6 v6
  refine ⟨h6, (k1.join k2 (js := [aT4, o]) (ds := [sB])).join (k3.join k6 (js := [aT4, o]) (ds := [sB]))
      (js := [aT4, o]) (ds := [sB]), fun hNM hZ => ?_,
    r1.trans (r2.trans (r3.trans ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans r6))))⟩
  have f3 := h.fit64 (j := aT3) (by idx)
  have fz := h.fit64 (j := aZero) (by idx)
  have fn := h.fit64 (j := aNM) (by idx)
  have x2 : num t2.mem B w aT3 = num s.mem B w aT3 := by
    rw [k2.num (by idx) (by simp) f3, k1.num (by simp) (by simp; decide) f3]
  have z1 : num t1.mem B w aZero = 0 := by rw [k1.num (by simp) (by simp; decide) fz, hZ]
  have n1 : num t1.mem B w aNM = num s.mem B w aNM := k1.num (by simp) (by simp; decide) fn
  rw [x2] at v3
  rw [s1, z1, n1] at v2
  rw [v6, c4]
  refine halfMod_impl (P := 2 ^ (32 * w)) (by omega) (val32_lt _ _ _ _) ?_ v3 (val32_lt _ _ _ _) b3 rfl
  rw [v2]; split <;> omega

end VG.Proof.Rsa.Arm.Keys
