module
public import VerifiedGarbage.Impl.Rsa.X86.Inverse
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.KeyMath
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs

import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Rsa.X86.KeyBits
import VerifiedGarbage.Proof.Rsa.X86.KeyHalf
import VerifiedGarbage.Proof.Rsa.X86.KeySelect
import VerifiedGarbage.Proof.Rsa.X86.KeySub
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # `inverse` on i686: the halving modulo `m` at the end of a step -/

@[expose] public section

namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Proof.Rsa.KeyBits32
open VG.Proof.Rsa (subMod halfMod)

/-- The halving of `[aT3]` modulo `m` into `[o]`. -/
def halfModP (w o : Nat) : List (Prog isa) := [
  .block (bitOf w sB aT3), sel w aT4 aZero aNM sB, sub3 w o aT3 aT4,
  .block [.alu .xor .ebx (.mem (VG.Impl.Mont.X86.sc sB))], half w o]

theorem halfModP_ok {s : State} {B : Addr} {Z w N o : Nat} (h : Ws s B Z w N)
    (hN15 : 15 ≤ N) (ho : o < N) (hoT3 : o ≠ aT3) (hoT4 : o ≠ aT4) :
    WP isa (seqs (halfModP w o)) s fun t => Ws t B Z w N ∧ Keep B w [aT4, o] [sB] s.mem t.mem ∧
      (num s.mem B w aNM + num s.mem B w aM = 2 ^ (32 * w) → num s.mem B w aZero = 0 →
        num t.mem B w o = halfMod (num s.mem B w aM) (num s.mem B w aT3)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have hsB : sB + 4 ≤ hdr := by decide
  simp only [aT3, aT4] at hoT3 hoT4
  unfold halfModP
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (bitOf_ok h (by idx) hsB) fun t1 ⟨h1, k1, s1, r1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have b1 : slot t1.mem B sB ≤ 1 := by rw [s1]; omega
  refine WP.mono (sel_ok h1 (by idx) (by idx) (by idx) hsB b1)
    fun t2 ⟨h2, k2, v2, r2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h2 ho (by idx) (by idx) hoT3 hoT4) fun t3 ⟨h3, k3, v3, b3, r3⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine wp_logicS (.inr rfl) (readSrc_sc h3.workspace (by have := h3.hdr_le; unfold sB hdr at *; omega))
    fun t4 u5 => WP.block_nil ?_
  have h5 := h3.rest u5.keeps (by decide) (by decide)
  have sB3 : slot t3.mem B sB = slot t1.mem B sB := by
    rw [k3.slot hsB (by simp), k2.slot hsB (by simp)]
  have c4 : (t4.gpr .ebx).toNat = ((t3.gpr .ebx).toNat + num s.mem B w aT3 % 2) % 2 := by
    rw [u5.gpr, ite_eq_right (by decide)]
    have e : (t3.mem.readW (off B sB) 32).toNat = num s.mem B w aT3 % 2 := by
      change slot t3.mem B sB = _; rw [sB3, s1]
    rw [bv_xor_bits b3 (by rw [e]; omega), e]
  refine WP.mono (half_ok h5 ho (by rw [c4]; omega)) fun t ⟨h6, k6, v6, r6⟩ => ?_
  have m4 : t4.mem = t3.mem := u5.mem
  rw [m4] at k6 v6
  refine ⟨h6, (k1.join k2 (js := [aT4, o]) (ds := [sB])).join (k3.join k6 (js := [aT4, o]) (ds := [sB]))
      (js := [aT4, o]) (ds := [sB]), fun hNM hZ => ?_,
    (r1.mono (by decide)).trans ((r2.mono (by decide)).trans (r3.trans ((u5.keeps.mono (by decide)).trans (r6.mono (by decide)))))⟩
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

end VG.Proof.Rsa.X86.Keys
