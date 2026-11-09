module

public import VerifiedGarbage.Proof.RsaPss.X86.CtHash
import VerifiedGarbage.Proof.RsaPss.X86.CtSel
public import VerifiedGarbage.Proof.Mgf1.Basic
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPss.X86.CtInit
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86.SseDword
public import VerifiedGarbage.Proof.RsaPss.X86.CtBase

/-!
# RSASSA-PSS on x86: facts for `DB ⊕= MGF1(H, dbLen)`

The slots and `EM`'s place miss what hashing writes (`ctW_slot`, `ctW_em`),
and the counter's bytes, big-endian (`ctrByte`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.Proof.MdStream (Md)

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- The hash function as MGF1 takes it has digests of `hLen` bytes. -/
theorem PssHash.valid : Proof.Mgf1.Valid h.G := by
  refine ⟨by rw [h.glen]; exact h.D_pos, fun x => ?_⟩
  rw [h.hash, h.ok.link.hash, List.length_take, Md.hash, h.md.digest_length, h.glen]
  exact Nat.min_eq_left h.D_le

/-- A slot is in what the body may write. -/
theorem slotW (hg : Geo L scr) {d : Nat} (hd : d + 4 ≤ frameBytes) : ∃ R ∈ L.W, Region.Sub (slotR L d) R :=
  ⟨L.FR, List.mem_cons_self, Offset.sub_base _ (by rw [hg.F]; exact hd)⟩

/-- Two slots apart. -/
theorem slotSep {d e : Nat} (hd : d + 4 ≤ frameBytes) (he : e + 4 ≤ frameBytes) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (slotR L d).Disjoint (slotR L e) :=
  Lay.fr_sep h (by unfold frameBytes at hd; omega_arith) (by unfold frameBytes at he; omega_arith)

/-- A slot other than `sLb` and `sBi` misses `ctW`. -/
theorem ctW_slot (hg : Geo L scr) {T : Nat} (hT : T ≤ 2048) {d : Nat} (hd : d + 4 ≤ frameBytes)
    (hb : d + 4 ≤ sBi ∨ sBi + 4 ≤ d) (hl : d + 4 ≤ sLb ∨ sLb + 4 ≤ d) :
    ∀ r ∈ ctW h L scr T, (slotR L d).Disjoint r := by
  have hN := h.N_le
  have hB := h.B_le
  have hso := h.so_le
  obtain ⟨σ', ok⟩ := hg.ok
  have hF : d + 4 ≤ L.F + 16 := by rw [hg.F]; omega_arith
  have hC : L.C ≤ 2 ^ 32 := by have := ok.BC; have := L.B.isLt; omega_arith
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hg.slot ok (by pomega) hF
  · exact Lay.fr_low (by unfold frameBytes at hd; omega_arith) hC
  · exact hg.slot ok (by pomega) hF
  · exact slotSep hd (by decide) hl
  · exact hg.slot ok (by pomega) hF
  · exact hg.slot ok (by pomega) hF
  · exact hg.slot ok (by pomega) hF
  · exact slotSep hd (by decide) hb
  · exact hg.slot ok (by pomega) hF

/-- A range of `EM`'s place misses `ctW`. -/
theorem ctW_em (hg : Geo L scr) {T : Nat} (hT : T ≤ 2048) {o n : Nat} (h₁ : oEm ≤ o) (h₂ : o + n ≤ oY) :
    ∀ r ∈ ctW h L scr T, (sR scr o n).Disjoint r := by
  have hN := h.N_le
  have hB := h.B_le
  have hso := h.so_le
  obtain ⟨σ', ok⟩ := hg.ok
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Geo.sep (by pomega) (by pomega) (by pomega)
  · exact hg.low ok (by pomega)
  · exact Geo.sep (by pomega) (by pomega) (by pomega)
  · exact (hg.slot ok (by pomega) (by rw [hg.F]; decide)).symm
  · exact Geo.sep (by pomega) (by pomega) (by pomega)
  · exact Geo.sep (by pomega) (by pomega) (by pomega)
  · exact Geo.sep (by pomega) (by pomega) (by pomega)
  · exact (hg.slot ok (by pomega) (by rw [hg.F]; decide)).symm
  · exact Geo.sep (by pomega) (by pomega) (by pomega)

/-- The counter's bytes. -/
theorem i2osp4_getD (c j : Nat) (hj : j < 4) :
    (Spec.Rsa.i2osp c 4).getD j 0 = BitVec.ofNat 8 (c / 256 ^ (3 - j)) := by
  simp [Spec.Rsa.i2osp, List.getD_eq_getElem?_getD, hj]

theorem i2osp4_length (c : Nat) : (Spec.Rsa.i2osp c 4).length = 4 := by simp [Spec.Rsa.i2osp]

/-- Bit `8k + j` of a word with its bytes reversed. -/
theorem bswap_bit (v : BitVec 32) {k j : Nat} (hk : k < 4) (hj : j < 8) :
    (bswap v).getLsbD (8 * k + j) = v.getLsbD (8 * (3 - k) + j) := by
  unfold bswap
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  repeat' split
  all_goals first | omega_arith | (rw [decide_eq_true (by omega_arith), Bool.true_and]; congr 1; omega_arith)

/-- Byte `k` of the counter, big-endian. -/
theorem ctrByte {c : Nat} (hc : c < 2 ^ 32) {k : Nat} (hk : k < 4) :
    (bswap (BitVec.ofNat 32 c)).extractLsb' (8 * k) 8 = BitVec.ofNat 8 (c / 256 ^ (3 - k)) := by
  have e : (bswap (BitVec.ofNat 32 c)).extractLsb' (8 * k) 8 = (BitVec.ofNat 32 c).extractLsb' (8 * (3 - k)) 8 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    exact bswap_bit _ hk hi
  rw [e]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
    Nat.shiftRight_eq_div_pow, Nat.pow_mul]

/-- A byte of our part of `scratch` after a word is written there. -/
theorem sa_writeW32 (scr : BitVec 32) (m : Mem) {o i : Nat} (v : BitVec 32) (ho : o + 4 < 2 ^ 64)
    (hi : i < 2 ^ 64) :
    (m.writeW (sa scr o) v) (sa scr i) = if o ≤ i ∧ i < o + 4 then v.extractLsb' (8 * (i - o)) 8 else m (sa scr i) := by
  by_cases e : o ≤ i ∧ i < o + 4
  · rw [ite_eq_left e, show sa scr i = sa scr o + BitVec.ofNat 64 (i - o) by
      rw [sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' e.1]]
    exact VG.X86.writeW_byte m _ v (by omega_arith) (by decide)
  · rw [ite_eq_right e]
    refine VG.X86.writeW_byte_off m _ v _ ?_
    rw [sa, sa, Offset.sub_toNat' _ (by omega_arith) hi]
    split <;> omega_arith

/-! ## The parameters and the stages of an iteration -/

end VG.Proof.RsaPss.X86
