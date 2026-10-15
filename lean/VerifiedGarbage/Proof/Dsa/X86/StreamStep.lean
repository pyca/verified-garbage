module

public import VerifiedGarbage.Proof.Dsa.X86.FetchByte
public import VerifiedGarbage.Proof.Dsa.X86.Reduce

/-! # A bounded streaming reduction iteration -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic VG.Impl.Dsa.X86

def streamRanges (n : Nat) : List (Nat × Nat) :=
  [(slot n 7, 8 * n), (slot n 6, 8 * n), (slot n 1, 8 * n), (slot n 2, 16 * n + 4)]

theorem counter_equal {i len : Nat} (hi : i < 2 ^ 32) (hl : len < 2 ^ 32) :
    (BitVec.ofNat 32 i - BitVec.ofNat 32 len == 0) = decide (i = len) := by
  apply Bool.eq_iff_iff.mpr
  have za : ∀ x : BitVec 32, 0 + x = x := BitVec.zero_add
  simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add, za]
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hl] using h'
  · rintro rfl; rfl

theorem streamStep_ok {n size m i len : Nat} {base : Addr} {s : State} {p : BitVec 32}
    (h : Context n m base size s) (hm : 255 < m) (hi : i < len) (hlen : len < 2 ^ 32)
    (hp : s.mem.readW (off base sourcePointer) 32 = p) (hc : s.gpr .esi = BitVec.ofNat 32 i)
    (hfit : p.toNat + len ≤ 2 ^ 32)
    (hr : InRegions (s.rd ++ s.wr) (p.setWidth 64 + BitVec.ofNat 64 i) 1)
    (hv : wordsVal s.mem base (slot n 6) n < m)
    (hpad : wordsVal s.mem base (slot n 7) n < 2 ^ 32) :
    WP isa (.block (streamStep n len)) s fun t =>
      Context n m base size t ∧ t.gpr .esi = BitVec.ofNat 32 (i + 1) ∧ t.zf = some (decide (i + 1 = len)) ∧
      wordsVal t.mem base (slot n 6) n =
        (256 * wordsVal s.mem base (slot n 6) n + (s.mem (p.setWidth 64 + BitVec.ofNat 64 i)).toNat) % m ∧
      wordsVal t.mem base (slot n 7) n < 2 ^ 32 ∧
      Outs base (streamRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  have sz := h.size_le
  have nw := h.scr.nowrap
  have b6 := slot_bound (n := n) (i := 6) (by decide)
  have s06 := slot_le (n := n) (i := 0) (j := 7) (by decide)
  have s67 := slot_le (n := n) (i := 6) (j := 7) (by decide)
  have hd7 := slot_header n 7
  unfold streamStep
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (fetchByte_ok h.scr h.modulus.n0 h.size_le hp hc (by omega) hr hpad)
    fun u ⟨Bu, Ou, Ku⟩ => ?_)
  have cu := h.outside_keep Ku (by decide) (by decide) Ou
    (.inl (by unfold stride at s06; omega)) (by omega)
  have Yu : wordsVal u.mem base (slot n 6) n = wordsVal s.mem base (slot n 6) n := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact Ou.val32 (by unfold stride at s67; omega) (by unfold stride at b6; omega)
  have bu : wordsVal u.mem base (slot n 7) n < m := by
    rw [Bu]; have := (s.mem (p.setWidth 64 + BitVec.ofNat 64 i)).isLt; omega
  refine WP.block_append (WP.mono (reduceStep_ok cu (by rw [Yu]; exact hv) bu) fun v ⟨cv, Kv, Vv⟩ => ?_)
  have Bv := context_slot_val cu (i := 7) (by decide) (by decide) (by decide) (by decide) Kv
  have count : v.gpr .esi = BitVec.ofNat 32 i := by rw [Kv.gpr _ (by decide), Ku.1 _ (by decide), hc]
  refine wp_addS rfl fun w uw _ => ?_
  refine wp_cmpS rfl fun t ft zt => WP.block_nil ?_
  have mt : t.mem = v.mem := ft.mem.trans uw.mem
  have kt : Keeps powerClob v t := (uw.keeps.mono (by decide)).trans (ft.keeps _)
  have ct : Context n m base size t := ⟨cv.scr.of_keeps kt (by decide), cv.size_le,
    mt ▸ cv.modulus, cv.gt_one, mt ▸ cv.inverse⟩
  have plus : w.gpr .esi = BitVec.ofNat 32 (i + 1) := by rw [uw.gpr, count, BitVec.ofNat_add]; rfl
  refine ⟨ct, by rw [ft.gpr, plus], ?_, ?_, ?_, ?_, ?_⟩
  · rw [zt, plus, counter_equal (by omega) hlen]
  · rw [mt, Vv, Yu, Bu]
  · rw [mt, Bv, Bu]
    exact Nat.lt_of_lt_of_le (s.mem (p.setWidth 64 + BitVec.ofNat 64 i)).isLt (by decide)
  · have ou : Outs base (streamRanges n) s.mem u.mem := Outs.of_outside (Ou.mono (n' := 8 * n) (Nat.le_refl _) (by have := h.modulus.n0; change 0 < n at this; omega)) (by simp [streamRanges])
    have ov : Outs base (streamRanges n) u.mem v.mem := Kv.mem.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [streamRanges, contextMod, accLen, words] <;> omega)
    rw [mt]; exact ou.trans ov
  · exact (((Ku.mono (by decide)).trans ((OpKeep.keeps Kv).mono (by decide))).trans kt)

end VG.Proof.Dsa.X86
