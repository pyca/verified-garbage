module

public import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Avx2
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Basic
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLanes
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VMem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-DSA on x86-64: coefficients in the lanes of AVX2 registers

The AVX2 code does to each 128-bit lane what the SSE2 code does to a register
(`toY`), so the proofs of the SSE2 code hold of each lane (`ylanes`,
ML-KEM's): `YConsts` is `VConsts` in both lanes (`yconsts_ok`); lane `l` of a
256-bit load of coefficient `j` holds coefficients `j + 4l` to `j + 4l + 3`
(`lane_load`), and a 256-bit store at coefficient `j` writes coefficients `j`
to `j + 7` (`coeffAt_write256`, `frame_write2Y`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep XOnly XKeep YOnly ylanes yld_ok yconst_ok ifp ifn)
open VG.Spec.MlDsa (q n Poly Zq)
open VG.Proof.MlDsa (coeffAt polyAt PolyIs)

/-- `VConsts` in both lanes. -/
def YConsts (s : State) : Prop := ∀ l < 2, VConsts (s.proj l)

theorem yonly_yconsts {rs : List XReg} {s s' : State} (h : YOnly rs s s') (hc : YConsts s)
    (h14 : XReg.xmm14 ∉ rs) (h15 : XReg.xmm15 ∉ rs) : YConsts s' := fun l hl =>
  ⟨by rw [State.proj_xmm, h.lane _ h15 l hl]; exact (hc l hl).q,
    by rw [State.proj_xmm, h.lane _ h14 l hl]; exact (hc l hl).qinv⟩

/-- The constants in both lanes. -/
theorem yconsts_ok (s : State) :
    WP isa (.block yconsts) s fun s' => YConsts s' ∧ Keep [.rax] s s' ∧ s'.mem = s.mem ∧
      s'.mxcsr = s.mxcsr ∧ ∀ r, r ≠ .xmm15 → r ≠ .xmm14 → ∀ l < 2, s'.lane r l = s.lane r l := by
  rw [yconsts, WP.block_append_iff]
  refine WP.mono (yconst_ok .xmm15 _ s) fun s1 ⟨l1, k1, m1, x1, o1⟩ =>
    WP.mono (yconst_ok .xmm14 _ s1) fun s2 ⟨l2, k2, m2, x2, o2⟩ =>
      ⟨fun l hl => ⟨?_, ?_⟩, (k1.trans k2).mono (by simp), m2.trans m1, x2.trans x1,
        fun r h15 h14 l hl => by rw [o2 r h14 l hl, o1 r h15 l hl]⟩
  · rw [State.proj_xmm, o2 _ (by decide) l hl, l1 l hl]; decide
  · rw [State.proj_xmm, l2 l hl]; decide

/-- The eight doublewords of a 256-bit value, as those of its lanes. -/
theorem extract_ymm (hi lo : BitVec 128) {e : Nat} (he : e < 8) :
    (hi ++ lo).extractLsb' (32 * e) 32 = if e < 4 then dword lo e else dword hi (e - 4) := by
  by_cases h4 : e < 4
  · rw [ifp h4]
    apply BitVec.eq_of_getLsbD_eq; intro i hi'
    simp only [dword, BitVec.getLsbD_extractLsb', hi', decide_true, Bool.true_and, BitVec.getLsbD_append,
      ifp (show 32 * e + i < 128 by omega)]
  · rw [ifn h4]
    apply BitVec.eq_of_getLsbD_eq; intro i hi'
    simp only [dword, BitVec.getLsbD_extractLsb', hi', decide_true, Bool.true_and, BitVec.getLsbD_append,
      ifn (show ¬32 * e + i < 128 by omega)]
    exact congrArg _ (by omega)

/-- Coefficient `i` after storing `x` at coefficient `j`. -/
theorem coeffAt_write256 (m : Mem) (p : Addr) {j : Nat} (hj : j + 8 ≤ 256) (x : BitVec 256) {i : Nat}
    (hi : i < 256) :
    coeffAt (m.writeW (coeffAddr p j) x) p i =
      if j ≤ i ∧ i < j + 8 then x.extractLsb' (32 * (i - j)) 32 else coeffAt m p i := by
  split
  · rename_i h
    rw [coeffAt_eq, show coeffAddr p i = coeffAddr p j + BitVec.ofNat 64 (4 * (i - j)) by
      rw [coeffAddr_add, show j + (i - j) = i by omega]]
    rw [show 32 * (i - j) = 8 * (4 * (i - j)) by omega]
    exact readW_writeW_inside (k := 4 * (i - j)) (n := 4) _ _ _ (by omega) (by decide)
  · exact Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

theorem pR_contains32 (p : Addr) {j : Nat} (hj : j + 8 ≤ 256) : (pR p).Contains (coeffAddr p j) 32 :=
  Offset.contains_base p (by omega) (by omega)

theorem f_in32 {rs : List Region} {fP : Addr} (hw : pR fP ∈ rs) {j : Nat} (hj : j + 8 ≤ 256) :
    InRegions rs (coeffAddr fP j) 32 :=
  ⟨_, hw, pR_contains32 fP hj⟩

theorem frame_write2Y {m m' : Mem} {p : Addr} (hf : Frame [pR p] m m') {j j' : Nat} (hj : j + 8 ≤ 256)
    (hj' : j' + 8 ≤ 256) (x y : BitVec 256) :
    Frame [pR p] m ((m'.writeW (coeffAddr p j) x).writeW (coeffAddr p j') y) :=
  (hf.writeW (List.mem_singleton_self _) x (pR_contains32 p hj)).writeW (List.mem_singleton_self _) y
    (pR_contains32 p hj')

/-- Lane `l` of a 256-bit load of coefficient `j`. -/
theorem lane_load {p : Addr} {j l : Nat} :
    coeffAddr p j + BitVec.ofNat 64 (16 * l) = coeffAddr p (j + 4 * l) := by
  rw [show 16 * l = 4 * (4 * l) by omega, coeffAddr_add]

end VG.Proof.MlDsa.X86_64.Arith
