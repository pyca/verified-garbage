module

public import VerifiedGarbage.Impl.Mont.ArmPacked
public import VerifiedGarbage.Proof.Mont.Arm.Step
import VerifiedGarbage.Proof.Mont.Arm.Row
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Convert the packed accumulator to the existing reducer's digit format. -/

@[expose] public section
namespace VG.Proof.Mont.Arm.Packed
open VG VG.Arm VG.Proof.Mont VG.Proof.Mont.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Packed
open VG.Proof.X25519.Arm (Rest wp_str wp_movw mask16)

def expandSteps (acc dst k : Nat) : List Instr :=
  (List.range k).flatMap fun j => digitAt .r12 acc j ++ [.str .r7 .r12 (dst + 4 * j)]

 theorem expandSteps_ok {s : State} {base : Addr} {size acc dst n : Nat}
    (hs : Scr s base size) (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16)
    (src : acc + 4 * ((n + 1) / 2) ≤ dst) (fit : dst + 4 * n ≤ size) :
    ∀ k, k ≤ n → WP isa (.block (expandSteps acc dst k)) s fun t =>
      Outside base dst (4 * k) s.mem t.mem ∧ Digs t.mem base dst k ∧
      dval t.mem base dst k = pval s.mem base acc k ∧ Rest [.r7] s t
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _), rfl, Rest.refl _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    have eq : expandSteps acc dst (k + 1) = expandSteps acc dst k ++
        (digitAt .r12 acc k ++ [.str .r7 .r12 (dst + 4 * k)]) := by
      simp only [expandSteps, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rw [eq]
    refine VG.Proof.X25519.Arm.WP.append (expandSteps_ok hs h6 src fit k (by omega))
      fun u ⟨out, digs, val, rest⟩ => ?_
    have hu := hs.of_rest rest (by decide)
    refine digitAt_ok hu (K := 0) (by simp) (Nat.zero_add _)
      (by rw [rest.gpr _ (by decide)]; exact h6) (by omega) fun v uv => ?_
    have hv := hu.of_rest (uv.rest (ws := [.r7]) (by simp)) (by decide)
    refine wp_str (hv.off_lt (by omega)) (hv.ea (by omega)) (hv.write (by omega)) fun t vt => WP.block_nil ?_
    have old : pdig u.mem base acc k = pdig s.mem base acc k := by
      unfold pdig hdig
      rw [out.w32 (by omega) (by omega)]
    have pdlt : pdig s.mem base acc k < 2 ^ 16 := hdig_lt _ _
    have mem : t.mem = u.mem.writeW (off base (dst + 4 * k)) (BitVec.ofNat 32 (pdig s.mem base acc k)) := by
      rw [vt.mem, uv.mem, uv.gpr, old]
    have wr := writeW32_outside u.mem base (d := dst + 4 * k)
      (BitVec.ofNat 32 (pdig s.mem base acc k)) (by omega)
    rw [← mem] at wr
    have low := wr.dval (d := dst) (k := k) (by omega) (by omega)
    have top : w32 t.mem base (dst + 4 * k) = pdig s.mem base acc k := by
      rw [mem, w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine ⟨(out.mono (Nat.le_refl _) (by omega)).trans (wr.mono (by omega) (by omega)), ?_, ?_,
      rest.trans ((uv.rest (by simp)).trans (vt.rest _))⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [wr.w32 (by omega) (by omega)]; exact digs j hj
      · rw [top]; exact pdlt
    · rw [dval, low, top, val, pval]

 theorem expand_ok {s : State} {base : Addr} {size acc dst n : Nat}
    (hs : Scr s base size) (src : acc + 4 * ((n + 1) / 2) ≤ dst) (fit : dst + 4 * n ≤ size) :
    WP isa (.block (expand acc dst n)) s fun t =>
      Outside base dst (4 * n) s.mem t.mem ∧ Digs t.mem base dst n ∧
      dval t.mem base dst n = pval s.mem base acc n ∧ Rest [.r6, .r7] s t := by
  simp only [expand, List.cons_append, List.nil_append]
  refine wp_movw fun u uu => ?_
  refine WP.mono (expandSteps_ok (hs.of_rest (uu.rest (ws := [.r6, .r7]) (by simp)) (by decide))
    uu.gpr src fit n (Nat.le_refl _)) fun t ⟨out, digs, val, keep⟩ => ?_
  rw [uu.mem] at out val
  exact ⟨out, digs, val, (uu.rest (by simp)).trans (keep.mono (by simp))⟩

end VG.Proof.Mont.Arm.Packed
