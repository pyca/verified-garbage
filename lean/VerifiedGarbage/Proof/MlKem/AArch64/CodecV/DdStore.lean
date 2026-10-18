module

public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdLoop

/-!
# ML-KEM on AArch64: storing decompressed coefficients

Two vectors stored as the next eight coefficients of the output (`wp_strq2`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DD

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.CodecV
open VG.Spec.MlKem

theorem num1 {w : Width} (hw : w.nb = 1) (s₀ : State) (g : Nat) : num w s₀ g 1 = byte w s₀ g := by
  simp [num, digits, hw]

/-- What a store of coefficients keeps of the state. -/
structure StFr (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  v : t.v = s.v
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem StFr.trans {s t u : State} (h : StFr s t) (h' : StFr t u) : StFr s u :=
  ⟨h'.gpr.trans h.gpr, h'.v.trans h.v, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

theorem StFr.refl (s : State) : StFr s s := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `a` and `b` stored at `x3 + o`, coefficients `t … t + 7`. -/
theorem wp_strq2 {s : State} {p : Addr} {m₀ : Mem} {a b : VReg} {o t : Nat} {Gf old : Nat → BitVec 32}
    {is : List Instr} {Q : State → Prop}
    (hw : ∀ i, i + 4 ≤ 256 → InRegions s.wr (coeffAddr p i) 16)
    (h3 : s.gpr .x3 + BitVec.ofNat 64 o = coeffAddr p t) (ho : o % 16 = 0 ∧ o + 16 < 4096 * 16)
    (ht : t + 8 ≤ 256) (hc : CoeffsUpTo s.mem p t Gf old) (hf : Frame [polyRegion p] m₀ s.mem)
    (ha : ∀ e < 4, vword (s.v a) e = Gf (t + e)) (hb : ∀ e < 4, vword (s.v b) e = Gf (t + 4 + e))
    (k : ∀ s', StFr s s' → CoeffsUpTo s'.mem p (t + 8) Gf old → Frame [polyRegion p] m₀ s'.mem →
      WP isa (.block is) s' Q) :
    WP isa (.block (.strq a .x3 o :: .strq b .x3 (o + 16) :: is)) s Q := by
  refine wp_strq (a := coeffAddr p t) ⟨ho.1, by omega⟩ h3 (hw t (by omega)) fun s1 h1 => ?_
  refine wp_strq (a := coeffAddr p (t + 4)) ⟨by omega, ho.2⟩
    (by rw [h1.gpr, ← ptr_add, h3]; exact coeffAddr_step _ _) (by rw [h1.wr]; exact hw _ (by omega))
    fun s2 h2 => k s2 ⟨by rw [h2.gpr, h1.gpr], by rw [h2.v, h1.v], by rw [h2.rd, h1.rd],
      by rw [h2.wr, h1.wr], by rw [h2.sp, h1.sp]⟩ ?_ ?_
  · rw [h2.mem, h1.v, h1.mem, show t + 8 = t + 4 + 4 by omega]
    exact (hc.write16 (by omega) ha).write16 (by omega) hb
  · rw [h2.mem, h1.mem]
    exact frame16 (frame16 hf (by omega) _) (by omega) _

end VG.Proof.MlKem.AArch64.DD
