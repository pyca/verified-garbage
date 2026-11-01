module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointFn
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.LadderP
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The ladder by calls of the point functions, on PPC64LE: copies and calls

`copyPt n o a` copies the point at `a` to `o` (`copyPt_ok`), and
`ptCall S dbl` calls `vg_<curve>_point_double` or `vg_<curve>_point_add` on
the working space at `r3` (`ptCall_ok`): it changes only `fnClob`, `O` and
the point functions' own working space, and `O` then holds `rcbAdd` of what
`a`, `3b`, `P` and `Q` (or `P`) stood for (`fn_ok`). As on 32-bit ARM
(`Proof/Weierstrass/Arm/LadderPCall.lean`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Point

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Weierstrass.PPC64LE.Point
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont

/-- `o = a`, for points whose slots (`n` 64-bit words, at multiples of 4) are
in the working space, with `o`'s apart from each other and from `a`'s. -/
theorem copyPt_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {n : Nat} {o a : Pt}
    (h4 : ∀ d ∈ [o.x, o.y, o.z, a.x, a.y, a.z], d % 4 = 0)
    (hin : ∀ d ∈ [o.x, o.y, o.z, a.x, a.y, a.z], d + 8 * n ≤ size)
    (hoo : (o.x + 8 * n ≤ o.y ∨ o.y + 8 * n ≤ o.x) ∧ (o.x + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.x) ∧
      (o.y + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.y))
    (hoa : ∀ d ∈ [o.x, o.y, o.z], ∀ e ∈ [a.x, a.y, a.z], d + 8 * n ≤ e ∨ e + 8 * n ≤ d) :
    WP isa (.block (copyPt n o a)) s fun s' =>
      wordsVal s'.mem base o.x n = wordsVal s.mem base a.x n ∧
      wordsVal s'.mem base o.y n = wordsVal s.mem base a.y n ∧
      wordsVal s'.mem base o.z n = wordsVal s.mem base a.z n ∧
      Kp [.r4] s s' ∧ Outs base [(o.x, 8 * n), (o.y, 8 * n), (o.z, 8 * n)] s.mem s'.mem := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin hoa h4
  obtain ⟨iox, ioy, ioz, iax, iay, iaz⟩ := hin
  obtain ⟨⟨xax, xay, xaz⟩, ⟨yax, yay, yaz⟩, ⟨zax, zay, zaz⟩⟩ := hoa
  obtain ⟨xy, xz, yz⟩ := hoo
  obtain ⟨fox, foy, foz, fax, fay, faz⟩ := h4
  rw [copyPt, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copy_ok n hs h3 fox fax (by omega_using [iox]) (by omega_using [iax])
    (by omega_using [xax])) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok n (k₁.ws hs) (k₁.at h3) foy fay (by omega_using [ioy]) (by omega_using [iay])
    (by omega_using [yay])) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  refine WP.mono (copy_ok n (k₂.ws (k₁.ws hs)) (k₂.at (k₁.at h3)) foz faz (by omega_using [ioz])
    (by omega_using [iaz]) (by omega_using [zaz])) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  refine ⟨?_, ?_, ?_, (k₁.trans k₂).trans k₃, ?_⟩
  · rw [O₃.wordsVal (d := o.x) (by omega_using [xz]) (by omega_using [iox, hn]),
      O₂.wordsVal (d := o.x) (by omega_using [xy]) (by omega_using [iox, hn]), e₁]
  · rw [O₃.wordsVal (d := o.y) (by omega_using [yz]) (by omega_using [ioy, hn]), e₂,
      O₁.wordsVal (d := a.y) (by omega_using [xay]) (by omega_using [iay, hn])]
  · rw [e₃, O₂.wordsVal (d := a.z) (by omega_using [yaz]) (by omega_using [iaz, hn]),
      O₁.wordsVal (d := a.z) (by omega_using [xaz]) (by omega_using [iaz, hn])]
  · exact ((Outs.of_outside O₁ (by simp)).trans (Outs.of_outside O₂ (by simp))).trans
      (Outs.of_outside O₃ (by simp))

/-- What the slot of number `x` stands for, in the working space at `base`. -/
def Eb (k m : Nat) [NeZero m] (dbl : Bool) (mem : Mem) (base : Addr) (x : Nat) : Fin m :=
  toM m (2 ^ (64 * k)) (wordsVal mem base (enc k dbl x) k)

/-- What the point function `ptName S a0 dbl` computes from the values of
the slots: Algorithm 9 or 8 for `a0`, else Algorithm 1. -/
def ptVal {m : Nat} [NeZero m] (a0 dbl : Bool) (E : Nat → Fin m) : Fin m × Fin m × Fin m :=
  if a0 then
    (if dbl then Impl.Weierstrass.Point.rcbDbl0 (E 10) (E 3) (E 4) (E 5)
    else Impl.Weierstrass.Point.rcbAdd0m (E 10) (E 3) (E 4) (E 5) (E 6) (E 7))
  else VG.Proof.Weierstrass.rcbAdd (E 9) (E 10) (E 3) (E 4) (E 5) (E 6) (E 7) (E 8)

theorem ptOps_opsOk (a0 dbl : Bool) : OpsOk (ptOps a0 dbl) := by
  cases a0
  · exact rcbIds_opsOk
  · exact ops0_opsOk dbl

theorem ptOps_run {m : Nat} [NeZero m] (E : Nat → Fin m) (a0 dbl : Bool) :
    (runOps (ptOps a0 dbl) E 0, runOps (ptOps a0 dbl) E 1, runOps (ptOps a0 dbl) E 2) =
      ptVal a0 dbl E := by
  cases a0
  · exact rcb_run rcbIds_apart E
  · exact ops0_run E dbl

/-- A call of a point function, from the working space at `r3`: only
`fnClob`, `O` and the own working space change, and `O` holds `rcbAdd` of
what the constants and the operands stood for. -/
theorem ptCall_ok {S : Impl.Weierstrass.Mont.Modulus} [NeZero S.m] (hM : ModOk S.k S.m) (hodd : S.m % 2 = 1)
    (hk3 : 3 ≤ S.k) (hk6 : S.k ≤ 6) (dbl : Bool) {a0 : Bool} {s : State} {base : Addr} (hw : WsReg s base)
    (hlt : ∀ x ∈ rIds, wordsVal s.mem base (enc S.k dbl x) S.k < S.m) :
    WP isa (ptCall S dbl a0) s fun s' => Rk fnClob s s' ∧
      Outs base [(Impl.Weierstrass.Point.oAt S.k, 3 * Impl.Weierstrass.Point.elemBytes S.k),
        (Impl.Weierstrass.Point.ownAt S.k, 4096 - Impl.Weierstrass.Point.ownAt S.k)] s.mem s'.mem ∧
      (∀ j < 3, wordsVal s'.mem base (enc S.k dbl j) S.k < S.m) ∧
      (Eb S.k S.m dbl s'.mem base 0, Eb S.k S.m dbl s'.mem base 1, Eb S.k S.m dbl s'.mem base 2) =
        ptVal a0 dbl (Eb S.k S.m dbl s.mem base) := by
  have hcov : Covers [⟨base, 8192⟩] s.wr := Covers.of_mem fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hw.wr
  have g3 : ∀ t : State, (t.callEntry.withRegions [] [⟨base, 8192⟩]).gpr .r3 = t.gpr .r3 := fun t => by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide)]
  rw [ptCall]
  refine WP.call (k := ⟨fun t => PrePt S.k S.m dbl t ∧ t.gpr .r3 = base ∧ t.mem = s.mem,
      fun t t' => (∀ r, r ∉ fnClob → t'.gpr r = t.gpr r) ∧
        Outs (t.gpr .r3) [(Impl.Weierstrass.Point.oAt S.k, 3 * Impl.Weierstrass.Point.elemBytes S.k),
          (Impl.Weierstrass.Point.ownAt S.k, 4096 - Impl.Weierstrass.Point.ownAt S.k)] t.mem t'.mem ∧
        (∀ j < 3, wordsVal t'.mem (t.gpr .r3) (enc S.k dbl j) S.k < S.m) ∧
        (toM S.m (2 ^ (64 * S.k)) (wordsVal t'.mem (t.gpr .r3) (enc S.k dbl 0) S.k),
          toM S.m (2 ^ (64 * S.k)) (wordsVal t'.mem (t.gpr .r3) (enc S.k dbl 1) S.k),
          toM S.m (2 ^ (64 * S.k)) (wordsVal t'.mem (t.gpr .r3) (enc S.k dbl 2) S.k)) =
        ptVal a0 dbl (Eb S.k S.m dbl t.mem (t.gpr .r3)),
      fun _ _ => True⟩)
    (fun t ⟨hp, _, _⟩ => by
      obtain ⟨tr, t', he, A, G, O, L, E⟩ := fnOps_ok hM hodd (ptOps_opsOk a0 dbl) hp
      exact ⟨tr, t', he, A, G, O, L, E.trans (ptOps_run _ a0 dbl)⟩)
    (rd := []) (wr := [⟨base, 8192⟩])
    ⟨⟨by rw [State.withRegions_wr, g3, hw.r3], by rw [g3, hw.r3]; exact hw.nowrap, hk3, hk6,
        fun x hx => by
          rw [g3, hw.r3, State.withRegions_mem, State.callEntry_mem]
          exact hlt x hx⟩,
      by rw [g3, hw.r3],
      by rw [State.withRegions_mem, State.callEntry_mem]⟩
    (Covers.right hcov) hcov ?_ (by cases a0 <;> cases dbl <;> rfl)
  intro s' r' w' p' _ _ _ ⟨G, O, L, E⟩
  simp only [State.withRegions_mem, State.callEntry_mem, g3, hw.r3, State.withRegions_gpr] at G O L E
  refine ⟨⟨fun r hr => ?_, r', w', p'⟩, O, L, E⟩
  have hl : r ∉ linkRegs := not_mem_sub hr
  rw [G r hr, State.callEntry_gpr _ hl]

end VG.Proof.Weierstrass.PPC64LE.Point
