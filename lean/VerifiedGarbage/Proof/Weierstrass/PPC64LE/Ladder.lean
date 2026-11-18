module

public import VerifiedGarbage.Proof.Weierstrass.Rcb0
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
public import VerifiedGarbage.Proof.Weierstrass.Layout
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointFprog
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.LadderP
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Mont.RangeCover

/-! ### `Weierstrass.PPC64LE.LadderPCall`, which the modules that import this one used -/

section

/-! ### `Weierstrass.PPC64LE.PointFn`, which this module and modules that import it used -/

section

/-!
# Complete point addition and doubling as functions, on PPC64LE: correctness

`fnOps S dbl ops` (`Impl/Weierstrass/PPC64LE/Point.lean`), for field
operations `ops` that write only the result and the temporaries (`OpsOk`),
from a state that its precondition describes (`PrePt`: the working space at `r3`, writable, and
every coordinate it reads below the prime), returns with the callee-saved
registers, `sp` and `lr` kept, the registers but `fnClob` kept, the memory
changed only at `O` and in the own working space, and `O`'s coordinates
below the prime, standing for what `ops` computes from what the constants
and the operands stand for (`fnOps_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Point

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Weierstrass.PPC64LE.Point
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Impl.Weierstrass.Point (elemBytes ownAt aAt b3At oAt pAt qAt)

/-- The numbers of the layout, for `omega`. -/
theorem lay_nums {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) :
    ownAt k + 64 + 6 * elemBytes k = own k ∧ own k + 64 * k = 4096 ∧ elemBytes k = 8 * k ∧
    b3At k + elemBytes k = ownAt k ∧ aAt k + elemBytes k = b3At k ∧
    qAt k + 3 * elemBytes k = aAt k ∧ pAt k + 3 * elemBytes k = qAt k ∧
    oAt k + 3 * elemBytes k = pAt k ∧ 1000 ≤ oAt k ∧ ownAt k % 8 = 0 := by
  obtain rfl | rfl | rfl | rfl : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega_using [hk3, hk6]
  all_goals decide +kernel

/-- The slots the function reads first lie below its own working space. -/
theorem enc_rIds {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (dbl : Bool) :
    ∀ x ∈ rIds, enc k dbl x + 8 * k ≤ ownAt k := by
  obtain rfl | rfl | rfl | rfl : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega_using [hk3, hk6]
  all_goals cases dbl <;> decide +kernel

/-- The slots `enc` gives are laid out as the program needs. -/
theorem enc_lay {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (dbl : Bool) : LayR k 17 wIds (enc k dbl) := by
  obtain rfl | rfl | rfl | rfl : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega_using [hk3, hk6]
  all_goals cases dbl <;> exact ⟨by decide +kernel, by decide +kernel⟩

/-- Those it writes lie apart from the saved `lr` and within `O` or the own
working space. -/
theorem enc_wIds {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (dbl : Bool) :
    ∀ w ∈ wIds, (enc k dbl w + 8 * k ≤ ownAt k ∨ ownAt k + 8 ≤ enc k dbl w) ∧
      ((oAt k ≤ enc k dbl w ∧ enc k dbl w + 8 * k ≤ pAt k) ∨
        (ownAt k ≤ enc k dbl w ∧ enc k dbl w + 8 * k ≤ 4096)) := by
  obtain rfl | rfl | rfl | rfl : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega_using [hk3, hk6]
  all_goals cases dbl <;> decide +kernel

/-- The precondition of the function, on the state: the working space at
`r3`, its `8192` bytes writable, and the numbers it reads below `m`. -/
structure PrePt (k m : Nat) (dbl : Bool) (s : State) : Prop where
  wr : s.wr = [⟨s.gpr .r3, 8192⟩]
  fit : (s.gpr .r3).toNat + 8192 ≤ 2 ^ 64
  k3 : 3 ≤ k
  k6 : k ≤ 6
  lt : ∀ x ∈ rIds, wordsVal s.mem (s.gpr .r3) (enc k dbl x) k < m

/-- The environment of the entry: what the numbers of the slots stand for. -/
def E₀ (k m : Nat) [NeZero m] (dbl : Bool) (s : State) (x : Nat) : Fin m :=
  toM m (2 ^ (64 * k)) (wordsVal s.mem (s.gpr .r3) (enc k dbl x) k)

theorem rIds_lt : ∀ x ∈ rIds, x < 17 := by decide

/-- A function of field operations `ops` that write only the result and the
temporaries (`OpsOk`): the registers but `fnClob`, `sp` and `lr` kept, the
memory changed only at `O` and in the own working space, and `O`'s
coordinates below the prime, standing for what `ops` computes from what the
slots stand for. -/
theorem fnOps_ok {S : Impl.Weierstrass.Mont.Modulus} [NeZero S.m] (hM : ModOk S.k S.m) (hodd : S.m % 2 = 1)
    {dbl : Bool} {ops : List FOp} (hO : OpsOk ops) {s : State} (hp : PrePt S.k S.m dbl s) :
    WP isa (Point.fnOps S dbl ops) s fun s' => abiPreserved s s' ∧ (∀ r, r ∉ fnClob → s'.gpr r = s.gpr r) ∧
      Outs (s.gpr .r3) [(oAt S.k, 3 * elemBytes S.k), (ownAt S.k, 4096 - ownAt S.k)] s.mem s'.mem ∧
      (∀ j < 3, wordsVal s'.mem (s.gpr .r3) (enc S.k dbl j) S.k < S.m) ∧
      (toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (s.gpr .r3) (enc S.k dbl 0) S.k),
        toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (s.gpr .r3) (enc S.k dbl 1) S.k),
        toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (s.gpr .r3) (enc S.k dbl 2) S.k)) =
        (runOps ops (E₀ S.k S.m dbl s) 0, runOps ops (E₀ S.k S.m dbl s) 1,
          runOps ops (E₀ S.k S.m dbl s) 2) := by
  have hl := lay_nums hp.k3 hp.k6
  have hR := enc_rIds hp.k3 hp.k6 dbl
  have hW := enc_wIds hp.k3 hp.k6 dbl
  have hfit := hp.fit
  have hs : Ws s (s.gpr .r3) 4096 := ⟨⟨8192, by decide, by rw [hp.wr]; simp, hfit⟩, by decide⟩
  have h3 : At s (s.gpr .r3) .r3 0 := by simp [At, off]
  rw [Point.fnOps]
  -- The entry: `lr` saved.
  have hent : WP isa (.block (entry S.k)) s fun s₁ => Kp fnClob s s₁ ∧
      s₁.mem = s.mem.writeW (off (s.gpr .r3) (saveAt S.k)) s.lr := by
    refine wp_step exec_mflr (wp_step (std_ok (hs.write _ _) (h3.write _) (by decide) (d := saveAt S.k)
      (by simp only [saveAt]; omega_using [hl]) (by simp only [saveAt]; omega_using [hl])) (WP.block_nil ?_))
    simp only [write_gpr, ite_true, Nat.zero_add]
    exact ⟨(Kp.write s _ (by decide)).trans (Kp.store _ _ _), rfl⟩
  refine WP.seq (WP.mono hent fun s₁ ⟨K₁, m₁⟩ => ?_)
  have O₁ := writeW_outside s.mem (s.gpr .r3) (d := saveAt S.k) s.lr (by simp only [saveAt]; omega_using [hl])
  rw [← m₁] at O₁
  have hI : InvR S.k 17 (enc S.k dbl) (s.gpr .r3) S.m rIds (E₀ S.k S.m dbl s) s₁ := by
    have heq : ∀ x ∈ rIds, wordsVal s₁.mem (s.gpr .r3) (enc S.k dbl x) S.k =
        wordsVal s.mem (s.gpr .r3) (enc S.k dbl x) S.k := fun x hx =>
      O₁.wordsVal (by have := hR x hx; simp only [saveAt]; omega_using [this]) (by have := hR x hx; omega_using [hl, this])
    exact ⟨⟨by rw [K₁.g], by rw [K₁.wr, hp.wr]; simp, hfit⟩, rIds_lt,
      fun x hx => by rw [heq x hx]; exact hp.lt x hx, fun x hx => by rw [heq x hx]; rfl⟩
  refine WP.seq (WP.mono (opsR_ok hM rfl (enc_lay hp.k3 hp.k6 dbl) (unitMod_pow_two hodd _) hO hI)
    fun s₂ ⟨K, I₂⟩ => ?_)
  -- The restore.
  have hs₂ : Ws s₂ (s.gpr .r3) 4096 := ⟨⟨8192, by decide, by rw [K.wr, K₁.wr, hp.wr]; simp, hfit⟩, by decide⟩
  have h3₂ : At s₂ (s.gpr .r3) .r3 0 := by rw [At, K.gpr _ (by decide), K₁.g]; exact h3
  have hsv : word s₂.mem (s.gpr .r3) (saveAt S.k) = s.lr := by
    rw [Outs.word K.mem (fun r hr => ?_) (by simp only [saveAt]; omega_using [hl]), m₁, word_writeW_self]
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
    rcases hr with ⟨x, hx, rfl⟩ | rfl
    · rcases (hW x hx).1 with h | h <;> [exact .inr (by simp only [saveAt]; omega_using [h]);
        exact .inl (by simp only [saveAt]; omega_using [h])]
    · exact .inl (by simp only [saveAt]; omega_using [hl])
  refine wp_step (ld_ok hs₂ h3₂ (by decide) (by simp only [saveAt]; omega_using [hl]) (d := saveAt S.k)
    (by simp only [saveAt]; omega_using [hl])) (wp_step exec_mtlr (WP.block_nil ?_))
  simp only [write_gpr, ite_true, Nat.zero_add, hsv]
  refine ⟨⟨fun r hr => ?_, ?_, rfl⟩, fun r hr => ?_, ?_, fun j hj => ?_, ?_⟩
  · have hr' : r ∉ fnClob := fun h => absurd h ((by decide : ∀ r ∈ preserved, r ∉ fnClob) r hr)
    have : r ≠ .r0 := fun h => hr' (h ▸ by decide)
    simp only [write_gpr, this, ite_false]
    rw [K.gpr r hr', K₁.gpr r hr']
  · simp only [write_sp]; rw [K.sp, K₁.sp]
  · have : r ≠ .r0 := fun h => hr (h ▸ by decide)
    simp only [this, ite_false]
    rw [K.gpr r hr, K₁.gpr r hr]
  · simp only [write_mem]
    refine (Outs.cover (rs := [(saveAt S.k, 8)]) ?_ fun r hr => ?_).trans (Outs.cover K.mem fun r hr => ?_)
    · rw [m₁]; exact Outs.of_outside (writeW_outside s.mem _ s.lr (by simp only [saveAt]; omega_using [hl]))
        (List.mem_singleton_self _)
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by simp only [saveAt]; omega_using [],
        by simp only [saveAt]; omega_using [hl]⟩
    · simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
      rcases hr with ⟨x, hx, rfl⟩ | rfl
      · rcases (hW x hx).2 with h | h
        · exact ⟨_, List.mem_cons_self, h.1, by dsimp only; omega_using [hl, h]⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.1, by dsimp only; omega_using [h]⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by dsimp only; omega_using [hl], by dsimp only; omega_using [hl]⟩
  · simp only [write_mem]; exact I₂.lt j (hO.outs j hj)
  · simp only [write_mem]
    rw [I₂.val 0 (hO.outs 0 (by decide)), I₂.val 1 (hO.outs 1 (by decide)),
      I₂.val 2 (hO.outs 2 (by decide))]

end VG.Proof.Weierstrass.PPC64LE.Point

end

end

/-!
# The ladder by calls of the point functions, on PPC64LE: copies and calls

`copyPt n o a` copies the point at `a` to `o` (`copyPt_ok`), and
`ptCall S dbl` calls `vg_<curve>_point_double` or `vg_<curve>_point_add` on
the working space at `r3` (`ptCall_ok`): it changes only `fnClob`, `O` and
the point functions' own working space, and `O` then holds `rcbAdd` of what
`a`, `3b`, `P` and `Q` (or `P`) stood for (`ptVal`). As on 32-bit ARM
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

end

end

/-! ### `Weierstrass.PPC64LE.Fprog`, which this module and modules that import it used -/

section

/-!
# Field programs on slots, on PPC64LE

`fprog S ops` (`Impl/Weierstrass/PPC64LE/Call.lean`) runs the field
operations `ops` on slots of the working space, one by one by calls of the
functions of the modulus `S` (`fprog_ok`), as on 32-bit ARM
(`Proof/Weierstrass/Arm/Bits.lean`): on slots that are apart from each other
and below the functions' own working space (`Proof.Mont.Lay` of
`own M.n` bytes), what the slots stand for (`toM`) follows `runOps ops`, the
program on environments (`Inv`). A slot is read only once it holds a number
below `m`: either it did at the start (`V`) or an earlier operation wrote it
(`Proof.Weierstrass.readsOk`). Only the registers `fnClob`, the slots
written and the functions' own working space change (`KeepR`, with the
slots their own offsets).

The complete addition `rcb` is such a program, and computes `rcbAdd`
(`rcb_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Proof.Weierstrass.PPC64LE.Point (KeepR)

/-- The state holds the environment `E` in Montgomery's form in the slots
`V` (of `Sl`), below `m`, and the working space is at `r3`. -/
structure Inv (n : Nat) (base : Addr) (m : Nat) [NeZero m] (Sl : Nat → Prop) (V : List Nat)
    (E : Nat → Fin m) (s : State) : Prop where
  ws : WsReg s base
  sl : ∀ x ∈ V, Sl x
  lt : ∀ x ∈ V, wordsVal s.mem base x n < m
  val : ∀ x ∈ V, toM m (2 ^ (64 * n)) (wordsVal s.mem base x n) = E x

theorem Inv.sub {n : Nat} {base : Addr} {m : Nat} [NeZero m] {Sl : Nat → Prop} {V V' : List Nat}
    {E : Nat → Fin m} {s : State} (h : Inv n base m Sl V E s) (hV : ∀ x ∈ V', x ∈ V) :
    Inv n base m Sl V' E s :=
  ⟨h.ws, fun x hx => h.sl x (hV x hx), fun x hx => h.lt x (hV x hx), fun x hx => h.val x (hV x hx)⟩

/-- An operation writing `o`, which then holds `v`, keeps the invariant. -/
theorem Inv.update {M : Mod} {base : Addr} {m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay M (own M.n) Sl) {V : List Nat} {E : Nat → Fin m} {s s' : State}
    (hI : Inv M.n base m Sl V E s) {o : Nat} (ho : Sl o) (hk : KeepR M.n (fun x => x) base [o] s s')
    (hr : wordsVal s'.mem base o M.n < m) {v : Fin m}
    (hv : toM m (2 ^ (64 * M.n)) (wordsVal s'.mem base o M.n) = v) :
    Inv M.n base m Sl (o :: V) (Function.update E o v) s' := by
  have hn := hI.ws.nowrap
  have hown : own M.n ≤ 4096 := Nat.sub_le _ _
  have heq : ∀ x ∈ V, x ≠ o → wordsVal s'.mem base x M.n = wordsVal s.mem base x M.n := by
    intro x hx hxo
    have hxS := hI.sl x hx
    have h1 := hL.le x hxS
    have h2 := hL.apart x o hxS ho hxo
    refine outs_wordsVal hk.mem (fun r hr => ?_) (by omega_using [hown, h1])
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h2
    · exact .inl h1
  refine ⟨hI.ws.of_keep (hk.gpr _ (by decide)) hk.wr, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ho
    · exact hI.sl x hx
  · intro x hx
    by_cases hxo : x = o
    · subst hxo; exact hr
    · have hx' := List.mem_of_ne_of_mem hxo hx
      rw [heq x hx' hxo]; exact hI.lt x hx'
  · intro x hx
    by_cases hxo : x = o
    · subst hxo; rw [Function.update_self]; exact hv
    · have hx' := List.mem_of_ne_of_mem hxo hx
      rw [heq x hx' hxo, Function.update_of_ne hxo]
      exact hI.val x hx'

/-- One operation. -/
theorem fop_ok {M : Mod} {base : Addr} {S : Impl.Weierstrass.Mont.Modulus} [NeZero S.m]
    (hM : ModOk S.k S.m) (hk : S.k = M.n) {Sl : Nat → Prop} (hL : Lay M (own M.n) Sl)
    (hm : UnitMod S.m (2 ^ (64 * M.n))) {V : List Nat} {E : Nat → Fin S.m} {s : State}
    (hI : Inv M.n base S.m Sl V E s) {op : FOp} (hS : ∀ x ∈ op.out :: op.ins, Sl x)
    (hR : ∀ x ∈ op.ins, x ∈ V) :
    WP isa (opCode S op) s fun s' =>
      KeepR M.n (fun x => x) base [op.out] s s' ∧ Inv M.n base S.m Sl (op.out :: V) (op.run E) s' := by
  have hle : ∀ x, Sl x → x + 8 * S.k ≤ own S.k := fun x hx => by rw [hk]; exact hL.le x hx
  cases op with
  | mul o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    refine WP.mono (mulCall_ok hM hI.ws (hle o hS.1) (hle a hS.2.1) (hle b hS.2.2)
        (by rw [hk]; exact hI.lt b hR.2))
      fun s' ⟨K, hlt, heq⟩ => ?_
    rw [hk] at K hlt heq
    refine ⟨.of_call K, hI.update hL hS.1 (.of_call K) hlt ?_⟩
    rw [toM_mul hm heq, hI.val a hR.1, hI.val b hR.2]
  | add o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    have hA := hI.lt a hR.1
    have hB := hI.lt b hR.2
    refine WP.mono (addCall_ok hM hI.ws (hle o hS.1) (hle a hS.2.1) (hle b hS.2.2)
        (by rw [hk]; omega_using [hA, hB]))
      fun s' ⟨K, heq⟩ => ?_
    rw [hk] at K heq
    refine ⟨.of_call K, hI.update hL hS.1 (.of_call K) ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (by omega_using [hA])
    · rw [heq, toM_add, hI.val a hR.1, hI.val b hR.2]
  | sub o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    have hA := hI.lt a hR.1
    have hB := hI.lt b hR.2
    refine WP.mono (subCall_ok hM hI.ws (hle o hS.1) (hle a hS.2.1) (hle b hS.2.2)
        (by rw [hk]; exact hA) (by rw [hk]; exact hB))
      fun s' ⟨K, heq⟩ => ?_
    rw [hk] at K heq
    refine ⟨.of_call K, hI.update hL hS.1 (.of_call K) ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (by omega_using [hA])
    · rw [heq, toM_sub (by omega_using [hB]), hI.val a hR.1, hI.val b hR.2]

/-- A field program. -/
theorem fprog_ok {M : Mod} {base : Addr} {S : Impl.Weierstrass.Mont.Modulus} [NeZero S.m]
    (hM : ModOk S.k S.m) (hk : S.k = M.n) {Sl : Nat → Prop} (hL : Lay M (own M.n) Sl)
    (hm : UnitMod S.m (2 ^ (64 * M.n))) :
    ∀ (ops : List FOp) {V : List Nat} {E : Nat → Fin S.m} {s : State},
      Inv M.n base S.m Sl V E s → (∀ op ∈ ops, ∀ x ∈ op.out :: op.ins, Sl x) →
      readsOk ops V = true →
      WP isa (fprog S ops) s fun s' => KeepR M.n (fun x => x) base (ops.map FOp.out) s s' ∧
        Inv M.n base S.m Sl (validAfter ops V) (runOps ops E) s'
  | [], _, _, s, hI, _, _ => WP.block_nil ⟨KeepR.refl _ _ _ _ s, hI⟩
  | op :: ops, V, E, s, hI, hS, hR => by
    simp only [readsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hR
    refine Point.progs_wp _ _ (WP.mono (fop_ok hM hk hL hm hI (hS op (List.mem_cons_self ..)) hR.1)
      fun s₁ ⟨k₁, I₁⟩ => ?_)
    refine WP.mono (fprog_ok hM hk hL hm ops I₁ (fun op' h => hS op' (List.mem_cons_of_mem _ h)) hR.2)
      fun s₂ ⟨k₂, I₂⟩ => ⟨(k₁.mono fun w hw => ?_).trans (k₂.mono fun w hw => ?_), I₂⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      simp [hw]
    · simp [hw]

/-! ## The complete addition -/

/-- `o = p + q` by `rcb`, on slots of `Sl` that are apart (`RcbApart`; `p` may
be `q`), from a state holding `E`, in particular `p`, `q`, `a` and `3b`
(`rcbR`): `o` holds `rcbAdd` of their values, and the slots but those `rcb`
writes (`rcbW`) keep theirs. -/
theorem rcb_ok {M : Mod} {base : Addr} {S' : Impl.Weierstrass.Mont.Modulus} [NeZero S'.m]
    (hM : ModOk S'.k S'.m) (hk : S'.k = M.n) {Sl : Nat → Prop} (hL : Lay M (own M.n) Sl)
    (hm : UnitMod S'.m (2 ^ (64 * M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o)
    (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) {V : List Nat} {E : Nat → Fin S'.m} {s : State}
    (hI : Inv M.n base S'.m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (fprog S' (rcb S p q o)) s fun s' => KeepR M.n (fun x => x) base (rcbW S o) s s' ∧
      Inv M.n base S'.m Sl (rcbW S o ++ V) (runOps (rcb S p q o) E) s' ∧
      (runOps (rcb S p q o) E o.x, runOps (rcb S p q o) E o.y, runOps (rcb S p q o) E o.z) =
        VG.Proof.Weierstrass.rcbAdd (E S.a) (E S.b3) (E p.x) (E p.y) (E p.z) (E q.x) (E q.y)
          (E q.z) ∧
      ∀ x, x ∉ rcbW S o → runOps (rcb S p q o) E x = E x := by
  have hR : readsOk (rcb S p q o) V = true := by
    rw [rcb_eq_rename]
    exact readsOk_mono (readsOk_rename _ rcbN_reads) hV
  refine WP.mono (fprog_ok hM hk hL hm _ hI (fun op hop x hx => hSl x (rcb_slots op hop x hx)) hR)
    fun s' ⟨hk', hI'⟩ => ⟨hk'.mono fun w hw => ?_, hI'.sub fun x hx => ?_, rcb_run hA E,
      fun x hx => runOps_of_not_out _ _ fun op hop h => hx (h ▸ rcb_out op hop)⟩
  · obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    exact rcb_out op hop
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (rcb_out_mem hx)
    · exact Or.inl hx

end VG.Proof.Weierstrass.PPC64LE

end

end

/-!
# The ladder, on PPC64LE

An iteration of `ladder L S` (`Impl/Weierstrass/PPC64LE.lean`) computes
`D = R + R` and `T = D + G` with the complete addition (`rcb_ok`), and
selects `T` into `R` if the scalar's bit is set, else `D`
(`ladderBody_ok`), for the scalar `k` whose bits are the table at `L.bits`,
as on 32-bit ARM (`Proof/Weierstrass/Arm/Ladder.lean`). `ladder_ok` takes the
loop's invariant `Q j` on what `R` holds, and that an iteration keeps it
(`Step`): the callers' invariant is that `R` represents `[k >>> j]P`
(`step_rep`, in `Rep.lean`), and only they need the group law. The field
arithmetic is calls of the functions of `S`, whose own working space is
above the ladder's slots (`LadLay` of `own n` bytes) and below its table
(`LadLayI`). This is the ladder of curves whose points do not fit the point
functions' slots (`ladderP`, for coordinates of more than 6 words).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Point

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Spec.Weierstrass (Curve Fe)

/-- What a slot holding `x` stands for, modulo `C.p`. -/
abbrev tmv (C : Curve) (n : Nat) (base : Addr) (s : State) (x : Nat) : Fe C :=
  toM C.p (2 ^ (64 * n)) (wordsVal s.mem base x n)

/-- That an iteration keeps the invariant `Q`: from `(X : Y : Z)` that
`Q (j + 1)` accepts, `Q j` accepts `T = D + G` if bit `j` of `k` is set, else
`D = (X : Y : Z) + (X : Y : Z)`, by the complete addition with the curve's
`a`, `3b` and `G` as the slots `L.S.a`, `L.S.b3` and `L.G` hold them (for
`a0`, by the formulas for `a = 0`). -/
def Step (L : LadderCfg) (C : Curve) (base : Addr) (s : State) (k : Nat)
    (Q : Nat → Fe C → Fe C → Fe C → Prop) (a0 : Bool := false) : Prop :=
  ∀ j < L.nbits, ∀ X Y Z X2 Y2 Z2 X3 Y3 Z3 : Fe C, Q (j + 1) X Y Z →
    ladDbl a0 (tmv C L.M.n base s L.S.a) (tmv C L.M.n base s L.S.b3) X Y Z = (X2, Y2, Z2) →
    ladAdd a0 (tmv C L.M.n base s L.S.a) (tmv C L.M.n base s L.S.b3) X2 Y2 Z2
      (tmv C L.M.n base s L.G.x) (tmv C L.M.n base s L.G.y) (tmv C L.M.n base s L.G.z) =
      (X3, Y3, Z3) →
    Q j (if k.testBit j then X3 else X2) (if k.testBit j then Y3 else Y2)
      (if k.testBit j then Z3 else Z2)

/-- What the ladder writes: `ladW` and the functions' own working space. -/
def ladWx (L : LadderCfg) : List (Nat × Nat) := ladW L ++ [(own L.M.n, 64 * L.M.n)]

/-- The ladder's slots: `LadLay` below the functions' own working space, at
multiples of 4, with the table of bits above it and its length an
immediate. -/
structure LadLayI (L : LadderCfg) : Prop where
  lay : LadLay L (own L.M.n) 8192
  al : ∀ x ∈ ladSlots L, x % 4 = 0
  bits : 4096 ≤ L.bits
  nbits : L.nbits < 2 ^ 15

theorem own_add (n : Nat) (h : 8 * n ≤ own n) : own n + 64 * n = 4096 := by
  simp only [own, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes] at h ⊢; omega_using [h]

/-- A slot the ladder does not write is apart from what it writes. -/
theorem LadLayI.apart_wx {L : LadderCfg} (hL : LadLayI L) {x : Nat} (hx : x ∈ ladSlots L)
    (hxw : x ∉ ladWs L) : ∀ w ∈ ladWx L, x + 8 * L.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro w hw
  simp only [ladWx, List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · exact hL.lay.apart_w hx hxw w hw
  · exact .inl (hL.lay.lay.le x hx)

/-- The table of bits is apart from what the ladder writes. -/
theorem LadLayI.bits_wx {L : LadderCfg} (hL : LadLayI L) {t : Nat} (ht : t < L.nbits) :
    ∀ w ∈ ladWx L, L.bits + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ L.bits + t := by
  have hR := hL.lay.lay.le _ (ladPts_slots L L.R.x (by simp))
  have ho := own_add L.M.n (by omega_using [hR])
  have hb := hL.bits
  intro w hw
  simp only [ladWx, List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · have := hL.lay.bits_w w hw; omega_using [ht, this]
  · simp only; omega_using [ho, hb]

/-- The loop's invariant at `r31 = j`: `Q j` accepts what `R` holds. -/
structure LadInv (L : LadderCfg) (C : Curve) (base : Addr) (Q : Nat → Fe C → Fe C → Fe C → Prop)
    (s₀ s : State) (j : Nat) : Prop where
  ws : WsReg s base
  r31 : s.gpr .r31 = BitVec.ofNat 64 j
  keep : Rk powClob s₀ s
  unch : Unch base (ladWx L) s₀.mem s.mem
  lt : ∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal s.mem base x L.M.n < C.p
  q : Q j (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z)

/-- After both additions: `D` and `T` hold `R + R` and `D + G`. -/
structure AddsPost (L : LadderCfg) (C : Curve) (base : Addr) (E : Nat → Fe C) (s s' : State) : Prop where
  ws : WsReg s' base
  keep : Rk fnClob s s'
  unch : Unch base (ladWx L) s.mem s'.mem
  lt : ∀ x ∈ [L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z], wordsVal s'.mem base x L.M.n < C.p
  vals : ∃ X2 Y2 Z2 X3 Y3 Z3 : Fe C,
    VG.Proof.Weierstrass.rcbAdd (E L.S.a) (E L.S.b3) (E L.R.x) (E L.R.y) (E L.R.z) (E L.R.x)
      (E L.R.y) (E L.R.z) = (X2, Y2, Z2) ∧
    VG.Proof.Weierstrass.rcbAdd (E L.S.a) (E L.S.b3) X2 Y2 Z2 (E L.G.x) (E L.G.y) (E L.G.z) =
      (X3, Y3, Z3) ∧
    tmv C L.M.n base s' L.D.x = X2 ∧ tmv C L.M.n base s' L.D.y = Y2 ∧
    tmv C L.M.n base s' L.D.z = Z2 ∧ tmv C L.M.n base s' L.T.x = X3 ∧
    tmv C L.M.n base s' L.T.y = Y3 ∧ tmv C L.M.n base s' L.T.z = Z3

/-- What a program writing the slots `W` of `ladWs`, through the functions,
changes of what the ladder writes. -/
theorem keep_unch {L : LadderCfg} {base : Addr} {W : List Nat} {s s' : State}
    (h : KeepR L.M.n (fun x => x) base W s s') (hW : ∀ w ∈ W, w ∈ ladWs L) :
    Unch base (ladWx L) s.mem s'.mem :=
  fun x hx => h.mem x fun r hr => hx r (by
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
    simp only [ladWx, ladW, List.mem_append, List.mem_map, List.mem_singleton]
    rcases hr with ⟨w, hw, rfl⟩ | rfl
    · exact .inl (.inl ⟨w, hW w hw, rfl⟩)
    · exact .inr rfl)

/-- The two additions, from a state holding `E` in the slots `ladR`. -/
theorem ladAdds_ok {L : LadderCfg} {C : Curve} {base : Addr} (hL : LadLayI L)
    {S : Impl.Weierstrass.Mont.Modulus} (hM : ModOk S.k S.m) (hkS : S.k = L.M.n) (hmS : S.m = C.p)
    (hp : UnitMod C.p (2 ^ (64 * L.M.n))) {E : Nat → Fe C} {s : State}
    (hI : Inv L.M.n base C.p (· ∈ ladSlots L) (ladR L) E s) {rest : Prog isa}
    {Q : State → Prop} (h : ∀ s', AddsPost L C base E s s' → WP isa rest s' Q) :
    WP isa (.seq (fprog S (rcb L.S L.R L.R L.D)) (.seq (fprog S (rcb L.S L.D L.G L.T)) rest))
      s Q := by
  obtain ⟨c, w, m', k', d⟩ := S
  dsimp only at hkS hmS hM ⊢
  subst hkS hmS
  have hL' := hL.lay
  refine WP.seq (WP.mono (rcb_ok (S' := ⟨c, w, C.p, L.M.n, d⟩) hM rfl hL'.lay hp hL'.a1 (ladR_S₁ L) hI
    (ladR_V₁ L)) fun s₂ ⟨k₂, I₂, t₂, n₂⟩ => ?_)
  refine WP.seq (WP.mono (rcb_ok (S' := ⟨c, w, C.p, L.M.n, d⟩) hM rfl hL'.lay hp hL'.a2 (ladR_S₂ L) I₂
    (ladR_V₂ L)) fun s₃ ⟨k₃, I₃, t₃, n₃⟩ => h s₃ ?_)
  have hro : ∀ x ∈ ladRo L, x ∉ rcbW L.S L.D := fun x hx h =>
    hL'.ro x hx (by simp only [ladWs, List.mem_append]; exact Or.inl (Or.inr h))
  have hDT : ∀ x ∈ [L.D.x, L.D.y, L.D.z], x ∉ rcbW L.S L.T := fun x hx =>
    hL'.a2.apart x (by revert x; sub_list)
  have hD : ∀ x ∈ [L.D.x, L.D.y, L.D.z], x ∈ rcbW L.S L.T ++ (rcbW L.S L.D ++ ladR L) := by
    sub_list
  have hT : ∀ x ∈ [L.T.x, L.T.y, L.T.z], x ∈ rcbW L.S L.T ++ (rcbW L.S L.D ++ ladR L) := by
    sub_list
  refine ⟨I₃.ws, ⟨fun r hr => (k₃.gpr r hr).trans (k₂.gpr r hr), k₃.rd.trans k₂.rd, k₃.wr.trans k₂.wr,
    k₃.sp.trans k₂.sp⟩, ((keep_unch k₂ fun w hw => ?_).trans (keep_unch k₃ fun w hw => ?_)).mono
      fun w hw => ?_, fun x hx => ?_, ?_⟩
  · simp only [ladWs, List.mem_append]; exact .inl (.inr hw)
  · simp only [ladWs, List.mem_append]; exact .inr hw
  · rcases List.mem_append.mp hw with hw | hw <;> exact hw
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    exact I₃.lt x (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> mem_list)
  · refine ⟨_, _, _, _, _, _, t₂.symm, ?_, (I₃.val L.D.x (hD L.D.x (by simp))).trans (n₃ L.D.x (hDT L.D.x (by simp))),
      (I₃.val L.D.y (hD L.D.y (by simp))).trans (n₃ L.D.y (hDT L.D.y (by simp))),
      (I₃.val L.D.z (hD L.D.z (by simp))).trans (n₃ L.D.z (hDT L.D.z (by simp))),
      I₃.val L.T.x (hT L.T.x (by simp)), I₃.val L.T.y (hT L.T.y (by simp)),
      I₃.val L.T.z (hT L.T.z (by simp))⟩
    rw [← n₂ L.S.a (hro L.S.a (by simp [ladRo])), ← n₂ L.S.b3 (hro L.S.b3 (by simp [ladRo])),
      ← n₂ L.G.x (hro L.G.x (by simp [ladRo])), ← n₂ L.G.y (hro L.G.y (by simp [ladRo])),
      ← n₂ L.G.z (hro L.G.z (by simp [ladRo]))]
    exact t₃.symm

/-- The mask of the bit, and `R = D` or `T` by it. -/
theorem ladSel_ok {L : LadderCfg} {base : Addr} (hL : LadLayI L) {s : State} (hw : WsReg s base)
    {t : Nat} (ht : t < L.nbits) (h31 : s.gpr .r31 = BitVec.ofNat 64 t)
    {c : Bool} (hc : s.mem (off base (L.bits + t)) = if c then 1 else 0) :
    WP isa (.block (bitMask L.bits ++ selPt L.M.n L.R L.D L.T)) s
      fun s' => Kp [.r4, .r5, .r10] s s' ∧
        Unch base [(L.R.x, 8 * L.M.n), (L.R.y, 8 * L.M.n), (L.R.z, 8 * L.M.n)] s.mem s'.mem ∧
        wordsVal s'.mem base L.R.x L.M.n =
          (if c then wordsVal s.mem base L.T.x L.M.n else wordsVal s.mem base L.D.x L.M.n) ∧
        wordsVal s'.mem base L.R.y L.M.n =
          (if c then wordsVal s.mem base L.T.y L.M.n else wordsVal s.mem base L.D.y L.M.n) ∧
        wordsVal s'.mem base L.R.z L.M.n =
          (if c then wordsVal s.mem base L.T.z L.M.n else wordsVal s.mem base L.D.z L.M.n) := by
  have hlb := hL.lay.bits
  have hx := hL.lay.lay.le _ (ladPts_slots L L.R.x (by simp))
  have ho := own_add L.M.n (by omega_using [hx])
  refine wp_append (WP.mono (bitMask_bool_ok hw.ws hw.at3 h31 (by omega_using [ht, hlb]) (c := c) hc)
    fun s₄ ⟨c₄, k₄, hm₄⟩ => ?_)
  have hap : ∀ x ∈ [L.R.x, L.R.y, L.R.z, L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z],
      ∀ y ∈ [L.R.x, L.R.y, L.R.z, L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z], x ≠ y →
      x + 8 * L.M.n ≤ y ∨ y + 8 * L.M.n ≤ x :=
    fun x hx y hy hxy => hL.lay.lay.apart x y (ladPts_slots L x hx) (ladPts_slots L y hy) hxy
  obtain ⟨rxy, rxz, ryz⟩ := hL.lay.rne
  refine WP.mono (selPt_ok (k₄.ws hw.ws) (k₄.at hw.at3) c c₄ (n := L.M.n) (o := L.R) (a := L.D) (b := L.T)
    (fun d hd => hL.al d (ladPts_slots L d hd))
    (fun d hd => by have := hL.lay.lay.le d (ladPts_slots L d hd); omega_using [ho, this])
    ⟨hap L.R.x (by simp) L.R.y (by simp) rxy, hap L.R.x (by simp) L.R.z (by simp) rxz,
      hap L.R.y (by simp) L.R.z (by simp) ryz⟩
    (fun d hd e he => hap d (List.mem_append_left [L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z] hd) e
      (List.mem_append_right [L.R.x, L.R.y, L.R.z] he) fun h => hL.lay.rdt d hd (h ▸ he)))
    fun s₅ ⟨ex₅, ey₅, ez₅, k₅, O₅⟩ => ?_
  refine ⟨k₄.trans (k₅.mono (by decide)), by rw [← hm₄]; exact O₅, by rw [ex₅, hm₄], by rw [ey₅, hm₄],
    by rw [ez₅, hm₄]⟩

section body
variable {L : LadderCfg} {C : Curve} {base : Addr}

/-- An iteration. -/
theorem ladderBody_ok {k : Nat} {Q : Nat → Fe C → Fe C → Fe C → Prop} {S : Impl.Weierstrass.Mont.Modulus}
    (hM : ModOk S.k S.m) (hkS : S.k = L.M.n) (hmS : S.m = C.p) (hp : UnitMod C.p (2 ^ (64 * L.M.n)))
    (hL : LadLayI L) {s₀ : State} (hlt₀ : ∀ x ∈ ladRo L, wordsVal s₀.mem base x L.M.n < C.p)
    (hstep : Step L C base s₀ k Q)
    (hbits : ∀ t < L.nbits, s₀.mem (off base (L.bits + t)) = if k.testBit t then 1 else 0)
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ L.nbits) (hI : LadInv L C base Q s₀ s j) :
    WP isa (ladderBody L S) s fun s' => LadInv L C base Q s₀ s' (j - 1) := by
  have hn := hI.ws.nowrap
  have hnb := hL.lay.nbits
  have hlb := hL.lay.bits
  -- The slots read only hold what they held at the start.
  have hro : ∀ x ∈ ladRo L, wordsVal s.mem base x L.M.n = wordsVal s₀.mem base x L.M.n :=
    fun x hx => hI.unch.wordsVal
      (hL.apart_wx (ladR_slots L x (mem_ladRo_ladR hx)) (hL.lay.ro x hx))
      (by have := hL.lay.lay.le x (ladR_slots L x (mem_ladRo_ladR hx)); have := own_lt L.M.n; omega_arith)
  have hE : ∀ x ∈ ladRo L, tmv C L.M.n base s x = tmv C L.M.n base s₀ x := fun x hx => by
    rw [tmv, hro x hx]
  -- `r31 -= 1`.
  rw [ladderBody]
  refine WP.seq (wp_decCounter hj hI.r31 (WP.block_nil ?_))
  generalize hs₁ : s.write .r31 (BitVec.ofNat 64 (j - 1)) = s₁
  have K₁ : Kp [.r31] s s₁ := by rw [← hs₁]; exact Kp.write _ _ (by decide)
  have m₁ : s₁.mem = s.mem := by rw [← hs₁]; rfl
  have c₁ : s₁.gpr .r31 = BitVec.ofNat 64 (j - 1) := by rw [← hs₁]; simp only [write_gpr, ite_true]
  have I₁ : Inv L.M.n base C.p (· ∈ ladSlots L) (ladR L) (tmv C L.M.n base s) s₁ := by
    refine ⟨hI.ws.of_kp K₁, ladR_slots L, fun x hx => ?_, fun x _ => by rw [tmv, m₁]⟩
    rw [m₁]
    simp only [ladR, List.mem_append] at hx
    rcases hx with hx | hx
    · rw [hro x hx]; exact hlt₀ x hx
    · exact hI.lt x hx
  -- The additions.
  refine ladAdds_ok hL hM hkS hmS hp I₁ fun s₃ A => ?_
  obtain ⟨X2, Y2, Z2, X3, Y3, Z3, h2, h3, dx, dy, dz, tx, ty, tz⟩ := A.vals
  have hU₃ : Unch base (ladWx L) s₀.mem s₃.mem :=
    (hI.unch.trans (by rw [← m₁]; exact A.unch)).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw <;> exact hw
  have hbyte : s₃.mem (off base (L.bits + (j - 1))) = if k.testBit (j - 1) then 1 else 0 := by
    rw [hU₃.byte (hL.bits_wx (by omega_using [hj, hjn])) (by omega_using [hjn, hlb]), hbits _ (by omega_using [hj, hjn])]
  have c₃ : s₃.gpr .r31 = BitVec.ofNat 64 (j - 1) := by rw [A.keep.g, c₁]
  have hstep := hstep (j - 1) (by omega_using [hj, hjn]) (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y)
    (tmv C L.M.n base s L.R.z) X2 Y2 Z2 X3 Y3 Z3 (by rw [Nat.sub_add_cancel hj]; exact hI.q)
    (by rw [← hE L.S.a (by simp [ladRo]), ← hE L.S.b3 (by simp [ladRo])]; exact h2)
    (by rw [← hE L.S.a (by simp [ladRo]), ← hE L.S.b3 (by simp [ladRo]), ← hE L.G.x (by simp [ladRo]),
        ← hE L.G.y (by simp [ladRo]), ← hE L.G.z (by simp [ladRo])]; exact h3)
  have K₃ : Rk powClob s₀ s₃ :=
    (hI.keep.trans (K₁.rk (rs' := powClob))).trans (A.keep.mono (rs' := powClob))
  refine WP.mono (ladSel_ok hL A.ws (by omega_using [hj, hjn]) c₃ hbyte) fun s' ⟨k', U', ex, ey, ez⟩ => ?_
  refine ⟨A.ws.of_kp k', by rw [k'.g, c₃], K₃.trans (k'.rk (rs' := powClob)), ?_, ?_, ?_⟩
  · exact (hU₃.trans U').mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact List.mem_append_left _ (mem_ladW_R w hw)
  · have hlt := A.lt
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt ⊢
    refine ⟨?_, ?_, ?_⟩
    · rw [ex]; split
      · exact hlt.2.2.2.1
      · exact hlt.1
    · rw [ey]; split
      · exact hlt.2.2.2.2.1
      · exact hlt.2.1
    · rw [ez]; split
      · exact hlt.2.2.2.2.2
      · exact hlt.2.2.1
  · have hx : tmv C L.M.n base s' L.R.x = if k.testBit (j - 1) then X3 else X2 := by
      show toM _ _ _ = _
      rw [ex]; split
      · exact tx
      · exact dx
    have hy : tmv C L.M.n base s' L.R.y = if k.testBit (j - 1) then Y3 else Y2 := by
      show toM _ _ _ = _
      rw [ey]; split
      · exact ty
      · exact dy
    have hz : tmv C L.M.n base s' L.R.z = if k.testBit (j - 1) then Z3 else Z2 := by
      show toM _ _ _ = _
      rw [ez]; split
      · exact tz
      · exact dz
    rw [hx, hy, hz]
    exact hstep

/-- `Q 0` accepts what `R` holds at the end, if `Q L.nbits` accepts what it
holds at the start and an iteration keeps `Q` (`Step`), for the scalar `k`
whose bits are the table at `L.bits`; only `powClob` and `ladWx` change. -/
theorem ladder_ok {k : Nat} {Q : Nat → Fe C → Fe C → Fe C → Prop} {S : Impl.Weierstrass.Mont.Modulus}
    (hM : ModOk S.k S.m) (hkS : S.k = L.M.n) (hmS : S.m = C.p) (hp : UnitMod C.p (2 ^ (64 * L.M.n)))
    (hL : LadLayI L) {s : State} (hs : WsReg s base)
    (hlt : ∀ x ∈ ladR L, wordsVal s.mem base x L.M.n < C.p) (hstep : Step L C base s k Q)
    (hR : Q L.nbits (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z))
    (hbits : ∀ t < L.nbits, s.mem (off base (L.bits + t)) = if k.testBit t then 1 else 0) :
    WP isa (ladder L S) s fun s' => Rk powClob s s' ∧ Unch base (ladWx L) s.mem s'.mem ∧
      (∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal s'.mem base x L.M.n < C.p) ∧
      Q 0 (tmv C L.M.n base s' L.R.x) (tmv C L.M.n base s' L.R.y) (tmv C L.M.n base s' L.R.z) := by
  have hnb := hL.lay.nbits
  have hnb' := hL.nbits
  rw [ladder]
  refine WP.seq (wp_step (exec_li hnb') (WP.block_nil ?_))
  have K₁ : Kp [.r31] s (s.write .r31 (BitVec.ofNat 64 L.nbits)) := Kp.write _ _ (by decide)
  refine countLoop_ok (Inv := fun j s' => LadInv L C base Q s s' j) (n := L.nbits)
    (fun j s' hi => hi.r31)
    (fun j s' h1 h2 hi => ladderBody_ok hM hkS hmS hp hL (fun x hx => hlt x (mem_ladRo_ladR hx))
      hstep hbits h1 h2 hi)
    (fun s' hi => ⟨hi.keep, hi.unch, hi.lt, hi.q⟩) hnb.1 (by omega_using [hnb])
    ⟨hs.of_kp K₁, by simp only [write_gpr, ite_true], K₁.rk, Unch.refl _ _ _,
      fun x hx => hlt x (List.mem_append_right _ hx), hR⟩

end body

end VG.Proof.Weierstrass.PPC64LE.Point
