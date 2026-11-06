module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Digit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.DigitTiming
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Window
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.StepDTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTableTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CacheBuild
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableCoZ
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# Timing of the public NAF multiplication

The pieces of the multiplication whose timing taint tracking checks
(`WindowChecks`); the cache of the table's `Z²` and `Z³` (`cache_relCT`)
and `D = O` and the count (`head_relCT`), for the values they set, in two
runs multiplying the same point by the same scalar.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.PubNaf

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- The pieces of the multiplication whose timing taint tracking checks. -/
structure WindowChecks (K : WinCfg) : Prop where
  table : TableChecks K
  cache : FieldCT (cache K)
  infinity : FieldCT (.block (Jacobian.infinity K K.D))
  counter : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
    (.block [.movz .x .x19 (BitVec.ofNat 16 (64 * K.M.n)) 0])
  step : StepChecks K
  finish : FieldCT (finish K)

theorem digitLive_sub (K : WinCfg) :
    ∀ x ∈ digitLive K, x ∈ [K.D.x, K.D.y, K.D.z] ++ (winRo K ++ winTblSlots K) := by
  intro x hx
  simp only [digitLive, jacCoords, List.mem_append] at hx ⊢
  rcases hx with (hx | hx) | hx
  · exact Or.inr (Or.inl hx)
  · exact Or.inr (Or.inr hx)
  · exact Or.inl hx

/-- The slots read only and the table survive the cache. -/
theorem cache_keep {K : WinCfg} {size : Nat} (hL : NafLay K size) {base : Addr} {m m' : Mem}
    (hU : Unch base (cacheW K ++ loopW K) m m') (hn : base.toNat + size ≤ 2 ^ 64) :
    ∀ x ∈ winRo K ++ winTblSlots K, wordsVal m' base x K.M.n = wordsVal m base x K.M.n := by
  have hW := hL.win
  have hC := hL.cache
  intro x hx
  have hs : x ∈ winSlots K := by
    rcases List.mem_append.mp hx with hx | hx
    · exact winRo_slots K x hx
    · simp only [winSlots, List.mem_append]; exact Or.inr hx
  refine hU.wordsVal (fun w hw => ?_) (by have := hW.lay.le x hs; omega_using [hn, this])
  rcases List.mem_append.mp hw with hw | hw
  · simp only [cacheW, List.mem_singleton] at hw; subst hw; exact Or.inl (hC.slots x hs)
  · rcases List.mem_append.mp hx with hx | hx
    · exact hW.ro_w hx w (loopW_sub K w hw)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have hi' := List.mem_range.mp hi
      simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw
      rcases hw with ⟨y, hy, rfl⟩ | rfl
      · exact (hW.tbl_apart (List.mem_append_right _ hy) hi').symm
      · exact hW.lay.tmp _ hs

/-- The cache, for the values of the table: the slots read only and the table keep their values. -/
theorem cache_relCT {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : NafLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hc : WindowChecks K) {P : Point C} {E : Nat → Fe C} :
    RelCT isa (fun s t => FieldPair K.M base size C.p (· ∈ winSlots K) (winRo K ++ winTblSlots K) E s t ∧
        OddTbl K C base P 8 s ∧ OddTbl K C base P 8 t)
      (cache K) (FieldPair K.M base size C.p (· ∈ winSlots K) (winRo K ++ winTblSlots K) E) := by
  apply relCT_of_ct hc.cache (fun s t h => h.1.public)
  intro s t ⟨hp', Ts, Tt⟩
  let F := fun (a : State) (b : State) => Scr b base size ∧ KeepRegs (nafClob K.M.n) a b ∧
    Unch base (cacheW K ++ loopW K) a.mem b.mem ∧ ModOkA K.M size C.p b.mem base ∧
    OddTbl K C base P 8 b ∧ CacheUpTo K C base 8 b
  refine ⟨F s, F t, cacheTo_ok hL hp hp'.left.scr hp'.left.mod Ts 8 (Nat.le_refl _),
    cacheTo_ok hL hp hp'.right.scr hp'.right.mod Tt 8 (Nat.le_refl _), fun s' t' fs ft => ?_⟩
  obtain ⟨ss, ks, Us, Ms, -, -⟩ := fs
  obtain ⟨st, kt, Ut, Mt, -, -⟩ := ft
  have inv : ∀ {a b : State}, Inv K.M base size C.p (· ∈ winSlots K) (winRo K ++ winTblSlots K) E a →
      Scr b base size → ModOkA K.M size C.p b.mem base → Unch base (cacheW K ++ loopW K) a.mem b.mem →
      Inv K.M base size C.p (· ∈ winSlots K) (winRo K ++ winTblSlots K) E b :=
    fun ia sb mb ub => ⟨sb, mb, ia.sl, fun x hx => by
      rw [cache_keep hL ub ia.scr.nowrap x hx]; exact ia.lt x hx, fun x hx => by
      rw [cache_keep hL ub ia.scr.nowrap x hx]; exact ia.val x hx⟩
  exact ⟨inv hp'.left ss Ms Us, inv hp'.right st Mt Ut, ks.sp.trans (hp'.sp.trans kt.sp.symm)⟩

/-- `D = O` and the count, for the values they set. -/
theorem head_relCT {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : NafLay K size)
    (hone : K.one < C.p) (hc : WindowChecks K) {E : Nat → Fe C} :
    RelCT isa (FieldPair K.M base size C.p (· ∈ winSlots K) (winRo K ++ winTblSlots K) E)
      (.block (Jacobian.infinity K K.D ++
        ([.movz .x .x19 (BitVec.ofNat 16 (64 * K.M.n)) 0] : List Instr)))
      (fun s t => (∃ E', FieldPair K.M base size C.p (· ∈ winSlots K) (digitLive K) E' s t) ∧
        s.gpr .x19 = BitVec.ofNat 64 (64 * K.M.n) ∧ t.gpr .x19 = BitVec.ofNat 64 (64 * K.M.n)) := by
  have hW := hL.win
  have hDs : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ winSlots K := fun x hx => winOther_mem (D_other K x hx)
  apply RelCT.block_append
  refine RelCT.seq (infinity_relCT hW.lay hL.al.al hDs hone hc.infinity) ?_
  have cnt := keepsField_relCT (M := K.M) (base := base) (size := size) (m := C.p)
    (Sl := (· ∈ winSlots K)) (V := [K.D.x, K.D.y, K.D.z] ++ (winRo K ++ winTblSlots K))
    (E := infinityEnv K.M C.p K.one E K.D) (pub := [.x0]) (rs := [.x19]) (Pre := fun _ => True)
    (Post := fun a => a.gpr .x19 = BitVec.ofNat 64 (64 * K.M.n)) (by decide) hc.counter
    (fun a b hp _ _ => ⟨hp.sp, fun q hq => pub_x0 hp (Taint.mem_ofRegs.mp hq)⟩)
    (fun a _ _ => setCounter_ok a (j := 64 * K.M.n) (by have := hL.n6; omega_arith))
  exact cnt.mono (fun _ _ h => ⟨h, trivial, trivial⟩)
    (fun _ _ ⟨h, a, b⟩ => ⟨⟨_, h.sub (digitLive_sub K)⟩, a, b⟩)

end VG.Proof.Weierstrass.AArch64.PubNaf
