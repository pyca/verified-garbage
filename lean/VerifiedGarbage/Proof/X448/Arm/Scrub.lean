module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Ed448.CombFacts
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.X448.Arm.Lit
import VerifiedGarbage.Proof.X448.Arm.BaseLit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.X448.Arm.Lit
meta import VerifiedGarbage.Proof.X448.Arm.BaseLit
meta import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.X448.Contract
public import VerifiedGarbage.Proof.Xdh.Arm
public import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Xdh.Arm
meta import VerifiedGarbage.Spec.X448.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.X448.Contract
public import VerifiedGarbage.Proof.X448.Arm.Main
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X448.Arm.Main
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
public import VerifiedGarbage.Impl.X448.Arm.Base
public import VerifiedGarbage.Proof.Ed448.CombRef
public import VerifiedGarbage.Proof.X448.Arm.Ops
import VerifiedGarbage.Proof.X448.Arm.Iter
import VerifiedGarbage.Proof.Ed448.Arm.BaseStep
import VerifiedGarbage.Proof.Ed448.Arm.BaseMain
import VerifiedGarbage.Proof.X448.Arm.Bits
import VerifiedGarbage.Proof.X448.Arm.BitWrite
import VerifiedGarbage.Proof.X448.Arm.Finish
import VerifiedGarbage.Proof.X448.Arm.Inv
import VerifiedGarbage.Proof.X448.Arm.Carry
import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Impl.X448.Arm.Base
meta import VerifiedGarbage.Proof.Ed448.CombRef
meta import VerifiedGarbage.Proof.X448.Arm.Ops
meta import VerifiedGarbage.Proof.X448.Arm.Iter
meta import VerifiedGarbage.Proof.Ed448.Arm.BaseStep
meta import VerifiedGarbage.Proof.Ed448.Arm.BaseMain
meta import VerifiedGarbage.Proof.X448.Arm.Bits
meta import VerifiedGarbage.Proof.X448.Arm.BitWrite
meta import VerifiedGarbage.Proof.X448.Arm.Finish
meta import VerifiedGarbage.Proof.X448.Arm.Inv
meta import VerifiedGarbage.Proof.X448.Arm.Carry
meta import VerifiedGarbage.Proof.Framework.Range

/-! ### `X448.Arm.Base`, which only this module used -/

section

/-!
# X448 of the base point on ARMv7: `Verified`

`vg_x448_base` is Ed448's base-point multiplication on this target, the
four-column comb (`Proof/Ed448/Arm/BaseStep.lean`'s `combLoop_ok`), on the
bits of the decoded scalar (X448's `bits_ok`, and `zeroTop_ok` for the eight
bits above them), then `Y² / X²` of the comb's point by the ladder's inversion
and output (`invert_ok`, `finish_ok`): `correctBase`, given that this is X448
of the base point (`Proof.Ed448.BaseCombUOk`, proven with the group law in
`Proof/Ed448/CombFacts.lean`, which only the registration file imports).

Constant time (by taint tracking: the only branches are on the loop counters,
and every address is an argument plus a constant or a counter; with `umaal`,
by `taintU`, on the code itself),
satisfiability, and the shared contract of `Spec/`.
-/

@[expose] public section

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448
open VG.Proof.Ed448 (BaseCombUOk comb)
open VG.Proof.Ed448.Arm (CombInv combLoop_ok initSlots_ok initSlots_E initSlots_bounded baseEntry_eq pt
  doubleFields)
open VG.Proof.X25519.Arm (wp_mov wp_strb op2_imm op2_reg)

variable {fv : Bool}

/-- The bytes of bits 448–455 at `BITS` are zero. -/
theorem zeroTop_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block zeroTop) s fun t =>
      (∀ j < 8, t.mem (off base (BITS + 448 + j)) = 0) ∧ Outside base (BITS + 448) 8 s.mem t.mem ∧
        Keeps [.r3] s t := by
  have hB : BITS = 3072 := rfl
  unfold zeroTop
  refine wp_mov (op2_imm (by decide)) fun u hu => ?_
  obtain ku : Keeps [.r3] s u := rest_keeps (hu.rest (by decide))
  obtain hsu := hs.of_keeps ku (by decide)
  let inv := fun n (t : State) =>
    (∀ j < n, t.mem (off base (BITS + 448 + j)) = 0) ∧ Outside base (BITS + 448) 8 u.mem t.mem ∧ Keeps [] u t
  obtain step : ∀ n t, n < 8 → inv n t →
      WP isa (.block [.strb .r3 .r0 (BITS + 448 + n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    obtain hst := hsu.of_keeps tk (by decide)
    refine wp_strb (by omega_using [hB, hn]) (hst.ea (by omega_using [hB, hn]))
      (hst.write (by omega_using [hB, hn])) fun v hv => WP.block_nil ⟨fun j hj => ?_, tm.trans ?_,
        tk.trans (rest_keeps (hv.rest _))⟩
    · rw [hv.mem, writeW8_apply]
      obtain eq : off base (BITS + 448 + j) = off base (BITS + 448 + n) ↔ j = n := by
        rw [off_eq_iff base (by omega_using [hB, hj, hn]) (by omega_using [hB, hn])]
        omega_using []
      by_cases he : j = n
      · rw [ite_eq_left (eq.mpr he), tk.1 _ (by decide), hu.gpr]; rfl
      · rw [ite_eq_right (fun h => he (eq.mp h))]; exact tf j (by omega_using [hj, he])
    · intro x hx
      rw [hv.mem]
      exact writeW8_outside _ _ _ (by omega_using [hB, hn]) (by omega_using [hn, hx])
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) u
    ⟨fun _ hj => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩) fun t ⟨tf, tm, tk⟩ =>
    ⟨tf, by rw [← hu.mem]; exact tm, ku.trans (tk.mono (by simp))⟩

/-- `X²` and `Y²`. -/
def uFields : List FieldOp := [.mul 2 0 0, .mul 1 1 1]

theorem correctBase (hu : BaseCombUOk) {s₀ : State} (hp : BasePre s₀) :
    WP isa (x448Base fv) s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      Proof.X448.x448BaseArm.post s₀ s' := by
  obtain ⟨base, hbase⟩ : ∃ b, State.addr (s₀.gpr .r2) = b := ⟨_, rfl⟩
  have hB : BITS = 3072 := rfl
  have hw₀ : (⟨base, 8192⟩ : Region) ∈ s₀.wr := by rw [hp.wr, ← hbase]; simp
  obtain kd : ∀ j < 56, 8192 ≤ ofs base (off (State.addr (s₀.gpr .r1)) j) :=
    fun j hj => far (hbase ▸ hp.scalar_sc) hj (by decide)
  obtain kr : ∀ j < 56, InRegions (s₀.rd ++ s₀.wr) (off (State.addr (s₀.gpr .r1)) j) 1 := fun j hj =>
    ⟨scalarR s₀, by rw [hp.rd]; simp, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩
  obtain ⟨hz, hx⟩ := hu (Spec.X448.bytesAt s₀.mem (State.addr (s₀.gpr .r1)) 56)
  obtain ⟨K, hK⟩ : ∃ K, Spec.X448.decodeScalar448 (Spec.X448.bytesAt s₀.mem (State.addr (s₀.gpr .r1)) 56) = K :=
    ⟨_, rfl⟩
  rw [hK] at hz hx
  unfold x448Base
  rw [baseEntry_eq, List.append_assoc, List.append_assoc, List.singleton_append]
  -- The entry.
  refine WP.seq (wp_mov (op2_reg _ _) fun u hu' => ?_)
  refine VG.Proof.X25519.Arm.WP.append (setupHead_ok (s := u) (base := base) (by rw [hu'.gpr, hbase])
    (by rw [hu'.wr]; exact hw₀) (by rw [hu'.gpr]; exact hp.sc_fit)) fun v ⟨hsv, rv, rl, svv, ov, kv⟩ => ?_
  refine VG.Proof.X25519.Arm.WP.append (initSlots_ok hsv) fun w ⟨lw, ow, kw⟩ => ?_
  obtain hsw : Scr w base := hsv.of_keeps kw (by decide)
  refine WP.mono (zeroTop_ok hsw) fun x ⟨zx, ox, kx⟩ => ?_
  obtain hsx : Scr x base := hsw.of_keeps kx (by decide)
  obtain ksx : Keeps [.r3, .r8, .r10, .r0, .r6, .r4] s₀ x :=
    (rest_keeps (hu'.rest (by decide))).trans ((kv.mono (by decide)).trans ((kw.mono (by decide)).trans
      (kx.mono (by decide))))
  obtain r1x : x.gpr .r1 = s₀.gpr .r1 := ksx.1 _ (by decide)
  obtain r8x : x.gpr .r8 = s₀.gpr .r0 := by
    rw [kx.1 _ (by decide), kw.1 _ (by decide), rv, hu'.other _ (by decide)]
  obtain r10x : x.gpr .r10 = s₀.gpr .lr := by
    rw [kx.1 _ (by decide), kw.1 _ (by decide), rl, hu'.other _ (by decide)]
  obtain mx : Outside base 0 8192 s₀.mem x.mem := by
    rw [← hu'.mem]
    exact (ov.mono (by decide) (by decide)).trans ((ow.mono (by decide) (by decide)).trans
      (ox.mono (by omega_using [hB]) (by omega_using [hB])))
  obtain sn : ∀ i < 8, saved[i]! ≠ .r3 := by decide
  obtain svx : Saved base s₀.gpr x.mem := by
    have svw : Saved base s₀.gpr w.mem := by
      intro i hi
      rw [ow.word (by omega_using [hi]) (by omega_using [hi]), svv i hi]
      exact hu'.other _ (sn i hi)
    exact svw.outside ox (by omega_using [hB])
  -- The scalar's bits.
  refine WP.seq (WP.mono (bits_ok (k := State.addr (s₀.gpr .r1)) hsx (by rw [r1x])
    (by rw [r1x]; exact hp.scalar_fit) (by rw [ksx.2.1, ksx.2.2]; exact kr) kd)
    fun y ⟨gy, rdy, wry, oy, bitsy⟩ => ?_)
  rw [bytesAt_outside mx kd, hK] at bitsy
  obtain ky : Keeps bitRegs x y := ⟨gy, rdy, wry⟩
  obtain hsy : Scr y base := hsx.of_keeps ky (by decide)
  obtain bits : ∀ t < 456, y.mem (off base (BITS + t)) = BitVec.ofNat 8 ((K >>> t) &&& 1) := fun t ht => by
    rcases Nat.lt_or_ge t 448 with h | h
    · exact bitsy t h
    · rw [oy _ (Or.inr (by rw [ofs_off' base (by omega_using [hB, ht])]; omega_using [h])), hz t h,
        show BITS + t = BITS + 448 + (t - 448) by omega_using [h]]
      exact zx (t - 448) (by omega_using [ht, h])
  obtain slotOut : ∀ i : Index, ∀ j < 28, limbs y.mem base (slot i.val) j = limbs w.mem base (slot i.val) j :=
    fun i j hj => by
      have hi := i.isLt
      rw [oy.limbs (d := slot i.val) (Or.inl (by simp only [slot]; omega_using [hB, hi]))
          (by simp only [slot]; omega_using [hi]) hj,
        ox.limbs (d := slot i.val) (Or.inl (by simp only [slot]; omega_using [hB, hi]))
          (by simp only [slot]; omega_using [hi]) hj]
  obtain ey : ∀ i : Index, E y.mem base i = toFe (Impl.Ed448.Arm.initVal i.val) := fun i => by
    rw [← initSlots_E lw i]
    exact congrArg toFe (Radix16.valN_congr (slotOut i))
  obtain by' : BoundedEnv y.mem base := fun i j hj => by
    rw [slotOut i j hj]; exact initSlots_bounded lw i j hj
  -- The comb.
  refine WP.seq (WP.mono (combLoop_ok (s₀ := y) (s := y) bits (fun s' h1 h2 h3 h4 h5 => ?_))
    fun z hz' => ?_)
  · have k' : Keeps (.r11 :: workRegs) y s' :=
      ⟨fun r hr => h2 r (fun e => hr (by subst r; exact List.mem_cons_self)), h4, h5⟩
    refine ⟨hsy.of_keeps k' (by decide), h3 ▸ by', k', h1, h3 ▸ Outside2.refl _ _ _ _ _ _, ?_, ?_, ?_⟩
    · rw [h3]; simp only [pt, ey]
      rw [show ((0 : Index) : Nat) = 0 from rfl, show ((1 : Index) : Nat) = 1 from rfl,
        show ((2 : Index) : Nat) = 2 from rfl,
        show Impl.Ed448.Arm.initVal 0 = Spec.Ed448.identity.X.val from rfl,
        show Impl.Ed448.Arm.initVal 1 = Spec.Ed448.identity.Y.val from rfl,
        show Impl.Ed448.Arm.initVal 2 = Spec.Ed448.identity.Z.val from rfl, toFe_self, toFe_self, toFe_self]
      rfl
    · rw [h3, ey, show ((10 : Index) : Nat) = 10 from rfl,
        show Impl.Ed448.Arm.initVal 10 = Spec.Ed448.basePoint.Z.val from rfl, toFe_self]
      rfl
    · rw [h3, ey]; exact toFe_self _
  -- `X²` and `Y²`, the inversion and the output.
  rw [show uOps = uFields.map FieldOp.impl from rfl]
  refine WP.seq (WP.mono (ops_ok hz'.scr hz'.bounded uFields) fun a ⟨ka, ba, ea⟩ => ?_)
  obtain hsa := ka.scr hz'.scr
  refine WP.seq (WP.mono (invert_ok hsa ba) fun b ⟨kb, bb, eb⟩ => ?_)
  obtain kyb : Keeps (.r11 :: workRegs) y b :=
    hz'.regs.trans ((ka.regs.mono (fun _ h => List.mem_cons_of_mem _ h)).trans kb.regs)
  obtain r8b : b.gpr .r8 = s₀.gpr .r0 := by rw [kyb.1 _ (by decide), gy _ (by decide), r8x]
  obtain r10b : b.gpr .r10 = s₀.gpr .lr := by rw [kyb.1 _ (by decide), gy _ (by decide), r10x]
  obtain svb : Saved base s₀.gpr b.mem :=
    (((svx.outside oy (by decide)).outside2 hz'.mem (by decide) (by decide)).outside2 ka.mem (by decide)
      (by decide)).outside2 kb.mem (by decide) (by decide)
  obtain wrb : b.wr = s₀.wr := by rw [kyb.2.2, wry, ksx.2.2]
  obtain hwb : ∀ j < 56, InRegions b.wr (off (State.addr (s₀.gpr .r0)) j) 1 := fun j hj =>
    ⟨outR s₀, by rw [wrb, hp.wr]; simp, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩
  refine WP.mono (finish_ok (kb.scr hsa) bb (congrArg State.addr r8b) (by rw [r8b]; exact hp.out_fit) hwb
    (fun j hj => far_output (hbase ▸ hp.out_sc) hj) svb) fun s' ⟨restored, lr', _, _, result⟩ => ?_
  refine ⟨fun r hr => ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact restored 0 (by decide)
    · exact restored 1 (by decide)
    · exact restored 2 (by decide)
    · exact restored 3 (by decide)
    · exact restored 4 (by decide)
    · exact restored 5 (by decide)
    · exact restored 6 (by decide)
    · exact restored 7 (by decide)
    · exact lr'.trans r10b
  · change Spec.X448.bytesAt s'.mem (State.addr (s₀.gpr .r0)) 56 = _
    rw [result, hx]
    apply congrArg Spec.X448.encodeUCoordinate
    obtain hX : E z.mem base 0 = (comb K 114).X := congrArg Spec.Ed448.Point.X hz'.r
    obtain hY : E z.mem base 1 = (comb K 114).Y := congrArg Spec.Ed448.Point.Y hz'.r
    rw [eb, invEnv_x2, invEnv_eval, ea, ← hX, ← hY]
    rfl

/-! ## `Verified` -/

/-- A state satisfying `vg_x448_base`'s precondition. -/
def satBaseState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 56⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]

theorem x448Base_ok (hu : BaseCombUOk) (s : State) (hs : Proof.X448.x448BaseArm.pre s) :
    ∃ t s', Exec isa (Impl.X448.Arm.x448Base fv) s t s' ∧ abiPreserved s s' ∧
      Proof.X448.x448BaseArm.post s s' := by
  obtain ⟨t, s', he, h⟩ := correctBase hu (BasePre.of s hs)
  exact ⟨t, s', he, ⟨h.1, Exec.sp he⟩, h.2⟩

theorem x448Base_ct : ConstantTime isa Proof.X448.x448BaseArm.pre Proof.X448.x448BaseArm.pub
    (Impl.X448.Arm.x448Base fv) := by
  obtain ha : ∀ s₁ s₂, Proof.X448.x448BaseArm.pre s₁ → Proof.X448.x448BaseArm.pre s₂ →
      Proof.X448.x448BaseArm.pub s₁ s₂ → VG.Arm.Taint.Agree (Taint.ofRegs [.r0, .r1, .r2]) s₁ s₂ := by
    intro s₁ s₂ _ _ ⟨h1, h2, h3, _⟩
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption
  cases fv
  · exact Taint.constantTime_eraseOff_of_eq (Taint.ofRegs [.r0, .r1, .r2]) (Taint.noBase_ofRegs _) ha
      (c' := x448BaseErased) rfl (by native_taint_decide)
  · exact VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r0, .r1, .r2]) ha (by taint_decide)

theorem x448Base_verified (hu : BaseCombUOk) :
    Verified Arm.target (Impl.X448.Arm.x448Base fv) (Spec.X448.x448BaseContract Arm.abi) :=
  Verified.of_correct (x448Base_ok hu) x448Base_ct (by
    sig_implies [Spec.X448.x448BaseContract, Spec.X448.x448BaseSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Proof.X448.x448BaseArm]
      [satBaseState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using satBaseState)

end VG.Proof.X448.Arm

end

end

/-! ### `X448.Arm.Exchange`, which only this module used -/

section

/-! ### `X448.Arm.Verified`, which only this module used -/

section

/-!
# X448 on ARMv7: `Verified`

Constant time (by taint tracking: the only branches are on the loop counters,
and every address is an argument plus a constant or a counter; with `umaal`,
by `taintU`, for which what a `umaal` writes is secret),
satisfiability, and the shared contract of `Spec/`.
-/

@[expose] public section

namespace VG.Proof.X448.Arm

open VG VG.Arm

variable {fv : Bool}

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 56⟩, ⟨0x3000, 56⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]

theorem x448_ok (s : State) (hs : Proof.X448.x448Arm.pre s) :
    ∃ t s', Exec isa (Impl.X448.Arm.x448 fv) s t s' ∧ abiPreserved s s' ∧
      Proof.X448.x448Arm.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (Pre.of s hs)
  exact ⟨t, s', he, ⟨h.1, Exec.sp he⟩, h.2⟩

theorem x448_ct : ConstantTime isa Proof.X448.x448Arm.pre Proof.X448.x448Arm.pub
    (Impl.X448.Arm.x448 fv) := by
  obtain ha : ∀ s₁ s₂, Proof.X448.x448Arm.pre s₁ → Proof.X448.x448Arm.pre s₂ →
      Proof.X448.x448Arm.pub s₁ s₂ → VG.Arm.Taint.Agree (Taint.ofRegs [.r0, .r1, .r2, .r3]) s₁ s₂ := by
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, _⟩
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  cases fv
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3]) ha (by native_taint_decide)
  · exact VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r0, .r1, .r2, .r3]) ha (by taint_decide)

theorem x448_verified :
    Verified Arm.target (Impl.X448.Arm.x448 fv) (Proof.X448.x448Contract Arm.abi) :=
  Verified.of_correct x448_ok x448_ct (by
    sig_implies [Proof.X448.x448Contract, Proof.X448.x448Sig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Proof.X448.x448Arm]
      [satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using satState)

end VG.Proof.X448.Arm

end

end

/-!
# X448 exchange, with RFC 7748's check, on ARMv7

Untrusted: everything here is checked by Lean. Each implementation of
`vg_x448` is a callee of `Impl.Xdh.Arm.exchange` by its shared contract
(`callee`), so `vg_x448_exchange`, which calls it and checks its result
(`Proof/Xdh/Arm.lean`), is `Verified` against its shared contract, with the
8 bytes of stack its frames use.
-/

@[expose] public section

namespace VG.Proof.X448.Arm.Exchange

open VG VG.Arm VG.Proof.Xdh.Arm

theorem callee {c : Prog isa} (hv : Verified Arm.target c (Proof.X448.x448Contract Arm.abi))
    (hn : c.noFrames = true) : Callee 56 8192 Spec.X448.x448 c (Proof.X448.x448Contract Arm.abi) where
  hv := hv.1
  hct := hv.2.1
  pre s h := by
    obtain ⟨rd, wr, d1, d2, d3, d4, d5, b0, b1, b2, b3⟩ := h
    sig_pre [Proof.X448.x448Contract, Proof.X448.x448Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
    sig_reduce [Proof.X448.x448Contract, Proof.X448.x448Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr, List.getD]
    sig_and_intros
    all_goals first
      | with_reducible assumption
      | trivial
      | omega_using []
      | exact Region.Disjoint.symm ‹_›
  post s s' h := by
    sig_post [Proof.X448.x448Contract, Proof.X448.x448Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] at h
    exact h
  pub s₁ s₂ h := by
    obtain ⟨q0, q1, q2, q3, qsp⟩ := h
    sig_pub [Proof.X448.x448Contract, Proof.X448.x448Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
    sig_reduce [Proof.X448.x448Contract, Proof.X448.x448Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
    sig_and_intros
    all_goals first | with_reducible assumption | trivial
  nf := hn

/-- `vg_x448_exchange` calling `c`, an implementation of `vg_x448`, as `name`. -/
theorem exchange_verified {c : Prog isa} (name : String)
    (hv : Verified Arm.target c (Proof.X448.x448Contract Arm.abi)) (hn : c.noFrames = true)
    (ht : ∃ hc, (taint.check (Taint.ofRegs [.r1]) (.block (Impl.Xdh.Arm.check 56)) hc).isSome = true) :
    Verified Arm.target (Impl.Xdh.Arm.exchange name c 56) (Spec.X448.exchangeContract Arm.abi 8) :=
  Verified.of_correct (k := exContract 56 8192 Spec.X448.x448) (exchange_correct (callee hv hn) (by decide))
    (exchange_ct (callee hv hn) ht) (by
      contract_implies [Spec.X448.exchangeContract, Spec.X448.exchangeSig, Proof.X448.x448Sig,
        exContract, ExPre, CallPre, ExPost, Pub, Proof.Xdh.Arm.outR, Proof.Xdh.Arm.scR, Proof.Xdh.Arm.ptR, Proof.Xdh.Arm.wsR,
        Proof.Xdh.Arm.frR, ret32, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val,
        Arm.State.addr] [Proof.X448.Arm.satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.X448.Arm.satState)

/-- The taint analysis of the check. -/
theorem check_taint : ∃ hc, (taint.check (Taint.ofRegs [.r1]) (.block (Impl.Xdh.Arm.check 56)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `vg_x448_exchange` with the field's multiplication `fv` (`Proof/Variants/Curve448Field/Arm.lean`). -/
theorem exchange_variant (fv : Bool) :
    Verified Arm.target
      (Impl.Xdh.Arm.exchange ("vg_x448" ++ Impl.X448.Arm.suffix fv) (Impl.X448.Arm.x448 fv) 56)
      (Spec.X448.exchangeContract Arm.abi 8) :=
  exchange_verified _ Proof.X448.Arm.x448_verified (by cases fv <;> lit_decide) check_taint

end VG.Proof.X448.Arm.Exchange

end

end

/-!
# X448 on ARMv7, without secret residue

`vg_x448_base`, with either multiplication of the field
(`Proof/Variants/Curve448Field/Arm.lean`), has no frames: it is emitted
followed by instructions that set the registers a callee may change, and the
flags, to constants (`Impl.X448.Arm.Fn`). `vg_x448_exchange` calls `vg_x448`
from frames of 8 bytes, and its postcondition reads the memory on return only
at `out` (`Arm.Scrub.PostOut`): it is emitted followed by a wipe of those
bytes too. The code's shape is the same with either multiplication but where
it is chosen (`mulFn_shape`, `ops_shape`), so what the cleanup needs of it is
proven once for both; `Fn` has the theorem of each, which its registration
binds.
-/

@[expose] public section

namespace VG.Proof.X448.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack

/-- The byte `k` of a region of more than `k` bytes at `o`. -/
theorem contains_of {o : Addr} {k N : Nat} (hk : k < N) : Region.Contains ⟨o, N⟩ (o + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains]
  rw [BitVec.add_comm o, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
  have := Nat.mod_le k (2 ^ 64)
  omega_using [hk]

/-- The `n` octets at `o` read the memory only within `⟨o, N⟩`, `n ≤ N`. -/
theorem bytesAt_of {m₁ m₂ : Mem} {o : Addr} {n N : Nat}
    (h : ∀ a, Region.Contains ⟨o, N⟩ a 1 → m₁ a = m₂ a) (hN : n ≤ N) :
    Spec.X448.bytesAt m₂ o n = Spec.X448.bytesAt m₁ o n := by
  simp only [Spec.X448.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  exact (h _ (contains_of (by omega_using [this, hN]))).symm

/-! ### The shape of the field's code

What the cleanup needs of a function that multiplies in the field
(`Code.noFrames`, `armStack`, `noIcall`) depends only on its shape, which is
the same with either multiplication but where it is chosen (`mulFn`): these
state it once for both, and each caller proves its own shape for any `u`
from them, rather than evaluating each variant's code again. -/

theorem mulFn_shape (u : Bool) : (Impl.X448.Arm.mulFn u).noFrames = true ∧
    armStack (Impl.X448.Arm.mulFn u) = 0 ∧ noIcall (Impl.X448.Arm.mulFn u) = true := by
  cases u <;> simp only [Impl.X448.Arm.mulFn, Impl.X448.Arm.fn, Impl.X448.Arm.mul, Impl.X448.Arm.mulU,
    Code.noFrames, armStack, noIcall, Bool.false_eq_true, ↓reduceIte, Bool.and_self, Nat.max_self, and_self]

theorem ops_shape (u : Bool) (os : List Impl.X448.Arm.Op) : (Impl.X448.Arm.ops u os).noFrames = true ∧
    armStack (Impl.X448.Arm.ops u os) = 0 ∧ noIcall (Impl.X448.Arm.ops u os) = true := by
  induction os with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons o os ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    obtain ⟨m1, m2, m3⟩ := mulFn_shape u
    cases o <;> simp only [Impl.X448.Arm.ops, Impl.X448.Arm.Op.code, Impl.X448.Arm.callFn,
      Impl.X448.Arm.mulA24Call, Impl.X448.Arm.mulA24Fn, Impl.X448.Arm.addFn, Impl.X448.Arm.subFn,
      Impl.X448.Arm.fn, Code.noFrames, armStack, noIcall, h1, h2, h3, m1, m2, m3, Bool.and_self,
      Nat.max_self, and_self]

theorem x448Base_noFrames (u : Bool) : (Impl.X448.Arm.x448Base u).noFrames = true := by
  simp only [
    Impl.Ed448.Arm.combStep, Impl.Ed448.Arm.combLoop, Impl.X448.Arm.callFn, Impl.X448.Arm.Op.code,
    Impl.X448.Arm.ops, Impl.X448.Arm.sqn, Impl.X448.Arm.invert, Impl.X448.Arm.bits,
    Impl.X448.Arm.finish, Impl.X448.Arm.x448Base, Code.noFrames,
    (Proof.X448.Arm.Scrub.ops_shape _ _).1, (Proof.X448.Arm.Scrub.mulFn_shape _).1, Bool.and_self]

theorem exchange_codeOk (u : Bool) :
    CodeOk (Impl.Xdh.Arm.exchange ("vg_x448" ++ Impl.X448.Arm.suffix u) (Impl.X448.Arm.x448 u) 56) 8 := by
  simp only [CodeOk,
    Impl.X448.Arm.callFn, Impl.X448.Arm.Op.code, Impl.X448.Arm.ops, Impl.X448.Arm.stepBody,
    Impl.X448.Arm.step, Impl.X448.Arm.ladder, Impl.X448.Arm.sqn, Impl.X448.Arm.invert,
    Impl.X448.Arm.bits, Impl.X448.Arm.finish, Impl.X448.Arm.afterSetup, Impl.X448.Arm.x448,
    Impl.Xdh.Arm.exchange, armStack, noIcall, (Proof.X448.Arm.Scrub.ops_shape _ _).2.1,
    (Proof.X448.Arm.Scrub.ops_shape _ _).2.2, (Proof.X448.Arm.Scrub.mulFn_shape _).2.1,
    (Proof.X448.Arm.Scrub.mulFn_shape _).2.2, Bool.and_self, Nat.max_self, List.length_cons,
    List.length_nil]
  decide

theorem frameOk_8 : FrameOk 8 := by decide

theorem exchangeOut (stack : Nat) :
    PostOut (Spec.X448.exchangeContract abi stack) (Spec.X448.exchangeSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun
    | [out, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.X448.exchangeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [bytesAt_of hb.1 (Nat.le_refl 56)]
      exact h

end VG.Proof.X448.Arm.Scrub

namespace VG.Proof.X448.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_x448_exchange`, with either multiplication of the field. -/
theorem exchange (u : Bool) :
    VerifiedScrubbed target (Impl.X448.Arm.Fn.exchange u) (Spec.X448.exchangeContract abi 8) 32 :=
  verifiedScrubbedF (api := Spec.X448.exchangeApi)
    { code := Impl.Xdh.Arm.exchange ("vg_x448" ++ Impl.X448.Arm.suffix u) (Impl.X448.Arm.x448 u) 56
      verified := Exchange.exchange_variant u }
    (Scrub.exchangeOut _) (scrubSideF_of (Scrub.exchange_codeOk u) Scrub.frameOk_8 _)

/-- `vg_x448_base`, with either multiplication of the field. -/
theorem x448Base (u : Bool) :
    VerifiedScrubbed target (Impl.X448.Arm.Fn.x448Base u) (Spec.X448.x448BaseContract abi) 0 :=
  verifiedScrubbed (api := Spec.X448.x448BaseApi)
    { code := Impl.X448.Arm.x448Base u, verified := Proof.X448.Arm.x448Base_verified Proof.Ed448.baseCombU_ok }
    (Scrub.x448Base_noFrames u)

end VG.Proof.X448.Arm.Fn
