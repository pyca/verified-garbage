module

public import VerifiedGarbage.Proof.X448.Arm.Main
public import VerifiedGarbage.Impl.X448.Arm.Base
public import VerifiedGarbage.Proof.Ed448.CombRef
public import VerifiedGarbage.Proof.X448.Arm.Ops
import VerifiedGarbage.Proof.X448.Arm.Iter
import VerifiedGarbage.Proof.Ed448.Arm.BaseInit
import VerifiedGarbage.Proof.Ed448.Arm.BaseStep
import VerifiedGarbage.Proof.Ed448.Arm.BaseMain
import VerifiedGarbage.Proof.X448.Arm.Bits
import VerifiedGarbage.Proof.X448.Arm.BitWrite
import VerifiedGarbage.Proof.X448.Arm.Finish
import VerifiedGarbage.Proof.X448.Arm.Inv
import VerifiedGarbage.Proof.X448.Arm.Carry
import VerifiedGarbage.Proof.X448.Arm.BaseLit
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X448.Arm.Main
meta import VerifiedGarbage.Impl.X448.Arm.Base
meta import VerifiedGarbage.Proof.Ed448.CombRef
meta import VerifiedGarbage.Proof.X448.Arm.Ops
meta import VerifiedGarbage.Proof.X448.Arm.Iter
meta import VerifiedGarbage.Proof.Ed448.Arm.BaseInit
meta import VerifiedGarbage.Proof.Ed448.Arm.BaseStep
meta import VerifiedGarbage.Proof.Ed448.Arm.BaseMain
meta import VerifiedGarbage.Proof.X448.Arm.Bits
meta import VerifiedGarbage.Proof.X448.Arm.BitWrite
meta import VerifiedGarbage.Proof.X448.Arm.Finish
meta import VerifiedGarbage.Proof.X448.Arm.Inv
meta import VerifiedGarbage.Proof.X448.Arm.Carry
meta import VerifiedGarbage.Proof.X448.Arm.BaseLit
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
meta import VerifiedGarbage.Proof.X448.Contract

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
and every address is an argument plus a constant or a counter),
satisfiability, and the shared contract of `Spec/`.
-/

@[expose] public section

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448
open VG.Proof.Ed448 (BaseCombUOk comb)
open VG.Proof.Ed448.Arm (CombInv combLoop_ok initSlots_ok initSlots_E initSlots_bounded baseEntry_eq pt
  doubleFields)
open VG.Proof.X25519.Arm (wp_mov wp_strb op2_imm op2_reg)

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
    WP isa x448Base s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
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
    ∃ t s', Exec isa Impl.X448.Arm.x448Base s t s' ∧ abiPreserved s s' ∧
      Proof.X448.x448BaseArm.post s s' := by
  obtain ⟨t, s', he, h⟩ := correctBase hu (BasePre.of s hs)
  exact ⟨t, s', he, ⟨h.1, Exec.sp he⟩, h.2⟩

theorem x448Base_ct : ConstantTime isa Proof.X448.x448BaseArm.pre Proof.X448.x448BaseArm.pub
    Impl.X448.Arm.x448Base := by
  refine Taint.constantTime_eraseOff_of_eq (Taint.ofRegs [.r0, .r1, .r2]) (Taint.noBase_ofRegs _) ?_
    (c' := x448BaseErased) rfl (by native_taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, _⟩
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> with_reducible assumption

theorem x448Base_verified (hu : BaseCombUOk) :
    Verified Arm.target Impl.X448.Arm.x448Base (Spec.X448.x448BaseContract Arm.abi) :=
  Verified.of_correct (x448Base_ok hu) x448Base_ct (by
    sig_implies [Spec.X448.x448BaseContract, Spec.X448.x448BaseSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Proof.X448.x448BaseArm]
      [satBaseState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using satBaseState)

end VG.Proof.X448.Arm
