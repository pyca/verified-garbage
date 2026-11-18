module

import VerifiedGarbage.Proof.Ed448.AArch64.FieldSums
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Ed448.AArch64.FieldSums
meta import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.X448.AArch64.Fast.Erase
meta import VerifiedGarbage.Proof.X448.AArch64.Fast.Erase
public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Combine
public import VerifiedGarbage.Proof.X448.AArch64.Fast.Finish
public import VerifiedGarbage.Proof.X448.AArch64.Fast.Setup
import VerifiedGarbage.Proof.X448.AArch64.Fast.Weave
public import VerifiedGarbage.Impl.X448.AArch64.BaseFn
public import VerifiedGarbage.Proof.X448.BaseAdd
public import VerifiedGarbage.Spec.X448.Contract
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X448.AArch64.Finish
import VerifiedGarbage.Proof.X448.Bytes
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
meta import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Combine
meta import VerifiedGarbage.Proof.X448.AArch64.Fast.Finish
meta import VerifiedGarbage.Proof.X448.AArch64.Fast.Setup
meta import VerifiedGarbage.Proof.X448.AArch64.Fast.Weave
meta import VerifiedGarbage.Impl.X448.AArch64.BaseFn
meta import VerifiedGarbage.Proof.X448.BaseAdd
meta import VerifiedGarbage.Spec.X448.Contract
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.X448.AArch64.Finish
meta import VerifiedGarbage.Proof.X448.Bytes
meta import Mathlib.Tactic.FieldSimp
meta import Mathlib.Tactic.Ring

/-! ### `X448.AArch64.Base.Main`, which only this module used -/

section

/-! ### `X448.AArch64.Base.Finish`, which only this module used -/

section

/-!
# X448 of the base point on AArch64: `Y² / X²`, encoded

Untrusted: everything here is checked by Lean. `Y²` and `X²` go to the ladder's
`x₂` and `z₂` slots; the ladder's inversion and finish (`Fast.invert_ok`,
`Fast.finish_ok`) encode `Y² · (X²)^(p-2)` to the output, reloaded from the
working space, and restore the callee-saved registers.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 Saved ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- `Y²` to slot 1 and `X²` to slot 2. -/
theorem squares_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) :
    WP isa (.block (Impl.X448.AArch64.Fast.codeOf [.mul X2 AY AY, .mul Z2 AX AX])) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧
      EV t.mem base = Function.update (Function.update (EV s.mem base) 1 (EV s.mem base 1 * EV s.mem base 1)) 2
        (EV s.mem base 0 * EV s.mem base 0) := by
  refine block_codeOf (mulOp hs hb 1 1 1 (Or.inl rfl) fun t1 k1 b1 _ _ e1 => ?_)
  refine mulOp (k1.scr hs) b1 2 0 0 (Or.inl rfl) fun t2 k2 b2 _ _ e2 => WP.block_nil ⟨k1.trans k2, b2, ?_⟩
  rw [e2, e1]
  rfl

end VG.Proof.X448.AArch64.Base

end

end


/-!
# X448 of the base point on AArch64: the whole function

Untrusted: everything here is checked by Lean. The contract the proof is
written against (the facts of `Spec.X448.x448BaseContract` it uses, stated for
AArch64), and `vg_x448_base`'s correctness against it: the comb leaves `[k] B`
on edwards448, whose `y² / x²` is `X448(k, 5)` (`x448_basePoint`).
-/

@[expose] public section

namespace VG.Proof.X448

open VG VG.AArch64 VG.Impl.X448.AArch64.Base in
/-- `vg_x448_base(out = x0, scalar = x1, scratch = x2)`, with the comb's tables at the
static `combSym`. -/
def x448BaseAArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 56⟩
    let scalar : Region := ⟨s.gpr .x1, 56⟩
    let scratch : Region := ⟨s.gpr .x2, 8192⟩
    s.rd = [scalar, ⟨s.syms combSym, 8 * combWords.length⟩] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ scalar.Disjoint scratch ∧ (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64 ∧
      Proof.X448.AArch64.Base.CombHeld s [out, scratch]
  post s s' := Spec.X448.bytesAt s'.mem (s.gpr .x0) 56 =
    Spec.X448.x448 (Spec.X448.bytesAt s.mem (s.gpr .x1) 56) Spec.X448.basePoint
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.sp = s₂.sp ∧
    s₁.syms combSym = s₂.syms combSym

end VG.Proof.X448

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 Saved ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- The precondition, by name. -/
structure Pre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x1, 56⟩, ⟨s.syms combSym, 8 * combWords.length⟩]
  wr : s.wr = [⟨s.gpr .x0, 56⟩, ⟨s.gpr .x2, 8192⟩]
  out_sc : (⟨s.gpr .x0, 56⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩
  scalar_sc : (⟨s.gpr .x1, 56⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩
  sc_fit : (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64
  held : CombHeld s [⟨s.gpr .x0, 56⟩, ⟨s.gpr .x2, 8192⟩]

theorem Pre.of (s : State) (h : Proof.X448.x448BaseAArch64.pre s) : Pre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- A byte of a region disjoint from the working space is beyond it. -/
theorem far {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < n) (hn : n ≤ 2 ^ 64) : 8192 ≤ ofs base (p + BitVec.ofNat 64 i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega_using [hi]) (by omega_using [hi, hn])) ?_
  simp only [Region.Contains]; simp only [ofs] at h; omega_using [h]

theorem far_output {base p : Addr} (hd : (⟨p, 56⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < 8192) : 56 ≤ ofs p (off base i) := by
  refine Nat.le_of_not_lt fun h => hd _ ?_ (Offset.contains_base base (d := i) (n := 1) (k := 8192) (by omega_using [hi]) (by omega_using [hi]))
  simp only [Region.Contains]
  change ofs p (off base i) + 1 ≤ 56
  omega_using [h]

/-- The tables, from the precondition. -/
theorem Pre.tbl {s : State} (hp : Pre s) : TblAt s (s.gpr .x2) (s.syms combSym) :=
  hp.held.tblAt (by rw [hp.rd]; exact List.mem_append_left _ (List.mem_cons_of_mem _
    (List.mem_singleton_self _))) (by simp)

theorem decodeScalar448_lt (kb : List Byte) : Spec.X448.decodeScalar448 kb < 256 ^ 56 := by
  rw [Spec.X448.decodeScalar448, VG.Proof.X448.decodeLittleEndian_eq]
  exact Nat.lt_of_lt_of_le (VG.Proof.X25519.leNum_lt _)
    (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))

open VG.Proof.Ed448 (Rep baseAff)

theorem correct {sE : State} (hp : Pre sE) :
    WP isa x448Base sE fun s' => (∀ r ∈ preserved, s'.gpr r = sE.gpr r) ∧
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (sE.v r).extractLsb' 0 64) ∧
      Proof.X448.x448BaseAArch64.post sE s' := by
  have hn := hp.sc_fit
  have hw : (⟨sE.gpr .x2, 8192⟩ : Region) ∈ sE.wr := by rw [hp.wr]; simp
  have kr : ∀ q < 56, InRegions (sE.rd ++ sE.wr) (sE.gpr .x1 + BitVec.ofNat 64 q) 1 := fun q hq =>
    ⟨⟨sE.gpr .x1, 56⟩, by rw [hp.rd]; simp, Offset.contains_base _ (by omega_using [hq]) (by omega_using [hq])⟩
  have kd : ∀ q < 56, 8192 ≤ ofs (sE.gpr .x2) (sE.gpr .x1 + BitVec.ofNat 64 q) :=
    fun q hq => far hp.scalar_sc hq (by decide)
  set base := sE.gpr .x2 with hbase
  set kb := Spec.X448.bytesAt sE.mem (sE.gpr .x1) 56
  set k := Spec.X448.decodeScalar448 kb
  unfold x448Base
  refine WP.seq (WP.mono (setup_ok rfl hw hn rfl kr kd hp.tbl) fun s1 R => ?_)
  have f1 : Frame s1 base s1 :=
    ⟨R.pre.scr, R.pre.env, R.pre.zero, rfl, rfl, rfl, rfl, Outside2.refl _ _ _ _ _ _⟩
  refine WP.seq (WP.mono (Ed448.AArch64.CombBase.call_ok (Or.inl rfl) f1 R.pre) fun s2 ⟨f2, a2, c2⟩ => ?_)
  refine WP.seq (WP.mono (Ed448.AArch64.Point56.combineCall_frame f2 a2 c2) fun s3 ⟨f3, r3⟩ => ?_)
  rw [VG.Proof.X448.comb_total (decodeScalar448_lt kb)] at r3
  unfold VG.Impl.X448.AArch64.Base.finish
  refine WP.seq (WP.mono (squares_ok f3.scr f3.env) fun s4 ⟨k4, b4, e4⟩ => ?_)
  have hs4 := k4.scr f3.scr
  refine WP.seq (WP.mono (invert_ok hs4 b4) fun s5 ⟨k5, b5, e5⟩ => ?_)
  have hs5 : Scr s5 base := hs4.of_keeps k5.regs (by decide)
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.X448.AArch64.moveOutput_ok s5) fun s6 ⟨x16, m6, k6⟩ => ?_
  have hs6 : Scr s6 base := hs5.of_keeps k6 (by decide)
  -- The working space outside the slots and the products' working space, from `s1` on.
  have o15 : Outside2 base 64 2816 ACC 1152 s1.mem s5.mem := (f3.mem.trans k4.mem).trans k5.mem
  have o16 : Outside2 base 64 2816 ACC 1152 s1.mem s6.mem := by rw [m6]; exact o15
  have out6 : s6.gpr .x1 = sE.gpr .x0 := by
    rw [x16, k5.regs.1 _ (by decide), k4.regs.1 _ (by decide), f3.out, R.out]
  have wr6 : s6.wr = sE.wr := by rw [k6.2.2, k5.regs.2.2, k4.regs.2.2, f3.wr, R.wr]
  have hw6 : ∀ j < 56, InRegions s6.wr (off (sE.gpr .x0) j) 1 := fun j hj =>
    ⟨⟨sE.gpr .x0, 56⟩, by rw [wr6, hp.wr]; simp, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩
  have sv6 : Saved base sE.gpr s6.mem := R.saved.outside2 o16 (by decide) (by decide)
  have svx6 : SavedX base sE.gpr s6.mem := R.savedX.outside2 o16 (by decide) (by decide)
  have svV6 : SavedV base sE.v s6.mem := R.savedV.outside2 o16 (by decide) (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.Fast.finish_ok hs6 (by rw [m6]; exact b5) out6 hw6 (fun j hj => far_output hp.out_sc hj)
    sv6 svx6 svV6) fun s' ⟨rb, x20, rx, rv, kf, _, result⟩ => ⟨?_, ?_, ?_⟩
  · intro r hr
    have lr : s'.gpr .x30 = sE.gpr .x30 := by
      rw [kf.1 _ (by decide), k6.1 _ (by decide), k5.regs.1 _ (by decide), k4.regs.1 _ (by decide),
        f3.lr, R.lr]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rb
    · exact x20
    · exact rx 0 (by decide)
    · exact rx 1 (by decide)
    · exact rx 2 (by decide)
    · exact rx 3 (by decide)
    · exact rx 4 (by decide)
    · exact rx 5 (by decide)
    · exact rx 6 (by decide)
    · exact rx 7 (by decide)
    · exact lr
  · intro r hr
    simp only [preservedV, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rv 0 (by decide)
    · exact rv 1 (by decide)
    · exact rv 2 (by decide)
    · exact rv 3 (by decide)
    · exact rv 4 (by decide)
    · exact rv 5 (by decide)
    · exact rv 6 (by decide)
    · exact rv 7 (by decide)
  · change Spec.X448.bytesAt s'.mem (sE.gpr .x0) 56 = _
    rw [result, m6, e5, invEnv_x2, invEnv_eval, e4]
    refine (VG.Proof.X448.Edwards.x448_basePoint kb _ ?_).symm
    have hu := VG.Proof.X448.u_rep r3
    rw [natCast_zsmul] at hu
    rw [← hu, VG.Proof.X448.invert_eq]
    rfl

end VG.Proof.X448.AArch64.Base

end

end

/-!
# X448 of the base point on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Constant time (by taint
tracking: the only branches are on the counters, every address is an argument
or the static's address plus a constant or a counter, and the digits' masks
only select), and the shared contract of `Spec/`, under the calling convention
with the comb's tables (`Abi.withConsts combConsts`).
-/

@[expose] public section

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64.Base

/-- The analysis, of the code without what it does not read, its comb's field operations analysed
once each (`Base/Erase.lean`). -/
theorem x448Base_check :
    ∃ h, ((taintS [combSym]).check (Taint.ofRegs [.x0, .x1, .x2]) Impl.X448.AArch64.Base.x448Base h).isSome =
      true := by
  apply exists_isSome_of_eraseT
  refine Split.exists_isSome (c' := ?c') ?s ?g
  case s =>
    simp only [x448Base, finish, Code.eraseT, Impl.X448.AArch64.Fast.invert, ops_eraseT, sqn_eraseT]
    exact .refl _
  case g => taint_decide_sum [VG.Proof.Ed448.AArch64.CombBase.combSum, VG.Proof.Ed448.AArch64.addSum, VG.Proof.Ed448.AArch64.powSum]

theorem x448Base_ct : ConstantTime isa Proof.X448.x448BaseAArch64.pre Proof.X448.x448BaseAArch64.pub
    Impl.X448.AArch64.Base.x448Base :=
  let ⟨_, hc⟩ := x448Base_check
  VG.Taint.constantTime (A := taintS [combSym]) (Taint.ofRegs [.x0, .x1, .x2])
    (fun _ _ _ _ ⟨h0, h1, h2, hsp, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2⟩, fun n hn => by
      simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) hc

/-- A state satisfying the precondition: the tables at `0x100000`. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x4000 | _ => 0
  sp := 0x8000
  mem := satMem
  rd := [⟨0x2000, 56⟩, ⟨0x100000, 58368⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .x1, 56⟩, ⟨s.syms combSym, 8 * combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x0, 56⟩, ⟨s.gpr .x2, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .x0, 56⟩ ⟨s.gpr .x1, 56⟩)
    (h2 : Region.Disjoint ⟨s.gpr .x0, 56⟩ ⟨s.gpr .x2, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .x1, 56⟩ ⟨s.gpr .x2, 8192⟩)
    (f0 : (s.gpr .x0).toNat + 56 ≤ 2 ^ 64) (f1 : (s.gpr .x1).toNat + 56 ≤ 2 ^ 64)
    (f2 : (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64)
    (ht : CombHeld s [⟨s.gpr .x0, 56⟩, ⟨s.gpr .x2, 8192⟩])
    (hal : (s.syms combSym).toNat % 64 = 0) :
    (Spec.X448.x448BaseContract (AArch64.abi.withConsts combConsts)).pre s := by
  sig_pre [Spec.X448.x448BaseContract, Spec.X448.x448BaseSig, AArch64.abi, AArch64.argRegs,
    combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact hdw, hal, by rw [hrd]; rfl, hw, h1, h2, h3, f0, f1, f2⟩

theorem sat_spec : (Spec.X448.x448BaseContract (AArch64.abi.withConsts combConsts)).pre satState := by
  have hl := combWords_length
  have held : ∀ i < combWords.length, satState.mem.readW (satState.syms combSym +
      BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := satMem_held
  refine spec_pre (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) ⟨held, ?_, ?_⟩ (by decide)
  all_goals rw [hl]
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem implies : Proof.X448.x448BaseAArch64.Implies
    (Spec.X448.x448BaseContract (AArch64.abi.withConsts combConsts)) where
  pre s h := by
    sig_pre [Spec.X448.x448BaseContract, Spec.X448.x448BaseSig, AArch64.abi, AArch64.argRegs,
      combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, -, ht, hw, -, h2, h3, -, -, h5⟩ := h
    refine ⟨?_, hw, h2, h3, h5, hheld, hfit, by rw [hw] at hdw; exact hdw⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  post := by
    intro s s' _ h
    sig_post [Spec.X448.x448BaseContract, Spec.X448.x448BaseSig, AArch64.abi, AArch64.argRegs,
      combConsts_eq, Abi.withConsts]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.X448.x448BaseContract, Spec.X448.x448BaseSig, AArch64.abi, AArch64.argRegs,
      combConsts_eq, Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2⟩ := h
    exact ⟨h0, h1, h2, hsp, hsy⟩
  sat := ⟨satState, sat_spec⟩

theorem x448Base_ok (s : State) (hs : Proof.X448.x448BaseAArch64.pre s) :
    ∃ t s', Exec isa Impl.X448.AArch64.Base.x448Base s t s' ∧ abiPreserved s s' ∧
      Proof.X448.x448BaseAArch64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (Pre.of s hs)
  exact ⟨t, s', he, ⟨h.1, Exec.sp he, h.2.1⟩, h.2.2⟩

theorem x448Base_verified :
    Verified AArch64.target Impl.X448.AArch64.Base.x448Base
      (Spec.X448.x448BaseContract (AArch64.abi.withConsts combConsts)) :=
  Verified.of_correct x448Base_ok x448Base_ct implies

end VG.Proof.X448.AArch64.Base
