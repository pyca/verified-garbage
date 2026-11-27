module

public import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMemory
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified
meta import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMemory
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Ed25519.AArch64.FixedBaseMain
public import VerifiedGarbage.Spec.X25519.Contract
public import VerifiedGarbage.Impl.X25519.AArch64.Base
import VerifiedGarbage.Proof.Ed25519.AArch64.Codec
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddCodec
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.X25519.AArch64.Base.Lit
meta import VerifiedGarbage.Proof.X25519.AArch64.Base.Lit
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Ed25519.AArch64.Divstep
import VerifiedGarbage.Proof.Ed25519.AArch64.Bits
import VerifiedGarbage.Proof.X25519.Edwards.Base
public import VerifiedGarbage.Proof.Ed25519.AArch64.PointEncode
public import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Spec.Weierstrass
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.X25519.Edwards.Ladder
import VerifiedGarbage.Proof.X25519.AArch64.Ops
import VerifiedGarbage.Proof.X25519.AArch64.Top
meta import VerifiedGarbage.Proof.Ed25519.AArch64.FixedBaseMain
meta import VerifiedGarbage.Spec.X25519.Contract
meta import VerifiedGarbage.Impl.X25519.AArch64.Base
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Codec
meta import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddCodec
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Divstep
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Bits
meta import VerifiedGarbage.Proof.X25519.Edwards.Base
meta import VerifiedGarbage.Proof.Ed25519.AArch64.PointEncode
meta import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers
meta import VerifiedGarbage.Spec.Ed25519.Contract
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Spec.Weierstrass
meta import Mathlib.Tactic.Ring.RingNF
meta import Mathlib.Tactic.FieldSimp
meta import Mathlib.Tactic.Ring
meta import VerifiedGarbage.Proof.X25519.Edwards.Ladder
meta import VerifiedGarbage.Proof.X25519.AArch64.Ops

/-! ### `X25519.AArch64.Base.Main`, which only this module used -/

section

/-! ### `X25519.AArch64.Base.Engine`, which this module and modules that import it used -/

section

/-!
# X25519 of the base point on AArch64: the engine

The scalar's nibbles, clamped (`clampNibbles_ok`), are those of
`decodeScalar25519` (`nib_clamped`); the comb computes `[k] B` from them
(`combMultiply_ok`), and `uEncode` its u-coordinate `(Z + Y) / (Z - Y)`, which
`Proof/X25519/Edwards/Ladder.lean` shows is `X25519(k, 9)` (`engine_ok`).
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Base

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.X25519.AArch64.Base
open VG.Proof.Ed25519.AArch64
open VG.Proof.Ed25519 (Rep dZ baseAff toZ_add toZ_sub toZ_mul toZ_pow)
open VG.Spec.X25519 (Fe P decodeScalar25519)
open VG.Proof.X25519.Edwards (clamped_bit u_rep)
open VG.Proof.Ed25519.Word64 (val4)

/-! ## The clamped nibbles -/

private theorem bits_clamped : ∀ b0 < 2, ∀ b1 < 2, ∀ b2 < 2, ∀ b3 < 2,
    ((b3 * 2 + 0) * 2 + 0) * 2 + 0 = (((b3 * 2 + b2) * 2 + b1) * 2 + b0) &&& 8 ∧
    ((0 * 2 + 1) * 2 + b1) * 2 + b0 = ((((b3 * 2 + b2) * 2 + b1) * 2 + b0) &&& 3) ||| 4 := by decide

open VG.Proof.Ed25519 (nib nib_bits nib_lt) in
/-- The nibbles of the decoded scalar are the bytes', clamped. -/
theorem nib_clamped {kb : List Byte} (hk : kb.length = 32) {i : Nat} (hi : i < 64) :
    nib (decodeScalar25519 kb) i =
      if i = 0 then nib (Spec.Ed25519.decodeLE kb) 0 &&& 8
      else if i = 63 then (nib (Spec.Ed25519.decodeLE kb) 63 &&& 3) ||| 4
      else nib (Spec.Ed25519.decodeLE kb) i := by
  have lt : ∀ q, (Spec.Ed25519.decodeLE kb / 2 ^ q) % 2 < 2 := fun q => Nat.mod_lt _ (by decide)
  rw [nib_bits, nib_bits, nib_bits, nib_bits, clamped_bit hk (by omega_using [hi]), clamped_bit hk (by omega_using [hi]),
    clamped_bit hk (by omega_using [hi]), clamped_bit hk (by omega_using [hi])]
  by_cases h0 : i = 0
  · subst h0
    simp only [Nat.mul_zero, Nat.zero_add, ↓reduceIte, Nat.reduceLT, Nat.reduceEqDiff, or_false, or_self]
    exact (bits_clamped _ (lt 0) _ (lt 1) _ (lt 2) _ (lt 3)).1
  · by_cases h63 : i = 63
    · subst h63
      simp only [Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.reduceLT, Nat.reduceEqDiff, or_true, or_self]
      exact (bits_clamped _ (lt 252) _ (lt 253) _ (lt 254) _ (lt 255)).2
    · rw [ite_eq_right h0, ite_eq_right h63, ite_eq_right (by omega_using [h0, h63, hi]),
        ite_eq_right (by omega_using [h0, h63, hi]), ite_eq_right (by omega_using [h0, h63, hi]),
        ite_eq_right (by omega_using [h0, h63, hi]), ite_eq_right (by omega_using [h0, h63, hi]),
        ite_eq_right (by omega_using [h0, h63, hi]), ite_eq_right (by omega_using [h0, h63, hi]),
        ite_eq_right (by omega_using [h0, h63, hi])]

private theorem clamp_byte : ∀ n < 16,
    ((((BitVec.ofNat 8 n).setWidth 64 &&& (BitVec.setWidth 64 (BitVec.setWidth 32 (8 : BitVec 16) <<< (16 * 0)))).setWidth
      32).setWidth 8 : BitVec 8) = BitVec.ofNat 8 (n &&& 8) ∧
    ((((BitVec.ofNat 8 n).setWidth 64 &&& (BitVec.setWidth 64 (BitVec.setWidth 32 (3 : BitVec 16) <<< (16 * 0)))) |||
      (BitVec.setWidth 64 (BitVec.setWidth 32 (4 : BitVec 16) <<< (16 * 0)))).setWidth 32).setWidth 8 =
        BitVec.ofNat 8 ((n &&& 3) ||| 4) := by decide

/-- A byte store at `base + d`, read at `base + e`. -/
theorem write1_off (m : Mem) (base : Addr) {d e : Nat} (hd : d < 2 ^ 64) (he : e < 2 ^ 64) (v : BitVec 8) :
    (m.write (off base d) 1 v) (off base e) = if e = d then v else m (off base e) := by
  rw [VG.Proof.X25519.AArch64.write1_apply]
  by_cases h : e = d
  · subst h; rw [ite_eq_left rfl, ite_eq_left rfl]
  · rw [ite_eq_right fun h' => h ((off_eq_iff base he hd).mp h'), ite_eq_right h]

/-- A byte store at `base + d` leaves the other bytes. -/
theorem write1_outside (m : Mem) (base : Addr) {d : Nat} (hd : d < 2 ^ 64) {x : Addr}
    (hx : ofs base x ≠ d) (v : BitVec 8) : (m.write (off base d) 1 v) x = m x := by
  rw [VG.Proof.X25519.AArch64.write1_apply, ite_eq_right fun h => hx (by rw [h]; exact ofs_off' base hd)]

open VG.Proof.Ed25519 (nib nib_lt) in
theorem clampNibbles_ok {s : State} {base : Addr} (hs : Scr s base) {S : Nat} (hb : NibAt s.mem base 64 S) :
    WP isa (.block clampNibbles) s fun t => CK base s t ∧
      ∀ i < 64, t.mem (off base (NIB + i)) = BitVec.ofNat 8
        (if i = 0 then nib S 0 &&& 8 else if i = 63 then (nib S 63 &&& 3) ||| 4 else nib S i) := by
  have hN : NIB = 768 := rfl
  have hw : ∀ d < 8192, InRegions s.wr (off base d) 1 := fun d hd =>
    ⟨_, hs.wr, Offset.contains_base _ hd (by omega_using [hd])⟩
  have hr : ∀ d < 8192, InRegions (s.rd ++ s.wr) (off base d) 1 := fun d hd =>
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ hd (by omega_using [hd])⟩
  have e0 : base + BitVec.ofNat 64 NIB = off base NIB := rfl
  have e1 : base + BitVec.ofNat 64 (NIB + 63) = off base (NIB + 63) := rfl
  have b0 : s.mem (off base NIB) = BitVec.ofNat 8 (nib S 0) := hb 0 (by decide)
  have b1 : ∀ v : BitVec 8, (s.mem.write (off base NIB) 1 v) (off base (NIB + 63)) = BitVec.ofNat 8 (nib S 63) := fun v => by
    rw [write1_off _ _ (by decide) (by decide), ite_eq_right (by decide)]; exact hb 63 (by decide)
  have c0 := (clamp_byte (nib S 0) (nib_lt S 0)).1
  have c1 := (clamp_byte (nib S 63) (nib_lt S 63)).2
  have rb : ∀ (m : Mem) (a : Addr), ((m.read a 1).setWidth 32).setWidth 64 = (m a).setWidth 64 :=
    VG.Proof.X25519.AArch64.read1_toNat
  apply WP.of_runBlock
  simp only [clampNibbles, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, State.read,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, Nat.mod_one, and_self, Size.bits,
    show NIB < 4096 * 1 from by decide, show NIB + 63 < 4096 * 1 from by decide, show 16 * 0 < 32 from by decide,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hs.x0, e0, e1, hr NIB (by decide), hr (NIB + 63) (by decide),
    hw NIB (by decide), hw (NIB + 63) (by decide), rb, b0, b1, c0, c1,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r _ _ hc => ?_, rfl, rfl, rfl, fun x hx hy => ?_⟩, fun i hi => ?_⟩
  · have h8 : r ≠ .x8 := fun h => hc (by subst h; decide)
    have h9 : r ≠ .x9 := fun h => hc (by subst h; decide)
    simp only [RegUpd.gpr_write, h8, h9, ite_false]
  · dsimp only [RegUpd.mem_write]
    rw [write1_outside _ _ (by decide) (by omega_using [hy, hN]), write1_outside _ _ (by decide) (by omega_using [hy, hN])]
  · rw [write1_off _ _ (by decide) (by omega_using [hi, hN]), write1_off _ _ (by decide) (by omega_using [hi, hN])]
    by_cases h0 : i = 0
    · subst h0
      rw [ite_eq_right (by decide), ite_eq_left (by decide), ite_eq_left rfl]
    · by_cases h63 : i = 63
      · subst h63
        rw [ite_eq_left rfl, ite_eq_right h0, ite_eq_left rfl]
      · rw [ite_eq_right (by omega_using [h63]), ite_eq_right (by omega_using [h0]), ite_eq_right h0, ite_eq_right h63]
        exact hb i hi

/-! ## The u-coordinate -/

theorem uOps_eval (e : Env) :
    evalOps uOps e 0 = e 2 + e 1 ∧ evalOps uOps e 2 = e 2 - e 1 := by
  simp [uOps, evalOps, evalOp, Fun.update]

theorem uEncode_ok [VG.Proof.Ed25519.AArch64.Divstep.Sound] {s : State} {base : Addr} (hs : Scr s base) :
    WP isa uEncode s fun t => CounterKeep base s t ∧
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) =
        ((env s.mem base 2 + env s.mem base 1) *
          Spec.X25519.pow (env s.mem base 2 - env s.mem base 1) (P - 2)).val := by
  rw [uEncode]
  refine WP.seq (WP.mono (fieldCode_ok uOps hs) fun a ⟨ka, va⟩ => ?_)
  obtain kac : CounterKeep base s a := ⟨fun r hr _ => ka.gpr r hr, ka.rd, ka.wr, ka.sp, ka.mem⟩
  refine WP.seq (WP.mono (pointAffine_ok (kac.scr hs)) fun b ⟨kb, bx, _⟩ => ?_)
  refine WP.mono (freezeField_ok ((kb.scr (kac.scr hs))) 0) fun t ⟨tv, kt⟩ => ?_
  refine ⟨(kac.trans kb).trans (CounterKeep.of_keeps kt (by decide)), ?_⟩
  rw [tv, bx, va, (uOps_eval _).1, (uOps_eval _).2]

/-! ## The engine -/

theorem engine_ok [VG.Proof.Ed25519.AArch64.Divstep.Sound] : EngineOk engine fun kb =>
    Spec.X25519.x25519 kb Spec.X25519.basePoint := by
  intro s base k T hs hp hr hd htb hT
  obtain hk : (Spec.Ed25519.bytesAt s.mem k 32).length = 32 := by simp [Spec.Ed25519.bytesAt]
  obtain ⟨kb, ekb⟩ : ∃ kb, Spec.Ed25519.bytesAt s.mem k 32 = kb := ⟨_, rfl⟩
  rw [ekb] at hk ⊢
  rw [engine]
  refine WP.seq (WP.mono_syms (scalarNibbles_ok hs hp hr hd) fun b ⟨kab, bn⟩ syb => ?_)
  rw [ekb] at bn
  obtain hsb := kab.scratch hs
  refine WP.seq (WP.mono_syms (clampNibbles_ok hsb bn) fun c ⟨kbc, cn⟩ syc => ?_)
  obtain hsc := kbc.scratch hsb
  obtain kac := kab.trans kbc
  obtain hS : decodeScalar25519 kb < 2 ^ 256 := by
    obtain h := Edwards.decodeScalar25519_shift hk
    rw [Nat.shiftRight_eq_div_pow] at h
    have := (Nat.div_eq_zero_iff_lt (by positivity)).mp h
    omega_using [h]
  obtain htc : TblAt c base T := htb.of_far (by rw [kac.rd, kac.wr])
    (fun x hx => ck_outside kac x (Or.inr (by omega_using [hx])))
  refine WP.seq (WP.mono (combMultiply_ok hsc htc (by rw [syc, syb]; exact hT) hS
    (fun i hi => by rw [cn i hi, nib_clamped hk hi])) fun d ⟨dp, kd⟩ => ?_)
  refine WP.mono (uEncode_ok (kd.scratch hsc)) fun t ⟨kt, tv⟩ => ⟨(kac.trans kd).trans kt.ck, ?_⟩
  rw [tv]
  change _ = Spec.X25519.x25519 kb Spec.X25519.basePoint
  rw [VG.Proof.X25519.Edwards.x25519_basePoint hk _ (u_rep dp), Proof.X25519.encodeUCoordinate_eq]
  simp only [point]

end VG.Proof.X25519.AArch64.Base

end

end

/-!
# X25519 of the base point on AArch64: memory and ABI obligations

As Ed25519's `scalarBase` (`Proof/Ed25519/AArch64/FixedBaseMain.lean`), with
the engine of `Engine.lean` and its result read as a u-coordinate.
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Base

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.X25519.AArch64.Base
open VG.Proof.Ed25519.AArch64
open VG.Proof.Ed25519.Word64 (val4)
open VG.Spec.Ed25519 (bytesAt)

/-- `vg_x25519_base(out = x0, scalar = x1, scratch = x2)`, with the comb's tables at the
static's address. -/
def baseLocal : Contract isa where
  pre s := s.rd = [⟨s.gpr .x1, 32⟩, tblRegion s] ∧ s.wr = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x2, 8192⟩] ∧
    (⟨s.gpr .x1, 32⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩ ∧
    (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64 ∧ CombHeld s [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x2, 8192⟩]
  post s t := Spec.X25519.bytesAt t.mem (s.gpr .x0) 32 =
    Spec.X25519.x25519 (Spec.X25519.bytesAt s.mem (s.gpr .x1) 32) Spec.X25519.basePoint
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧
    s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧ s.syms combSym = t.syms combSym

theorem x25519Base_correct [VG.Proof.Ed25519.AArch64.Divstep.Sound] {s : State} (hs : baseLocal.pre s) :
    WP isa x25519Base s fun t => abiPreserved s t ∧ baseLocal.post s t ∧
      (Region.Disjoint ⟨s.gpr .x0, 32⟩ ⟨s.gpr .x2, 8192⟩ → ScratchTail (s.gpr .x2) s.mem t.mem) :=
  baseWrap_ok (e := engine) (R := fun kb => Spec.X25519.x25519 kb Spec.X25519.basePoint)
    (fun h1 h2 h3 h4 h5 h6 => engine_ok h1 h2 h3 h4 h5 h6) (by lit_decide) hs

end VG.Proof.X25519.AArch64.Base

end

end

/-!
# X25519 of the base point on AArch64: constant time and the contract

As for Ed25519's `scalarBase`: the scalar's bits, the comb and the encoding
have a public trace (one taint check of the engine, whose addresses are the
working space `x0` plus constants or public counters), and so do the setup and
the finish.
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Base

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.X25519.AArch64.Base
open VG.Proof.Ed25519.AArch64

/-- The engine: Ed25519's nibbles and comb (`scalarNibbles_ct`, `combMultiply_ct`), with the clamping
and the encoding of `u` between and after them. -/
theorem engine_ct (base k T : Addr) :
    CT (fun x y => BaseEnginePre base k T x ∧ BaseEnginePre base k T y) engine (fun _ _ => True) := by
  have hw : ∀ s, (Scr s base ∧ s.syms combSym = T) →
      WP isa (.block clampNibbles) s (fun t => Scr t base ∧ t.syms combSym = T) := fun s ⟨hs, hT⟩ => by
    have hwr : ∀ d < 8192, InRegions s.wr (off base d) 1 := fun d hd =>
      ⟨_, hs.wr, Offset.contains_base _ hd (by omega_using [hd])⟩
    have hrd : ∀ d < 8192, InRegions (s.rd ++ s.wr) (off base d) 1 := fun d hd =>
      ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ hd (by omega_using [hd])⟩
    have e0 : base + BitVec.ofNat 64 NIB = off base NIB := rfl
    have e1 : base + BitVec.ofNat 64 (NIB + 63) = off base (NIB + 63) := rfl
    apply WP.of_runBlock
    simp only [clampNibbles, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
      State.read, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, Nat.mod_one, and_self, Size.bits,
      show NIB < 4096 * 1 from by decide, show NIB + 63 < 4096 * 1 from by decide, show 16 * 0 < 32 from by decide,
      BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hs.x0, e0, e1, hrd NIB (by decide),
      hrd (NIB + 63) (by decide), hwr NIB (by decide), hwr (NIB + 63) (by decide),
      Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
    exact ⟨⟨hs.x0, hs.wr, hs.nowrap⟩, hT⟩
  have hc : CT (fun x y => (Scr x base ∧ x.syms combSym = T) ∧ (Scr y base ∧ y.syms combSym = T))
      (.block clampNibbles) (fun _ _ => True) :=
    CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact h.1.1.x0.trans h.2.1.x0.symm) (by taint_decide)
  rw [engine]
  refine CT.seq (scalarNibbles_ct base k T) (CT.seq ((hc.wp fun x y h => ⟨hw x h.1, hw y h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2) (CT.seq (combMultiply_ct base T) ?_))
  exact CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_ofRegs h) (by taint_decide)

private def BaseStart (base k out T : Addr) (s : State) : Prop :=
  baseLocal.pre s ∧ s.gpr .x0 = out ∧ s.gpr .x1 = k ∧ s.gpr .x2 = base ∧ s.syms combSym = T

private def BasePrepared (base k out T : Addr) (s : State) : Prop :=
  BaseEnginePre base k T s ∧ s.mem.readW (off base 48) 64 = out

private def BaseReady (base out : Addr) (s : State) : Prop :=
  Scr s base ∧ s.mem.readW (off base 48) 64 = out

private theorem start_ok {base k out T : Addr} {s : State} (hs : BaseStart base k out T s) :
    WP isa (.block (scalarSave ++ scalarBaseSetup)) s (BasePrepared base k out T) := by
  obtain ⟨⟨hr, hw, hd, hn, hct⟩, ho, hk, hb, hT⟩ := hs
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw, hb]; simp
  have htb : TblAt s base T := by
    rw [← hb, ← hT]; exact hct.tblAt (by rw [hr]; simp) (by simp)
  rw [WP.block_append_iff]
  refine WP.mono_syms (scalarSave_ok hb hws) fun a ⟨ga, ra, wa, _, ma, _⟩ sya => ?_
  have hwa : (⟨a.gpr .x2, 8192⟩ : Region) ∈ a.wr := by rw [ga, hb, wa]; exact hws
  refine WP.mono_syms (scalarBaseSetup_ok a hwa) fun b ⟨pb, gb, rb, wb, _, ob, mb⟩ syb => ?_
  rw [ga, hb] at pb ob mb
  refine ⟨⟨⟨pb, by rw [wb, wa]; exact hws, by rw [← hb]; exact hn⟩,
    (gb _ (by decide)).trans ((congrFun ga _).trans hk), ?_, ?_, ?_, by rw [syb, sya]; exact hT⟩,
    ob.trans ho⟩
  · intro q hq
    exact ⟨⟨k, 32⟩, by rw [rb, ra, hr, hk]; simp, Offset.contains_base _ (by omega_using [hq]) (by omega_using [hq])⟩
  · intro q hq
    rw [hk, hb] at hd
    exact farScr hd hq (by decide)
  · exact htb.of_far (by rw [rb, ra, wb, wa]) fun x hx => by
      rw [mb x (Or.inr (by omega_using [hx])), ma x (Or.inr (by omega_using [hx]))]

private theorem start_ct (base k out T : Addr) :
    CT (fun x y => BaseStart base k out T x ∧ BaseStart base k out T y)
      (.block (scalarSave ++ scalarBaseSetup))
      (fun x y => BasePrepared base k out T x ∧ BasePrepared base k out T y) := by
  have hc : CT (fun x y => BaseStart base k out T x ∧ BaseStart base k out T y)
      (.block (scalarSave ++ scalarBaseSetup)) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0, .x1, .x2]) _ (by taint_decide)
    intro x y h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.2.1.trans h.2.2.1.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
    · exact h.1.2.2.2.1.trans h.2.2.2.2.1.symm
  exact (hc.wp (fun _ _ h => ⟨start_ok h.1, start_ok h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

private theorem engine_ready [VG.Proof.Ed25519.AArch64.Divstep.Sound] {base k out T : Addr} {s : State} (hs : BasePrepared base k out T s) :
    WP isa engine s (BaseReady base out) := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, ho⟩ := hs
  refine WP.mono (engine_ok h1 h2 h3 h4 h5 h6) fun t ⟨kt, _⟩ => ?_
  exact ⟨kt.scratch h1, ((ck_outside kt).word
    (d := 48) (Or.inl (by decide)) (by decide)).trans ho⟩

private theorem engine_ct' [VG.Proof.Ed25519.AArch64.Divstep.Sound] (base k out T : Addr) :
    CT (fun x y => BasePrepared base k out T x ∧ BasePrepared base k out T y)
      engine (fun x y => BaseReady base out x ∧ BaseReady base out y) := by
  have hc := (engine_ct base k T).mono
    (fun _ _ (h : BasePrepared base k out T _ ∧ BasePrepared base k out T _) => ⟨h.1.1, h.2.1⟩)
    (fun _ _ h => h)
  exact (hc.wp (fun _ _ h => ⟨engine_ready h.1, engine_ready h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

private theorem finish_ct (base out : Addr) :
    CT (fun x y => BaseReady base out x ∧ BaseReady base out y)
      scalarBaseFinish (fun _ _ => True) := by
  have hc : CT (fun x y => BaseReady base out x ∧ BaseReady base out y)
      (.block scalarBaseFinishArgs) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    intro x y h
    exact agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.1.x0.trans h.2.1.x0.symm)
  have hw : ∀ s, BaseReady base out s → WP isa (.block scalarBaseFinishArgs) s
      (fun t => t.gpr .x2 = base ∧ t.gpr .x0 = out) := by
    intro s h
    exact WP.mono (scalarBaseFinishArgs_ok h.1) fun _ ht => ⟨ht.1, ht.2.1.trans h.2⟩
  have hc' := (hc.wp (fun _ _ h => ⟨hw _ h.1, hw _ h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)
  rw [scalarBaseFinish]
  refine CT.seq hc' ?_
  apply CT.taint (Taint.ofRegs [.x2, .x0]) _ (by taint_decide)
  intro x y h
  apply agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.trans h.2.2.symm

theorem x25519Base_ct [VG.Proof.Ed25519.AArch64.Divstep.Sound] : ConstantTime isa baseLocal.pre baseLocal.pub x25519Base := by
  intro x y tx ty x' y' hx hy ⟨hsp, ho, hk, hb, hsy⟩ ex ey
  have hc := CT.seq (start_ct (x.gpr .x2) (x.gpr .x1) (x.gpr .x0) (x.syms combSym))
    (CT.seq (engine_ct' (x.gpr .x2) (x.gpr .x1) (x.gpr .x0) (x.syms combSym))
      (finish_ct (x.gpr .x2) (x.gpr .x0)))
  exact (hc _ _ _ _ _ _ ⟨hsp, ⟨hx, rfl, rfl, rfl, rfl⟩, ⟨hy, ho.symm, hk.symm, hb.symm, hsy.symm⟩⟩
    ex ey).1

theorem x25519Base_ok [VG.Proof.Ed25519.AArch64.Divstep.Sound] (s : State) (hs : baseLocal.pre s) :
    ∃ t s', Exec isa x25519Base s t s' ∧ abiPreserved s s' ∧ baseLocal.post s s' :=
  let ⟨t, s', he, ha, hp, _⟩ := x25519Base_correct hs
  ⟨t, s', he, ha, hp⟩

/-- The shared contract's precondition, from its facts. -/
theorem x25519Base_spec_pre {s : State}
    (hrd : s.rd = [⟨s.gpr .x1, 32⟩, ⟨s.syms combSym, 8 * combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x2, 8192⟩])
    (h1 : Region.Disjoint ⟨s.gpr .x0, 32⟩ ⟨s.gpr .x1, 32⟩)
    (h2 : Region.Disjoint ⟨s.gpr .x0, 32⟩ ⟨s.gpr .x2, 8192⟩)
    (h3 : Region.Disjoint ⟨s.gpr .x1, 32⟩ ⟨s.gpr .x2, 8192⟩)
    (f0 : (s.gpr .x0).toNat + 32 ≤ 2 ^ 64) (f1 : (s.gpr .x1).toNat + 32 ≤ 2 ^ 64)
    (f2 : (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64)
    (ht : CombHeld s [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x2, 8192⟩])
    (hal : (s.syms combSym).toNat % 64 = 0) :
    (Spec.X25519.x25519BaseContract (AArch64.abi.withConsts combConsts)).pre s := by
  sig_pre [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
    AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  obtain ⟨held, fit, hdw⟩ := ht
  exact ⟨by rw [hrd]; rfl, held, fit, by rw [hw]; exact hdw, hal, by rw [hrd]; rfl, hw, h1, h2, h3, f0, f1, f2⟩

theorem x25519Base_sat :
    (Spec.X25519.x25519BaseContract (AArch64.abi.withConsts combConsts)).pre baseSatState := by
  have hl := combWords_length
  have held : ∀ i < combWords.length, baseSatState.mem.readW (baseSatState.syms combSym +
      BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := satMem_held
  refine x25519Base_spec_pre (by rw [hl]; rfl) rfl (Region.disjoint_of_sep (by decide))
    (Region.disjoint_of_sep (by decide)) (Region.disjoint_of_sep (by decide)) (by decide) (by decide)
    (by decide) ⟨held, ?_, ?_⟩ (by decide)
  all_goals rw [hl]
  · decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem x25519Base_implies : baseLocal.Implies
    (Spec.X25519.x25519BaseContract (AArch64.abi.withConsts combConsts)) where
  pre s h := by
    sig_pre [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
      stackBelow] at h
    obtain ⟨hd, hheld, hfit, hdw, -, ht, hw, -, -, h3, -, -, h5⟩ := h
    refine ⟨?_, hw, h3, h5, hheld, hfit, by rw [hw] at hdw; exact hdw⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
  post := by
    intro s s' _ h
    sig_post [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2⟩ := h
    exact ⟨hsp, h0, h1, h2, hsy⟩
  sat := ⟨baseSatState, x25519Base_sat⟩

/-- The function writes only the first 1024 bytes of `scratch`. -/
theorem x25519Base_written [VG.Proof.Ed25519.AArch64.Divstep.Sound] (s : State) (t : List Leak)
    (s' : State) (hs : (Spec.X25519.x25519BaseContract (AArch64.abi.withConsts combConsts)).pre s)
    (he : Exec isa x25519Base s t s') :
    Sig.writtenWithin (AArch64.abi.withConsts combConsts) Spec.X25519.x25519BaseSig
      [("scratch", 1024)] s s' := by
  have hl := x25519Base_implies.pre s hs
  have hd : Region.Disjoint ⟨s.gpr .x0, 32⟩ ⟨s.gpr .x2, 8192⟩ := by
    sig_pre [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      AArch64.abi, AArch64.argRegs, combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
      stackBelow] at hs
    exact hs.2.2.2.2.2.2.2.2.1
  obtain ⟨t', s'', he', -, -, htail⟩ := x25519Base_correct hl
  obtain ⟨-, rfl⟩ := Exec.det he he'
  simp [Sig.writtenWithin, AArch64.abi, AArch64.argRegs, Abi.withConsts, combConsts_eq,
    Spec.X25519.x25519BaseSig, Sig.words, Sig.arrays, Param.words, ArgWord.bits]
  all_goals exact fun i h1 h2 => htail hd i h1 (by simpa [Elem.size] using h2)

theorem x25519Base_verified [VG.Proof.Ed25519.AArch64.Divstep.Sound] :
    Verified AArch64.target x25519Base (Spec.X25519.x25519BaseContract (AArch64.abi.withConsts combConsts)) :=
  Verified.of_correct x25519Base_ok x25519Base_ct x25519Base_implies

end VG.Proof.X25519.AArch64.Base
