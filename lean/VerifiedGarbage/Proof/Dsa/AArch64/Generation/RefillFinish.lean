module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillLoop
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OutputPlan
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OutputArgs
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.RsaOaep.AArch64.Loops
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecOut
public import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Output
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OnSuccess
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryWork
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.EntropyRequest

/-! ### `Dsa.AArch64.Generation.FinishOutput`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.OutputZero`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.ZeroBytes`, which only this module used -/

section

/-! Precise byte and memory framing for the shared native output-clearing loop. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64
open VG.WriteBytes (writeW8_apply)

structure OutputZeroInv (s : State) (out : Addr) (n j : Nat) (t : State) : Prop where
  keep : Keep [.x11, .x12] s t
  r10 : t.gpr .x11 = out + BitVec.ofNat 64 j
  r11 : t.gpr .x12 = BitVec.ofNat 64 (n - j)
  bytes : ∀ i < j, t.mem (out + BitVec.ofNat 64 i) = 0
  frame : ∀ x, (∀ i < j, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x

theorem zeroOut_bytes_ok {s : State} {F S op : Addr} {k : Nat}
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep s.mem F S V W)
    (hO : W 19 = op) (hK : W 21 = BitVec.ofNat 64 k)
    (hk1 : 0 < k) (hk' : k < 2 ^ 64)
    (hout : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1) :
    WP isa zeroOut s fun t => (∀ i < k, t.mem (op + BitVec.ofNat 64 i) = 0) ∧
      (∀ x, (∀ i < k, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧ Keep [.x11, .x12, .x13] s t := by
  have ho : s.mem.readW (F + BitVec.ofNat 64 sOut) 64 = op := (R.fr 19 (by decide)).trans hO
  have hk : s.mem.readW (F + BitVec.ofNat 64 sK) 64 = BitVec.ofNat 64 k := (R.fr 21 (by decide)).trans hK
  unfold zeroOut
  refine WP.seq (WP.mono (WP.keep [.x11, .x12, .x13] (Q := fun t => t.gpr .x11 = op ∧
      t.gpr .x12 = BitVec.ofNat 64 k ∧ t.gpr .x13 = 0 ∧ t.mem = s.mem) (by
    brun [exec_ldrSp (off := sOut) (by decide), exec_ldrSp (off := sK) (by decide), L.sp,
      L.ld (d := sOut) (n := 8) (by decide), L.ld (d := sK) (n := 8) (by decide), ho, hk]) rfl rfl rfl)
    fun s₁ ⟨⟨hsi, hcx, hax, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (VG.Proof.RsaOaep.AArch64.count_loop (cr := .x12) hk1 (OutputZeroInv s₁ op k) ?_
    ⟨Keep.refl _ _, by rw [hsi, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero], by rw [hcx, Nat.sub_zero],
      fun i hi => absurd hi (by omega_using []), fun x _ => rfl⟩) fun t hI => ⟨hI.bytes, fun x hx => by
        rw [hI.frame x hx, hm₁], ((k₁.trans hI.keep).mono (by decide))⟩
  intro j hj t hI
  have hst : InRegions t.wr (op + BitVec.ofNat 64 j) 1 := by
    rw [hI.keep.wr, k₁.wr]; exact hout j hj
  have hax' : (t.gpr .x13).setWidth 8 = 0 := by rw [hI.keep.gpr .x13 (by decide), hax]; rfl
  have hp : BitVec.ofNat 64 (k - j) - 1#64 = BitVec.ofNat 64 (k - (j + 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_using [hj]
  refine WP.mono (WP.keep [.x11, .x12] (Q := fun t' =>
      t'.mem = t.mem.writeW (op + BitVec.ofNat 64 j) (0 : BitVec 8) ∧
      t'.gpr .x11 = op + BitVec.ofNat 64 (j + 1) ∧ t'.gpr .x12 = BitVec.ofNat 64 (k - (j + 1)))
      (by brun [hI.r10, hI.r11, hst, hax', hp, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; rfl)
      rfl rfl rfl) fun t' ⟨⟨hm, hsi', hcx'⟩, k'⟩ => ?_
  refine ⟨⟨(hI.keep.trans k').mono (by decide), hsi', hcx', ?_, ?_⟩, ?_⟩
  · intro i hi
    rw [hm, writeW8_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega_using [hk', hj, hi]) (by omega_using [hk', hj]) hij))]
      exact hI.bytes i (by omega_using [hi, hij])
  · intro x hx
    rw [hm, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega_using [])))]
    exact hI.frame x fun i hi => hx i (by omega_using [hi])
  · rw [hcx']
    exact VG.Proof.RsaOaep.AArch64.counter_ne (by omega_using [hj]) hk'

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! Every failed search clears the complete output and returns zero. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64

theorem outputZero_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} {len : Nat}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hlen : W 7 = BitVec.ofNat 64 len)
    (hl : 0 < len ∧ len ≤ 1024) (hw : (⟨W 6, len⟩ : Region) ∈ s.wr)
    (_hb : (W 6).toNat + len ≤ 2 ^ 64) (_ha : Apart F S ⟨W 6, len⟩) :
    WP isa Impl.Dsa.AArch64.Generation.outputZero s fun t =>
      t.gpr .x0 = 0 ∧ Spec.Rsa.bytesAt t.mem (W 6) len = List.replicate len 0 ∧
      Frame [⟨F, frameBytes⟩, ⟨W 6, len⟩] s.mem t.mem ∧ Keep (.x0 :: mmRegs) s t := by
  unfold Impl.Dsa.AArch64.Generation.outputZero
  refine WP.seq (WP.mono (zeroArgs_ok L R) fun u ⟨Lu, Ru, fu, ku⟩ => ?_)
  refine WP.seq (WP.mono (zeroOut_bytes_ok (op := W 6) (k := len) Lu Ru (by simp [upd]) (by simpa [upd] using hlen)
    hl.1 (by omega_using [hl]) (fun i hi => by
      rw [ku.wr]
      exact ⟨⟨W 6, len⟩, hw, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hl, hi])⟩))
    fun v ⟨zeros, fv, kv⟩ => ?_)
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0 ∧ t.mem = v.mem)
    (by brun) rfl rfl rfl) fun t ⟨⟨hr, hm⟩, kt⟩ => ?_
  refine ⟨hr, ?_, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  · apply List.ext_getElem
    · simp only [VG.Proof.Bignum.bytesAt_length, List.length_replicate]
    · intro i hi hi'
      have hil : i < len := by simpa only [VG.Proof.Bignum.bytesAt_length] using hi
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate, hm]
      exact zeros i hil
  · have ff : Frame [⟨W 6, len⟩] u.mem t.mem := by
      intro a ha
      rw [hm]
      apply fv a
      intro i hi he
      apply ha ⟨W 6, len⟩ (by simp)
      rw [he]
      exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hl, hi])
    exact (fu.mono (by simp)).trans (ff.mono (by simp))

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! # Normalize every search outcome to the public output and status convention -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem finishOutput_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (o : OutputPlan p)
    (hw : (⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ : Region) ∈ s.wr)
    (expected : Option Spec.Dsa.Params)
    (result : ((W 19 ≠ 1 ∧ expected = none) ∨
      (W 19 = 1 ∧ ∃ a, expected = some a ∧
        Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) = Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen a))) :
    WP isa Impl.Dsa.AArch64.Generation.finishOutput s fun t =>
      t.gpr .x0 = (if expected.isSome then 1 else 0) ∧
      Spec.Rsa.bytesAt t.mem (p.saved 6) (2 * p.geo.pLen + p.geo.qLen) =
        (expected.map (Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen)).getD
          (List.replicate (2 * p.geo.pLen + p.geo.qLen) 0) ∧
      Frame [⟨p.geo.F, frameBytes⟩, ⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩] s.mem t.mem ∧
      Keep (.x0 :: mmRegs) s t := by
  have pn : 0 < p.geo.pLen ∧ p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega_using [hh]
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega_using [hh]
  obtain ⟨V, R⟩ := h.rep
  unfold Impl.Dsa.AArch64.Generation.finishOutput
  refine WP.seq (WP.mono (successStatus_ok h.layout R) fun u ⟨hz, hm, ku⟩ => ?_)
  have mu := h.congr hm ku
  have hwu : (⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ : Region) ∈ u.wr := by rw [ku.wr]; exact hw
  rcases result with ⟨h19, he⟩ | ⟨h19, a, he, bytes⟩
  · have hn : W 19 ≠ 1 := h19
    refine WP.ite false (by exact hz.trans (congrArg some (beq_eq_false_iff_ne.mpr hn)))
      (fun impossible => Bool.noConfusion impossible) (fun _ => ?_)
    obtain ⟨Vu, Ru⟩ := mu.rep
    have h6 := mu.slots 6 (by simp [generationSlots])
    have h7 := (mu.slots 7 (by simp [generationSlots])).trans o.lengthSlot
    have call := outputZero_ok mu.layout Ru h7 ⟨by omega_using [pn], by omega_using [pn, qn]⟩
    rw [h6] at call
    refine WP.mono (call hwu o.bound o.apart) fun t ⟨hr, bt, ft, kt⟩ => ?_
    rw [he]
    exact ⟨hr, bt, by simpa only [hm] using ft, (ku.trans kt).mono (by decide)⟩
  · refine WP.ite true (by apply hz.trans; rw [h19]; rfl)
      (fun _ => ?_) (fun impossible => Bool.noConfusion impossible)
    have bytesu : Spec.Rsa.bytesAt u.mem (VG.Proof.Bignum.off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) =
        Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen a := hm ▸ bytes
    refine WP.mono (output_copy_context mu o hwu _ (VG.Proof.Dsa.Generation.encodeParams_length _ _ _) bytesu)
      fun t ⟨hr, bt, ft, kt⟩ => ?_
    rw [he]
    refine ⟨hr, bt, ?_, (ku.trans kt).mono (by decide)⟩
    rw [hm] at ft
    exact ft.mono (by intro r hr; rcases List.mem_singleton.mp hr with rfl; simp)

end VG.Proof.Dsa.AArch64.Generation

end

end


-- separate module: the end's symbolic execution, built in parallel with the constant-time proofs importing `RefillLoop`

/-! # The refillable-tape search's end on AArch64

`finish`: the words written to `used` and `state` and the status kept for
each way the controller ended (`results`), the parameters or zeros at `out`
(`finishOutput`), and the status returned. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.Generation.Refill

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 (Lay Rep Geo upd nW cF)
open VG.Impl.RsaOaep.AArch64 (frameBytes oRsa)
open VG.Impl.Dsa.Generation.Layout (packed)
open VG.Proof.Dsa.AArch64.Generation

/-! ## Blocks -/

/-- The memory with `state[0]`, `state[3]` and `used[0]` written. -/
def written (m : Mem) (St U : Addr) (r0 r3 uv : BitVec 64) : Mem :=
  ((m.writeW St r0).writeW (off St 24) r3).writeW U uv

/-- What the blocks writing the words read and write. -/
structure ResEnv (s : State) (F St U : Addr) : Prop where
  sp : s.sp = F
  ctl : (⟨F, 480⟩ : Region) ∈ s.wr
  st : (⟨St, 32⟩ : Region) ∈ s.wr
  us : (⟨U, 8⟩ : Region) ∈ s.wr

theorem contains_head (a : Addr) {n k : Nat} (h : n ≤ k) : (⟨a, k⟩ : Region).Contains a n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact h

theorem stores_run {s : State} {F St U : Addr} (e : ResEnv s F St U) {a b c : BitVec 64} (k : Nat) (hk : k < 2 ^ 16)
    (h11 : s.gpr .x11 = a) (h10 : s.gpr .x10 = b) (h12 : s.gpr .x12 = c) (h14 : s.gpr .x14 = St)
    (h15 : s.gpr .x15 = U) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.stores ++ Impl.Dsa.AArch64.Generation.Refill.statusWord k)) s
      fun t => t.mem = (written s.mem St U a b c).writeW (off F 472) (BitVec.ofNat 64 k) ∧ t.sp = s.sp ∧
        t.rd = s.rd ∧ t.wr = s.wr := by
  have s472 : InRegions s.wr (s.sp + BitVec.ofNat 64 472) 8 := by rw [e.sp]; exact ctl_in e.ctl (k := 3) (by decide)
  have st0 : InRegions s.wr St 8 := ⟨_, e.st, contains_head St (n := 8) (k := 32) (by decide)⟩
  have st24 : InRegions s.wr (St + BitVec.ofNat 64 24) 8 := ⟨_, e.st, Offset.contains_base St (by decide) (by decide)⟩
  have us0 : InRegions s.wr U 8 := ⟨_, e.us, contains_head U (n := 8) (k := 8) (by decide)⟩
  have hm := movi_small hk
  simp only [Impl.Dsa.AArch64.Generation.Refill.stores, Impl.Dsa.AArch64.Generation.Refill.statusWord,
    Impl.Dsa.AArch64.Generation.Refill.ctl, Nat.reduceMul, Nat.reduceAdd, List.cons_append, List.nil_append,
    VG.Impl.Bignum.AArch64.st]
  brun [State.write, exec_str_x (off := 0) (by decide), exec_str_x (off := 24) (by decide),
    exec_storeSp (off := 472) (by decide), s472, st0, st24, us0, h10, h11, h12, h14, h15, hm]
  simp only [written, e.sp, off]

theorem shl_small (n k : Nat) (h : n * 2 ^ k < 2 ^ 64) : BitVec.ofNat 64 n <<< k = BitVec.ofNat 64 (n * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have : n < 2 ^ 64 := by
    have := Nat.one_le_two_pow (n := k)
    exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right n (by omega)) h
  rw [Nat.mod_eq_of_lt this]

/-- A seed that ran out: the octets left from its start, the budget, and
whether they reach it. -/
theorem ranOutCheck_run {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hv : (⟨F, 480⟩ : Region) ∈ s.wr) {c len pLen : Nat}
    (h3 : ctlWord s.mem F 3 = BitVec.ofNat 64 c) (h15 : W 15 = BitVec.ofNat 64 len)
    (hc : c ≤ len) (hl : len < 2 ^ 64) (hp3 : pLen = 128 ∨ pLen = 256 ∨ pLen = 384) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.ranOutCheck pLen)) s fun t =>
      (t.gpr .x10 = BitVec.ofNat 64 (len - c) ∧ t.gpr .x9 = BitVec.ofNat 64 pLen ∧
        t.gpr .x11 = BitVec.ofNat 64 (32769 * pLen) ∧
        t.gpr .x12 = BitVec.ofNat 64 (if 32769 * pLen ≤ len - c then 1 else 0) ∧ t.mem = s.mem) ∧
      Keep [.x9, .x10, .x11, .x12, .x13] s t := by
  have w15 : s.mem.readW (s.sp + BitVec.ofNat 64 120) 64 = BitVec.ofNat 64 len := by
    rw [L.sp]; exact (R.fr 15 (by decide)).trans h15
  have w3 : s.mem.readW (s.sp + BitVec.ofNat 64 472) 64 = BitVec.ofNat 64 c := by rw [L.sp]; exact h3
  have l120 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 120) 8 := by rw [L.sp]; exact L.ld (d := 120) (by decide)
  have l472 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 472) 8 := by rw [L.sp]; exact ctl_in' hv (k := 3) (by decide)
  have hsub : BitVec.ofNat 64 len - BitVec.ofNat 64 c = BitVec.ofNat 64 (len - c) := Offset.ofNat_sub_ofNat hc
  have hp : pLen ≤ 384 := by omega_using [hp3]
  have e15 := shl_small pLen 15 (by omega_using [hp3])
  have eb : BitVec.ofNat 64 (pLen * 2 ^ 15) + BitVec.ofNat 64 pLen = BitVec.ofNat 64 (32769 * pLen) := by
    rw [← BitVec.ofNat_add]; congr 1; omega_using []
  refine WP.keep [.x9, .x10, .x11, .x12, .x13] ?_ (by rcases hp3 with rfl | rfl | rfl <;> decide) rfl
    (by rcases hp3 with rfl | rfl | rfl <;> decide +kernel)
  simp only [Impl.Dsa.AArch64.Generation.Refill.ranOutCheck, Impl.Dsa.AArch64.Generation.Refill.ctl,
    Nat.reduceMul, Nat.reduceAdd]
  brun [State.write, exec_ldrSp (off := 120) (by decide), exec_ldrSp (off := 472) (by decide), w15, w3, l120, l472,
    hsub, movi_small (show pLen < 2 ^ 16 by omega_using [hp3]), movi_small (show 0 < 2 ^ 16 by decide),
    movi_small (show 1 < 2 ^ 16 by decide), exec_lsl_x (by decide : 15 < 64), e15, eb,
    loop_subs_ge (show len - c < 2 ^ 64 by omega_using [hl]) (show 32769 * pLen < 2 ^ 64 by omega_using [hp3])]
  by_cases h : 32769 * pLen ≤ len - c <;> simp [h]

/-- The next tape's length. -/
theorem request_run {s : State} {L B pLen : Nat} (hL : L < 2 ^ 32) (hB : B < 2 ^ 32) (hp : pLen ≤ 384)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 pLen) (h10 : s.gpr .x10 = BitVec.ofNat 64 L)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 B) :
    WP isa (.block Impl.Dsa.AArch64.Generation.Refill.request) s fun t =>
      (t.gpr .x10 = BitVec.ofNat 64 (VG.Proof.Entropy.request (256 * pLen) B L) ∧ t.gpr .x11 = BitVec.ofNat 64 B ∧
        t.mem = s.mem) ∧ Keep [.x10, .x12, .x13] s t := by
  have e8 := shl_small pLen 8 (by omega_using [hp])
  refine WP.keep [.x10, .x12, .x13] ?_ (by decide) rfl (by decide +kernel)
  unfold Impl.Dsa.AArch64.Generation.Refill.request
  brun [State.write, exec_lsl_x (by decide : 8 < 64), e8, h9, h10, h11,
    loop_subs_ge (show L < 2 ^ 64 by omega_using [hL]) (show pLen * 2 ^ 8 < 2 ^ 64 by omega_using [hp])]
  unfold VG.Proof.Entropy.request
  by_cases h1 : pLen * 2 ^ 8 ≤ L
  · simp only [h1, decide_true, ite_true, ← BitVec.ofNat_add,
      loop_subs_ge (show L + L < 2 ^ 64 by omega_using [hL]) (show B < 2 ^ 64 by omega_using [hB])]
    by_cases h2 : B ≤ L + L
    · simp only [h2, decide_true, ite_true]; congr 1; omega_using [h2]
    · simp only [h2, decide_false, Bool.false_eq_true, ite_false]; congr 1; omega_using [h1, h2]
  · simp only [h1, decide_false, Bool.false_eq_true, ite_false, ← BitVec.ofNat_add,
      loop_subs_ge (show pLen * 2 ^ 8 + pLen * 2 ^ 8 < 2 ^ 64 by omega_using [hp]) (show B < 2 ^ 64 by omega_using [hB])]
    by_cases h2 : B ≤ pLen * 2 ^ 8 + pLen * 2 ^ 8
    · simp only [h2, decide_true, ite_true]; congr 1; omega_using [h2]
    · simp only [h2, decide_false, Bool.false_eq_true, ite_false]; congr 1; omega_using [h1, h2]

/-- The pointers to `state` and `used`, and the controller's status. -/
theorem resultsStart_run {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hv : (⟨F, 480⟩ : Region) ∈ s.wr) :
    WP isa (.block Impl.Dsa.AArch64.Generation.Refill.resultsStart) s fun t =>
      (t.gpr .x14 = ctlWord s.mem F 1 ∧ t.gpr .x15 = ctlWord s.mem F 0 ∧ t.gpr .x3 = W 19 ∧ t.mem = s.mem) ∧
        Keep [.x3, .x14, .x15] s t := by
  have w : s.mem.readW (s.sp + BitVec.ofNat 64 152) 64 = W 19 := by rw [L.sp]; exact R.fr 19 (by decide)
  have l : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 152) 8 := by rw [L.sp]; exact L.ld (d := 152) (by decide)
  have l448 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 448) 8 := by rw [L.sp]; exact ctl_in' hv (k := 0) (by decide)
  have l456 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 456) 8 := by rw [L.sp]; exact ctl_in' hv (k := 1) (by decide)
  refine WP.keep [.x3, .x14, .x15] ?_ (by decide)
  simp only [Impl.Dsa.AArch64.Generation.Refill.resultsStart, Impl.Dsa.AArch64.Generation.Refill.ctl,
    Nat.reduceMul, Nat.reduceAdd]
  brun [State.write, exec_ldrSp (off := 152) (by decide), exec_ldrSp (off := 448) (by decide),
    exec_ldrSp (off := 456) (by decide), w, l, l448, l456]
  simp only [ctlWord, off, L.sp, and_self]

theorem minusOne_run {s : State} :
    WP isa (.block [.subImm .x .x3 .x3 1]) s fun t =>
      (eval (.zero .x .x3) t = some (s.gpr .x3 == 1) ∧ t.mem = s.mem) ∧ Keep [.x3] s t := by
  refine WP.keep [.x3] ?_ (by decide)
  brun [State.write, eval]
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, beq_iff_eq, BitVec.sub_eq_iff_eq_add]
  rfl

theorem prefixE_run {s : State} {F : Addr} (hsp : s.sp = F) (hv : (⟨F, 480⟩ : Region) ∈ s.wr) :
    WP isa (.block [.ldrSp .x11 (Impl.Dsa.AArch64.Generation.Refill.ctl 2),
        .ldrSp .x12 (Impl.Dsa.AArch64.Generation.Refill.ctl 3)]) s fun t =>
      (t.gpr .x11 = ctlWord s.mem F 2 ∧ t.gpr .x12 = ctlWord s.mem F 3 ∧ t.mem = s.mem) ∧ Keep [.x11, .x12] s t := by
  have l2 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 464) 8 := by rw [hsp]; exact ctl_in' hv (k := 2) (by decide)
  have l3 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 472) 8 := by rw [hsp]; exact ctl_in' hv (k := 3) (by decide)
  refine WP.keep [.x11, .x12] ?_ (by decide)
  simp only [Impl.Dsa.AArch64.Generation.Refill.ctl, Nat.reduceMul, Nat.reduceAdd]
  brun [State.write, exec_ldrSp (off := 464) (by decide), exec_ldrSp (off := 472) (by decide), l2, l3]
  simp only [ctlWord, off, hsp, and_self]

theorem prefixZ_run {s : State} {F : Addr} (hsp : s.sp = F) (hv : (⟨F, 480⟩ : Region) ∈ s.wr) {d : Nat}
    (hd : d = 472 ∨ d = 128) :
    WP isa (.block [VG.Impl.Bignum.AArch64.movi .x11 0, VG.Impl.Bignum.AArch64.movi .x10 0,
        .ldrSp .x12 d]) s fun t =>
      (t.gpr .x11 = 0 ∧ t.gpr .x10 = 0 ∧ t.gpr .x12 = s.mem.readW (off F d) 64 ∧ t.mem = s.mem) ∧
        Keep [.x10, .x11, .x12] s t := by
  have l : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 d) 8 := by
    rw [hsp]; exact ⟨_, List.mem_append_right _ hv, Offset.contains_base F (by omega_using [hd]) (by omega_using [hd])⟩
  refine WP.keep [.x10, .x11, .x12] ?_ (by rcases hd with rfl | rfl <;> decide) rfl
    (by rcases hd with rfl | rfl <;> decide +kernel)
  brun [State.write, exec_ldrSp (off := d) (by omega_using [hd]), l, movi_small (show 0 < 2 ^ 16 by decide)]
  simp only [off, hsp]

/-! ## The words for `used` and `state` -/

/-- The expected parameters. -/
def expectedOf (r : Spec.Dsa.ParameterSearchResult) : Option Spec.Dsa.Params :=
  match r.outcome with
  | .accepted a => some a
  | _ => none

theorem results_frame (m : Mem) (St U F : Addr) (r0 r3 uv v : BitVec 64) :
    Frame [⟨St, 32⟩, ⟨U, 8⟩, ctlRegion F] m ((written m St U r0 r3 uv).writeW (off F 472) v) :=
  (((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (contains_head St (by decide))).writeW (List.mem_cons_self ..) _
    (Offset.contains_base St (d := 24) (by decide) (by decide))).writeW
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _ (contains_head U (by decide)) |>.writeW
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) _
    (ctl_contains F (k := 3) (by decide))

section
variable {pBytes : Nat} {s₀ : State} (h : RefillABI pBytes s₀)

theorem state_hash : (inState s₀).Disjoint ⟨(refillGeometry h).hash, oRsa⟩ :=
  (h.scrState.symm.sub_right h.arena_sub).sub_right ((refillGeometry h).part_sub
    ((refillGeometry h).small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)))

theorem used_hash : (inUsed s₀).Disjoint ⟨(refillGeometry h).hash, oRsa⟩ :=
  (h.usedScr.sub_right h.arena_sub).sub_right ((refillGeometry h).part_sub
    ((refillGeometry h).small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)))

/-- The regions the end writes, apart from the search's memory. -/
theorem results_regions : ∀ r ∈ [inState s₀, inUsed s₀, ctlRegion (refillBase s₀)],
    r.Disjoint ⟨refillBase s₀, frameBytes⟩ ∧ r.Disjoint ⟨(refillGeometry h).hash, oRsa⟩ ∧
      (⟨(randTape h).ptr, (randTape h).bytes.length⟩ : Region).Disjoint r ∧
      r.Disjoint ⟨s₀.gpr .x5, VG.Impl.Dsa.Generation.Layout.usedBytes pBytes⟩ := by
  have hrl : (⟨(randTape h).ptr, (randTape h).bytes.length⟩ : Region) = inRand s₀ := by
    simp only [randTape, bytesAt_length, inRand]
  have fb : ∀ {r : Region}, (r = inOut s₀ ∨ r = inUsed s₀ ∨ r = inRand s₀ ∨ r = inScr s₀ ∨ r = inState s₀) →
      r.Disjoint ⟨refillBase s₀, frameBytes⟩ := fun hr => by
    have := h.frame_disjoint hr (d := 0) (n := frameBytes) (by decide)
    simpa only [off, BitVec.add_zero] using this
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨fb (by simp), state_hash h, hrl ▸ h.randState, h.scrState.symm.sub_right h.arena_sub⟩
  · exact ⟨fb (by simp), used_hash h, hrl ▸ h.usedRand.symm, h.usedScr.sub_right h.arena_sub⟩
  · exact ⟨ctl_frame _, h.ctl_hash, rand_ctl h, h.ctl_arena⟩

theorem genMem_results {hs : GenerationTape (refillGeometry h)} (hin : HsIn h hs) {W : Nat → BitVec 64} {s t : State}
    (hm : GenerationMemory ((refillContext h).withHs hs) W s)
    (hf : Frame [inState s₀, inUsed s₀, ctlRegion (refillBase s₀)] s.mem t.mem)
    (hsp : t.sp = s.sp) (hr : t.rd = s.rd) (hw : t.wr = s.wr) :
    GenerationMemory ((refillContext h).withHs hs) W t := by
  obtain ⟨V, R⟩ := hm.rep
  have Rt : Rep t.mem (refillBase s₀) (refillGeometry h).hash V W :=
    rep_of_disjoint_frame R hf (fun r hr => ((results_regions h) r hr).1.symm)
      (fun r hr => ((results_regions h) r hr).2.1.symm)
  exact ⟨lay_of_rep hm.layout R Rt rfl hsp hw, ⟨V, Rt⟩, hm.slots, hm.scratch.congr hw,
    tapeMemory_frame hm.seeds hf (fun r hr => ((results_regions h) r hr).2.2.1) hr hw,
    tapeMemory_frame hm.hs hf (fun r hr => ((results_regions h) r hr).2.2.1.sub_left hin) hr hw,
    tapeMemory_frame hm.rand hf (fun r hr => ((results_regions h) r hr).2.2.1) hr hw⟩

/-- After `results`: the words written to `state` and `used` over the memory `m₁` the
controller left, the status kept in `ctl 3`, and the parameters still to output. -/
def ResultsDone (v : State) (n c : Nat) (t : State) : Prop :=
  ∃ (hs : GenerationTape (refillGeometry h)) (W : Nat → BitVec 64) (m₁ : Mem) (r0 r3 uv : BitVec 64) (st : Nat),
    HsIn h hs ∧ GenerationMemory ((refillContext h).withHs hs) W t ∧ W 19 = BitVec.ofNat 64 (exitStatus h n c) ∧
    Frame (ctlRegion (refillBase s₀) :: (refillContext h).changed) v.mem m₁ ∧
    t.mem = (written m₁ (s₀.gpr .x7) (s₀.gpr .x2) r0 r3 uv).writeW (off (refillBase s₀) 472) (BitVec.ofNat 64 st) ∧
    r0 = BitVec.ofNat 64 (total h).remaining ∧
    r3 = BitVec.ofNat 64 (VG.Proof.Dsa.Generation.requested pBytes (total h)) ∧
    uv = BitVec.ofNat 64 (total h).used ∧ st = (total h).status ∧
    ((W 19 ≠ 1 ∧ expectedOf (total h) = none) ∨
      (W 19 = 1 ∧ ∃ a, expectedOf (total h) = some a ∧
        Spec.Rsa.bytesAt t.mem (off (s₀.gpr .x5) packed) (2 * pBytes + Spec.Dsa.generationQLen pBytes) =
          Spec.Dsa.encodeParams pBytes (Spec.Dsa.generationQLen pBytes) a)) ∧
    t.sp = refillBase s₀ ∧ t.rd = v.rd ∧ t.wr = v.wr

theorem results_ok {v t : State} {n c : Nat} (hv : v.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr)
    (hd : LoopDone h v n c t) :
    WP isa (Impl.Dsa.AArch64.Generation.Refill.results pBytes) t (ResultsDone h v n c) := by
  obtain ⟨hs, W, hin, hm, c0, c1, fv, rdv, wrv, hx19, c3, cases⟩ := hd
  have hp3 : pBytes = 128 ∨ pBytes = 256 ∨ pBytes = 384 := by
    have := h.lengths; unfold Spec.Dsa.generationLengthsValid at this; omega_using [this]
  have hp : pBytes ≤ 384 := by omega_using [hp3]
  have wt : t.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr := wrv.trans hv
  have env : ∀ x : State, x.sp = refillBase s₀ → x.wr = t.wr → ResEnv x (refillBase s₀) (s₀.gpr .x7) (s₀.gpr .x2) :=
    fun x hsp hw =>
    { sp := hsp
      ctl := by rw [hw, wt]; exact List.mem_cons_self ..
      st := by rw [hw, wt]; exact List.mem_cons_of_mem _ (by rw [h.wr]; simp [inState])
      us := by rw [hw, wt]; exact List.mem_cons_of_mem _ (by rw [h.wr]; simp [inUsed]) }
  have hlen : (randTape h).bytes.length < 2 ^ 32 := by
    have hr := h.randLength
    rw [h.width] at hr
    change (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .x3) (s₀.gpr .x4).toNat).length < _
    rw [bytesAt_length]; unfold Spec.Dsa.parameterEntropy at hr; omega_using [hp3, hr]
  have h15 : W 15 = BitVec.ofNat 64 (randTape h).bytes.length :=
    (hm.slots 15 (by simp [generationSlots])).trans ((refillContext h).withHs hs).randLengthSlot
  have hv480 : (⟨refillBase s₀, 480⟩ : Region) ∈ t.wr := by rw [wt]; exact List.mem_cons_self ..
  have packedSub : ∀ r ∈ [inState s₀, inUsed s₀, ctlRegion (refillBase s₀)],
      (⟨off (s₀.gpr .x5) packed, 2 * pBytes + Spec.Dsa.generationQLen pBytes⟩ : Region).Disjoint r := by
    have qn : Spec.Dsa.generationQLen pBytes ≤ 32 := by unfold Spec.Dsa.generationQLen; split <;> omega_using []
    intro r hr
    exact ((results_regions h) r hr).2.2.2.symm.sub_left ((refillGeometry h).part_sub
      ((refillGeometry h).small_bound (d := packed) (n := 2 * pBytes + Spec.Dsa.generationQLen pBytes) (by decide)
        (by unfold VG.Impl.Dsa.Generation.Layout.arithmeticBytes; omega_using [hp3, qn])))
  -- the end, from the words stored
  have fin : ∀ {x y : State} {a b d : BitVec 64} {st : Nat}, x.mem = t.mem → x.sp = refillBase s₀ →
      x.rd = t.rd → x.wr = t.wr →
      y.mem = (written x.mem (s₀.gpr .x7) (s₀.gpr .x2) a b d).writeW (off (refillBase s₀) 472) (BitVec.ofNat 64 st) →
      y.sp = x.sp → y.rd = x.rd → y.wr = x.wr →
      a = BitVec.ofNat 64 (total h).remaining → b = BitVec.ofNat 64 (VG.Proof.Dsa.Generation.requested pBytes (total h)) →
      d = BitVec.ofNat 64 (total h).used → st = (total h).status →
      ((W 19 ≠ 1 ∧ expectedOf (total h) = none) ∨
        (W 19 = 1 ∧ ∃ p, expectedOf (total h) = some p ∧
          Spec.Rsa.bytesAt t.mem (off (s₀.gpr .x5) packed) (2 * pBytes + Spec.Dsa.generationQLen pBytes) =
            Spec.Dsa.encodeParams pBytes (Spec.Dsa.generationQLen pBytes) p)) →
      ResultsDone h v n c y := by
    intro x y a b d st xm xsp xrd xwr ym ysp yrd ywr ha hb hd hst out
    have fw : Frame [inState s₀, inUsed s₀, ctlRegion (refillBase s₀)] x.mem y.mem := by
      rw [ym]; exact results_frame _ _ _ _ _ _ _ _
    have hmx : GenerationMemory ((refillContext h).withHs hs) W x := by
      obtain ⟨V, R⟩ := hm.rep
      have Rx : Rep x.mem (refillBase s₀) (refillGeometry h).hash V W := xm ▸ R
      exact hm.frame (lay_of_rep hm.layout R Rx rfl (xsp.trans hm.layout.sp.symm) xwr) ⟨V, Rx⟩ (fun _ _ => rfl)
        (by rw [xm]; exact Frame.refl _ _) xrd xwr
    refine ⟨hs, W, t.mem, a, b, d, st, hin, genMem_results h hin hmx fw ysp yrd ywr, hx19, fv, by rw [ym, xm],
      ha, hb, hd, hst, ?_, ysp.trans xsp, yrd.trans (xrd.trans rdv), ywr.trans (xwr.trans wrv)⟩
    rcases out with o | ⟨h19, p, he, bytes⟩
    · exact Or.inl o
    · refine Or.inr ⟨h19, p, he, ?_⟩
      rw [VG.Proof.Dsa.Generation.frame_bytesAt fw packedSub (by unfold Spec.Dsa.generationQLen; split <;> omega_using [hp3]), xm]
      exact bytes
  obtain ⟨V, R⟩ := hm.rep
  unfold Impl.Dsa.AArch64.Generation.Refill.results
  refine WP.seq (WP.mono (resultsStart_run hm.layout R hv480) fun t₁ ⟨⟨x14₁, x15₁, x3₁, m₁⟩, k₁⟩ => ?_)
  replace x14₁ : t₁.gpr .x14 = s₀.gpr .x7 := x14₁.trans c1
  replace x15₁ : t₁.gpr .x15 = s₀.gpr .x2 := x15₁.trans c0
  have sp₁ : t₁.sp = refillBase s₀ := k₁.sp.trans hm.layout.sp
  have ev₁ : eval (.zero .x .x3) t₁ = some (W 19 == 0) := by simp only [eval, State.read, x3₁, BitVec.setWidth_eq]
  have cw₁ : ∀ k, ctlWord t₁.mem (refillBase s₀) k = ctlWord t.mem (refillBase s₀) k := fun k => by rw [m₁]
  rcases cases with ⟨h19, hc, htot⟩ | ⟨h19, hc, c2, hk, htot⟩ | ⟨h19, a, u, hu, h16, htot, bytes⟩
  · -- no seeds left
    refine WP.ite false (ev₁.trans (by rw [h19]; rfl)) (fun hh => Bool.noConfusion hh) (fun _ => ?_)
    refine WP.seq (WP.mono minusOne_run fun t₂ ⟨⟨ev₂, m₂⟩, k₂⟩ => ?_)
    refine WP.ite false (ev₂.trans (by rw [x3₁, h19]; rfl)) (fun hh => Bool.noConfusion hh) (fun _ => ?_)
    have sp₂ : t₂.sp = refillBase s₀ := k₂.sp.trans sp₁
    simp only [Impl.Dsa.AArch64.Generation.Refill.exhaustedWords, Impl.Dsa.AArch64.Generation.Refill.ctl,
      List.append_assoc, Nat.reduceMul, Nat.reduceAdd]
    apply WP.block_append
    refine WP.mono (prefixZ_run sp₂ (by rw [k₂.wr, k₁.wr]; exact hv480) (d := 472) (Or.inl rfl))
      fun t₃ ⟨⟨x11, x10, x12, m₃⟩, k₃⟩ => ?_
    have mt₃ : t₃.mem = t.mem := m₃.trans (m₂.trans m₁)
    refine WP.mono (stores_run (env t₃ (k₃.sp.trans sp₂) (k₃.wr.trans (k₂.wr.trans k₁.wr)))
      3 (by decide) x11 x10 x12 ((k₃.gpr .x14 (by decide)).trans ((k₂.gpr .x14 (by decide)).trans x14₁))
      ((k₃.gpr .x15 (by decide)).trans ((k₂.gpr .x15 (by decide)).trans x15₁)))
      fun t₄ ⟨m₄, sp₄, rd₄, wr₄⟩ => ?_
    refine fin mt₃ (k₃.sp.trans sp₂) (k₃.rd.trans (k₂.rd.trans k₁.rd)) (k₃.wr.trans (k₂.wr.trans k₁.wr))
      m₄ sp₄ rd₄ wr₄ ?_ ?_ ?_ ?_ (Or.inl ⟨by rw [h19]; decide, by rw [htot]; rfl⟩)
    all_goals simp only [htot, Spec.Dsa.ParameterSearchResult.remaining, VG.Proof.Dsa.Generation.requested,
      VG.Proof.Entropy.requested, Spec.Entropy.Result.status, Spec.Entropy.Outcome.status]
    all_goals first | rfl | (rw [mt₃]; exact c3) | (rw [m₂, m₁]; exact c3)
  · -- the tape ran out
    refine WP.ite true (ev₁.trans (by rw [h19]; rfl)) (fun _ => ?_) (fun hh => Bool.noConfusion hh)
    obtain ⟨V₁, R₁⟩ := (genMem_keep hm m₁ k₁).rep
    have L₁ := (genMem_keep hm m₁ k₁).layout
    refine WP.seq (WP.mono (ranOutCheck_run L₁ R₁ (by rw [k₁.wr]; exact hv480) (by change ctlWord t₁.mem (refillBase s₀) 3 = _; rw [cw₁]; exact c3) h15 hc
      (by omega_using [hlen]) hp3) fun t₂ ⟨⟨x10₂, x9₂, x11₂, x12₂, m₂⟩, k₂⟩ => ?_)
    have sp₂ : t₂.sp = refillBase s₀ := k₂.sp.trans sp₁
    have mt₂ : t₂.mem = t.mem := m₂.trans m₁
    by_cases hL : 32769 * pBytes ≤ (randTape h).bytes.length - c
    · refine WP.ite false (by simp [eval, State.read, x12₂, hL]) (fun hh => Bool.noConfusion hh) (fun _ => ?_)
      simp only [Impl.Dsa.AArch64.Generation.Refill.exhaustedWords, Impl.Dsa.AArch64.Generation.Refill.ctl,
        List.append_assoc, Nat.reduceMul, Nat.reduceAdd]
      apply WP.block_append
      refine WP.mono (prefixZ_run sp₂ (by rw [k₂.wr, k₁.wr]; exact hv480) (d := 472) (Or.inl rfl))
        fun t₃ ⟨⟨x11, x10, x12, m₃⟩, k₃⟩ => ?_
      have mt₃ : t₃.mem = t.mem := m₃.trans mt₂
      refine WP.mono (stores_run (env t₃ (k₃.sp.trans sp₂) (k₃.wr.trans (k₂.wr.trans k₁.wr)))
        3 (by decide) x11 x10 x12 ((k₃.gpr .x14 (by decide)).trans ((k₂.gpr .x14 (by decide)).trans x14₁))
        ((k₃.gpr .x15 (by decide)).trans ((k₂.gpr .x15 (by decide)).trans x15₁)))
        fun t₄ ⟨m₄, sp₄, rd₄, wr₄⟩ => ?_
      have hL' : Spec.Dsa.parameterEntropy pBytes ≤ (randTape h).bytes.length - c := by
        unfold Spec.Dsa.parameterEntropy; omega_using [hL]
      refine fin mt₃ (k₃.sp.trans sp₂) (k₃.rd.trans (k₂.rd.trans k₁.rd)) (k₃.wr.trans (k₂.wr.trans k₁.wr))
        m₄ sp₄ rd₄ wr₄ ?_ ?_ ?_ ?_ (Or.inl ⟨by rw [h19]; decide, ?_⟩)
      all_goals simp only [htot, VG.Proof.Dsa.Generation.ranOutResult, hL', ↓reduceIte,
        Spec.Dsa.ParameterSearchResult.remaining, VG.Proof.Dsa.Generation.requested,
        VG.Proof.Entropy.requested, Spec.Entropy.Result.status, Spec.Entropy.Outcome.status, expectedOf]
      all_goals first | rfl | (rw [mt₃]; exact c3) | (rw [mt₂]; exact c3)
    · refine WP.ite true (by simp [eval, State.read, x12₂, hL]) (fun _ => ?_) (fun hh => Bool.noConfusion hh)
      simp only [Impl.Dsa.AArch64.Generation.Refill.entropyWords, List.append_assoc]
      apply WP.block_append
      refine WP.mono (request_run (L := (randTape h).bytes.length - c) (B := Spec.Dsa.parameterEntropy pBytes)
        (by omega_using [hlen]) (by unfold Spec.Dsa.parameterEntropy; omega_using [hp3]) hp x9₂ x10₂ x11₂) fun t₃ ⟨⟨x10₃, x11₃, m₃⟩, k₃⟩ => ?_
      have sp₃ : t₃.sp = refillBase s₀ := k₃.sp.trans sp₂
      have mt₃ : t₃.mem = t.mem := m₃.trans mt₂
      apply WP.block_append
      refine WP.mono (prefixE_run sp₃ (by rw [k₃.wr, k₂.wr, k₁.wr]; exact hv480))
        fun t₄ ⟨⟨x11₄, x12₄, m₄⟩, k₄⟩ => ?_
      have mt₄ : t₄.mem = t.mem := m₄.trans mt₃
      refine WP.mono (stores_run (env t₄ (k₄.sp.trans sp₃) (k₄.wr.trans (k₃.wr.trans (k₂.wr.trans k₁.wr))))
        0 (by decide) x11₄ ((k₄.gpr .x10 (by decide)).trans x10₃) x12₄
        ((k₄.gpr .x14 (by decide)).trans ((k₃.gpr .x14 (by decide)).trans ((k₂.gpr .x14 (by decide)).trans x14₁)))
        ((k₄.gpr .x15 (by decide)).trans ((k₃.gpr .x15 (by decide)).trans ((k₂.gpr .x15 (by decide)).trans x15₁))))
        fun t₅ ⟨m₅, sp₅, rd₅, wr₅⟩ => ?_
      have hL' : ¬Spec.Dsa.parameterEntropy pBytes ≤ (randTape h).bytes.length - c := by
        unfold Spec.Dsa.parameterEntropy; omega_using [hL]
      refine fin mt₄ (k₄.sp.trans sp₃) (k₄.rd.trans (k₃.rd.trans (k₂.rd.trans k₁.rd)))
        (k₄.wr.trans (k₃.wr.trans (k₂.wr.trans k₁.wr))) m₅ sp₅ rd₅ wr₅ ?_ ?_ ?_ ?_ (Or.inl ⟨by rw [h19]; decide, ?_⟩)
      all_goals simp only [htot, VG.Proof.Dsa.Generation.ranOutResult, hL', ↓reduceIte,
        Spec.Dsa.ParameterSearchResult.remaining, VG.Proof.Dsa.Generation.requested,
        VG.Proof.Entropy.requested, Spec.Entropy.Result.status, Spec.Entropy.Outcome.status, expectedOf]
      · exact (congrArg (fun m => ctlWord m (refillBase s₀) 2) mt₃).trans c2
      · simp only [VG.Proof.Dsa.Generation.parameterRequest]
      · exact (congrArg (fun m => ctlWord m (refillBase s₀) 3) mt₃).trans c3
  · -- parameters
    refine WP.ite false (ev₁.trans (by rw [h19]; rfl)) (fun hh => Bool.noConfusion hh) (fun _ => ?_)
    refine WP.seq (WP.mono minusOne_run fun t₂ ⟨⟨ev₂, m₂⟩, k₂⟩ => ?_)
    refine WP.ite true (ev₂.trans (by rw [x3₁, h19]; rfl)) (fun _ => ?_) (fun hh => Bool.noConfusion hh)
    have sp₂ : t₂.sp = refillBase s₀ := k₂.sp.trans sp₁
    simp only [Impl.Dsa.AArch64.Generation.Refill.acceptedWords, List.append_assoc]
    apply WP.block_append
    refine WP.mono (prefixZ_run sp₂ (by rw [k₂.wr, k₁.wr]; exact hv480) (d := 128) (Or.inr rfl))
      fun t₃ ⟨⟨x11, x10, x12, m₃⟩, k₃⟩ => ?_
    have mt₃ : t₃.mem = t.mem := m₃.trans (m₂.trans m₁)
    refine WP.mono (stores_run (env t₃ (k₃.sp.trans sp₂) (k₃.wr.trans (k₂.wr.trans k₁.wr)))
      1 (by decide) x11 x10 x12 ((k₃.gpr .x14 (by decide)).trans ((k₂.gpr .x14 (by decide)).trans x14₁))
      ((k₃.gpr .x15 (by decide)).trans ((k₂.gpr .x15 (by decide)).trans x15₁)))
      fun t₄ ⟨m₄, sp₄, rd₄, wr₄⟩ => ?_
    refine fin mt₃ (k₃.sp.trans sp₂) (k₃.rd.trans (k₂.rd.trans k₁.rd)) (k₃.wr.trans (k₂.wr.trans k₁.wr))
      m₄ sp₄ rd₄ wr₄ ?_ ?_ ?_ ?_ (Or.inr ⟨h19, a, by rw [htot]; rfl, bytes⟩)
    all_goals simp only [htot, Spec.Dsa.ParameterSearchResult.remaining, VG.Proof.Dsa.Generation.requested,
      VG.Proof.Entropy.requested, Spec.Entropy.Result.status, Spec.Entropy.Outcome.status]
    all_goals first | rfl | (rw [mt₃]; exact (R.fr 16 (by decide)).trans h16) |
      (rw [m₂, m₁]; exact (R.fr 16 (by decide)).trans h16)

end

section
variable {pBytes : Nat} {s₀ : State} (h : RefillABI pBytes s₀)

/-- The search's end, from the controller's: what `results` wrote, the
output, and the status in `x0`. -/
def FinishDone (v t : State) : Prop :=
  ∃ (m₁ : Mem) (r0 r3 uv : BitVec 64), Frame (ctlRegion (refillBase s₀) :: (refillContext h).changed) v.mem m₁ ∧
    r0 = BitVec.ofNat 64 (total h).remaining ∧
    r3 = BitVec.ofNat 64 (VG.Proof.Dsa.Generation.requested pBytes (total h)) ∧
    uv = BitVec.ofNat 64 (total h).used ∧
    Frame [⟨refillBase s₀, frameBytes⟩, inOut s₀]
      ((written m₁ (s₀.gpr .x7) (s₀.gpr .x2) r0 r3 uv).writeW (off (refillBase s₀) 472)
        (BitVec.ofNat 64 (total h).status)) t.mem ∧
    t.gpr .x0 = BitVec.ofNat 64 (total h).status ∧
    Spec.Rsa.bytesAt t.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat =
      ((expectedOf (total h)).map (Spec.Dsa.encodeParams pBytes (Spec.Dsa.generationQLen pBytes))).getD
        (List.replicate (s₀.gpr .x1).toNat 0) ∧
    t.sp = refillBase s₀ ∧ t.rd = v.rd ∧ t.wr = v.wr

theorem finish_ok {v t : State} {n c : Nat} (hv : v.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr) (hd : LoopDone h v n c t) :
    WP isa (Impl.Dsa.AArch64.Generation.Refill.finish pBytes) t (FinishDone h v) := by
  have o := refillOutputPlan h
  have outLen : 2 * pBytes + Spec.Dsa.generationQLen pBytes = (s₀.gpr .x1).toNat := by
    rw [← h.width]; exact h.outLength.symm
  unfold Impl.Dsa.AArch64.Generation.Refill.finish
  simp only [VG.Impl.Bignum.AArch64.seqs]
  refine WP.seq (WP.mono (results_ok h hv hd) fun t₁ D => ?_)
  obtain ⟨hs, W, m₁, r0, r3, uv, st, hin, hm, -, fv, mt₁, hr0, hr3, huv, hst, out, sp₁, rd₁, wr₁⟩ := D
  have o' : OutputPlan ((refillContext h).withHs hs) := ⟨o.lengthSlot, o.bound, o.separate⟩
  have hw : (⟨((refillContext h).withHs hs).saved 6,
      2 * ((refillContext h).withHs hs).geo.pLen + ((refillContext h).withHs hs).geo.qLen⟩ : Region) ∈ t₁.wr := by
    change (⟨s₀.gpr .x0, 2 * pBytes + Spec.Dsa.generationQLen pBytes⟩ : Region) ∈ t₁.wr
    rw [outLen, wr₁, hv]; exact List.mem_cons_of_mem _ (by rw [h.wr]; simp [inOut])
  refine WP.seq (WP.mono (finishOutput_ok hm o' hw (expectedOf (total h)) out) fun t₂ ⟨_, bytes₂, f₂, k₂⟩ => ?_)
  have f₂' : Frame [⟨refillBase s₀, frameBytes⟩, inOut s₀] t₁.mem t₂.mem := by
    refine f₂.mono fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl
    · exact Or.inl rfl
    · right; change _ = (⟨s₀.gpr .x0, (s₀.gpr .x1).toNat⟩ : Region); rw [← outLen]; rfl
  have c3 : ctlWord t₂.mem (refillBase s₀) 3 = BitVec.ofNat 64 (total h).status := by
    rw [ctlWord_frame f₂' (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ctl_frame _
      · exact (h.frame_disjoint (r := inOut s₀) (by simp) (d := 448) (n := 32) (by decide)).symm) (by decide),
      mt₁, hst]
    exact ctlWord_write_self _ _ 3 _
  have sp₂ : t₂.sp = refillBase s₀ := k₂.sp.trans sp₁
  have l : InRegions (t₂.rd ++ t₂.wr) (t₂.sp + BitVec.ofNat 64 472) 8 := by
    rw [sp₂]
    exact ctl_in' (s := t₂) (F := refillBase s₀) (by rw [k₂.wr, wr₁, hv]; exact List.mem_cons_self ..) (k := 3) (by decide)
  have w : t₂.mem.readW (t₂.sp + BitVec.ofNat 64 472) 64 = BitVec.ofNat 64 (total h).status := by
    rw [sp₂]; exact c3
  refine WP.mono (WP.keep [.x0] (Q := fun t₃ => t₃.gpr .x0 = BitVec.ofNat 64 (total h).status ∧ t₃.mem = t₂.mem) (by
    simp only [Impl.Dsa.AArch64.Generation.Refill.ctl, Nat.reduceMul, Nat.reduceAdd]
    brun [State.write, exec_ldrSp (off := 472) (by decide), l, w]) (by decide)) fun t₃ ⟨⟨x0₃, m₃⟩, k₃⟩ => ?_
  refine ⟨m₁, r0, r3, uv, fv, hr0, hr3, huv, by rw [m₃, ← hst, ← mt₁]; exact f₂', x0₃, ?_,
    k₃.sp.trans sp₂, k₃.rd.trans (k₂.rd.trans rd₁), k₃.wr.trans (k₂.wr.trans wr₁)⟩
  rw [m₃]
  have := bytes₂
  change Spec.Rsa.bytesAt t₂.mem (s₀.gpr .x0) (2 * pBytes + Spec.Dsa.generationQLen pBytes) =
    ((expectedOf (total h)).map (Spec.Dsa.encodeParams pBytes (Spec.Dsa.generationQLen pBytes))).getD
      (List.replicate (2 * pBytes + Spec.Dsa.generationQLen pBytes) 0) at this
  rw [outLen] at this
  exact this

end

end VG.Proof.Dsa.AArch64.Generation.Refill
