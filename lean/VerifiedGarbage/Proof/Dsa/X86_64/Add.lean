module

public import VerifiedGarbage.Proof.Dsa.X86_64.Frame
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Bignum.X86_64.CrtArith
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
import VerifiedGarbage.Proof.Dsa.X86_64.Exponent
import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceByte
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRedc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.R2
import Mathlib.Tactic.Push

/-! ### `Dsa.X86_64.ReduceSetup`, which this module and modules that import it used -/

section

/-! # Preparing the ordinary accumulator for streaming byte reduction -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- Clearing an operand preserves the linked workspace and modulus. -/
theorem clear_mod_ok {s : State} {B : Addr} {Z o w wx m : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hm : ModCtx s (off B o) (slot wx 8) wx minv m)
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 31) {j : Nat} (hj : j < 8) (hjn : j ≠ aN) :
    WP isa (Arithmetic.zero j) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      wv t.mem (off B o) (slot wx j) wx = 0 ∧
      Arrays (off B o) wx [j] s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (zeroArr_ok hc.good (Nat.le_refl _) (by omega_using [hw]) hw' hj)
    fun t ⟨hv, hf, hk⟩ => ?_
  have ha : Arrays (off B o) wx [j] s.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self j) hf (Nat.le_refl _) (Nat.le_refl _)
  have ht := arrays_context hc ha (by simpa using hj) hk
  have hnZ := hc.good.scr.nowrap
  have hnot : aN ∉ [j] := by simpa using Ne.symm hjn
  refine ⟨ht, ⟨ht.good, (ha.wv_of_not_mem (by decide) hnot hnZ).trans hm.modulus, ?_⟩, (wv_eq_zero_iff _ _ _ _).mpr (fun i hi =>
      (wv_eq_zero_iff _ _ _ _).mp hv i (by omega_using [hi])), ha, hk⟩
  rw [ha.word0_of_not_mem (by decide) hnot hnZ (by omega_using [hw])]
  exact hm.inverse

/-- A public number of doublings retains the modulus and workspace. -/
theorem double_mod_ok {s : State} {B : Addr} {Z o w wx m c : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hm : ModCtx s (off B o) (slot wx 8) wx minv m)
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 31) (hc1 : 1 ≤ c) (hc' : c < 2 ^ 31)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 c)
    (hlt : wv s.mem (off B o) (slot wx aR2) wx < m) :
    WP isa (doubles aN aAcc aTmp aR2 sCnt) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      wv t.mem (off B o) (slot wx aR2) wx =
        2 ^ c * wv s.mem (off B o) (slot wx aR2) wx % m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (doubles_ok hc.good.scr hc.rdi hc.hdr (Nat.le_refl _) hw hw'
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hc1 hc' hcx (by rw [hm.modulus]; exact hlt)) fun t ⟨hv, hf, hh, hk⟩ => ?_
  have hfc : Frm (off B o) (constantRanges wx) s.mem t.mem :=
    hf.mono (fun r hr => List.mem_cons_of_mem _ hr)
  have ht := hc.of_frmT hfc (constantRanges_work wx) hk.2.2 (hk.gpr (by decide))
  have hz := hc.good.scr.nowrap
  have hn := (hf.r2_wv hz (by decide) (by decide) (by decide) (by decide)).trans hm.modulus
  have hi : ((word t.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hf.r2_word hz (by decide) (by decide) (by decide) (by decide)]
    exact hm.inverse
  rw [hm.modulus] at hv
  refine ⟨ht, ⟨ht.good, hn, hi⟩, hv, ?_, hk⟩
  intro x hx
  apply hfc x
  intro r hr
  have hb := constantRanges_work wx r hr
  have h := hx (136, slot wx 8 + tabBytes wx - 136) (List.mem_singleton_self _)
  have : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  omega_using [hb, h]

/-- Reduction starts with ordinary zero and multiplier 256R, even for
composite moduli with zero high limbs. -/
theorem reduceSetup_ok (M : Mont) {s : State} {B : Addr} {Z o w wx m : Nat}
    {minv : BitVec 64} (hc : SubCtx s B Z o w wx minv)
    (hw : 2 ≤ wx) (hw48 : wx ≤ 48) (hm : 1 < m) (hodd : m % 2 = 1)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa (Arithmetic.reduceSetup M.mm) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      wv t.mem (off B o) (slot wx aR2) wx = 256 * 2 ^ (64 * wx) % m ∧
      wv t.mem (off B o) (slot wx aY) wx = 0 ∧
      wv t.mem (off B o) (slot wx aX) wx = 0 ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hw' : wx < 2 ^ 31 := by omega_using [hw48]
  have hz := hc.good.scr.nowrap
  unfold Arithmetic.reduceSetup seqs
  refine WP.seq (WP.mono (prepare_ok M hc hw hw48 hm hodd hn hinv)
    fun u ⟨hcu, hmu, huone, hur2, hfu, hku⟩ => ?_)
  refine WP.seq (WP.mono (mont_step M hmu (Nat.le_refl _) hw hw'
    (by unfold MmUse; decide) (by rw [huone]; exact hm))
    fun v ⟨hmv, hlt, hv, hfv, hkv⟩ => ?_)
  rw [huone, Nat.mul_one, hur2, show 128 * wx = 64 * wx + 64 * wx by omega_using [], Nat.pow_add, Nat.mod_mod] at hv
  have hvR : wv v.mem (off B o) (slot wx aR2) wx = 2 ^ (64 * wx) % m := by
    have e := VG.Proof.Bignum.mont_cancel (coprime_pow2 hodd (64 * wx)) hv
    simpa only [Nat.mod_eq_of_lt hlt] using e
  have hcv := arrays_context hcu hfv (by decide) hkv
  have hfw := hfu.trans (arrays_work hfv (by decide))
  have hkw := (hku.trans hkv).mono (show ∀ r ∈ mmRegs ++ mmRegs, r ∈ mmRegs by decide)
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun z =>
    z.gpr .rcx = 8 ∧ z.mem = v.mem) (by xrun) rfl) fun z ⟨⟨hcx, hmem⟩, hkz⟩ => ?_)
  have hcz : SubCtx z B Z o w wx minv := ⟨hcv.scr.congr hkz.2.2,
    (hkz.gpr (by decide)).trans hcv.rdi, hmem ▸ hcv.hdr, hmem ▸ hcv.link,
    hmem ▸ hcv.nw, hmem ▸ hcv.narr, hcv.lo, hcv.hi⟩
  have hmz : ModCtx z (off B o) (slot wx 8) wx minv m :=
    ⟨hcz.good, hmem ▸ hmv.modulus, hmem ▸ hmv.inverse⟩
  refine WP.seq (WP.mono (double_mod_ok hcz hmz hw hw' (by decide) (by decide)
    (c := 8) hcx (hmem ▸ hlt)) fun a ⟨hca, hma, ha, hfa, hka⟩ => ?_)
  rw [hmem, hvR, Nat.mul_mod_mod] at ha
  change wv a.mem (off B o) (slot wx aR2) wx = 256 * 2 ^ (64 * wx) % m at ha
  rw [hmem] at hfa
  refine WP.seq (WP.mono (clear_mod_ok hca hma hw hw' (by decide) (by decide))
    fun b ⟨hcb, hmb, hb, hfb, hkb⟩ => ?_)
  have bR := (hfb.wv_of_not_mem (show aR2 < 8 by decide) (by decide) hz).trans ha
  refine WP.mono (clear_mod_ok hcb hmb hw hw' (by decide) (by decide))
    fun t ⟨hct, hmt, ht, hft, hkt⟩ => ?_
  exact ⟨hct, hmt,
    (hft.wv_of_not_mem (by decide) (by decide) hz).trans bR,
    (hft.wv_of_not_mem (by decide) (by decide) hz).trans hb, ht,
    ((hfw.trans hfa).trans (arrays_work hfb (by decide))).trans (arrays_work hft (by decide)),
    ((((hkw.trans hkz).trans hka).trans hkb).trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.ReduceInit`, which this module and modules that import it used -/

section

/-! # Initial source and count for DSA modular reduction -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- A temporary header slot lies entirely in the mutable child region. -/
theorem header_work {B : Addr} {w i : Nat} {mem mem' : Mem}
    (hi : 17 ≤ i) (hi' : i < 32) (h : Outside B (8 * i) 8 mem mem') :
    Frm B (workRanges w) mem mem' := by
  intro x hx
  apply h x
  have hb := hx (136, slot w 8 + tabBytes w - 136) (List.mem_singleton_self _)
  have : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_using []
  omega

/-- Initialize source and count without touching the prepared arrays. -/
theorem reduceInit_ok {s : State} {B p : Addr} {Z o w wx m : Nat} {minv : BitVec 64}
    {bytes : List Byte} {sp sl : Nat}
    (hc : SubCtx s B Z o w wx minv) (hm : ModCtx s (off B o) (slot wx 8) wx minv m)
    (hsp : sp < 32) (hsl : sl < 32)
    (hp : word s.mem B (8 * sp) = p)
    (hl : word s.mem B (8 * sl) = BitVec.ofNat 64 bytes.length)
    (h64 : bytes.length < 2 ^ 64) :
    WP isa (.block (Arithmetic.reduceInit sp sl)) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      (∀ j < 8, wv t.mem (off B o) (slot wx j) wx = wv s.mem (off B o) (slot wx j) wx) ∧
      word t.mem (off B o) (8 * Crt.sSrc) = p ∧
      word t.mem (off B o) (8 * Crt.sRem) = BitVec.ofNat 64 bytes.length ∧
      t.zf = some (decide (bytes.length = 0)) ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hlo := hc.lo
  have hhi := hc.hi
  have hslot : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_using []
  have hcl := hdr_lt_slot wx 8 (show Crt.sLink < 32 by decide)
  have hcs := hdr_lt_slot wx 8 (show Crt.sSrc < 32 by decide)
  have hcr := hdr_lt_slot wx 8 (show Crt.sRem < 32 by decide)
  refine WP.mono (WP.keep [.rax, .rsi, .rcx] (Q := fun t =>
    t.mem = (s.mem.writeW (off (off B o) (8 * Crt.sSrc)) p).writeW
      (off (off B o) (8 * Crt.sRem)) (BitVec.ofNat 64 bytes.length) ∧
    t.zf = some (decide (bytes.length = 0))) ?_ rfl) fun t ⟨⟨hmem, hz⟩, hk⟩ => ?_
  · unfold Arithmetic.reduceInit
    xrun [State.ea, hdr, Crt.ws, hc.rdi, hdrOff, hc.link, hp, hl,
      hc.good.scr.ld (show 8 * Crt.sLink + 8 ≤ slot wx 8 by omega_using [hcl]),
      hc.scr.ld (show 8 * sp + 8 ≤ Z by omega_using [hsp, hlo, hhi, hslot]),
      hc.scr.ld (show 8 * sl + 8 ≤ Z by omega_using [hsl, hlo, hhi, hslot]),
      hc.good.scr.st (show 8 * Crt.sSrc + 8 ≤ slot wx 8 by omega_using [hcs]),
      hc.good.scr.st (show 8 * Crt.sRem + 8 ≤ slot wx 8 by omega_using [hcr]),
      BitVec.and_self, ofNat_beq_zero h64]
  have hs : Outside (off B o) (8 * Crt.sSrc) 8 s.mem
      (s.mem.writeW (off (off B o) (8 * Crt.sSrc)) p) := writeW_outside _ _ _ (by decide)
  have hr : Outside (off B o) (8 * Crt.sRem) 8
      (s.mem.writeW (off (off B o) (8 * Crt.sSrc)) p) t.mem := by
    rw [hmem]; exact writeW_outside _ _ _ (by decide)
  have hf := (header_work (by decide) (by decide) hs).trans (header_work (w := wx) (by decide) (by decide) hr)
  have ht := hc.of_frmT hf (workRanges_ok wx) hk.2.2 (hk.gpr (by decide))
  have hn := hc.good.scr.nowrap
  have harr : ∀ j < 8, wv t.mem (off B o) (slot wx j) wx = wv s.mem (off B o) (slot wx j) wx := by
    intro j hj
    rw [hmem, hdrStore_wv _ _ _ (by decide) hj hn, hdrStore_wv _ _ _ (by decide) hj hn]
  refine ⟨ht, ⟨ht.good, (harr aN (by decide)).trans hm.modulus, ?_⟩, harr, ?_, ?_, hz,
    hf, hk.mono (by decide)⟩
  · rw [hmem, hdrStore_word _ _ _ (by decide) (by decide) hn,
      hdrStore_word _ _ _ (by decide) (by decide) hn]
    exact hm.inverse
  · rw [hmem, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · rw [hmem, word_writeW_self]

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.Reduce`, which the modules that import this one used -/

section

/-! # Complete streaming modular reduction for DSA -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/ReduceLoop.lean`, which only this module imported.
section

/-! # The nonempty streaming reduction loop -/

section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- The loop consumes the entire source and computes its Horner reduction.
The measure is the public remaining-byte count; its invariant includes all
memory and register frames needed to return to the parent workspace. -/
theorem reduceLoop_ok (M : Mont) {s : State} {B p : Addr} {Z o w wx m acc : Nat}
    {minv : BitVec 64} {bytes : List Byte}
    (h : ReduceState s B Z o w wx m minv p bytes acc)
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 31) (hm : 255 < m) (hodd : m % 2 = 1)
    (hnonempty : 0 < bytes.length) (hlen : bytes.length < 2 ^ 64) :
    WP isa (.loop (Arithmetic.reduceByte M.mm) .ne) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      wv t.mem (off B o) (slot wx aY) wx = VG.Proof.Dsa.reduceBytes m acc bytes ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  let target := VG.Proof.Dsa.reduceBytes m acc bytes
  let Inv := fun n t => ∃ (ptr : Addr) (bs : List Byte) (a : Nat),
    bs.length = n ∧ 0 < n ∧ n < 2 ^ 64 ∧ ReduceState t B Z o w wx m minv ptr bs a ∧
    VG.Proof.Dsa.reduceBytes m a bs = target ∧
    Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t
  refine WP.loop (M := isa) (body := Arithmetic.reduceByte M.mm) (c := .ne) Inv ?_ bytes.length s ?_
  · intro n u ⟨ptr, bs, a, hlen', hpos, hbound, hu, htarget, hfu, hku⟩
    cases bs with
    | nil => simp only [List.length_nil] at hlen'; omega
    | cons b bs =>
      refine WP.mono (reduceByte_ok M hu hw hw' hm hodd (by omega))
        fun t ⟨ht, hz, hft, hkt⟩ => ?_
      have hf := hfu.trans hft
      have hk := (hku.trans hkt).mono (show ∀ r ∈ mmRegs ++ mmRegs, r ∈ mmRegs by decide)
      have htval : VG.Proof.Dsa.reduceBytes m ((256 * a + b.toNat) % m) bs = target := htarget
      by_cases he : bs.length = 0
      · left
        refine ⟨?_, ht.ctx, ht.modulus, ?_, hf, hk⟩
        · change VG.X86_64.eval .ne t = some false
          simp only [VG.X86_64.eval, hz, he, decide_true, Option.map_some, Bool.not_true]
        · have hempty := List.length_eq_zero_iff.mp he
          rw [hempty] at htval
          simp only [VG.Proof.Dsa.reduceBytes, List.foldl_nil, Nat.mod_eq_of_lt ht.reduced] at htval
          exact ht.value.trans htval
      · right
        refine ⟨?_, bs.length, by simp only [List.length_cons] at hlen'; omega,
          ptr + 1, bs, _, rfl, by omega, by simp only [List.length_cons] at hlen'; omega,
          ht, htval, hf, hk⟩
        change VG.X86_64.eval .ne t = some true
        simp only [VG.X86_64.eval, hz, he, decide_false, Option.map_some, Bool.not_false]
  · exact ⟨p, bytes, acc, rfl, hnonempty, hlen, h, rfl,
      fun _ _ => rfl, Keep.refl _ _⟩

end VG.Proof.Dsa.X86_64
end

end

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- Reduce an arbitrary big-endian byte string, including the empty string,
modulo an odd integer greater than 255. No primality or divisibility relation
between the source and destination moduli is required. -/
theorem reduce_ok (M : Mont) {s : State} {B p : Addr} {Z o w wx m : Nat}
    {minv : BitVec 64} {bytes : List Byte} {sp sl : Nat}
    (hc : SubCtx s B Z o w wx minv) (hw : 2 ≤ wx) (hw48 : wx ≤ 48)
    (hm : 255 < m) (hodd : m % 2 = 1)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hsp : sp < 32) (hsl : sl < 32)
    (hp : word s.mem B (8 * sp) = p)
    (hl : word s.mem B (8 * sl) = BitVec.ofNat 64 bytes.length)
    (hs : Src s B Z p bytes) (hlen : bytes.length < 2 ^ 64) :
    WP isa (Arithmetic.reduce M.mm sp sl) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      wv t.mem (off B o) (slot wx aY) wx = Spec.Dsa.decodeBE bytes % m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Arithmetic.reduce seqs
  refine WP.seq (WP.mono (reduceSetup_ok M hc hw hw48 (by omega_using [hm]) hodd hn hinv)
    fun u ⟨hcu, hmu, hur, huy, hux, hfu, hku⟩ => ?_)
  refine WP.seq (WP.mono (reduceInit_ok hcu hmu hsp hsl
    ((work_parent hc hfu hsp).trans hp) ((work_parent hc hfu hsl).trans hl) hlen)
    fun v ⟨hcv, hmv, harr, hvp, hvl, hvz, hfv, hkv⟩ => ?_)
  have hf := hfu.trans hfv
  have hk := (hku.trans hkv).mono (show ∀ r ∈ mmRegs ++ mmRegs, r ∈ mmRegs by decide)
  have hvy := (harr aY (by decide)).trans huy
  have hvx := (harr aX (by decide)).trans hux
  have hv : ReduceState v B Z o w wx m minv p bytes 0 :=
    ⟨hcv, hmv, (harr aR2 (by decide)).trans hur,
      fun i hi _ => (wv_eq_zero_iff _ _ _ _).mp hvx i hi,
      hvy, by omega_using [hm], hvp, hvl, work_source hc hf hk hs⟩
  by_cases he : bytes.length = 0
  · refine WP.ite true ?_ (fun _ => WP.block_nil ?_) (fun h => Bool.noConfusion h)
    · change VG.X86_64.eval .e v = some true
      simp only [VG.X86_64.eval, hvz, he, decide_true]
    · refine ⟨hcv, hmv, ?_, hf, hk⟩
      rw [List.length_eq_zero_iff.mp he]
      exact hvy
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => ?_)
    · change VG.X86_64.eval .e v = some false
      simp only [VG.X86_64.eval, hvz, he, decide_false]
    · refine WP.mono (reduceLoop_ok M hv hw (by omega_using [hw48]) hm hodd (by omega_using [he]) hlen)
        fun t ⟨hct, hmt, htval, hft, hkt⟩ => ?_
      rw [VG.Proof.Dsa.reduceBytes_eq] at htval
      exact ⟨hct, hmt, htval, hf.trans hft, (hk.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.Multiply`, which the modules that import this one used -/

section

/-! ### `Dsa.X86_64.Power`, which the modules that import this one used -/

section

/-! # DSA exponentiation, including conversion out of Montgomery form -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- The ordinary result of exponentiation, for an odd (possibly composite)
modulus. The exponent may be caller bytes or bytes in the scratch suffix. -/
theorem encodedPower_ok (M : Mont) (Sq : MontS) {s : State} {B : Addr} {Z o w wx m x : Nat}
    {minv : BitVec 64} (hc : SubCtx s B Z o w wx minv)
    (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hm : 1 < m) (hodd : m % 2 = 1)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hone : wv s.mem (off B o) (slot wx aOne) wx = 1)
    (hxl : wv s.mem (off B o) (slot wx Crt.aXc) wx < m)
    (hxc : wv s.mem (off B o) (slot wx Crt.aXc) wx % m = x * 2 ^ (64 * wx) % m)
    (hyl : wv s.mem (off B o) (slot wx aY) wx < m)
    (hyc : wv s.mem (off B o) (slot wx aY) wx % m = 2 ^ (64 * wx) % m)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb) :
    WP isa (Arithmetic.encodedPower Sq.mm M.mm sp sl) s fun t =>
      SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx = Spec.Dsa.powMod x (Spec.Dsa.decodeBE eb) m ∧
      ModCtx t (off B o) (slot wx 8) wx minv m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hmctx : ModCtx s (off B o) (slot wx 8) wx minv m := ⟨hc.good, hn, hinv⟩
  have hnZ := hc.good.scr.nowrap
  have hR := coprime_pow2 hodd (64 * wx)
  unfold Arithmetic.encodedPower
  refine WP.seq (WP.mono (expLoop_ok M Sq hc hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc
    hsp hsl hep hel hL1 hL2 he) fun u ⟨hu, hlt, hv, hf, hk⟩ => ?_)
  have hmu := modCtx_exp hmctx hu.good hf (Nat.le_refl _)
  have oneSep := crtExpRanges_arr wx (j := aOne) (by decide) (by decide) (by decide) (by decide) (by decide)
  have oneSlot := slot_le (w := wx) (show aOne < 8 by decide)
  have huone : wv u.mem (off B o) (slot wx aOne) wx = 1 :=
    (hf.wv_eq (fun r hr => by have := oneSep r hr; omega_using [this]) (by omega_using [hnZ, oneSlot])).trans hone
  refine WP.mono (mont_step M hmu (Nat.le_refl _) hw2 (by omega_using [hwx, hw30])
    (by unfold MmUse; decide) (by rw [huone]; exact hm)) fun t ⟨hmt, hlt', hv', hf', hk'⟩ => ?_
  rw [huone] at hv'
  have result := VG.Proof.Dsa.mont_decode hR hv hv'
  rw [Nat.mod_eq_of_lt hlt', Nat.mod_eq_of_lt (VG.Proof.Dsa.powMod_lt _ _ (by omega_using [hm]))] at result
  exact ⟨arrays_context hu hf' (by decide) hk', result, hmt,
    (exp_work hf).trans (arrays_work hf' (by decide)), (hk.trans hk').mono (by decide)⟩

/-- Exponentiation of an ordinary, possibly unreduced base, using the
prepared constants and an exponent from the parent call header. -/
theorem powerCore_ok (M : Mont) (Sq : MontS) {s : State} {B : Addr} {Z o w wx m x : Nat}
    {minv : BitVec 64} (hc : SubCtx s B Z o w wx minv)
    (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hm : 1 < m) (hodd : m % 2 = 1)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hone : wv s.mem (off B o) (slot wx aOne) wx = 1)
    (hx : wv s.mem (off B o) (slot wx aX) wx = x)
    (hR2 : wv s.mem (off B o) (slot wx aR2) wx = 2 ^ (128 * wx) % m)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb) :
    WP isa (Arithmetic.powerCore Sq.mm M.mm sp sl) s fun t =>
      SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx = Spec.Dsa.powMod x (Spec.Dsa.decodeBE eb) m ∧
      ModCtx t (off B o) (slot wx 8) wx minv m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hR2' : wv s.mem (off B o) (slot wx aR2) wx =
      (2 ^ (64 * wx) * 2 ^ (64 * wx)) % m := by
    rw [hR2, ← Nat.pow_add, show 64 * wx + 64 * wx = 128 * wx by omega_using []]
  unfold Arithmetic.powerCore
  refine WP.seq (WP.mono (encodePower_ok M ⟨hc.good, hn, hinv⟩ (Nat.le_refl _) hw2 (by omega_using [hwx, hw30])
    hm hodd hx hR2' hone) fun u ⟨hu, hux, huy, huone, hf, hk⟩ => ?_)
  have hcu := arrays_context hc hf (by decide) hk
  have hfu := arrays_work hf (by decide)
  have hsrc := work_source hc hfu hk he
  refine WP.mono (encodedPower_ok M Sq hcu hw2 hwx hw30 hm hodd hu.modulus hu.inverse huone
    (by rw [hux]; exact Nat.mod_lt _ (by omega_using [hm]))
    (by rw [hux, Nat.mod_mod])
    (by rw [huy]; exact Nat.mod_lt _ (by omega_using [hm]))
    (by rw [huy, Nat.mod_mod]) hsp hsl
    ((work_parent hc hfu hsp).trans hep) ((work_parent hc hfu hsl).trans hel) hL1 hL2 hsrc)
    fun t ⟨hct, hresult, hmt, hft, hkt⟩ =>
      ⟨hct, hresult, hmt, hfu.trans hft, (hk.trans hkt).mono (by decide)⟩

/-- Complete exponentiation, including constants setup and loading the base.
Both byte buffers remain valid when they occupy the inactive scratch suffix. -/
theorem power_ok (M : Mont) (Sq : MontS) {s : State} {B : Addr} {Z o w wx m : Nat}
    {minv : BitVec 64} (hc : SubCtx s B Z o w wx minv)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hm : 1 < m) (hodd : m % 2 = 1)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    {bp bl sp sl : Nat} (hbp : bp < 32) (hbl : bl < 32) (hsp : sp < 32) (hsl : sl < 32)
    {base exp : Addr} {bb eb : List Byte}
    (hb : word s.mem B (8 * bp) = base)
    (hblen : word s.mem B (8 * bl) = BitVec.ofNat 64 bb.length)
    (hbs : Src s B Z base bb) (hb1 : 1 ≤ bb.length) (hbw : (bb.length + 7) / 8 ≤ wx)
    (he : word s.mem B (8 * sp) = exp)
    (helen : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hes : Src s B Z exp eb) (he1 : 1 ≤ eb.length) (he2 : eb.length ≤ 1024) :
    WP isa (Arithmetic.power Sq.mm M.mm bp bl sp sl) s fun t =>
      SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx =
        Spec.Dsa.powMod (Spec.Dsa.decodeBE bb) (Spec.Dsa.decodeBE eb) m ∧
      ModCtx t (off B o) (slot wx 8) wx minv m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Arithmetic.power
  refine WP.seq (WP.mono (prepare_ok M hc hw2 hw48 hm hodd hn hinv)
    fun u ⟨hcu, hmu, huone, hur2, hfu, hku⟩ => ?_)
  refine WP.seq (WP.mono (load_ok hcu hw2 hwx hw30 (by decide) hbp hbl
    ((work_parent hc hfu hbp).trans hb) ((work_parent hc hfu hbl).trans hblen)
    (work_source hc hfu hku hbs) hb1 (by omega_using [hw48, hbw]) hbw)
    fun v ⟨hcv, hvbase, hfv, hkv⟩ => ?_)
  have hfa : Arrays (off B o) wx [aX] u.mem v.mem :=
    Arrays.of_outside (List.mem_singleton_self aX) hfv (Nat.le_refl _) (Nat.le_refl _)
  have hfw := arrays_work hfa (by decide)
  have hz := hcu.good.scr.nowrap
  have vn := (hfa.wv_of_not_mem (show aN < 8 by decide) (by decide) hz).trans hmu.modulus
  have vi : ((word v.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hfa.word0_of_not_mem (by decide) (by decide) hz (by omega_using [hw2])]
    exact hmu.inverse
  have vone := (hfa.wv_of_not_mem (show aOne < 8 by decide) (by decide) hz).trans huone
  have vr2 := (hfa.wv_of_not_mem (show aR2 < 8 by decide) (by decide) hz).trans hur2
  have hf := hfu.trans hfw
  have hk := (hku.trans hkv).mono (show ∀ r ∈ mmRegs ++ mmRegs, r ∈ mmRegs by decide)
  refine WP.mono (powerCore_ok M Sq hcv hw2 hwx hw30 hm hodd vn vi vone hvbase vr2
    hsp hsl ((work_parent hc hf hsp).trans he) ((work_parent hc hf hsl).trans helen)
    he1 he2 (work_source hc hf hk hes)) fun t ⟨hct, hresult, hmt, hft, hkt⟩ =>
      ⟨hct, hresult, hmt, hf.trans hft, (hk.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64

end

end

/-! # Complete ordinary modular multiplication for DSA -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- Load both ordinary operands, prepare Montgomery constants and produce
their reduced product. Neither input must already be reduced. -/
theorem product_ok (M : Mont) {s : State} {B : Addr} {Z o w wx m : Nat}
    {minv : BitVec 64} (hc : SubCtx s B Z o w wx minv)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hm : 1 < m) (hodd : m % 2 = 1)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    {ap al bp bl : Nat} (hap : ap < 32) (hal : al < 32) (hbp : bp < 32) (hbl : bl < 32)
    {pa pb : Addr} {ba bb : List Byte}
    (ha : word s.mem B (8 * ap) = pa)
    (halen : word s.mem B (8 * al) = BitVec.ofNat 64 ba.length)
    (has : Src s B Z pa ba) (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ wx)
    (hb : word s.mem B (8 * bp) = pb)
    (hblen : word s.mem B (8 * bl) = BitVec.ofNat 64 bb.length)
    (hbs : Src s B Z pb bb) (hb1 : 1 ≤ bb.length) (hbw : (bb.length + 7) / 8 ≤ wx) :
    WP isa (Arithmetic.product M.mm ap al bp bl) s fun t =>
      SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx = Spec.Dsa.decodeBE ba * Spec.Dsa.decodeBE bb % m ∧
      ModCtx t (off B o) (slot wx 8) wx minv m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Arithmetic.product seqs
  refine WP.seq (WP.mono (prepare_ok M hc hw2 hw48 hm hodd hn hinv)
    fun u ⟨hcu, hmu, huone, hur2, hfu, hku⟩ => ?_)
  refine WP.seq (WP.mono (load_mod_ok hcu hmu hw2 hwx hw30 (by decide) (by decide) hap hal
    ((work_parent hc hfu hap).trans ha) ((work_parent hc hfu hal).trans halen)
    (work_source hc hfu hku has) ha1 (by omega_using [hw48, haw]) haw)
    fun v ⟨hcv, hmv, hva, hkeepv, hfv, hkv⟩ => ?_)
  have hfs := hfu.trans hfv
  have hks := (hku.trans hkv).mono (show ∀ r ∈ mmRegs ++ mmRegs, r ∈ mmRegs by decide)
  refine WP.seq (WP.mono (load_mod_ok hcv hmv hw2 hwx hw30 (by decide) (by decide) hbp hbl
    ((work_parent hc hfs hbp).trans hb) ((work_parent hc hfs hbl).trans hblen)
    (work_source hc hfs hks hbs) hb1 (by omega_using [hw48, hbw]) hbw)
    fun z ⟨hcz, hmz, hzb, hkeepz, hfz, hkz⟩ => ?_)
  have hza := (hkeepz aX (by decide) (by decide)).trans hva
  have hzone := ((hkeepz aOne (by decide) (by decide)).trans
    (hkeepv aOne (by decide) (by decide))).trans huone
  have hzr2 := ((hkeepz aR2 (by decide) (by decide)).trans
    (hkeepv aR2 (by decide) (by decide))).trans hur2
  rw [show 128 * wx = 64 * wx + 64 * wx by omega_using [], Nat.pow_add] at hzr2
  refine WP.mono (productCore_ok M hmz (Nat.le_refl _) hw2 (by omega_using [hw48]) hm hodd hza hzb hzr2 hzone)
    fun t ⟨hmt, hresult, hft, hkt⟩ =>
      ⟨arrays_context hcz hft (by decide) hkt, hresult, hmt,
        (hfs.trans hfz).trans (arrays_work hft (by decide)),
        ((hks.trans hkz).trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64

end

end

/-! # Loading and adding reduced DSA scalars -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- The ordinary addition body used by signing. Inputs are reduced by the
preceding product and digest-reduction operations. -/
theorem add_ok {s : State} {B : Addr} {Z o w wx m : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hm : ModCtx s (off B o) (slot wx 8) wx minv m)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    {ap al bp bl : Nat} (hap : ap < 32) (hal : al < 32) (hbp : bp < 32) (hbl : bl < 32)
    {pa pb : Addr} {ba bb : List Byte}
    (ha : word s.mem B (8 * ap) = pa)
    (halen : word s.mem B (8 * al) = BitVec.ofNat 64 ba.length)
    (has : Src s B Z pa ba) (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ wx)
    (hb : word s.mem B (8 * bp) = pb)
    (hblen : word s.mem B (8 * bl) = BitVec.ofNat 64 bb.length)
    (hbs : Src s B Z pb bb) (hb1 : 1 ≤ bb.length) (hbw : (bb.length + 7) / 8 ≤ wx)
    (haReduced : Spec.Dsa.decodeBE ba < m) (hbReduced : Spec.Dsa.decodeBE bb < m) :
    WP isa (seqs [Arithmetic.load aX ap al, Arithmetic.load aXm bp bl, Crt.addMod aY aX aXm]) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      wv t.mem (off B o) (slot wx aY) wx = (Spec.Dsa.decodeBE ba + Spec.Dsa.decodeBE bb) % m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold seqs
  refine WP.seq (WP.mono (load_mod_ok hc hm hw2 hwx hw30 (by decide) (by decide) hap hal
    ha halen has ha1 (by omega_using [hw48, haw]) haw) fun u ⟨hcu, hmu, hua, _, hfu, hku⟩ => ?_)
  refine WP.seq (WP.mono (load_mod_ok hcu hmu hw2 hwx hw30 (by decide) (by decide) hbp hbl
    ((work_parent hc hfu hbp).trans hb) ((work_parent hc hfu hbl).trans hblen)
    (work_source hc hfu hku hbs) hb1 (by omega_using [hw48, hbw]) hbw) fun v ⟨hcv, hmv, hvb, hvkeep, hfv, hkv⟩ => ?_)
  have hva := (hvkeep aX (by decide) (by decide)).trans hua
  refine WP.mono (addMod_ok hcv.good.scr hcv.good.rdi hcv.good.hdr (Nat.le_refl _) hw2 (by omega_using [hw48])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hva, hmv.modulus]; exact haReduced) (by rw [hvb, hmv.modulus]; exact hbReduced))
    fun t ⟨htv, hft, hkt⟩ => ?_
  have hct := arrays_context hcv hft (by decide) hkt
  have hn := hcv.good.scr.nowrap
  have hnt := (hft.wv_of_not_mem (show aN < 8 by decide) (by decide) hn).trans hmv.modulus
  have hit : ((word t.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hft.word0_of_not_mem (by decide) (by decide) hn (by omega_using [hw2])]
    exact hmv.inverse
  rw [hva, hvb, hmv.modulus] at htv
  exact ⟨hct, ⟨hct.good, hnt, hit⟩, htv, (hfu.trans hfv).trans (arrays_work hft (by decide)),
    ((hku.trans hkv).trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64
